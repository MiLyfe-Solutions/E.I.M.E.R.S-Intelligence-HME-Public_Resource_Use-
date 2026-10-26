import V185TrunkScan20Chunk006

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_42421 : List Nat := [1, 3, 3, 2, 2, 1, 4, 2, 2]
def baseStart_42421 : Nat := 118140960795 + 42421 * 2 ^ 59
def prefixEnd_42421 : Nat := 4983230072969 + 3 ^ 40 * 42421 * 2
def baseEnd_42421 : Nat := 19362100306207787859925

theorem tailTrace_42421 : CollatzResearch.WordTrace tailWord_42421 prefixEnd_42421 19362100306207787859925 := by
  unfold tailWord_42421
  simp only [CollatzResearch.WordTrace]
  refine ⟨1547220979323436775111117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1031480652882291183407411 1547220979323436775111117)
  ·
    refine ⟨580207867246288790666669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1547220979323436775111117 580207867246288790666669)
    ·
      refine ⟨217577950217358296500001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 580207867246288790666669 217577950217358296500001)
      ·
        refine ⟨163183462663018722375001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217577950217358296500001 163183462663018722375001)
        ·
          refine ⟨122387596997264041781251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163183462663018722375001 122387596997264041781251)
          ·
            refine ⟨183581395495896062671877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122387596997264041781251 183581395495896062671877)
            ·
              refine ⟨34421511655480511750977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 183581395495896062671877 34421511655480511750977)
              ·
                refine ⟨25816133741610383813233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34421511655480511750977 25816133741610383813233)
                ·
                  refine ⟨19362100306207787859925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25816133741610383813233 19362100306207787859925)
                  ·
                    rfl

theorem cell20_42421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 2, 2].length) (baseStart_42421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42421 prefixEnd_42421 := by exact prefixLift 42421
  have htrace : WordTrace (prefixWord ++ tailWord_42421) baseStart_42421 baseEnd_42421 := by
    simpa [prefixWord, tailWord_42421, baseEnd_42421] using wordTrace_append hprefix tailTrace_42421
  have hstable : (prefixWord ++ tailWord_42421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42421).length < 2 ^ (prefixWord ++ tailWord_42421).sum := by decide
  have hdescent : baseEnd_42421 < baseStart_42421 := by decide
  rcases family_descends (prefixWord ++ tailWord_42421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42428 : List Nat := [2, 2, 2, 4, 3, 1, 1, 5]
def baseStart_42428 : Nat := 118140960795 + 42428 * 2 ^ 59
def prefixEnd_42428 : Nat := 4983230072969 + 3 ^ 40 * 42428 * 2
def baseEnd_42428 : Nat := 6455098432315624875521

theorem tailTrace_42428 : CollatzResearch.WordTrace tailWord_42428 prefixEnd_42428 6455098432315624875521 := by
  unfold tailWord_42428
  simp only [CollatzResearch.WordTrace]
  refine ⟨773738145149038485307969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1031650860198717980410625 773738145149038485307969)
  ·
    refine ⟨580303608861778863980977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 773738145149038485307969 580303608861778863980977)
    ·
      refine ⟨435227706646334147985733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 580303608861778863980977 435227706646334147985733)
      ·
        refine ⟨81605194996187652747325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 435227706646334147985733 81605194996187652747325)
        ·
          refine ⟨30601948123570369780247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81605194996187652747325 30601948123570369780247)
          ·
            refine ⟨45902922185355554670371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30601948123570369780247 45902922185355554670371)
            ·
              refine ⟨68854383278033332005557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45902922185355554670371 68854383278033332005557)
              ·
                refine ⟨6455098432315624875521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68854383278033332005557 6455098432315624875521)
                ·
                  rfl

theorem cell20_42428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 5].length) (baseStart_42428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42428 prefixEnd_42428 := by exact prefixLift 42428
  have htrace : WordTrace (prefixWord ++ tailWord_42428) baseStart_42428 baseEnd_42428 := by
    simpa [prefixWord, tailWord_42428, baseEnd_42428] using wordTrace_append hprefix tailTrace_42428
  have hstable : (prefixWord ++ tailWord_42428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42428).length < 2 ^ (prefixWord ++ tailWord_42428).sum := by decide
  have hdescent : baseEnd_42428 < baseStart_42428 := by decide
  rcases family_descends (prefixWord ++ tailWord_42428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42439 : List Nat := [1, 1, 4, 1, 1, 3, 1, 5, 3]
def baseStart_42439 : Nat := 118140960795 + 42439 * 2 ^ 59
def prefixEnd_42439 : Nat := 4983230072969 + 3 ^ 40 * 42439 * 2
def baseEnd_42439 : Nat := 19370315996679725259851

theorem tailTrace_42439 : CollatzResearch.WordTrace tailWord_42439 prefixEnd_42439 19370315996679725259851 := by
  unfold tailWord_42439
  simp only [CollatzResearch.WordTrace]
  refine ⟨1547877493258225849266371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1031918328838817232844247 1547877493258225849266371)
  ·
    refine ⟨2321816239887338773899557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1547877493258225849266371 2321816239887338773899557)
    ·
      refine ⟨435340544978876020106167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2321816239887338773899557 435340544978876020106167)
      ·
        refine ⟨653010817468314030159251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435340544978876020106167 653010817468314030159251)
        ·
          refine ⟨979516226202471045238877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 653010817468314030159251 979516226202471045238877)
          ·
            refine ⟨367318584825926641964579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 979516226202471045238877 367318584825926641964579)
            ·
              refine ⟨550977877238889962946869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 367318584825926641964579 550977877238889962946869)
              ·
                refine ⟨51654175991145934026269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 550977877238889962946869 51654175991145934026269)
                ·
                  refine ⟨19370315996679725259851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51654175991145934026269 19370315996679725259851)
                  ·
                    rfl

theorem cell20_42439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 3].length) (baseStart_42439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42439 prefixEnd_42439 := by exact prefixLift 42439
  have htrace : WordTrace (prefixWord ++ tailWord_42439) baseStart_42439 baseEnd_42439 := by
    simpa [prefixWord, tailWord_42439, baseEnd_42439] using wordTrace_append hprefix tailTrace_42439
  have hstable : (prefixWord ++ tailWord_42439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42439).length < 2 ^ (prefixWord ++ tailWord_42439).sum := by decide
  have hdescent : baseEnd_42439 < baseStart_42439 := by decide
  rcases family_descends (prefixWord ++ tailWord_42439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42446 : List Nat := [4, 1, 1, 1, 2, 1, 3, 1, 6]
def baseStart_42446 : Nat := 118140960795 + 42446 * 2 ^ 59
def prefixEnd_42446 : Nat := 4983230072969 + 3 ^ 40 * 42446 * 2
def baseEnd_42446 : Nat := 19373510987418812026489

theorem tailTrace_42446 : CollatzResearch.WordTrace tailWord_42446 prefixEnd_42446 19373510987418812026489 := by
  unfold tailWord_42446
  simp only [CollatzResearch.WordTrace]
  refine ⟨193516600529108255596399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1032088536155244029847461 193516600529108255596399)
  ·
    refine ⟨290274900793662383394599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193516600529108255596399 290274900793662383394599)
    ·
      refine ⟨435412351190493575091899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290274900793662383394599 435412351190493575091899)
      ·
        refine ⟨653118526785740362637849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435412351190493575091899 653118526785740362637849)
        ·
          refine ⟨489838895089305271978387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 653118526785740362637849 489838895089305271978387)
          ·
            refine ⟨734758342633957907967581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489838895089305271978387 734758342633957907967581)
            ·
              refine ⟨275534378487734215487843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 734758342633957907967581 275534378487734215487843)
              ·
                refine ⟨413301567731601323231765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275534378487734215487843 413301567731601323231765)
                ·
                  refine ⟨19373510987418812026489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 413301567731601323231765 19373510987418812026489)
                  ·
                    rfl

theorem cell20_42446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_42446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42446 prefixEnd_42446 := by exact prefixLift 42446
  have htrace : WordTrace (prefixWord ++ tailWord_42446) baseStart_42446 baseEnd_42446 := by
    simpa [prefixWord, tailWord_42446, baseEnd_42446] using wordTrace_append hprefix tailTrace_42446
  have hstable : (prefixWord ++ tailWord_42446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42446).length < 2 ^ (prefixWord ++ tailWord_42446).sum := by decide
  have hdescent : baseEnd_42446 < baseStart_42446 := by decide
  rcases family_descends (prefixWord ++ tailWord_42446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42508 : List Nat := [2, 2, 1, 2, 5, 1, 1, 6]
def baseStart_42508 : Nat := 118140960795 + 42508 * 2 ^ 59
def prefixEnd_42508 : Nat := 4983230072969 + 3 ^ 40 * 42508 * 2
def baseEnd_42508 : Nat := 6467269825607383986523

theorem tailTrace_42508 : CollatzResearch.WordTrace tailWord_42508 prefixEnd_42508 6467269825607383986523 := by
  unfold tailWord_42508
  simp only [CollatzResearch.WordTrace]
  refine ⟨775197065004125316764089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1033596086672167089018785 775197065004125316764089)
  ·
    refine ⟨581397798753093987573067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 775197065004125316764089 581397798753093987573067)
    ·
      refine ⟨872096698129640981359601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 581397798753093987573067 872096698129640981359601)
      ·
        refine ⟨654072523597230736019701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 872096698129640981359601 654072523597230736019701)
        ·
          refine ⟨61319299087240381501847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 654072523597230736019701 61319299087240381501847)
          ·
            refine ⟨91978948630860572252771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61319299087240381501847 91978948630860572252771)
            ·
              refine ⟨137968422946290858379157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91978948630860572252771 137968422946290858379157)
              ·
                refine ⟨6467269825607383986523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 137968422946290858379157 6467269825607383986523)
                ·
                  rfl

theorem cell20_42508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 6].length) (baseStart_42508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42508 prefixEnd_42508 := by exact prefixLift 42508
  have htrace : WordTrace (prefixWord ++ tailWord_42508) baseStart_42508 baseEnd_42508 := by
    simpa [prefixWord, tailWord_42508, baseEnd_42508] using wordTrace_append hprefix tailTrace_42508
  have hstable : (prefixWord ++ tailWord_42508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42508).length < 2 ^ (prefixWord ++ tailWord_42508).sum := by decide
  have hdescent : baseEnd_42508 < baseStart_42508 := by decide
  rcases family_descends (prefixWord ++ tailWord_42508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42529 : List Nat := [1, 2, 3, 2, 2, 2, 8]
def baseStart_42529 : Nat := 118140960795 + 42529 * 2 ^ 59
def prefixEnd_42529 : Nat := 4983230072969 + 3 ^ 40 * 42529 * 2
def baseEnd_42529 : Nat := 2156821605448823584387

theorem tailTrace_42529 : CollatzResearch.WordTrace tailWord_42529 prefixEnd_42529 2156821605448823584387 := by
  unfold tailWord_42529
  simp only [CollatzResearch.WordTrace]
  refine ⟨1551160062932171220042641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1034106708621447480028427 1551160062932171220042641)
  ·
    refine ⟨1163370047199128415031981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1551160062932171220042641 1163370047199128415031981)
    ·
      refine ⟨436263767699673155636993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1163370047199128415031981 436263767699673155636993)
      ·
        refine ⟨327197825774754866727745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 436263767699673155636993 327197825774754866727745)
        ·
          refine ⟨245398369331066150045809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 327197825774754866727745 245398369331066150045809)
          ·
            refine ⟨184048776998299612534357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245398369331066150045809 184048776998299612534357)
            ·
              refine ⟨2156821605448823584387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 184048776998299612534357 2156821605448823584387)
              ·
                rfl

theorem cell20_42529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 8].length) (baseStart_42529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42529 prefixEnd_42529 := by exact prefixLift 42529
  have htrace : WordTrace (prefixWord ++ tailWord_42529) baseStart_42529 baseEnd_42529 := by
    simpa [prefixWord, tailWord_42529, baseEnd_42529] using wordTrace_append hprefix tailTrace_42529
  have hstable : (prefixWord ++ tailWord_42529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42529).length < 2 ^ (prefixWord ++ tailWord_42529).sum := by decide
  have hdescent : baseEnd_42529 < baseStart_42529 := by decide
  rcases family_descends (prefixWord ++ tailWord_42529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42549 : List Nat := [1, 3, 3, 1, 1, 5, 2, 1, 3]
def baseStart_42549 : Nat := 118140960795 + 42549 * 2 ^ 59
def prefixEnd_42549 : Nat := 4983230072969 + 3 ^ 40 * 42549 * 2
def baseEnd_42549 : Nat := 19420522994008231592735

theorem tailTrace_42549 : CollatzResearch.WordTrace tailWord_42549 prefixEnd_42549 19420522994008231592735 := by
  unfold tailWord_42549
  simp only [CollatzResearch.WordTrace]
  refine ⟨1551889522859714635770701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1034593015239809757180467 1551889522859714635770701)
  ·
    refine ⟨581958571072392988414013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1551889522859714635770701 581958571072392988414013)
    ·
      refine ⟨218234464152147370655255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 581958571072392988414013 218234464152147370655255)
      ·
        refine ⟨327351696228221055982883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218234464152147370655255 327351696228221055982883)
        ·
          refine ⟨491027544342331583974325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327351696228221055982883 491027544342331583974325)
          ·
            refine ⟨46033832282093585997593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 491027544342331583974325 46033832282093585997593)
            ·
              refine ⟨34525374211570189498195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46033832282093585997593 34525374211570189498195)
              ·
                refine ⟨51788061317355284247293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34525374211570189498195 51788061317355284247293)
                ·
                  refine ⟨19420522994008231592735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51788061317355284247293 19420522994008231592735)
                  ·
                    rfl

theorem cell20_42549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 3].length) (baseStart_42549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42549 prefixEnd_42549 := by exact prefixLift 42549
  have htrace : WordTrace (prefixWord ++ tailWord_42549) baseStart_42549 baseEnd_42549 := by
    simpa [prefixWord, tailWord_42549, baseEnd_42549] using wordTrace_append hprefix tailTrace_42549
  have hstable : (prefixWord ++ tailWord_42549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42549).length < 2 ^ (prefixWord ++ tailWord_42549).sum := by decide
  have hdescent : baseEnd_42549 < baseStart_42549 := by decide
  rcases family_descends (prefixWord ++ tailWord_42549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42577 : List Nat := [1, 2, 2, 1, 3, 2, 2, 5, 2]
def baseStart_42577 : Nat := 118140960795 + 42577 * 2 ^ 59
def prefixEnd_42577 : Nat := 4983230072969 + 3 ^ 40 * 42577 * 2
def baseEnd_42577 : Nat := 19433302956964578659287

theorem tailTrace_42577 : CollatzResearch.WordTrace tailWord_42577 prefixEnd_42577 19433302956964578659287 := by
  unfold tailWord_42577
  simp only [CollatzResearch.WordTrace]
  refine ⟨1552910766758275417789985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1035273844505516945193323 1552910766758275417789985)
  ·
    refine ⟨1164683075068706563342489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1552910766758275417789985 1164683075068706563342489)
    ·
      refine ⟨873512306301529922506867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1164683075068706563342489 873512306301529922506867)
      ·
        refine ⟨1310268459452294883760301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 873512306301529922506867 1310268459452294883760301)
        ·
          refine ⟨491350672294610581410113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1310268459452294883760301 491350672294610581410113)
          ·
            refine ⟨368513004220957936057585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 491350672294610581410113 368513004220957936057585)
            ·
              refine ⟨276384753165718452043189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 368513004220957936057585 276384753165718452043189)
              ·
                refine ⟨25911070609286104879049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 276384753165718452043189 25911070609286104879049)
                ·
                  refine ⟨19433302956964578659287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25911070609286104879049 19433302956964578659287)
                  ·
                    rfl

theorem cell20_42577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 5, 2].length) (baseStart_42577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42577 prefixEnd_42577 := by exact prefixLift 42577
  have htrace : WordTrace (prefixWord ++ tailWord_42577) baseStart_42577 baseEnd_42577 := by
    simpa [prefixWord, tailWord_42577, baseEnd_42577] using wordTrace_append hprefix tailTrace_42577
  have hstable : (prefixWord ++ tailWord_42577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42577).length < 2 ^ (prefixWord ++ tailWord_42577).sum := by decide
  have hdescent : baseEnd_42577 < baseStart_42577 := by decide
  rcases family_descends (prefixWord ++ tailWord_42577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42642 : List Nat := [3, 2, 3, 1, 4, 1, 1, 2, 3]
def baseStart_42642 : Nat := 118140960795 + 42642 * 2 ^ 59
def prefixEnd_42642 : Nat := 4983230072969 + 3 ^ 40 * 42642 * 2
def baseEnd_42642 : Nat := 19462970728113241492355

theorem tailTrace_42642 : CollatzResearch.WordTrace tailWord_42642 prefixEnd_42642 19462970728113241492355 := by
  unfold tailWord_42642
  simp only [CollatzResearch.WordTrace]
  refine ⟨388820377880697879726545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1036854341015194345937453 388820377880697879726545)
  ·
    refine ⟨291615283410523409794909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 388820377880697879726545 291615283410523409794909)
    ·
      refine ⟨109355731278946278673091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291615283410523409794909 109355731278946278673091)
      ·
        refine ⟨164033596918419418009637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109355731278946278673091 164033596918419418009637)
        ·
          refine ⟨30756299422203640876807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164033596918419418009637 30756299422203640876807)
          ·
            refine ⟨46134449133305461315211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30756299422203640876807 46134449133305461315211)
            ·
              refine ⟨69201673699958191972817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46134449133305461315211 69201673699958191972817)
              ·
                refine ⟨51901255274968643979613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69201673699958191972817 51901255274968643979613)
                ·
                  refine ⟨19462970728113241492355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51901255274968643979613 19462970728113241492355)
                  ·
                    rfl

theorem cell20_42642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_42642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42642 prefixEnd_42642 := by exact prefixLift 42642
  have htrace : WordTrace (prefixWord ++ tailWord_42642) baseStart_42642 baseEnd_42642 := by
    simpa [prefixWord, tailWord_42642, baseEnd_42642] using wordTrace_append hprefix tailTrace_42642
  have hstable : (prefixWord ++ tailWord_42642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42642).length < 2 ^ (prefixWord ++ tailWord_42642).sum := by decide
  have hdescent : baseEnd_42642 < baseStart_42642 := by decide
  rcases family_descends (prefixWord ++ tailWord_42642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42674 : List Nat := [3, 2, 1, 1, 1, 2, 4, 2, 4]
def baseStart_42674 : Nat := 118140960795 + 42674 * 2 ^ 59
def prefixEnd_42674 : Nat := 4983230072969 + 3 ^ 40 * 42674 * 2
def baseEnd_42674 : Nat := 19477576400063352425557

theorem tailTrace_42674 : CollatzResearch.WordTrace tailWord_42674 prefixEnd_42674 19477576400063352425557 := by
  unfold tailWord_42674
  simp only [CollatzResearch.WordTrace]
  refine ⟨389112161851715246017769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1037632431604573989380717 389112161851715246017769)
  ·
    refine ⟨291834121388786434513327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 389112161851715246017769 291834121388786434513327)
    ·
      refine ⟨437751182083179651769991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291834121388786434513327 437751182083179651769991)
      ·
        refine ⟨656626773124769477654987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437751182083179651769991 656626773124769477654987)
        ·
          refine ⟨984940159687154216482481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 656626773124769477654987 984940159687154216482481)
          ·
            refine ⟨738705119765365662361861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 984940159687154216482481 738705119765365662361861)
            ·
              refine ⟨138507209956006061692849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 738705119765365662361861 138507209956006061692849)
              ·
                refine ⟨103880407467004546269637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138507209956006061692849 103880407467004546269637)
                ·
                  refine ⟨19477576400063352425557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103880407467004546269637 19477576400063352425557)
                  ·
                    rfl

theorem cell20_42674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_42674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42674 prefixEnd_42674 := by exact prefixLift 42674
  have htrace : WordTrace (prefixWord ++ tailWord_42674) baseStart_42674 baseEnd_42674 := by
    simpa [prefixWord, tailWord_42674, baseEnd_42674] using wordTrace_append hprefix tailTrace_42674
  have hstable : (prefixWord ++ tailWord_42674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42674).length < 2 ^ (prefixWord ++ tailWord_42674).sum := by decide
  have hdescent : baseEnd_42674 < baseStart_42674 := by decide
  rcases family_descends (prefixWord ++ tailWord_42674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42688 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 7]
def baseStart_42688 : Nat := 118140960795 + 42688 * 2 ^ 59
def prefixEnd_42688 : Nat := 4983230072969 + 3 ^ 40 * 42688 * 2
def baseEnd_42688 : Nat := 19483966381541525958833

theorem tailTrace_42688 : CollatzResearch.WordTrace tailWord_42688 prefixEnd_42688 19483966381541525958833 := by
  unfold tailWord_42688
  simp only [CollatzResearch.WordTrace]
  refine ⟨778479634678070687540359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1037972846237427583387145 778479634678070687540359)
  ·
    refine ⟨1167719452017106031310539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 778479634678070687540359 1167719452017106031310539)
    ·
      refine ⟨1751579178025659046965809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1167719452017106031310539 1751579178025659046965809)
      ·
        refine ⟨1313684383519244285224357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1751579178025659046965809 1313684383519244285224357)
        ·
          refine ⟨246315821909858303479567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1313684383519244285224357 246315821909858303479567)
          ·
            refine ⟨369473732864787455219351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246315821909858303479567 369473732864787455219351)
            ·
              refine ⟨554210599297181182829027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369473732864787455219351 554210599297181182829027)
              ·
                refine ⟨831315898945771774243541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 554210599297181182829027 831315898945771774243541)
                ·
                  refine ⟨19483966381541525958833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 831315898945771774243541 19483966381541525958833)
                  ·
                    rfl

theorem cell20_42688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_42688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42688 prefixEnd_42688 := by exact prefixLift 42688
  have htrace : WordTrace (prefixWord ++ tailWord_42688) baseStart_42688 baseEnd_42688 := by
    simpa [prefixWord, tailWord_42688, baseEnd_42688] using wordTrace_append hprefix tailTrace_42688
  have hstable : (prefixWord ++ tailWord_42688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42688).length < 2 ^ (prefixWord ++ tailWord_42688).sum := by decide
  have hdescent : baseEnd_42688 < baseStart_42688 := by decide
  rcases family_descends (prefixWord ++ tailWord_42688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42694 : List Nat := [6, 1, 2, 1, 1, 3, 6]
def baseStart_42694 : Nat := 118140960795 + 42694 * 2 ^ 59
def prefixEnd_42694 : Nat := 4983230072969 + 3 ^ 40 * 42694 * 2
def baseEnd_42694 : Nat := 2165189438336907973201

theorem tailTrace_42694 : CollatzResearch.WordTrace tailWord_42694 prefixEnd_42694 2165189438336907973201 := by
  unfold tailWord_42694
  simp only [CollatzResearch.WordTrace]
  refine ⟨48661815854200137493723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1038118738222936266532757 48661815854200137493723)
  ·
    refine ⟨72992723781300206240585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48661815854200137493723 72992723781300206240585)
    ·
      refine ⟨54744542835975154680439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72992723781300206240585 54744542835975154680439)
      ·
        refine ⟨82116814253962732020659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54744542835975154680439 82116814253962732020659)
        ·
          refine ⟨123175221380944098030989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82116814253962732020659 123175221380944098030989)
          ·
            refine ⟨46190708017854036761621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123175221380944098030989 46190708017854036761621)
            ·
              refine ⟨2165189438336907973201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46190708017854036761621 2165189438336907973201)
              ·
                rfl

theorem cell20_42694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 6].length) (baseStart_42694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42694 prefixEnd_42694 := by exact prefixLift 42694
  have htrace : WordTrace (prefixWord ++ tailWord_42694) baseStart_42694 baseEnd_42694 := by
    simpa [prefixWord, tailWord_42694, baseEnd_42694] using wordTrace_append hprefix tailTrace_42694
  have hstable : (prefixWord ++ tailWord_42694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42694).length < 2 ^ (prefixWord ++ tailWord_42694).sum := by decide
  have hdescent : baseEnd_42694 < baseStart_42694 := by decide
  rcases family_descends (prefixWord ++ tailWord_42694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42698 : List Nat := [3, 1, 2, 1, 5, 2, 6]
def baseStart_42698 : Nat := 118140960795 + 42698 * 2 ^ 59
def prefixEnd_42698 : Nat := 4983230072969 + 3 ^ 40 * 42698 * 2
def baseEnd_42698 : Nat := 2165392294891770625051

theorem tailTrace_42698 : CollatzResearch.WordTrace tailWord_42698 prefixEnd_42698 2165392294891770625051 := by
  unfold tailWord_42698
  simp only [CollatzResearch.WordTrace]
  refine ⟨389330999829978270736187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1038215999546608721963165 389330999829978270736187)
  ·
    refine ⟨583996499744967406104281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 389330999829978270736187 583996499744967406104281)
    ·
      refine ⟨437997374808725554578211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 583996499744967406104281 437997374808725554578211)
      ·
        refine ⟨656996062213088331867317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437997374808725554578211 656996062213088331867317)
        ·
          refine ⟨61593380832477031112561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 656996062213088331867317 61593380832477031112561)
          ·
            refine ⟨46195035624357773334421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61593380832477031112561 46195035624357773334421)
            ·
              refine ⟨2165392294891770625051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46195035624357773334421 2165392294891770625051)
              ·
                rfl

theorem cell20_42698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 6].length) (baseStart_42698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42698 prefixEnd_42698 := by exact prefixLift 42698
  have htrace : WordTrace (prefixWord ++ tailWord_42698) baseStart_42698 baseEnd_42698 := by
    simpa [prefixWord, tailWord_42698, baseEnd_42698] using wordTrace_append hprefix tailTrace_42698
  have hstable : (prefixWord ++ tailWord_42698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42698).length < 2 ^ (prefixWord ++ tailWord_42698).sum := by decide
  have hdescent : baseEnd_42698 < baseStart_42698 := by decide
  rcases family_descends (prefixWord ++ tailWord_42698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42708 : List Nat := [2, 4, 1, 3, 1, 3, 1, 1, 4]
def baseStart_42708 : Nat := 118140960795 + 42708 * 2 ^ 59
def prefixEnd_42708 : Nat := 4983230072969 + 3 ^ 40 * 42708 * 2
def baseEnd_42708 : Nat := 19493094926510345292085

theorem tailTrace_42708 : CollatzResearch.WordTrace tailWord_42708 prefixEnd_42708 19493094926510345292085 := by
  unfold tailWord_42708
  simp only [CollatzResearch.WordTrace]
  refine ⟨778844364641842395404389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1038459152855789860539185 778844364641842395404389)
  ·
    refine ⟨146033318370345449138323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 778844364641842395404389 146033318370345449138323)
    ·
      refine ⟨219049977555518173707485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146033318370345449138323 219049977555518173707485)
      ·
        refine ⟨82143741583319315140307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219049977555518173707485 82143741583319315140307)
        ·
          refine ⟨123215612374978972710461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82143741583319315140307 123215612374978972710461)
          ·
            refine ⟨46205854640617114766423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123215612374978972710461 46205854640617114766423)
            ·
              refine ⟨69308781960925672149635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46205854640617114766423 69308781960925672149635)
              ·
                refine ⟨103963172941388508224453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69308781960925672149635 103963172941388508224453)
                ·
                  refine ⟨19493094926510345292085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103963172941388508224453 19493094926510345292085)
                  ·
                    rfl

theorem cell20_42708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_42708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42708 prefixEnd_42708 := by exact prefixLift 42708
  have htrace : WordTrace (prefixWord ++ tailWord_42708) baseStart_42708 baseEnd_42708 := by
    simpa [prefixWord, tailWord_42708, baseEnd_42708] using wordTrace_append hprefix tailTrace_42708
  have hstable : (prefixWord ++ tailWord_42708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42708).length < 2 ^ (prefixWord ++ tailWord_42708).sum := by decide
  have hdescent : baseEnd_42708 < baseStart_42708 := by decide
  rcases family_descends (prefixWord ++ tailWord_42708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42719 : List Nat := [1, 1, 2, 3, 2, 2, 4, 5]
def baseStart_42719 : Nat := 118140960795 + 42719 * 2 ^ 59
def prefixEnd_42719 : Nat := 4983230072969 + 3 ^ 40 * 42719 * 2
def baseEnd_42719 : Nat := 6499371875414398641791

theorem tailTrace_42719 : CollatzResearch.WordTrace tailWord_42719 prefixEnd_42719 6499371875414398641791 := by
  unfold tailWord_42719
  simp only [CollatzResearch.WordTrace]
  refine ⟨1558089932243833669459211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1038726621495889112972807 1558089932243833669459211)
  ·
    refine ⟨2337134898365750504188817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1558089932243833669459211 2337134898365750504188817)
    ·
      refine ⟨1752851173774312878141613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2337134898365750504188817 1752851173774312878141613)
      ·
        refine ⟨657319190165367329303105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1752851173774312878141613 657319190165367329303105)
        ·
          refine ⟨492989392624025496977329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 657319190165367329303105 492989392624025496977329)
          ·
            refine ⟨369742044468019122732997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 492989392624025496977329 369742044468019122732997)
            ·
              refine ⟨69326633337753585512437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 369742044468019122732997 69326633337753585512437)
              ·
                refine ⟨6499371875414398641791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69326633337753585512437 6499371875414398641791)
                ·
                  rfl

theorem cell20_42719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 5].length) (baseStart_42719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42719 prefixEnd_42719 := by exact prefixLift 42719
  have htrace : WordTrace (prefixWord ++ tailWord_42719) baseStart_42719 baseEnd_42719 := by
    simpa [prefixWord, tailWord_42719, baseEnd_42719] using wordTrace_append hprefix tailTrace_42719
  have hstable : (prefixWord ++ tailWord_42719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42719).length < 2 ^ (prefixWord ++ tailWord_42719).sum := by decide
  have hdescent : baseEnd_42719 < baseStart_42719 := by decide
  rcases family_descends (prefixWord ++ tailWord_42719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42764 : List Nat := [2, 2, 1, 2, 2, 1, 2, 3, 5]
def baseStart_42764 : Nat := 118140960795 + 42764 * 2 ^ 59
def prefixEnd_42764 : Nat := 4983230072969 + 3 ^ 40 * 42764 * 2
def baseEnd_42764 : Nat := 19518654852423039425189

theorem tailTrace_42764 : CollatzResearch.WordTrace tailWord_42764 prefixEnd_42764 19518654852423039425189 := by
  unfold tailWord_42764
  simp only [CollatzResearch.WordTrace]
  refine ⟨779865608540403177423673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1039820811387204236564897 779865608540403177423673)
  ·
    refine ⟨584899206405302383067755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 779865608540403177423673 584899206405302383067755)
    ·
      refine ⟨877348809607953574601633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 584899206405302383067755 877348809607953574601633)
      ·
        refine ⟨658011607205965180951225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 877348809607953574601633 658011607205965180951225)
        ·
          refine ⟨493508705404473885713419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 658011607205965180951225 493508705404473885713419)
          ·
            refine ⟨740263058106710828570129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493508705404473885713419 740263058106710828570129)
            ·
              refine ⟨555197293580033121427597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 740263058106710828570129 555197293580033121427597)
              ·
                refine ⟨208198985092512420535349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 555197293580033121427597 208198985092512420535349)
                ·
                  refine ⟨19518654852423039425189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 208198985092512420535349 19518654852423039425189)
                  ·
                    rfl

theorem cell20_42764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_42764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42764 prefixEnd_42764 := by exact prefixLift 42764
  have htrace : WordTrace (prefixWord ++ tailWord_42764) baseStart_42764 baseEnd_42764 := by
    simpa [prefixWord, tailWord_42764, baseEnd_42764] using wordTrace_append hprefix tailTrace_42764
  have hstable : (prefixWord ++ tailWord_42764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42764).length < 2 ^ (prefixWord ++ tailWord_42764).sum := by decide
  have hdescent : baseEnd_42764 < baseStart_42764 := by decide
  rcases family_descends (prefixWord ++ tailWord_42764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42788 : List Nat := [2, 3, 1, 3, 2, 1, 1, 1, 6]
def baseStart_42788 : Nat := 118140960795 + 42788 * 2 ^ 59
def prefixEnd_42788 : Nat := 4983230072969 + 3 ^ 40 * 42788 * 2
def baseEnd_42788 : Nat := 19529609106385622625091

theorem tailTrace_42788 : CollatzResearch.WordTrace tailWord_42788 prefixEnd_42788 19529609106385622625091 := by
  unfold tailWord_42788
  simp only [CollatzResearch.WordTrace]
  refine ⟨780303284496929226860509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1040404379329238969147345 780303284496929226860509)
  ·
    refine ⟨292613731686348460072691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 780303284496929226860509 292613731686348460072691)
    ·
      refine ⟨438920597529522690109037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292613731686348460072691 438920597529522690109037)
      ·
        refine ⟨164595224073571008790889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 438920597529522690109037 164595224073571008790889)
        ·
          refine ⟨123446418055178256593167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164595224073571008790889 123446418055178256593167)
          ·
            refine ⟨185169627082767384889751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123446418055178256593167 185169627082767384889751)
            ·
              refine ⟨277754440624151077334627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185169627082767384889751 277754440624151077334627)
              ·
                refine ⟨416631660936226616001941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 277754440624151077334627 416631660936226616001941)
                ·
                  refine ⟨19529609106385622625091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 416631660936226616001941 19529609106385622625091)
                  ·
                    rfl

theorem cell20_42788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_42788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42788 prefixEnd_42788 := by exact prefixLift 42788
  have htrace : WordTrace (prefixWord ++ tailWord_42788) baseStart_42788 baseEnd_42788 := by
    simpa [prefixWord, tailWord_42788, baseEnd_42788] using wordTrace_append hprefix tailTrace_42788
  have hstable : (prefixWord ++ tailWord_42788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42788).length < 2 ^ (prefixWord ++ tailWord_42788).sum := by decide
  have hdescent : baseEnd_42788 < baseStart_42788 := by decide
  rcases family_descends (prefixWord ++ tailWord_42788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42815 : List Nat := [1, 1, 2, 2, 7, 1, 1, 2, 3]
def baseStart_42815 : Nat := 118140960795 + 42815 * 2 ^ 59
def prefixEnd_42815 : Nat := 4983230072969 + 3 ^ 40 * 42815 * 2
def baseEnd_42815 : Nat := 19541932642093528724981

theorem tailTrace_42815 : CollatzResearch.WordTrace tailWord_42815 prefixEnd_42815 19541932642093528724981 := by
  unfold tailWord_42815
  simp only [CollatzResearch.WordTrace]
  refine ⟨1561591339896042064953899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1041060893264028043302599 1561591339896042064953899)
  ·
    refine ⟨2342387009844063097430849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1561591339896042064953899 2342387009844063097430849)
    ·
      refine ⟨1756790257383047323073137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2342387009844063097430849 1756790257383047323073137)
      ·
        refine ⟨1317592693037285492304853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1756790257383047323073137 1317592693037285492304853)
        ·
          refine ⟨30881078743061378725895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 1317592693037285492304853 30881078743061378725895)
          ·
            refine ⟨46321618114592068088843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30881078743061378725895 46321618114592068088843)
            ·
              refine ⟨69482427171888102133265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46321618114592068088843 69482427171888102133265)
              ·
                refine ⟨52111820378916076599949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69482427171888102133265 52111820378916076599949)
                ·
                  refine ⟨19541932642093528724981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52111820378916076599949 19541932642093528724981)
                  ·
                    rfl

theorem cell20_42815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 3].length) (baseStart_42815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42815 prefixEnd_42815 := by exact prefixLift 42815
  have htrace : WordTrace (prefixWord ++ tailWord_42815) baseStart_42815 baseEnd_42815 := by
    simpa [prefixWord, tailWord_42815, baseEnd_42815] using wordTrace_append hprefix tailTrace_42815
  have hstable : (prefixWord ++ tailWord_42815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42815).length < 2 ^ (prefixWord ++ tailWord_42815).sum := by decide
  have hdescent : baseEnd_42815 < baseStart_42815 := by decide
  rcases family_descends (prefixWord ++ tailWord_42815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42819 : List Nat := [1, 1, 1, 3, 1, 5, 3, 2, 3]
def baseStart_42819 : Nat := 118140960795 + 42819 * 2 ^ 59
def prefixEnd_42819 : Nat := 4983230072969 + 3 ^ 40 * 42819 * 2
def baseEnd_42819 : Nat := 19543758351087292591631

theorem tailTrace_42819 : CollatzResearch.WordTrace tailWord_42819 prefixEnd_42819 19543758351087292591631 := by
  unfold tailWord_42819
  simp only [CollatzResearch.WordTrace]
  refine ⟨1561737231881550748099511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1041158154587700498733007 1561737231881550748099511)
  ·
    refine ⟨2342605847822326122149267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1561737231881550748099511 2342605847822326122149267)
    ·
      refine ⟨3513908771733489183223901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2342605847822326122149267 3513908771733489183223901)
      ·
        refine ⟨1317715789400058443708963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3513908771733489183223901 1317715789400058443708963)
        ·
          refine ⟨1976573684100087665563445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1317715789400058443708963 1976573684100087665563445)
          ·
            refine ⟨185303782884383218646573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1976573684100087665563445 185303782884383218646573)
            ·
              refine ⟨69488918581643706992465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 185303782884383218646573 69488918581643706992465)
              ·
                refine ⟨52116688936232780244349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69488918581643706992465 52116688936232780244349)
                ·
                  refine ⟨19543758351087292591631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52116688936232780244349 19543758351087292591631)
                  ·
                    rfl

theorem cell20_42819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 3].length) (baseStart_42819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42819 prefixEnd_42819 := by exact prefixLift 42819
  have htrace : WordTrace (prefixWord ++ tailWord_42819) baseStart_42819 baseEnd_42819 := by
    simpa [prefixWord, tailWord_42819, baseEnd_42819] using wordTrace_append hprefix tailTrace_42819
  have hstable : (prefixWord ++ tailWord_42819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42819).length < 2 ^ (prefixWord ++ tailWord_42819).sum := by decide
  have hdescent : baseEnd_42819 < baseStart_42819 := by decide
  rcases family_descends (prefixWord ++ tailWord_42819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42822 : List Nat := [6, 1, 1, 2, 1, 1, 1, 3, 4]
def baseStart_42822 : Nat := 118140960795 + 42822 * 2 ^ 59
def prefixEnd_42822 : Nat := 4983230072969 + 3 ^ 40 * 42822 * 2
def baseEnd_42822 : Nat := 19545127632832615491619

theorem tailTrace_42822 : CollatzResearch.WordTrace tailWord_42822 prefixEnd_42822 19545127632832615491619 := by
  unfold tailWord_42822
  simp only [CollatzResearch.WordTrace]
  refine ⟨48807707839708820639335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1041231100580454840305813 48807707839708820639335)
  ·
    refine ⟨73211561759563230959003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48807707839708820639335 73211561759563230959003)
    ·
      refine ⟨109817342639344846438505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73211561759563230959003 109817342639344846438505)
      ·
        refine ⟨82363006979508634828879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109817342639344846438505 82363006979508634828879)
        ·
          refine ⟨123544510469262952243319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82363006979508634828879 123544510469262952243319)
          ·
            refine ⟨185316765703894428364979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123544510469262952243319 185316765703894428364979)
            ·
              refine ⟨277975148555841642547469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185316765703894428364979 277975148555841642547469)
              ·
                refine ⟨104240680708440615955301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 277975148555841642547469 104240680708440615955301)
                ·
                  refine ⟨19545127632832615491619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 104240680708440615955301 19545127632832615491619)
                  ·
                    rfl

theorem cell20_42822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_42822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42822 prefixEnd_42822 := by exact prefixLift 42822
  have htrace : WordTrace (prefixWord ++ tailWord_42822) baseStart_42822 baseEnd_42822 := by
    simpa [prefixWord, tailWord_42822, baseEnd_42822] using wordTrace_append hprefix tailTrace_42822
  have hstable : (prefixWord ++ tailWord_42822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42822).length < 2 ^ (prefixWord ++ tailWord_42822).sum := by decide
  have hdescent : baseEnd_42822 < baseStart_42822 := by decide
  rcases family_descends (prefixWord ++ tailWord_42822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42826 : List Nat := [3, 1, 2, 1, 1, 1, 6, 1, 4]
def baseStart_42826 : Nat := 118140960795 + 42826 * 2 ^ 59
def prefixEnd_42826 : Nat := 4983230072969 + 3 ^ 40 * 42826 * 2
def baseEnd_42826 : Nat := 19546953341826379358269

theorem tailTrace_42826 : CollatzResearch.WordTrace tailWord_42826 prefixEnd_42826 19546953341826379358269 := by
  unfold tailWord_42826
  simp only [CollatzResearch.WordTrace]
  refine ⟨390498135714047735901083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1041328361904127295736221 390498135714047735901083)
  ·
    refine ⟨585747203571071603851625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 390498135714047735901083 585747203571071603851625)
    ·
      refine ⟨439310402678303702888719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 585747203571071603851625 439310402678303702888719)
      ·
        refine ⟨658965604017455554333079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 439310402678303702888719 658965604017455554333079)
        ·
          refine ⟨988448406026183331499619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 658965604017455554333079 988448406026183331499619)
          ·
            refine ⟨1482672609039274997249429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 988448406026183331499619 1482672609039274997249429)
            ·
              refine ⟨69500278548716015496067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1482672609039274997249429 69500278548716015496067)
              ·
                refine ⟨104250417823074023244101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69500278548716015496067 104250417823074023244101)
                ·
                  refine ⟨19546953341826379358269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 104250417823074023244101 19546953341826379358269)
                  ·
                    rfl

theorem cell20_42826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_42826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42826 prefixEnd_42826 := by exact prefixLift 42826
  have htrace : WordTrace (prefixWord ++ tailWord_42826) baseStart_42826 baseEnd_42826 := by
    simpa [prefixWord, tailWord_42826, baseEnd_42826] using wordTrace_append hprefix tailTrace_42826
  have hstable : (prefixWord ++ tailWord_42826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42826).length < 2 ^ (prefixWord ++ tailWord_42826).sum := by decide
  have hdescent : baseEnd_42826 < baseStart_42826 := by decide
  rcases family_descends (prefixWord ++ tailWord_42826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42850 : List Nat := [3, 3, 2, 1, 2, 2, 1, 6]
def baseStart_42850 : Nat := 118140960795 + 42850 * 2 ^ 59
def prefixEnd_42850 : Nat := 4983230072969 + 3 ^ 40 * 42850 * 2
def baseEnd_42850 : Nat := 6519302531929654186057

theorem tailTrace_42850 : CollatzResearch.WordTrace tailWord_42850 prefixEnd_42850 6519302531929654186057 := by
  unfold tailWord_42850
  simp only [CollatzResearch.WordTrace]
  refine ⟨390716973692310760619501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1041911929846162028318669 390716973692310760619501)
  ·
    refine ⟨146518865134616535232313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 390716973692310760619501 146518865134616535232313)
    ·
      refine ⟨109889148850962401424235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146518865134616535232313 109889148850962401424235)
      ·
        refine ⟨164833723276443602136353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109889148850962401424235 164833723276443602136353)
        ·
          refine ⟨123625292457332701602265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164833723276443602136353 123625292457332701602265)
          ·
            refine ⟨92718969342999526201699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123625292457332701602265 92718969342999526201699)
            ·
              refine ⟨139078454014499289302549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92718969342999526201699 139078454014499289302549)
              ·
                refine ⟨6519302531929654186057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 139078454014499289302549 6519302531929654186057)
                ·
                  rfl

theorem cell20_42850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_42850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42850 prefixEnd_42850 := by exact prefixLift 42850
  have htrace : WordTrace (prefixWord ++ tailWord_42850) baseStart_42850 baseEnd_42850 := by
    simpa [prefixWord, tailWord_42850, baseEnd_42850] using wordTrace_append hprefix tailTrace_42850
  have hstable : (prefixWord ++ tailWord_42850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42850).length < 2 ^ (prefixWord ++ tailWord_42850).sum := by decide
  have hdescent : baseEnd_42850 < baseStart_42850 := by decide
  rcases family_descends (prefixWord ++ tailWord_42850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42860 : List Nat := [2, 2, 1, 1, 4, 4, 1, 3, 2]
def baseStart_42860 : Nat := 118140960795 + 42860 * 2 ^ 59
def prefixEnd_42860 : Nat := 4983230072969 + 3 ^ 40 * 42860 * 2
def baseEnd_42860 : Nat := 19562471868273372224797

theorem tailTrace_42860 : CollatzResearch.WordTrace tailWord_42860 prefixEnd_42860 19562471868273372224797 := by
  unfold tailWord_42860
  simp only [CollatzResearch.WordTrace]
  refine ⟨781616312366507375171017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1042155083155343166894689 781616312366507375171017)
  ·
    refine ⟨586212234274880531378263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 781616312366507375171017 586212234274880531378263)
    ·
      refine ⟨879318351412320797067395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 586212234274880531378263 879318351412320797067395)
      ·
        refine ⟨1318977527118481195601093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 879318351412320797067395 1318977527118481195601093)
        ·
          refine ⟨247308286334715224175205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1318977527118481195601093 247308286334715224175205)
          ·
            refine ⟨46370303687759104532851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 247308286334715224175205 46370303687759104532851)
            ·
              refine ⟨69555455531638656799277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46370303687759104532851 69555455531638656799277)
              ·
                refine ⟨26083295824364496299729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69555455531638656799277 26083295824364496299729)
                ·
                  refine ⟨19562471868273372224797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26083295824364496299729 19562471868273372224797)
                  ·
                    rfl

theorem cell20_42860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 3, 2].length) (baseStart_42860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42860 prefixEnd_42860 := by exact prefixLift 42860
  have htrace : WordTrace (prefixWord ++ tailWord_42860) baseStart_42860 baseEnd_42860 := by
    simpa [prefixWord, tailWord_42860, baseEnd_42860] using wordTrace_append hprefix tailTrace_42860
  have hstable : (prefixWord ++ tailWord_42860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42860).length < 2 ^ (prefixWord ++ tailWord_42860).sum := by decide
  have hdescent : baseEnd_42860 < baseStart_42860 := by decide
  rcases family_descends (prefixWord ++ tailWord_42860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42888 : List Nat := [2, 1, 3, 3, 3, 1, 2, 5]
def baseStart_42888 : Nat := 118140960795 + 42888 * 2 ^ 59
def prefixEnd_42888 : Nat := 4983230072969 + 3 ^ 40 * 42888 * 2
def baseEnd_42888 : Nat := 6525083943743239763783

theorem tailTrace_42888 : CollatzResearch.WordTrace tailWord_42888 prefixEnd_42888 6525083943743239763783 := by
  unfold tailWord_42888
  simp only [CollatzResearch.WordTrace]
  refine ⟨782126934315787766180659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1042835912421050354907545 782126934315787766180659)
  ·
    refine ⟨1173190401473681649270989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 782126934315787766180659 1173190401473681649270989)
    ·
      refine ⟨439946400552630618476621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1173190401473681649270989 439946400552630618476621)
      ·
        refine ⟨164979900207236481928733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 439946400552630618476621 164979900207236481928733)
        ·
          refine ⟨61867462577713680723275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164979900207236481928733 61867462577713680723275)
          ·
            refine ⟨92801193866570521084913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61867462577713680723275 92801193866570521084913)
            ·
              refine ⟨69600895399927890813685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92801193866570521084913 69600895399927890813685)
              ·
                refine ⟨6525083943743239763783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69600895399927890813685 6525083943743239763783)
                ·
                  rfl

theorem cell20_42888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 5].length) (baseStart_42888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42888 prefixEnd_42888 := by exact prefixLift 42888
  have htrace : WordTrace (prefixWord ++ tailWord_42888) baseStart_42888 baseEnd_42888 := by
    simpa [prefixWord, tailWord_42888, baseEnd_42888] using wordTrace_append hprefix tailTrace_42888
  have hstable : (prefixWord ++ tailWord_42888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42888).length < 2 ^ (prefixWord ++ tailWord_42888).sum := by decide
  have hdescent : baseEnd_42888 < baseStart_42888 := by decide
  rcases family_descends (prefixWord ++ tailWord_42888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42909 : List Nat := [1, 4, 2, 1, 2, 2, 2, 6]
def baseStart_42909 : Nat := 118140960795 + 42909 * 2 ^ 59
def prefixEnd_42909 : Nat := 4983230072969 + 3 ^ 40 * 42909 * 2
def baseEnd_42909 : Nat := 6528278934482326530421

theorem tailTrace_42909 : CollatzResearch.WordTrace tailWord_42909 prefixEnd_42909 6528278934482326530421 := by
  unfold tailWord_42909
  simp only [CollatzResearch.WordTrace]
  refine ⟨1565019801555496118875781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1043346534370330745917187 1565019801555496118875781)
  ·
    refine ⟨293441212791655522289209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1565019801555496118875781 293441212791655522289209)
    ·
      refine ⟨220080909593741641716907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293441212791655522289209 220080909593741641716907)
      ·
        refine ⟨330121364390612462575361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220080909593741641716907 330121364390612462575361)
        ·
          refine ⟨247591023292959346931521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330121364390612462575361 247591023292959346931521)
          ·
            refine ⟨185693267469719510198641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247591023292959346931521 185693267469719510198641)
            ·
              refine ⟨139269950602289632648981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185693267469719510198641 139269950602289632648981)
              ·
                refine ⟨6528278934482326530421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 139269950602289632648981 6528278934482326530421)
                ·
                  rfl

theorem cell20_42909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 6].length) (baseStart_42909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42909 prefixEnd_42909 := by exact prefixLift 42909
  have htrace : WordTrace (prefixWord ++ tailWord_42909) baseStart_42909 baseEnd_42909 := by
    simpa [prefixWord, tailWord_42909, baseEnd_42909] using wordTrace_append hprefix tailTrace_42909
  have hstable : (prefixWord ++ tailWord_42909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42909).length < 2 ^ (prefixWord ++ tailWord_42909).sum := by decide
  have hdescent : baseEnd_42909 < baseStart_42909 := by decide
  rcases family_descends (prefixWord ++ tailWord_42909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42933 : List Nat := [1, 3, 3, 2, 1, 2, 1, 4, 3]
def baseStart_42933 : Nat := 118140960795 + 42933 * 2 ^ 59
def prefixEnd_42933 : Nat := 4983230072969 + 3 ^ 40 * 42933 * 2
def baseEnd_42933 : Nat := 19595791057409562791165

theorem tailTrace_42933 : CollatzResearch.WordTrace tailWord_42933 prefixEnd_42933 19595791057409562791165 := by
  unfold tailWord_42933
  simp only [CollatzResearch.WordTrace]
  refine ⟨1565895153468548217749453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1043930102312365478499635 1565895153468548217749453)
  ·
    refine ⟨587210682550705581656045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1565895153468548217749453 587210682550705581656045)
    ·
      refine ⟨220204005956514593121017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 587210682550705581656045 220204005956514593121017)
      ·
        refine ⟨165153004467385944840763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220204005956514593121017 165153004467385944840763)
        ·
          refine ⟨247729506701078917261145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165153004467385944840763 247729506701078917261145)
          ·
            refine ⟨185797130025809187945859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247729506701078917261145 185797130025809187945859)
            ·
              refine ⟨278695695038713781918789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185797130025809187945859 278695695038713781918789)
              ·
                refine ⟨52255442819758834109773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 278695695038713781918789 52255442819758834109773)
                ·
                  refine ⟨19595791057409562791165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52255442819758834109773 19595791057409562791165)
                  ·
                    rfl

theorem cell20_42933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_42933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42933 prefixEnd_42933 := by exact prefixLift 42933
  have htrace : WordTrace (prefixWord ++ tailWord_42933) baseStart_42933 baseEnd_42933 := by
    simpa [prefixWord, tailWord_42933, baseEnd_42933] using wordTrace_append hprefix tailTrace_42933
  have hstable : (prefixWord ++ tailWord_42933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42933).length < 2 ^ (prefixWord ++ tailWord_42933).sum := by decide
  have hdescent : baseEnd_42933 < baseStart_42933 := by decide
  rcases family_descends (prefixWord ++ tailWord_42933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_42964 : List Nat := [2, 4, 1, 2, 1, 1, 5, 4]
def baseStart_42964 : Nat := 118140960795 + 42964 * 2 ^ 59
def prefixEnd_42964 : Nat := 4983230072969 + 3 ^ 40 * 42964 * 2
def baseEnd_42964 : Nat := 6536646767370410919235

theorem tailTrace_42964 : CollatzResearch.WordTrace tailWord_42964 prefixEnd_42964 6536646767370410919235 := by
  unfold tailWord_42964
  simp only [CollatzResearch.WordTrace]
  refine ⟨783512908178120256063973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1044683877570827008085297 783512908178120256063973)
  ·
    refine ⟨146908670283397548011995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 783512908178120256063973 146908670283397548011995)
    ·
      refine ⟨220363005425096322017993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146908670283397548011995 220363005425096322017993)
      ·
        refine ⟨165272254068822241513495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220363005425096322017993 165272254068822241513495)
        ·
          refine ⟨247908381103233362270243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165272254068822241513495 247908381103233362270243)
          ·
            refine ⟨371862571654850043405365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247908381103233362270243 371862571654850043405365)
            ·
              refine ⟨34862116092642191569253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 371862571654850043405365 34862116092642191569253)
              ·
                refine ⟨6536646767370410919235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34862116092642191569253 6536646767370410919235)
                ·
                  rfl

theorem cell20_42964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 4].length) (baseStart_42964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_42964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_42964 prefixEnd_42964 := by exact prefixLift 42964
  have htrace : WordTrace (prefixWord ++ tailWord_42964) baseStart_42964 baseEnd_42964 := by
    simpa [prefixWord, tailWord_42964, baseEnd_42964] using wordTrace_append hprefix tailTrace_42964
  have hstable : (prefixWord ++ tailWord_42964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_42964).length < 2 ^ (prefixWord ++ tailWord_42964).sum := by decide
  have hdescent : baseEnd_42964 < baseStart_42964 := by decide
  rcases family_descends (prefixWord ++ tailWord_42964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43029 : List Nat := [1, 3, 2, 1, 6, 1, 1, 3, 2]
def baseStart_43029 : Nat := 118140960795 + 43029 * 2 ^ 59
def prefixEnd_43029 : Nat := 4983230072969 + 3 ^ 40 * 43029 * 2
def baseEnd_43029 : Nat := 19639608073259895590773

theorem tailTrace_43029 : CollatzResearch.WordTrace tailWord_43029 prefixEnd_43029 19639608073259895590773 := by
  unfold tailWord_43029
  simp only [CollatzResearch.WordTrace]
  refine ⟨1569396561120756613244141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1046264374080504408829427 1569396561120756613244141)
  ·
    refine ⟨588523710420283729966553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1569396561120756613244141 588523710420283729966553)
    ·
      refine ⟨441392782815212797474915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 588523710420283729966553 441392782815212797474915)
      ·
        refine ⟨662089174222819196212373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 441392782815212797474915 662089174222819196212373)
        ·
          refine ⟨31035430041694649822455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 662089174222819196212373 31035430041694649822455)
          ·
            refine ⟨46553145062541974733683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31035430041694649822455 46553145062541974733683)
            ·
              refine ⟨69829717593812962100525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46553145062541974733683 69829717593812962100525)
              ·
                refine ⟨26186144097679860787697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69829717593812962100525 26186144097679860787697)
                ·
                  refine ⟨19639608073259895590773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26186144097679860787697 19639608073259895590773)
                  ·
                    rfl

theorem cell20_43029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 3, 2].length) (baseStart_43029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43029 prefixEnd_43029 := by exact prefixLift 43029
  have htrace : WordTrace (prefixWord ++ tailWord_43029) baseStart_43029 baseEnd_43029 := by
    simpa [prefixWord, tailWord_43029, baseEnd_43029] using wordTrace_append hprefix tailTrace_43029
  have hstable : (prefixWord ++ tailWord_43029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43029).length < 2 ^ (prefixWord ++ tailWord_43029).sum := by decide
  have hdescent : baseEnd_43029 < baseStart_43029 := by decide
  rcases family_descends (prefixWord ++ tailWord_43029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43060 : List Nat := [2, 5, 1, 2, 2, 2, 2, 1, 3]
def baseStart_43060 : Nat := 118140960795 + 43060 * 2 ^ 59
def prefixEnd_43060 : Nat := 4983230072969 + 3 ^ 40 * 43060 * 2
def baseEnd_43060 : Nat := 19653757317961565557313

theorem tailTrace_43060 : CollatzResearch.WordTrace tailWord_43060 prefixEnd_43060 19653757317961565557313 := by
  unfold tailWord_43060
  simp only [CollatzResearch.WordTrace]
  refine ⟨785263612004224453811317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1047018149338965938415089 785263612004224453811317)
  ·
    refine ⟨73618463625396042544811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 785263612004224453811317 73618463625396042544811)
    ·
      refine ⟨110427695438094063817217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73618463625396042544811 110427695438094063817217)
      ·
        refine ⟨82820771578570547862913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110427695438094063817217 82820771578570547862913)
        ·
          refine ⟨62115578683927910897185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82820771578570547862913 62115578683927910897185)
          ·
            refine ⟨46586684012945933172889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62115578683927910897185 46586684012945933172889)
            ·
              refine ⟨34940013009709449879667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46586684012945933172889 34940013009709449879667)
              ·
                refine ⟨52410019514564174819501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34940013009709449879667 52410019514564174819501)
                ·
                  refine ⟨19653757317961565557313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52410019514564174819501 19653757317961565557313)
                  ·
                    rfl

theorem cell20_43060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_43060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43060 prefixEnd_43060 := by exact prefixLift 43060
  have htrace : WordTrace (prefixWord ++ tailWord_43060) baseStart_43060 baseEnd_43060 := by
    simpa [prefixWord, tailWord_43060, baseEnd_43060] using wordTrace_append hprefix tailTrace_43060
  have hstable : (prefixWord ++ tailWord_43060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43060).length < 2 ^ (prefixWord ++ tailWord_43060).sum := by decide
  have hdescent : baseEnd_43060 < baseStart_43060 := by decide
  rcases family_descends (prefixWord ++ tailWord_43060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43078 : List Nat := [6, 1, 1, 1, 1, 1, 1, 8]
def baseStart_43078 : Nat := 118140960795 + 43078 * 2 ^ 59
def prefixEnd_43078 : Nat := 4983230072969 + 3 ^ 40 * 43078 * 2
def baseEnd_43078 : Nat := 6553991002811167652413

theorem tailTrace_43078 : CollatzResearch.WordTrace tailWord_43078 prefixEnd_43078 6553991002811167652413 := by
  unfold tailWord_43078
  simp only [CollatzResearch.WordTrace]
  refine ⟨49099491810726186930559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1047455825295491987851925 49099491810726186930559)
  ·
    refine ⟨73649237716089280395839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49099491810726186930559 73649237716089280395839)
    ·
      refine ⟨110473856574133920593759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73649237716089280395839 110473856574133920593759)
      ·
        refine ⟨165710784861200880890639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110473856574133920593759 165710784861200880890639)
        ·
          refine ⟨248566177291801321335959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165710784861200880890639 248566177291801321335959)
          ·
            refine ⟨372849265937701982003939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248566177291801321335959 372849265937701982003939)
            ·
              refine ⟨559273898906552973005909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372849265937701982003939 559273898906552973005909)
              ·
                refine ⟨6553991002811167652413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 559273898906552973005909 6553991002811167652413)
                ·
                  rfl

theorem cell20_43078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_43078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43078 prefixEnd_43078 := by exact prefixLift 43078
  have htrace : WordTrace (prefixWord ++ tailWord_43078) baseStart_43078 baseEnd_43078 := by
    simpa [prefixWord, tailWord_43078, baseEnd_43078] using wordTrace_append hprefix tailTrace_43078
  have hstable : (prefixWord ++ tailWord_43078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43078).length < 2 ^ (prefixWord ++ tailWord_43078).sum := by decide
  have hdescent : baseEnd_43078 < baseStart_43078 := by decide
  rcases family_descends (prefixWord ++ tailWord_43078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43109 : List Nat := [1, 3, 1, 3, 2, 3, 1, 4, 2]
def baseStart_43109 : Nat := 118140960795 + 43109 * 2 ^ 59
def prefixEnd_43109 : Nat := 4983230072969 + 3 ^ 40 * 43109 * 2
def baseEnd_43109 : Nat := 19676122253135172923779

theorem tailTrace_43109 : CollatzResearch.WordTrace tailWord_43109 prefixEnd_43109 19676122253135172923779 := by
  unfold tailWord_43109
  simp only [CollatzResearch.WordTrace]
  refine ⟨1572314400830930276156381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1048209600553953517437587 1572314400830930276156381)
  ·
    refine ⟨589617900311598853558643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1572314400830930276156381 589617900311598853558643)
    ·
      refine ⟨884426850467398280337965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 589617900311598853558643 884426850467398280337965)
      ·
        refine ⟨331660068925274355126737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 884426850467398280337965 331660068925274355126737)
        ·
          refine ⟨248745051693955766345053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331660068925274355126737 248745051693955766345053)
          ·
            refine ⟨93279394385233412379395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 248745051693955766345053 93279394385233412379395)
            ·
              refine ⟨139919091577850118569093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93279394385233412379395 139919091577850118569093)
              ·
                refine ⟨26234829670846897231705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 139919091577850118569093 26234829670846897231705)
                ·
                  refine ⟨19676122253135172923779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26234829670846897231705 19676122253135172923779)
                  ·
                    rfl

theorem cell20_43109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 4, 2].length) (baseStart_43109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43109 prefixEnd_43109 := by exact prefixLift 43109
  have htrace : WordTrace (prefixWord ++ tailWord_43109) baseStart_43109 baseEnd_43109 := by
    simpa [prefixWord, tailWord_43109, baseEnd_43109] using wordTrace_append hprefix tailTrace_43109
  have hstable : (prefixWord ++ tailWord_43109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43109).length < 2 ^ (prefixWord ++ tailWord_43109).sum := by decide
  have hdescent : baseEnd_43109 < baseStart_43109 := by decide
  rcases family_descends (prefixWord ++ tailWord_43109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43113 : List Nat := [1, 2, 1, 1, 1, 5, 2, 3, 4]
def baseStart_43113 : Nat := 118140960795 + 43113 * 2 ^ 59
def prefixEnd_43113 : Nat := 4983230072969 + 3 ^ 40 * 43113 * 2
def baseEnd_43113 : Nat := 19677947962128936790429

theorem tailTrace_43113 : CollatzResearch.WordTrace tailWord_43113 prefixEnd_43113 19677947962128936790429 := by
  unfold tailWord_43113
  simp only [CollatzResearch.WordTrace]
  refine ⟨1572460292816438959301993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1048306861877625972867995 1572460292816438959301993)
  ·
    refine ⟨1179345219612329219476495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1572460292816438959301993 1179345219612329219476495)
    ·
      refine ⟨1769017829418493829214743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1179345219612329219476495 1769017829418493829214743)
      ·
        refine ⟨2653526744127740743822115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1769017829418493829214743 2653526744127740743822115)
        ·
          refine ⟨3980290116191611115733173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2653526744127740743822115 3980290116191611115733173)
          ·
            refine ⟨373152198392963542099985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3980290116191611115733173 373152198392963542099985)
            ·
              refine ⟨279864148794722656574989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 373152198392963542099985 279864148794722656574989)
              ·
                refine ⟨104949055798020996215621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 279864148794722656574989 104949055798020996215621)
                ·
                  refine ⟨19677947962128936790429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 104949055798020996215621 19677947962128936790429)
                  ·
                    rfl

theorem cell20_43113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_43113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43113 prefixEnd_43113 := by exact prefixLift 43113
  have htrace : WordTrace (prefixWord ++ tailWord_43113) baseStart_43113 baseEnd_43113 := by
    simpa [prefixWord, tailWord_43113, baseEnd_43113] using wordTrace_append hprefix tailTrace_43113
  have hstable : (prefixWord ++ tailWord_43113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43113).length < 2 ^ (prefixWord ++ tailWord_43113).sum := by decide
  have hdescent : baseEnd_43113 < baseStart_43113 := by decide
  rcases family_descends (prefixWord ++ tailWord_43113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43168 : List Nat := [2, 1, 1, 4, 2, 3, 2, 1, 4]
def baseStart_43168 : Nat := 118140960795 + 43168 * 2 ^ 59
def prefixEnd_43168 : Nat := 4983230072969 + 3 ^ 40 * 43168 * 2
def baseEnd_43168 : Nat := 19703051460793189956871

theorem tailTrace_43168 : CollatzResearch.WordTrace tailWord_43168 prefixEnd_43168 19703051460793189956871 := by
  unfold tailWord_43168
  simp only [CollatzResearch.WordTrace]
  refine ⟨787233153808591676277079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1049644205078122235036105 787233153808591676277079)
  ·
    refine ⟨1180849730712887514415619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 787233153808591676277079 1180849730712887514415619)
    ·
      refine ⟨1771274596069331271623429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1180849730712887514415619 1771274596069331271623429)
      ·
        refine ⟨332113986762999613429393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1771274596069331271623429 332113986762999613429393)
        ·
          refine ⟨249085490072249710072045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 332113986762999613429393 249085490072249710072045)
          ·
            refine ⟨93407058777093641277017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 249085490072249710072045 93407058777093641277017)
            ·
              refine ⟨70055294082820230957763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93407058777093641277017 70055294082820230957763)
              ·
                refine ⟨105082941124230346436645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70055294082820230957763 105082941124230346436645)
                ·
                  refine ⟨19703051460793189956871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105082941124230346436645 19703051460793189956871)
                  ·
                    rfl

theorem cell20_43168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 4].length) (baseStart_43168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43168 prefixEnd_43168 := by exact prefixLift 43168
  have htrace : WordTrace (prefixWord ++ tailWord_43168) baseStart_43168 baseEnd_43168 := by
    simpa [prefixWord, tailWord_43168, baseEnd_43168] using wordTrace_append hprefix tailTrace_43168
  have hstable : (prefixWord ++ tailWord_43168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43168).length < 2 ^ (prefixWord ++ tailWord_43168).sum := by decide
  have hdescent : baseEnd_43168 < baseStart_43168 := by decide
  rcases family_descends (prefixWord ++ tailWord_43168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43188 : List Nat := [2, 5, 3, 1, 1, 1, 1, 6]
def baseStart_43188 : Nat := 118140960795 + 43188 * 2 ^ 59
def prefixEnd_43188 : Nat := 4983230072969 + 3 ^ 40 * 43188 * 2
def baseEnd_43188 : Nat := 6570726668587336430041

theorem tailTrace_43188 : CollatzResearch.WordTrace tailWord_43188 prefixEnd_43188 6570726668587336430041 := by
  unfold tailWord_43188
  simp only [CollatzResearch.WordTrace]
  refine ⟨787597883772363384141109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1050130511696484512188145 787597883772363384141109)
  ·
    refine ⟨73837301603659067263229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 787597883772363384141109 73837301603659067263229)
    ·
      refine ⟨27688988101372150223711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73837301603659067263229 27688988101372150223711)
      ·
        refine ⟨41533482152058225335567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27688988101372150223711 41533482152058225335567)
        ·
          refine ⟨62300223228087338003351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41533482152058225335567 62300223228087338003351)
          ·
            refine ⟨93450334842131007005027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62300223228087338003351 93450334842131007005027)
            ·
              refine ⟨140175502263196510507541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93450334842131007005027 140175502263196510507541)
              ·
                refine ⟨6570726668587336430041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 140175502263196510507541 6570726668587336430041)
                ·
                  rfl

theorem cell20_43188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 6].length) (baseStart_43188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43188 prefixEnd_43188 := by exact prefixLift 43188
  have htrace : WordTrace (prefixWord ++ tailWord_43188) baseStart_43188 baseEnd_43188 := by
    simpa [prefixWord, tailWord_43188, baseEnd_43188] using wordTrace_append hprefix tailTrace_43188
  have hstable : (prefixWord ++ tailWord_43188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43188).length < 2 ^ (prefixWord ++ tailWord_43188).sum := by decide
  have hdescent : baseEnd_43188 < baseStart_43188 := by decide
  rcases family_descends (prefixWord ++ tailWord_43188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43237 : List Nat := [1, 3, 1, 4, 2, 2, 1, 3, 3]
def baseStart_43237 : Nat := 118140960795 + 43237 * 2 ^ 59
def prefixEnd_43237 : Nat := 4983230072969 + 3 ^ 40 * 43237 * 2
def baseEnd_43237 : Nat := 19734544940935616656589

theorem tailTrace_43237 : CollatzResearch.WordTrace tailWord_43237 prefixEnd_43237 19734544940935616656589 := by
  unfold tailWord_43237
  simp only [CollatzResearch.WordTrace]
  refine ⟨1576982944367208136815965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1051321962911472091210643 1576982944367208136815965)
  ·
    refine ⟨591368604137703051305987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1576982944367208136815965 591368604137703051305987)
    ·
      refine ⟨887052906206554576958981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 591368604137703051305987 887052906206554576958981)
      ·
        refine ⟨166322419913728983179809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 887052906206554576958981 166322419913728983179809)
        ·
          refine ⟨124741814935296737384857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166322419913728983179809 124741814935296737384857)
          ·
            refine ⟨93556361201472553038643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124741814935296737384857 93556361201472553038643)
            ·
              refine ⟨140334541802208829557965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93556361201472553038643 140334541802208829557965)
              ·
                refine ⟨52625453175828311084237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140334541802208829557965 52625453175828311084237)
                ·
                  refine ⟨19734544940935616656589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52625453175828311084237 19734544940935616656589)
                  ·
                    rfl

theorem cell20_43237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_43237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43237 prefixEnd_43237 := by exact prefixLift 43237
  have htrace : WordTrace (prefixWord ++ tailWord_43237) baseStart_43237 baseEnd_43237 := by
    simpa [prefixWord, tailWord_43237, baseEnd_43237] using wordTrace_append hprefix tailTrace_43237
  have hstable : (prefixWord ++ tailWord_43237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43237).length < 2 ^ (prefixWord ++ tailWord_43237).sum := by decide
  have hdescent : baseEnd_43237 < baseStart_43237 := by decide
  rcases family_descends (prefixWord ++ tailWord_43237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43272 : List Nat := [2, 1, 3, 2, 3, 9]
def baseStart_43272 : Nat := 118140960795 + 43272 * 2 ^ 59
def prefixEnd_43272 : Nat := 4983230072969 + 3 ^ 40 * 43272 * 2
def baseEnd_43272 : Nat := 731500736838187055177

theorem tailTrace_43272 : CollatzResearch.WordTrace tailWord_43272 prefixEnd_43272 731500736838187055177 := by
  unfold tailWord_43272
  simp only [CollatzResearch.WordTrace]
  refine ⟨789129749620204557170035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1052172999493606076226713 789129749620204557170035)
  ·
    refine ⟨1183694624430306835755053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 789129749620204557170035 1183694624430306835755053)
    ·
      refine ⟨443885484161365063408145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1183694624430306835755053 443885484161365063408145)
      ·
        refine ⟨332914113121023797556109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 443885484161365063408145 332914113121023797556109)
        ·
          refine ⟨124842792420383924083541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 332914113121023797556109 124842792420383924083541)
          ·
            refine ⟨731500736838187055177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 124842792420383924083541 731500736838187055177)
            ·
              rfl

theorem cell20_43272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 9].length) (baseStart_43272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43272 prefixEnd_43272 := by exact prefixLift 43272
  have htrace : WordTrace (prefixWord ++ tailWord_43272) baseStart_43272 baseEnd_43272 := by
    simpa [prefixWord, tailWord_43272, baseEnd_43272] using wordTrace_append hprefix tailTrace_43272
  have hstable : (prefixWord ++ tailWord_43272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43272).length < 2 ^ (prefixWord ++ tailWord_43272).sum := by decide
  have hdescent : baseEnd_43272 < baseStart_43272 := by decide
  rcases family_descends (prefixWord ++ tailWord_43272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43279 : List Nat := [1, 1, 2, 1, 1, 1, 3, 5, 5]
def baseStart_43279 : Nat := 118140960795 + 43279 * 2 ^ 59
def prefixEnd_43279 : Nat := 4983230072969 + 3 ^ 40 * 43279 * 2
def baseEnd_43279 : Nat := 19753714885370137256417

theorem tailTrace_43279 : CollatzResearch.WordTrace tailWord_43279 prefixEnd_43279 19753714885370137256417 := by
  unfold tailWord_43279
  simp only [CollatzResearch.WordTrace]
  refine ⟨1578514810215049309844891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1052343206810032873229927 1578514810215049309844891)
  ·
    refine ⟨2367772215322573964767337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1578514810215049309844891 2367772215322573964767337)
    ·
      refine ⟨1775829161491930473575503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2367772215322573964767337 1775829161491930473575503)
      ·
        refine ⟨2663743742237895710363255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1775829161491930473575503 2663743742237895710363255)
        ·
          refine ⟨3995615613356843565544883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2663743742237895710363255 3995615613356843565544883)
          ·
            refine ⟨5993423420035265348317325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3995615613356843565544883 5993423420035265348317325)
            ·
              refine ⟨2247533782513224505618997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5993423420035265348317325 2247533782513224505618997)
              ·
                refine ⟨210706292110614797401781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2247533782513224505618997 210706292110614797401781)
                ·
                  refine ⟨19753714885370137256417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 210706292110614797401781 19753714885370137256417)
                  ·
                    rfl

theorem cell20_43279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 5].length) (baseStart_43279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43279 prefixEnd_43279 := by exact prefixLift 43279
  have htrace : WordTrace (prefixWord ++ tailWord_43279) baseStart_43279 baseEnd_43279 := by
    simpa [prefixWord, tailWord_43279, baseEnd_43279] using wordTrace_append hprefix tailTrace_43279
  have hstable : (prefixWord ++ tailWord_43279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43279).length < 2 ^ (prefixWord ++ tailWord_43279).sum := by decide
  have hdescent : baseEnd_43279 < baseStart_43279 := by decide
  rcases family_descends (prefixWord ++ tailWord_43279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43316 : List Nat := [2, 5, 1, 1, 1, 3, 2, 3, 2]
def baseStart_43316 : Nat := 118140960795 + 43316 * 2 ^ 59
def prefixEnd_43316 : Nat := 4983230072969 + 3 ^ 40 * 43316 * 2
def baseEnd_43316 : Nat := 19770602693562453022933

theorem tailTrace_43316 : CollatzResearch.WordTrace tailWord_43316 prefixEnd_43316 19770602693562453022933 := by
  unfold tailWord_43316
  simp only [CollatzResearch.WordTrace]
  refine ⟨789932155540502314470901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1053242874054003085961201 789932155540502314470901)
  ·
    refine ⟨74056139581922091981647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 789932155540502314470901 74056139581922091981647)
    ·
      refine ⟨111084209372883137972471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74056139581922091981647 111084209372883137972471)
      ·
        refine ⟨166626314059324706958707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111084209372883137972471 166626314059324706958707)
        ·
          refine ⟨249939471088987060438061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166626314059324706958707 249939471088987060438061)
          ·
            refine ⟨93727301658370147664273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 249939471088987060438061 93727301658370147664273)
            ·
              refine ⟨70295476243777610748205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93727301658370147664273 70295476243777610748205)
              ·
                refine ⟨26360803591416604030577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70295476243777610748205 26360803591416604030577)
                ·
                  refine ⟨19770602693562453022933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26360803591416604030577 19770602693562453022933)
                  ·
                    rfl

theorem cell20_43316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_43316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43316 prefixEnd_43316 := by exact prefixLift 43316
  have htrace : WordTrace (prefixWord ++ tailWord_43316) baseStart_43316 baseEnd_43316 := by
    simpa [prefixWord, tailWord_43316, baseEnd_43316] using wordTrace_append hprefix tailTrace_43316
  have hstable : (prefixWord ++ tailWord_43316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43316).length < 2 ^ (prefixWord ++ tailWord_43316).sum := by decide
  have hdescent : baseEnd_43316 < baseStart_43316 := by decide
  rcases family_descends (prefixWord ++ tailWord_43316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43320 : List Nat := [2, 1, 2, 1, 3, 1, 3, 5, 2]
def baseStart_43320 : Nat := 118140960795 + 43320 * 2 ^ 59
def prefixEnd_43320 : Nat := 4983230072969 + 3 ^ 40 * 43320 * 2
def baseEnd_43320 : Nat := 19772428402556216889583

theorem tailTrace_43320 : CollatzResearch.WordTrace tailWord_43320 prefixEnd_43320 19772428402556216889583 := by
  unfold tailWord_43320
  simp only [CollatzResearch.WordTrace]
  refine ⟨790005101533256656043707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1053340135377675541391609 790005101533256656043707)
  ·
    refine ⟨1185007652299884984065561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 790005101533256656043707 1185007652299884984065561)
    ·
      refine ⟨888755739224913738049171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1185007652299884984065561 888755739224913738049171)
      ·
        refine ⟨1333133608837370607073757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 888755739224913738049171 1333133608837370607073757)
        ·
          refine ⟨499925103314013977652659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1333133608837370607073757 499925103314013977652659)
          ·
            refine ⟨749887654971020966478989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499925103314013977652659 749887654971020966478989)
            ·
              refine ⟨281207870614132862429621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 749887654971020966478989 281207870614132862429621)
              ·
                refine ⟨26363237870074955852777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 281207870614132862429621 26363237870074955852777)
                ·
                  refine ⟨19772428402556216889583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26363237870074955852777 19772428402556216889583)
                  ·
                    rfl

theorem cell20_43320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 5, 2].length) (baseStart_43320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43320 prefixEnd_43320 := by exact prefixLift 43320
  have htrace : WordTrace (prefixWord ++ tailWord_43320) baseStart_43320 baseEnd_43320 := by
    simpa [prefixWord, tailWord_43320, baseEnd_43320] using wordTrace_append hprefix tailTrace_43320
  have hstable : (prefixWord ++ tailWord_43320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43320).length < 2 ^ (prefixWord ++ tailWord_43320).sum := by decide
  have hdescent : baseEnd_43320 < baseStart_43320 := by decide
  rcases family_descends (prefixWord ++ tailWord_43320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43351 : List Nat := [1, 1, 3, 2, 3, 1, 5, 1, 3]
def baseStart_43351 : Nat := 118140960795 + 43351 * 2 ^ 59
def prefixEnd_43351 : Nat := 4983230072969 + 3 ^ 40 * 43351 * 2
def baseEnd_43351 : Nat := 19786577647257886856123

theorem tailTrace_43351 : CollatzResearch.WordTrace tailWord_43351 prefixEnd_43351 19786577647257886856123 := by
  unfold tailWord_43351
  simp only [CollatzResearch.WordTrace]
  refine ⟨1581140865954205606465907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1054093910636137070977271 1581140865954205606465907)
  ·
    refine ⟨2371711298931308409698861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1581140865954205606465907 2371711298931308409698861)
    ·
      refine ⟨889391737099240653637073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2371711298931308409698861 889391737099240653637073)
      ·
        refine ⟨667043802824430490227805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 889391737099240653637073 667043802824430490227805)
        ·
          refine ⟨250141426059161433835427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 667043802824430490227805 250141426059161433835427)
          ·
            refine ⟨375212139088742150753141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250141426059161433835427 375212139088742150753141)
            ·
              refine ⟨35176138039569576633107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 375212139088742150753141 35176138039569576633107)
              ·
                refine ⟨52764207059354364949661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35176138039569576633107 52764207059354364949661)
                ·
                  refine ⟨19786577647257886856123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52764207059354364949661 19786577647257886856123)
                  ·
                    rfl

theorem cell20_43351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 3].length) (baseStart_43351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43351 prefixEnd_43351 := by exact prefixLift 43351
  have htrace : WordTrace (prefixWord ++ tailWord_43351) baseStart_43351 baseEnd_43351 := by
    simpa [prefixWord, tailWord_43351, baseEnd_43351] using wordTrace_append hprefix tailTrace_43351
  have hstable : (prefixWord ++ tailWord_43351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43351).length < 2 ^ (prefixWord ++ tailWord_43351).sum := by decide
  have hdescent : baseEnd_43351 < baseStart_43351 := by decide
  rcases family_descends (prefixWord ++ tailWord_43351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43365 : List Nat := [1, 3, 1, 3, 1, 3, 4, 4]
def baseStart_43365 : Nat := 118140960795 + 43365 * 2 ^ 59
def prefixEnd_43365 : Nat := 4983230072969 + 3 ^ 40 * 43365 * 2
def baseEnd_43365 : Nat := 6597655876245353463133

theorem tailTrace_43365 : CollatzResearch.WordTrace tailWord_43365 prefixEnd_43365 6597655876245353463133 := by
  unfold tailWord_43365
  simp only [CollatzResearch.WordTrace]
  refine ⟨1581651487903485997475549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1054434325268990664983699 1581651487903485997475549)
  ·
    refine ⟨593119307963807249053331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1581651487903485997475549 593119307963807249053331)
    ·
      refine ⟨889678961945710873579997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 593119307963807249053331 889678961945710873579997)
      ·
        refine ⟨333629610729641577592499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 889678961945710873579997 333629610729641577592499)
        ·
          refine ⟨500444416094462366388749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333629610729641577592499 500444416094462366388749)
          ·
            refine ⟨187666656035423387395781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 500444416094462366388749 187666656035423387395781)
            ·
              refine ⟨35187498006641885136709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 187666656035423387395781 35187498006641885136709)
              ·
                refine ⟨6597655876245353463133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35187498006641885136709 6597655876245353463133)
                ·
                  rfl

theorem cell20_43365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 4].length) (baseStart_43365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43365 prefixEnd_43365 := by exact prefixLift 43365
  have htrace : WordTrace (prefixWord ++ tailWord_43365) baseStart_43365 baseEnd_43365 := by
    simpa [prefixWord, tailWord_43365, baseEnd_43365] using wordTrace_append hprefix tailTrace_43365
  have hstable : (prefixWord ++ tailWord_43365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43365).length < 2 ^ (prefixWord ++ tailWord_43365).sum := by decide
  have hdescent : baseEnd_43365 < baseStart_43365 := by decide
  rcases family_descends (prefixWord ++ tailWord_43365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43402 : List Nat := [3, 1, 2, 5, 2, 1, 2, 1, 3]
def baseStart_43402 : Nat := 118140960795 + 43402 * 2 ^ 59
def prefixEnd_43402 : Nat := 4983230072969 + 3 ^ 40 * 43402 * 2
def baseEnd_43402 : Nat := 19809855436928376155915

theorem tailTrace_43402 : CollatzResearch.WordTrace tailWord_43402 prefixEnd_43402 19809855436928376155915 := by
  unfold tailWord_43402
  simp only [CollatzResearch.WordTrace]
  refine ⟨395750247192360329143115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1055333992512960877714973 395750247192360329143115)
  ·
    refine ⟨593625370788540493714673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 395750247192360329143115 593625370788540493714673)
    ·
      refine ⟨445219028091405370286005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 593625370788540493714673 445219028091405370286005)
      ·
        refine ⟨41739283883569253464313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 445219028091405370286005 41739283883569253464313)
        ·
          refine ⟨31304462912676940098235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41739283883569253464313 31304462912676940098235)
          ·
            refine ⟨46956694369015410147353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31304462912676940098235 46956694369015410147353)
            ·
              refine ⟨35217520776761557610515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46956694369015410147353 35217520776761557610515)
              ·
                refine ⟨52826281165142336415773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35217520776761557610515 52826281165142336415773)
                ·
                  refine ⟨19809855436928376155915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52826281165142336415773 19809855436928376155915)
                  ·
                    rfl

theorem cell20_43402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 3].length) (baseStart_43402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43402 prefixEnd_43402 := by exact prefixLift 43402
  have htrace : WordTrace (prefixWord ++ tailWord_43402) baseStart_43402 baseEnd_43402 := by
    simpa [prefixWord, tailWord_43402, baseEnd_43402] using wordTrace_append hprefix tailTrace_43402
  have hstable : (prefixWord ++ tailWord_43402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43402).length < 2 ^ (prefixWord ++ tailWord_43402).sum := by decide
  have hdescent : baseEnd_43402 < baseStart_43402 := by decide
  rcases family_descends (prefixWord ++ tailWord_43402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43406 : List Nat := [4, 1, 1, 4, 1, 1, 4, 1, 3]
def baseStart_43406 : Nat := 118140960795 + 43406 * 2 ^ 59
def prefixEnd_43406 : Nat := 4983230072969 + 3 ^ 40 * 43406 * 2
def baseEnd_43406 : Nat := 19811681145922140022565

theorem tailTrace_43406 : CollatzResearch.WordTrace tailWord_43406 prefixEnd_43406 19811681145922140022565 := by
  unfold tailWord_43406
  simp only [CollatzResearch.WordTrace]
  refine ⟨197893360094368749964759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1055431253836633333145381 197893360094368749964759)
  ·
    refine ⟨296840040141553124947139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197893360094368749964759 296840040141553124947139)
    ·
      refine ⟨445260060212329687420709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296840040141553124947139 445260060212329687420709)
      ·
        refine ⟨83486261289811816391383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 445260060212329687420709 83486261289811816391383)
        ·
          refine ⟨125229391934717724587075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83486261289811816391383 125229391934717724587075)
          ·
            refine ⟨187844087902076586880613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125229391934717724587075 187844087902076586880613)
            ·
              refine ⟨35220766481639360040115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 187844087902076586880613 35220766481639360040115)
              ·
                refine ⟨52831149722459040060173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35220766481639360040115 52831149722459040060173)
                ·
                  refine ⟨19811681145922140022565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52831149722459040060173 19811681145922140022565)
                  ·
                    rfl

theorem cell20_43406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_43406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43406 prefixEnd_43406 := by exact prefixLift 43406
  have htrace : WordTrace (prefixWord ++ tailWord_43406) baseStart_43406 baseEnd_43406 := by
    simpa [prefixWord, tailWord_43406, baseEnd_43406] using wordTrace_append hprefix tailTrace_43406
  have hstable : (prefixWord ++ tailWord_43406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43406).length < 2 ^ (prefixWord ++ tailWord_43406).sum := by decide
  have hdescent : baseEnd_43406 < baseStart_43406 := by decide
  rcases family_descends (prefixWord ++ tailWord_43406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43424 : List Nat := [2, 1, 1, 4, 1, 3, 2, 6]
def baseStart_43424 : Nat := 118140960795 + 43424 * 2 ^ 59
def prefixEnd_43424 : Nat := 4983230072969 + 3 ^ 40 * 43424 * 2
def baseEnd_43424 : Nat := 6606632278798025807497

theorem tailTrace_43424 : CollatzResearch.WordTrace tailWord_43424 prefixEnd_43424 6606632278798025807497 := by
  unfold tailWord_43424
  simp only [CollatzResearch.WordTrace]
  refine ⟨791901697344869536936663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1055868929793159382582217 791901697344869536936663)
  ·
    refine ⟨1187852546017304305404995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 791901697344869536936663 1187852546017304305404995)
    ·
      refine ⟨1781778819025956458107493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1187852546017304305404995 1781778819025956458107493)
      ·
        refine ⟨334083528567366835895155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1781778819025956458107493 334083528567366835895155)
        ·
          refine ⟨501125292851050253842733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334083528567366835895155 501125292851050253842733)
          ·
            refine ⟨187921984819143845191025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 501125292851050253842733 187921984819143845191025)
            ·
              refine ⟨140941488614357883893269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187921984819143845191025 140941488614357883893269)
              ·
                refine ⟨6606632278798025807497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 140941488614357883893269 6606632278798025807497)
                ·
                  rfl

theorem cell20_43424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 6].length) (baseStart_43424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43424 prefixEnd_43424 := by exact prefixLift 43424
  have htrace : WordTrace (prefixWord ++ tailWord_43424) baseStart_43424 baseEnd_43424 := by
    simpa [prefixWord, tailWord_43424, baseEnd_43424] using wordTrace_append hprefix tailTrace_43424
  have hstable : (prefixWord ++ tailWord_43424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43424).length < 2 ^ (prefixWord ++ tailWord_43424).sum := by decide
  have hdescent : baseEnd_43424 < baseStart_43424 := by decide
  rcases family_descends (prefixWord ++ tailWord_43424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43507 : List Nat := [1, 1, 1, 2, 2, 2, 5, 1, 5]
def baseStart_43507 : Nat := 118140960795 + 43507 * 2 ^ 59
def prefixEnd_43507 : Nat := 4983230072969 + 3 ^ 40 * 43507 * 2
def baseEnd_43507 : Nat := 19857780298014677655485

theorem tailTrace_43507 : CollatzResearch.WordTrace tailWord_43507 prefixEnd_43507 19857780298014677655485 := by
  unfold tailWord_43507
  simp only [CollatzResearch.WordTrace]
  refine ⟨1586830653389044249144775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1057887102259362832763183 1586830653389044249144775)
  ·
    refine ⟨2380245980083566373717163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1586830653389044249144775 2380245980083566373717163)
    ·
      refine ⟨3570368970125349560575745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2380245980083566373717163 3570368970125349560575745)
      ·
        refine ⟨2677776727594012170431809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3570368970125349560575745 2677776727594012170431809)
        ·
          refine ⟨2008332545695509127823857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2677776727594012170431809 2008332545695509127823857)
          ·
            refine ⟨1506249409271631845867893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2008332545695509127823857 1506249409271631845867893)
            ·
              refine ⟨141210882119215485550115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1506249409271631845867893 141210882119215485550115)
              ·
                refine ⟨211816323178823228325173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141210882119215485550115 211816323178823228325173)
                ·
                  refine ⟨19857780298014677655485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 211816323178823228325173 19857780298014677655485)
                  ·
                    rfl

theorem cell20_43507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 5].length) (baseStart_43507 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43507 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43507 prefixEnd_43507 := by exact prefixLift 43507
  have htrace : WordTrace (prefixWord ++ tailWord_43507) baseStart_43507 baseEnd_43507 := by
    simpa [prefixWord, tailWord_43507, baseEnd_43507] using wordTrace_append hprefix tailTrace_43507
  have hstable : (prefixWord ++ tailWord_43507).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43507).length < 2 ^ (prefixWord ++ tailWord_43507).sum := by decide
  have hdescent : baseEnd_43507 < baseStart_43507 := by decide
  rcases family_descends (prefixWord ++ tailWord_43507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43510 : List Nat := [5, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_43510 : Nat := 118140960795 + 43510 * 2 ^ 59
def prefixEnd_43510 : Nat := 4983230072969 + 3 ^ 40 * 43510 * 2
def baseEnd_43510 : Nat := 19859149579760000555473

theorem tailTrace_43510 : CollatzResearch.WordTrace tailWord_43510 prefixEnd_43510 19859149579760000555473 := by
  unfold tailWord_43510
  simp only [CollatzResearch.WordTrace]
  refine ⟨99183754523635985093999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1057960048252117174335989 99183754523635985093999)
  ·
    refine ⟨148775631785453977640999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99183754523635985093999 148775631785453977640999)
    ·
      refine ⟨223163447678180966461499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148775631785453977640999 223163447678180966461499)
      ·
        refine ⟨334745171517271449692249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223163447678180966461499 334745171517271449692249)
        ·
          refine ⟨251058878637953587269187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 334745171517271449692249 251058878637953587269187)
          ·
            refine ⟨376588317956930380903781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251058878637953587269187 376588317956930380903781)
            ·
              refine ⟨70610309616924446419459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 376588317956930380903781 70610309616924446419459)
              ·
                refine ⟨105915464425386669629189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70610309616924446419459 105915464425386669629189)
                ·
                  refine ⟨19859149579760000555473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105915464425386669629189 19859149579760000555473)
                  ·
                    rfl

theorem cell20_43510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_43510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43510 prefixEnd_43510 := by exact prefixLift 43510
  have htrace : WordTrace (prefixWord ++ tailWord_43510) baseStart_43510 baseEnd_43510 := by
    simpa [prefixWord, tailWord_43510, baseEnd_43510] using wordTrace_append hprefix tailTrace_43510
  have hstable : (prefixWord ++ tailWord_43510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43510).length < 2 ^ (prefixWord ++ tailWord_43510).sum := by decide
  have hdescent : baseEnd_43510 < baseStart_43510 := by decide
  rcases family_descends (prefixWord ++ tailWord_43510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43531 : List Nat := [1, 1, 1, 1, 7, 1, 2, 2, 4]
def baseStart_43531 : Nat := 118140960795 + 43531 * 2 ^ 59
def prefixEnd_43531 : Nat := 4983230072969 + 3 ^ 40 * 43531 * 2
def baseEnd_43531 : Nat := 19868734551977260855387

theorem tailTrace_43531 : CollatzResearch.WordTrace tailWord_43531 prefixEnd_43531 19868734551977260855387 := by
  unfold tailWord_43531
  simp only [CollatzResearch.WordTrace]
  refine ⟨1587706005302096348018447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1058470670201397565345631 1587706005302096348018447)
  ·
    refine ⟨2381559007953144522027671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1587706005302096348018447 2381559007953144522027671)
    ·
      refine ⟨3572338511929716783041507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2381559007953144522027671 3572338511929716783041507)
      ·
        refine ⟨5358507767894575174562261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3572338511929716783041507 5358507767894575174562261)
        ·
          refine ⟨125590025810029105653803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 5358507767894575174562261 125590025810029105653803)
          ·
            refine ⟨188385038715043658480705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125590025810029105653803 188385038715043658480705)
            ·
              refine ⟨141288779036282743860529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188385038715043658480705 141288779036282743860529)
              ·
                refine ⟨105966584277212057895397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141288779036282743860529 105966584277212057895397)
                ·
                  refine ⟨19868734551977260855387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105966584277212057895397 19868734551977260855387)
                  ·
                    rfl

theorem cell20_43531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 4].length) (baseStart_43531 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43531 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43531 prefixEnd_43531 := by exact prefixLift 43531
  have htrace : WordTrace (prefixWord ++ tailWord_43531) baseStart_43531 baseEnd_43531 := by
    simpa [prefixWord, tailWord_43531, baseEnd_43531] using wordTrace_append hprefix tailTrace_43531
  have hstable : (prefixWord ++ tailWord_43531).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43531).length < 2 ^ (prefixWord ++ tailWord_43531).sum := by decide
  have hdescent : baseEnd_43531 < baseStart_43531 := by decide
  rcases family_descends (prefixWord ++ tailWord_43531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43534 : List Nat := [4, 1, 1, 2, 3, 3, 2, 4]
def baseStart_43534 : Nat := 118140960795 + 43534 * 2 ^ 59
def prefixEnd_43534 : Nat := 4983230072969 + 3 ^ 40 * 43534 * 2
def baseEnd_43534 : Nat := 6623367944574194585125

theorem tailTrace_43534 : CollatzResearch.WordTrace tailWord_43534 prefixEnd_43534 6623367944574194585125 := by
  unfold tailWord_43534
  simp only [CollatzResearch.WordTrace]
  refine ⟨198476928036403482547207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1058543616194151906918437 198476928036403482547207)
  ·
    refine ⟨297715392054605223820811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198476928036403482547207 297715392054605223820811)
    ·
      refine ⟨446573088081907835731217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297715392054605223820811 446573088081907835731217)
      ·
        refine ⟨334929816061430876798413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 446573088081907835731217 334929816061430876798413)
        ·
          refine ⟨125598681023036578799405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 334929816061430876798413 125598681023036578799405)
          ·
            refine ⟨47099505383638717049777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125598681023036578799405 47099505383638717049777)
            ·
              refine ⟨35324629037729037787333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47099505383638717049777 35324629037729037787333)
              ·
                refine ⟨6623367944574194585125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35324629037729037787333 6623367944574194585125)
                ·
                  rfl

theorem cell20_43534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_43534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43534 prefixEnd_43534 := by exact prefixLift 43534
  have htrace : WordTrace (prefixWord ++ tailWord_43534) baseStart_43534 baseEnd_43534 := by
    simpa [prefixWord, tailWord_43534, baseEnd_43534] using wordTrace_append hprefix tailTrace_43534
  have hstable : (prefixWord ++ tailWord_43534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43534).length < 2 ^ (prefixWord ++ tailWord_43534).sum := by decide
  have hdescent : baseEnd_43534 < baseStart_43534 := by decide
  rcases family_descends (prefixWord ++ tailWord_43534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43562 : List Nat := [3, 1, 4, 1, 1, 2, 2, 1, 5]
def baseStart_43562 : Nat := 118140960795 + 43562 * 2 ^ 59
def prefixEnd_43562 : Nat := 4983230072969 + 3 ^ 40 * 43562 * 2
def baseEnd_43562 : Nat := 19882883796678930821927

theorem tailTrace_43562 : CollatzResearch.WordTrace tailWord_43562 prefixEnd_43562 19882883796678930821927 := by
  unfold tailWord_43562
  simp only [CollatzResearch.WordTrace]
  refine ⟨397209167047447160599235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1059224445459859094931293 397209167047447160599235)
  ·
    refine ⟨595813750571170740898853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 397209167047447160599235 595813750571170740898853)
    ·
      refine ⟨111715078232094513918535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 595813750571170740898853 111715078232094513918535)
      ·
        refine ⟨167572617348141770877803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111715078232094513918535 167572617348141770877803)
        ·
          refine ⟨251358926022212656316705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167572617348141770877803 251358926022212656316705)
          ·
            refine ⟨188519194516659492237529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251358926022212656316705 188519194516659492237529)
            ·
              refine ⟨141389395887494619178147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188519194516659492237529 141389395887494619178147)
              ·
                refine ⟨212084093831241928767221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141389395887494619178147 212084093831241928767221)
                ·
                  refine ⟨19882883796678930821927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 212084093831241928767221 19882883796678930821927)
                  ·
                    rfl

theorem cell20_43562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_43562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43562 prefixEnd_43562 := by exact prefixLift 43562
  have htrace : WordTrace (prefixWord ++ tailWord_43562) baseStart_43562 baseEnd_43562 := by
    simpa [prefixWord, tailWord_43562, baseEnd_43562] using wordTrace_append hprefix tailTrace_43562
  have hstable : (prefixWord ++ tailWord_43562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43562).length < 2 ^ (prefixWord ++ tailWord_43562).sum := by decide
  have hdescent : baseEnd_43562 < baseStart_43562 := by decide
  rcases family_descends (prefixWord ++ tailWord_43562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43569 : List Nat := [1, 2, 2, 3, 1, 1, 5, 1, 4]
def baseStart_43569 : Nat := 118140960795 + 43569 * 2 ^ 59
def prefixEnd_43569 : Nat := 4983230072969 + 3 ^ 40 * 43569 * 2
def baseEnd_43569 : Nat := 19886078787418017588565

theorem tailTrace_43569 : CollatzResearch.WordTrace tailWord_43569 prefixEnd_43569 19886078787418017588565 := by
  unfold tailWord_43569
  simp only [CollatzResearch.WordTrace]
  refine ⟨1589091979164428837901761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1059394652776285891934507 1589091979164428837901761)
  ·
    refine ⟨1191818984373321628426321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1589091979164428837901761 1191818984373321628426321)
    ·
      refine ⟨893864238279991221319741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1191818984373321628426321 893864238279991221319741)
      ·
        refine ⟨335199089354996707994903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 893864238279991221319741 335199089354996707994903)
        ·
          refine ⟨502798634032495061992355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335199089354996707994903 502798634032495061992355)
          ·
            refine ⟨754197951048742592988533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502798634032495061992355 754197951048742592988533)
            ·
              refine ⟨70706057910819618092675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 754197951048742592988533 70706057910819618092675)
              ·
                refine ⟨106059086866229427139013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70706057910819618092675 106059086866229427139013)
                ·
                  refine ⟨19886078787418017588565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106059086866229427139013 19886078787418017588565)
                  ·
                    rfl

theorem cell20_43569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 4].length) (baseStart_43569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43569 prefixEnd_43569 := by exact prefixLift 43569
  have htrace : WordTrace (prefixWord ++ tailWord_43569) baseStart_43569 baseEnd_43569 := by
    simpa [prefixWord, tailWord_43569, baseEnd_43569] using wordTrace_append hprefix tailTrace_43569
  have hstable : (prefixWord ++ tailWord_43569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43569).length < 2 ^ (prefixWord ++ tailWord_43569).sum := by decide
  have hdescent : baseEnd_43569 < baseStart_43569 := by decide
  rcases family_descends (prefixWord ++ tailWord_43569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43576 : List Nat := [2, 1, 2, 1, 4, 1, 4, 5]
def baseStart_43576 : Nat := 118140960795 + 43576 * 2 ^ 59
def prefixEnd_43576 : Nat := 4983230072969 + 3 ^ 40 * 43576 * 2
def baseEnd_43576 : Nat := 6629757926052368118401

theorem tailTrace_43576 : CollatzResearch.WordTrace tailWord_43576 prefixEnd_43576 6629757926052368118401 := by
  unfold tailWord_43576
  simp only [CollatzResearch.WordTrace]
  refine ⟨794673645069534516703291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1059564860092712688937721 794673645069534516703291)
  ·
    refine ⟨1192010467604301775054937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 794673645069534516703291 1192010467604301775054937)
    ·
      refine ⟨894007850703226331291203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1192010467604301775054937 894007850703226331291203)
      ·
        refine ⟨1341011776054839496936805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 894007850703226331291203 1341011776054839496936805)
        ·
          refine ⟨251439708010282405675651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1341011776054839496936805 251439708010282405675651)
          ·
            refine ⟨377159562015423608513477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251439708010282405675651 377159562015423608513477)
            ·
              refine ⟨70717417877891926596277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 377159562015423608513477 70717417877891926596277)
              ·
                refine ⟨6629757926052368118401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70717417877891926596277 6629757926052368118401)
                ·
                  rfl

theorem cell20_43576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 5].length) (baseStart_43576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43576 prefixEnd_43576 := by exact prefixLift 43576
  have htrace : WordTrace (prefixWord ++ tailWord_43576) baseStart_43576 baseEnd_43576 := by
    simpa [prefixWord, tailWord_43576, baseEnd_43576] using wordTrace_append hprefix tailTrace_43576
  have hstable : (prefixWord ++ tailWord_43576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43576).length < 2 ^ (prefixWord ++ tailWord_43576).sum := by decide
  have hdescent : baseEnd_43576 < baseStart_43576 := by decide
  rcases family_descends (prefixWord ++ tailWord_43576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43635 : List Nat := [1, 1, 1, 2, 2, 1, 1, 11]
def baseStart_43635 : Nat := 118140960795 + 43635 * 2 ^ 59
def prefixEnd_43635 : Nat := 4983230072969 + 3 ^ 40 * 43635 * 2
def baseEnd_43635 : Nat := 6638734328605040462765

theorem tailTrace_43635 : CollatzResearch.WordTrace tailWord_43635 prefixEnd_43635 6638734328605040462765 := by
  unfold tailWord_43635
  simp only [CollatzResearch.WordTrace]
  refine ⟨1591499196925322109804359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1060999464616881406536239 1591499196925322109804359)
  ·
    refine ⟨2387248795387983164706539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1591499196925322109804359 2387248795387983164706539)
    ·
      refine ⟨3580873193081974747059809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2387248795387983164706539 3580873193081974747059809)
      ·
        refine ⟨2685654894811481060294857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3580873193081974747059809 2685654894811481060294857)
        ·
          refine ⟨2014241171108610795221143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2685654894811481060294857 2014241171108610795221143)
          ·
            refine ⟨3021361756662916192831715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2014241171108610795221143 3021361756662916192831715)
            ·
              refine ⟨4532042634994374289247573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3021361756662916192831715 4532042634994374289247573)
              ·
                refine ⟨6638734328605040462765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 4532042634994374289247573 6638734328605040462765)
                ·
                  rfl

theorem cell20_43635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 11].length) (baseStart_43635 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43635 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43635 prefixEnd_43635 := by exact prefixLift 43635
  have htrace : WordTrace (prefixWord ++ tailWord_43635) baseStart_43635 baseEnd_43635 := by
    simpa [prefixWord, tailWord_43635, baseEnd_43635] using wordTrace_append hprefix tailTrace_43635
  have hstable : (prefixWord ++ tailWord_43635).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43635).length < 2 ^ (prefixWord ++ tailWord_43635).sum := by decide
  have hdescent : baseEnd_43635 < baseStart_43635 := by decide
  rcases family_descends (prefixWord ++ tailWord_43635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43673 : List Nat := [1, 2, 1, 2, 1, 2, 11]
def baseStart_43673 : Nat := 118140960795 + 43673 * 2 ^ 59
def prefixEnd_43673 : Nat := 4983230072969 + 3 ^ 40 * 43673 * 2
def baseEnd_43673 : Nat := 2214838580139542013497

theorem tailTrace_43673 : CollatzResearch.WordTrace tailWord_43673 prefixEnd_43673 2214838580139542013497 := by
  unfold tailWord_43673
  simp only [CollatzResearch.WordTrace]
  refine ⟨1592885170787654599687673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1061923447191769733125115 1592885170787654599687673)
  ·
    refine ⟨1194663878090740949765755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1592885170787654599687673 1194663878090740949765755)
    ·
      refine ⟨1791995817136111424648633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1194663878090740949765755 1791995817136111424648633)
      ·
        refine ⟨1343996862852083568486475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1791995817136111424648633 1343996862852083568486475)
        ·
          refine ⟨2015995294278125352729713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1343996862852083568486475 2015995294278125352729713)
          ·
            refine ⟨1511996470708594014547285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2015995294278125352729713 1511996470708594014547285)
            ·
              refine ⟨2214838580139542013497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 1511996470708594014547285 2214838580139542013497)
              ·
                rfl

theorem cell20_43673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 11].length) (baseStart_43673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43673 prefixEnd_43673 := by exact prefixLift 43673
  have htrace : WordTrace (prefixWord ++ tailWord_43673) baseStart_43673 baseEnd_43673 := by
    simpa [prefixWord, tailWord_43673, baseEnd_43673] using wordTrace_append hprefix tailTrace_43673
  have hstable : (prefixWord ++ tailWord_43673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43673).length < 2 ^ (prefixWord ++ tailWord_43673).sum := by decide
  have hdescent : baseEnd_43673 < baseStart_43673 := by decide
  rcases family_descends (prefixWord ++ tailWord_43673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43676 : List Nat := [2, 2, 3, 2, 2, 2, 1, 1, 5]
def baseStart_43676 : Nat := 118140960795 + 43676 * 2 ^ 59
def prefixEnd_43676 : Nat := 4983230072969 + 3 ^ 40 * 43676 * 2
def baseEnd_43676 : Nat := 19934916503001201021461

theorem tailTrace_43676 : CollatzResearch.WordTrace tailWord_43676 prefixEnd_43676 19934916503001201021461 := by
  unfold tailWord_43676
  simp only [CollatzResearch.WordTrace]
  refine ⟨796497294888393056023441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1061996393184524074697921 796497294888393056023441)
  ·
    refine ⟨597372971166294792017581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 796497294888393056023441 597372971166294792017581)
    ·
      refine ⟨224014864187360547006593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 597372971166294792017581 224014864187360547006593)
      ·
        refine ⟨168011148140520410254945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224014864187360547006593 168011148140520410254945)
        ·
          refine ⟨126008361105390307691209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168011148140520410254945 126008361105390307691209)
          ·
            refine ⟨94506270829042730768407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126008361105390307691209 94506270829042730768407)
            ·
              refine ⟨141759406243564096152611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94506270829042730768407 141759406243564096152611)
              ·
                refine ⟨212639109365346144228917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141759406243564096152611 212639109365346144228917)
                ·
                  refine ⟨19934916503001201021461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 212639109365346144228917 19934916503001201021461)
                  ·
                    rfl

theorem cell20_43676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_43676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43676 prefixEnd_43676 := by exact prefixLift 43676
  have htrace : WordTrace (prefixWord ++ tailWord_43676) baseStart_43676 baseEnd_43676 := by
    simpa [prefixWord, tailWord_43676, baseEnd_43676] using wordTrace_append hprefix tailTrace_43676
  have hstable : (prefixWord ++ tailWord_43676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43676).length < 2 ^ (prefixWord ++ tailWord_43676).sum := by decide
  have hdescent : baseEnd_43676 < baseStart_43676 := by decide
  rcases family_descends (prefixWord ++ tailWord_43676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43713 : List Nat := [1, 2, 6, 2, 1, 2, 1, 3, 2]
def baseStart_43713 : Nat := 118140960795 + 43713 * 2 ^ 59
def prefixEnd_43713 : Nat := 4983230072969 + 3 ^ 40 * 43713 * 2
def baseEnd_43713 : Nat := 19951804311193516787977

theorem tailTrace_43713 : CollatzResearch.WordTrace tailWord_43713 prefixEnd_43713 19951804311193516787977 := by
  unfold tailWord_43713
  simp only [CollatzResearch.WordTrace]
  refine ⟨1594344090642741431143793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1062896060428494287429195 1594344090642741431143793)
  ·
    refine ⟨1195758067982056073357845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1594344090642741431143793 1195758067982056073357845)
    ·
      refine ⟨56051159436658878438649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1195758067982056073357845 56051159436658878438649)
      ·
        refine ⟨42038369577494158828987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56051159436658878438649 42038369577494158828987)
        ·
          refine ⟨63057554366241238243481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42038369577494158828987 63057554366241238243481)
          ·
            refine ⟨47293165774680928682611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63057554366241238243481 47293165774680928682611)
            ·
              refine ⟨70939748662021393023917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47293165774680928682611 70939748662021393023917)
              ·
                refine ⟨26602405748258022383969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70939748662021393023917 26602405748258022383969)
                ·
                  refine ⟨19951804311193516787977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26602405748258022383969 19951804311193516787977)
                  ·
                    rfl

theorem cell20_43713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 3, 2].length) (baseStart_43713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43713 prefixEnd_43713 := by exact prefixLift 43713
  have htrace : WordTrace (prefixWord ++ tailWord_43713) baseStart_43713 baseEnd_43713 := by
    simpa [prefixWord, tailWord_43713, baseEnd_43713] using wordTrace_append hprefix tailTrace_43713
  have hstable : (prefixWord ++ tailWord_43713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43713).length < 2 ^ (prefixWord ++ tailWord_43713).sum := by decide
  have hdescent : baseEnd_43713 < baseStart_43713 := by decide
  rcases family_descends (prefixWord ++ tailWord_43713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43735 : List Nat := [1, 1, 3, 2, 1, 4, 2, 1, 5]
def baseStart_43735 : Nat := 118140960795 + 43735 * 2 ^ 59
def prefixEnd_43735 : Nat := 4983230072969 + 3 ^ 40 * 43735 * 2
def baseEnd_43735 : Nat := 19961845710659218054553

theorem tailTrace_43735 : CollatzResearch.WordTrace tailWord_43735 prefixEnd_43735 19961845710659218054553 := by
  unfold tailWord_43735
  simp only [CollatzResearch.WordTrace]
  refine ⟨1595146496563039188444659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1063430997708692792296439 1595146496563039188444659)
  ·
    refine ⟨2392719744844558782666989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1595146496563039188444659 2392719744844558782666989)
    ·
      refine ⟨897269904316709543500121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2392719744844558782666989 897269904316709543500121)
      ·
        refine ⟨672952428237532157625091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 897269904316709543500121 672952428237532157625091)
        ·
          refine ⟨1009428642356298236437637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 672952428237532157625091 1009428642356298236437637)
          ·
            refine ⟨189267870441805919332057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1009428642356298236437637 189267870441805919332057)
            ·
              refine ⟨141950902831354439499043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189267870441805919332057 141950902831354439499043)
              ·
                refine ⟨212926354247031659248565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141950902831354439499043 212926354247031659248565)
                ·
                  refine ⟨19961845710659218054553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 212926354247031659248565 19961845710659218054553)
                  ·
                    rfl

theorem cell20_43735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 5].length) (baseStart_43735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43735 prefixEnd_43735 := by exact prefixLift 43735
  have htrace : WordTrace (prefixWord ++ tailWord_43735) baseStart_43735 baseEnd_43735 := by
    simpa [prefixWord, tailWord_43735, baseEnd_43735] using wordTrace_append hprefix tailTrace_43735
  have hstable : (prefixWord ++ tailWord_43735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43735).length < 2 ^ (prefixWord ++ tailWord_43735).sum := by decide
  have hdescent : baseEnd_43735 < baseStart_43735 := by decide
  rcases family_descends (prefixWord ++ tailWord_43735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43766 : List Nat := [5, 1, 1, 1, 1, 2, 1, 8]
def baseStart_43766 : Nat := 118140960795 + 43766 * 2 ^ 59
def prefixEnd_43766 : Nat := 4983230072969 + 3 ^ 40 * 43766 * 2
def baseEnd_43766 : Nat := 6658664985120296007031

theorem tailTrace_43766 : CollatzResearch.WordTrace tailWord_43766 prefixEnd_43766 6658664985120296007031 := by
  unfold tailWord_43766
  simp only [CollatzResearch.WordTrace]
  refine ⟨99767322465670717676447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1064184772967154321882101 99767322465670717676447)
  ·
    refine ⟨149650983698506076514671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99767322465670717676447 149650983698506076514671)
    ·
      refine ⟨224476475547759114772007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149650983698506076514671 224476475547759114772007)
      ·
        refine ⟨336714713321638672158011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224476475547759114772007 336714713321638672158011)
        ·
          refine ⟨505072069982458008237017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336714713321638672158011 505072069982458008237017)
          ·
            refine ⟨378804052486843506177763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 505072069982458008237017 378804052486843506177763)
            ·
              refine ⟨568206078730265259266645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 378804052486843506177763 568206078730265259266645)
              ·
                refine ⟨6658664985120296007031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 568206078730265259266645 6658664985120296007031)
                ·
                  rfl

theorem cell20_43766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_43766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43766 prefixEnd_43766 := by exact prefixLift 43766
  have htrace : WordTrace (prefixWord ++ tailWord_43766) baseStart_43766 baseEnd_43766 := by
    simpa [prefixWord, tailWord_43766, baseEnd_43766] using wordTrace_append hprefix tailTrace_43766
  have hstable : (prefixWord ++ tailWord_43766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43766).length < 2 ^ (prefixWord ++ tailWord_43766).sum := by decide
  have hdescent : baseEnd_43766 < baseStart_43766 := by decide
  rcases family_descends (prefixWord ++ tailWord_43766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43804 : List Nat := [2, 2, 3, 1, 1, 3, 3, 5]
def baseStart_43804 : Nat := 118140960795 + 43804 * 2 ^ 59
def prefixEnd_43804 : Nat := 4983230072969 + 3 ^ 40 * 43804 * 2
def baseEnd_43804 : Nat := 6664446396933881584757

theorem tailTrace_43804 : CollatzResearch.WordTrace tailWord_43804 prefixEnd_43804 6664446396933881584757 := by
  unfold tailWord_43804
  simp only [CollatzResearch.WordTrace]
  refine ⟨798831566656531986353233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1065108755542042648470977 798831566656531986353233)
  ·
    refine ⟨599123674992398989764925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 798831566656531986353233 599123674992398989764925)
    ·
      refine ⟨224671378122149621161847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 599123674992398989764925 224671378122149621161847)
      ·
        refine ⟨337007067183224431742771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224671378122149621161847 337007067183224431742771)
        ·
          refine ⟨505510600774836647614157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337007067183224431742771 505510600774836647614157)
          ·
            refine ⟨189566475290563742855309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 505510600774836647614157 189566475290563742855309)
            ·
              refine ⟨71087428233961403570741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189566475290563742855309 71087428233961403570741)
              ·
                refine ⟨6664446396933881584757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71087428233961403570741 6664446396933881584757)
                ·
                  rfl

theorem cell20_43804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 5].length) (baseStart_43804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43804 prefixEnd_43804 := by exact prefixLift 43804
  have htrace : WordTrace (prefixWord ++ tailWord_43804) baseStart_43804 baseEnd_43804 := by
    simpa [prefixWord, tailWord_43804, baseEnd_43804] using wordTrace_append hprefix tailTrace_43804
  have hstable : (prefixWord ++ tailWord_43804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43804).length < 2 ^ (prefixWord ++ tailWord_43804).sum := by decide
  have hdescent : baseEnd_43804 < baseStart_43804 := by decide
  rcases family_descends (prefixWord ++ tailWord_43804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43841 : List Nat := [1, 2, 5, 3, 2, 1, 1, 2, 3]
def baseStart_43841 : Nat := 118140960795 + 43841 * 2 ^ 59
def prefixEnd_43841 : Nat := 4983230072969 + 3 ^ 40 * 43841 * 2
def baseEnd_43841 : Nat := 20010226998993960520787

theorem tailTrace_43841 : CollatzResearch.WordTrace tailWord_43841 prefixEnd_43841 20010226998993960520787 := by
  unfold tailWord_43841
  simp only [CollatzResearch.WordTrace]
  refine ⟨1599012634179019291803377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1066008422786012861202251 1599012634179019291803377)
  ·
    refine ⟨1199259475634264468852533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1599012634179019291803377 1199259475634264468852533)
    ·
      refine ⟨112430575840712293954925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1199259475634264468852533 112430575840712293954925)
      ·
        refine ⟨42161465940267110233097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112430575840712293954925 42161465940267110233097)
        ·
          refine ⟨31621099455200332674823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42161465940267110233097 31621099455200332674823)
          ·
            refine ⟨47431649182800499012235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31621099455200332674823 47431649182800499012235)
            ·
              refine ⟨71147473774200748518353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47431649182800499012235 71147473774200748518353)
              ·
                refine ⟨53360605330650561388765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71147473774200748518353 53360605330650561388765)
                ·
                  refine ⟨20010226998993960520787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53360605330650561388765 20010226998993960520787)
                  ·
                    rfl

theorem cell20_43841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 3].length) (baseStart_43841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43841 prefixEnd_43841 := by exact prefixLift 43841
  have htrace : WordTrace (prefixWord ++ tailWord_43841) baseStart_43841 baseEnd_43841 := by
    simpa [prefixWord, tailWord_43841, baseEnd_43841] using wordTrace_append hprefix tailTrace_43841
  have hstable : (prefixWord ++ tailWord_43841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43841).length < 2 ^ (prefixWord ++ tailWord_43841).sum := by decide
  have hdescent : baseEnd_43841 < baseStart_43841 := by decide
  rcases family_descends (prefixWord ++ tailWord_43841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43849 : List Nat := [1, 2, 1, 1, 2, 6, 1, 1, 5]
def baseStart_43849 : Nat := 118140960795 + 43849 * 2 ^ 59
def prefixEnd_43849 : Nat := 4983230072969 + 3 ^ 40 * 43849 * 2
def baseEnd_43849 : Nat := 20013878416981488254087

theorem tailTrace_43849 : CollatzResearch.WordTrace tailWord_43849 prefixEnd_43849 20013878416981488254087 := by
  unfold tailWord_43849
  simp only [CollatzResearch.WordTrace]
  refine ⟨1599304418150036658094601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1066202945433357772063067 1599304418150036658094601)
  ·
    refine ⟨1199478313612527493570951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1599304418150036658094601 1199478313612527493570951)
    ·
      refine ⟨1799217470418791240356427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1199478313612527493570951 1799217470418791240356427)
      ·
        refine ⟨2698826205628186860534641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1799217470418791240356427 2698826205628186860534641)
        ·
          refine ⟨2024119654221140145400981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2698826205628186860534641 2024119654221140145400981)
          ·
            refine ⟨94880608791615944315671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2024119654221140145400981 94880608791615944315671)
            ·
              refine ⟨142320913187423916473507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94880608791615944315671 142320913187423916473507)
              ·
                refine ⟨213481369781135874710261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142320913187423916473507 213481369781135874710261)
                ·
                  refine ⟨20013878416981488254087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 213481369781135874710261 20013878416981488254087)
                  ·
                    rfl

theorem cell20_43849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 5].length) (baseStart_43849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43849 prefixEnd_43849 := by exact prefixLift 43849
  have htrace : WordTrace (prefixWord ++ tailWord_43849) baseStart_43849 baseEnd_43849 := by
    simpa [prefixWord, tailWord_43849, baseEnd_43849] using wordTrace_append hprefix tailTrace_43849
  have hstable : (prefixWord ++ tailWord_43849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43849).length < 2 ^ (prefixWord ++ tailWord_43849).sum := by decide
  have hdescent : baseEnd_43849 < baseStart_43849 := by decide
  rcases family_descends (prefixWord ++ tailWord_43849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43852 : List Nat := [2, 2, 1, 3, 3, 1, 2, 4, 2]
def baseStart_43852 : Nat := 118140960795 + 43852 * 2 ^ 59
def prefixEnd_43852 : Nat := 4983230072969 + 3 ^ 40 * 43852 * 2
def baseEnd_43852 : Nat := 20015247698726811154075

theorem tailTrace_43852 : CollatzResearch.WordTrace tailWord_43852 prefixEnd_43852 20015247698726811154075 := by
  unfold tailWord_43852
  simp only [CollatzResearch.WordTrace]
  refine ⟨799706918569584085226905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1066275891426112113635873 799706918569584085226905)
  ·
    refine ⟨599780188927188063920179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 799706918569584085226905 599780188927188063920179)
    ·
      refine ⟨899670283390782095880269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 599780188927188063920179 899670283390782095880269)
      ·
        refine ⟨337376356271543285955101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 899670283390782095880269 337376356271543285955101)
        ·
          refine ⟨126516133601828732233163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 337376356271543285955101 126516133601828732233163)
          ·
            refine ⟨189774200402743098349745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126516133601828732233163 189774200402743098349745)
            ·
              refine ⟨142330650302057323762309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189774200402743098349745 142330650302057323762309)
              ·
                refine ⟨26686996931635748205433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142330650302057323762309 26686996931635748205433)
                ·
                  refine ⟨20015247698726811154075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26686996931635748205433 20015247698726811154075)
                  ·
                    rfl

theorem cell20_43852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 4, 2].length) (baseStart_43852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43852 prefixEnd_43852 := by exact prefixLift 43852
  have htrace : WordTrace (prefixWord ++ tailWord_43852) baseStart_43852 baseEnd_43852 := by
    simpa [prefixWord, tailWord_43852, baseEnd_43852] using wordTrace_append hprefix tailTrace_43852
  have hstable : (prefixWord ++ tailWord_43852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43852).length < 2 ^ (prefixWord ++ tailWord_43852).sum := by decide
  have hdescent : baseEnd_43852 < baseStart_43852 := by decide
  rcases family_descends (prefixWord ++ tailWord_43852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43856 : List Nat := [2, 1, 1, 1, 1, 4, 3, 3, 4]
def baseStart_43856 : Nat := 118140960795 + 43856 * 2 ^ 59
def prefixEnd_43856 : Nat := 4983230072969 + 3 ^ 40 * 43856 * 2
def baseEnd_43856 : Nat := 20017073407720575020725

theorem tailTrace_43856 : CollatzResearch.WordTrace tailWord_43856 prefixEnd_43856 20017073407720575020725 := by
  unfold tailWord_43856
  simp only [CollatzResearch.WordTrace]
  refine ⟨799779864562338426799711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1066373152749784569066281 799779864562338426799711)
  ·
    refine ⟨1199669796843507640199567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 799779864562338426799711 1199669796843507640199567)
    ·
      refine ⟨1799504695265261460299351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1199669796843507640199567 1799504695265261460299351)
      ·
        refine ⟨2699257042897892190449027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1799504695265261460299351 2699257042897892190449027)
        ·
          refine ⟨4048885564346838285673541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2699257042897892190449027 4048885564346838285673541)
          ·
            refine ⟨759166043315032178563789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4048885564346838285673541 759166043315032178563789)
            ·
              refine ⟨284687266243137066961421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 759166043315032178563789 284687266243137066961421)
              ·
                refine ⟨106757724841176400110533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 284687266243137066961421 106757724841176400110533)
                ·
                  refine ⟨20017073407720575020725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106757724841176400110533 20017073407720575020725)
                  ·
                    rfl

theorem cell20_43856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_43856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43856 prefixEnd_43856 := by exact prefixLift 43856
  have htrace : WordTrace (prefixWord ++ tailWord_43856) baseStart_43856 baseEnd_43856 := by
    simpa [prefixWord, tailWord_43856, baseEnd_43856] using wordTrace_append hprefix tailTrace_43856
  have hstable : (prefixWord ++ tailWord_43856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43856).length < 2 ^ (prefixWord ++ tailWord_43856).sum := by decide
  have hdescent : baseEnd_43856 < baseStart_43856 := by decide
  rcases family_descends (prefixWord ++ tailWord_43856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43880 : List Nat := [2, 1, 4, 2, 1, 3, 1, 6]
def baseStart_43880 : Nat := 118140960795 + 43880 * 2 ^ 59
def prefixEnd_43880 : Nat := 4983230072969 + 3 ^ 40 * 43880 * 2
def baseEnd_43880 : Nat := 6676009220561052740209

theorem tailTrace_43880 : CollatzResearch.WordTrace tailWord_43880 prefixEnd_43880 6676009220561052740209 := by
  unfold tailWord_43880
  simp only [CollatzResearch.WordTrace]
  refine ⟨800217540518864476236547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1066956720691819301648729 800217540518864476236547)
  ·
    refine ⟨1200326310778296714354821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 800217540518864476236547 1200326310778296714354821)
    ·
      refine ⟨225061183270930633941529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1200326310778296714354821 225061183270930633941529)
      ·
        refine ⟨168795887453197975456147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225061183270930633941529 168795887453197975456147)
        ·
          refine ⟨253193831179796963184221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168795887453197975456147 253193831179796963184221)
          ·
            refine ⟨94947686692423861194083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 253193831179796963184221 94947686692423861194083)
            ·
              refine ⟨142421530038635791791125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94947686692423861194083 142421530038635791791125)
              ·
                refine ⟨6676009220561052740209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 142421530038635791791125 6676009220561052740209)
                ·
                  rfl

theorem cell20_43880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 6].length) (baseStart_43880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43880 prefixEnd_43880 := by exact prefixLift 43880
  have htrace : WordTrace (prefixWord ++ tailWord_43880) baseStart_43880 baseEnd_43880 := by
    simpa [prefixWord, tailWord_43880, baseEnd_43880] using wordTrace_append hprefix tailTrace_43880
  have hstable : (prefixWord ++ tailWord_43880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43880).length < 2 ^ (prefixWord ++ tailWord_43880).sum := by decide
  have hdescent : baseEnd_43880 < baseStart_43880 := by decide
  rcases family_descends (prefixWord ++ tailWord_43880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43886 : List Nat := [4, 1, 2, 3, 2, 2, 1, 3, 2]
def baseStart_43886 : Nat := 118140960795 + 43886 * 2 ^ 59
def prefixEnd_43886 : Nat := 4983230072969 + 3 ^ 40 * 43886 * 2
def baseEnd_43886 : Nat := 20030766225173804020603

theorem tailTrace_43886 : CollatzResearch.WordTrace tailWord_43886 prefixEnd_43886 20030766225173804020603 := by
  unfold tailWord_43886
  simp only [CollatzResearch.WordTrace]
  refine ⟨200081739876998997148939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1067102612677327984794341 200081739876998997148939)
  ·
    refine ⟨300122609815498495723409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200081739876998997148939 300122609815498495723409)
    ·
      refine ⟨225091957361623871792557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300122609815498495723409 225091957361623871792557)
      ·
        refine ⟨84409484010608951922209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225091957361623871792557 84409484010608951922209)
        ·
          refine ⟨63307113007956713941657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84409484010608951922209 63307113007956713941657)
          ·
            refine ⟨47480334755967535456243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63307113007956713941657 47480334755967535456243)
            ·
              refine ⟨71220502133951303184365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47480334755967535456243 71220502133951303184365)
              ·
                refine ⟨26707688300231738694137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71220502133951303184365 26707688300231738694137)
                ·
                  refine ⟨20030766225173804020603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26707688300231738694137 20030766225173804020603)
                  ·
                    rfl

theorem cell20_43886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_43886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43886 prefixEnd_43886 := by exact prefixLift 43886
  have htrace : WordTrace (prefixWord ++ tailWord_43886) baseStart_43886 baseEnd_43886 := by
    simpa [prefixWord, tailWord_43886, baseEnd_43886] using wordTrace_append hprefix tailTrace_43886
  have hstable : (prefixWord ++ tailWord_43886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43886).length < 2 ^ (prefixWord ++ tailWord_43886).sum := by decide
  have hdescent : baseEnd_43886 < baseStart_43886 := by decide
  rcases family_descends (prefixWord ++ tailWord_43886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43890 : List Nat := [3, 2, 1, 2, 1, 1, 5, 3, 2]
def baseStart_43890 : Nat := 118140960795 + 43890 * 2 ^ 59
def prefixEnd_43890 : Nat := 4983230072969 + 3 ^ 40 * 43890 * 2
def baseEnd_43890 : Nat := 20032591934167567887253

theorem tailTrace_43890 : CollatzResearch.WordTrace tailWord_43890 prefixEnd_43890 20032591934167567887253 := by
  unfold tailWord_43890
  simp only [CollatzResearch.WordTrace]
  refine ⟨400199952750375165084281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1067199874001000440224749 400199952750375165084281)
  ·
    refine ⟨300149964562781373813211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 400199952750375165084281 300149964562781373813211)
    ·
      refine ⟨450224946844172060719817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300149964562781373813211 450224946844172060719817)
      ·
        refine ⟨337668710133129045539863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 450224946844172060719817 337668710133129045539863)
        ·
          refine ⟨506503065199693568309795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337668710133129045539863 506503065199693568309795)
          ·
            refine ⟨759754597799540352464693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 506503065199693568309795 759754597799540352464693)
            ·
              refine ⟨71226993543706908043565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 759754597799540352464693 71226993543706908043565)
              ·
                refine ⟨26710122578890090516337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71226993543706908043565 26710122578890090516337)
                ·
                  refine ⟨20032591934167567887253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26710122578890090516337 20032591934167567887253)
                  ·
                    rfl

theorem cell20_43890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_43890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43890 prefixEnd_43890 := by exact prefixLift 43890
  have htrace : WordTrace (prefixWord ++ tailWord_43890) baseStart_43890 baseEnd_43890 := by
    simpa [prefixWord, tailWord_43890, baseEnd_43890] using wordTrace_append hprefix tailTrace_43890
  have hstable : (prefixWord ++ tailWord_43890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43890).length < 2 ^ (prefixWord ++ tailWord_43890).sum := by decide
  have hdescent : baseEnd_43890 < baseStart_43890 := by decide
  rcases family_descends (prefixWord ++ tailWord_43890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43901 : List Nat := [1, 4, 1, 1, 2, 1, 10]
def baseStart_43901 : Nat := 118140960795 + 43901 * 2 ^ 59
def prefixEnd_43901 : Nat := 4983230072969 + 3 ^ 40 * 43901 * 2
def baseEnd_43901 : Nat := 2226401403766713168949

theorem tailTrace_43901 : CollatzResearch.WordTrace tailWord_43901 prefixEnd_43901 2226401403766713168949 := by
  unfold tailWord_43901
  simp only [CollatzResearch.WordTrace]
  refine ⟨1601201013961649538987557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1067467342641099692658371 1601201013961649538987557)
  ·
    refine ⟨300225190117809288560167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1601201013961649538987557 300225190117809288560167)
    ·
      refine ⟨450337785176713932840251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300225190117809288560167 450337785176713932840251)
      ·
        refine ⟨675506677765070899260377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450337785176713932840251 675506677765070899260377)
        ·
          refine ⟨506630008323803174445283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 675506677765070899260377 506630008323803174445283)
          ·
            refine ⟨759945012485704761667925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 506630008323803174445283 759945012485704761667925)
            ·
              refine ⟨2226401403766713168949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 759945012485704761667925 2226401403766713168949)
              ·
                rfl

theorem cell20_43901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 10].length) (baseStart_43901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43901 prefixEnd_43901 := by exact prefixLift 43901
  have htrace : WordTrace (prefixWord ++ tailWord_43901) baseStart_43901 baseEnd_43901 := by
    simpa [prefixWord, tailWord_43901, baseEnd_43901] using wordTrace_append hprefix tailTrace_43901
  have hstable : (prefixWord ++ tailWord_43901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43901).length < 2 ^ (prefixWord ++ tailWord_43901).sum := by decide
  have hdescent : baseEnd_43901 < baseStart_43901 := by decide
  rcases family_descends (prefixWord ++ tailWord_43901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43911 : List Nat := [1, 1, 4, 2, 3, 1, 3, 1, 4]
def baseStart_43911 : Nat := 118140960795 + 43911 * 2 ^ 59
def prefixEnd_43911 : Nat := 4983230072969 + 3 ^ 40 * 43911 * 2
def baseEnd_43911 : Nat := 20042176906384828187167

theorem tailTrace_43911 : CollatzResearch.WordTrace tailWord_43911 prefixEnd_43911 20042176906384828187167 := by
  unfold tailWord_43911
  simp only [CollatzResearch.WordTrace]
  refine ⟨1601565743925421246851587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1067710495950280831234391 1601565743925421246851587)
  ·
    refine ⟨2402348615888131870277381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1601565743925421246851587 2402348615888131870277381)
    ·
      refine ⟨450440365479024725677009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2402348615888131870277381 450440365479024725677009)
      ·
        refine ⟨337830274109268544257757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 450440365479024725677009 337830274109268544257757)
        ·
          refine ⟨126686352790975704096659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 337830274109268544257757 126686352790975704096659)
          ·
            refine ⟨190029529186463556144989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126686352790975704096659 190029529186463556144989)
            ·
              refine ⟨71261073444923833554371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190029529186463556144989 71261073444923833554371)
              ·
                refine ⟨106891610167385750331557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71261073444923833554371 106891610167385750331557)
                ·
                  refine ⟨20042176906384828187167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106891610167385750331557 20042176906384828187167)
                  ·
                    rfl

theorem cell20_43911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 4].length) (baseStart_43911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43911 prefixEnd_43911 := by exact prefixLift 43911
  have htrace : WordTrace (prefixWord ++ tailWord_43911) baseStart_43911 baseEnd_43911 := by
    simpa [prefixWord, tailWord_43911, baseEnd_43911] using wordTrace_append hprefix tailTrace_43911
  have hstable : (prefixWord ++ tailWord_43911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43911).length < 2 ^ (prefixWord ++ tailWord_43911).sum := by decide
  have hdescent : baseEnd_43911 < baseStart_43911 := by decide
  rcases family_descends (prefixWord ++ tailWord_43911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43939 : List Nat := [1, 1, 1, 4, 1, 2, 4, 6]
def baseStart_43939 : Nat := 118140960795 + 43939 * 2 ^ 59
def prefixEnd_43939 : Nat := 4983230072969 + 3 ^ 40 * 43939 * 2
def baseEnd_43939 : Nat := 6684985623113725084573

theorem tailTrace_43939 : CollatzResearch.WordTrace tailWord_43939 prefixEnd_43939 6684985623113725084573 := by
  unfold tailWord_43939
  simp only [CollatzResearch.WordTrace]
  refine ⟨1602586987823982028870871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1068391325215988019247247 1602586987823982028870871)
  ·
    refine ⟨2403880481735973043306307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1602586987823982028870871 2403880481735973043306307)
    ·
      refine ⟨3605820722603959564959461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2403880481735973043306307 3605820722603959564959461)
      ·
        refine ⟨676091385488242418429899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3605820722603959564959461 676091385488242418429899)
        ·
          refine ⟨1014137078232363627644849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 676091385488242418429899 1014137078232363627644849)
          ·
            refine ⟨760602808674272720733637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1014137078232363627644849 760602808674272720733637)
            ·
              refine ⟨142613026626426135137557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 760602808674272720733637 142613026626426135137557)
              ·
                refine ⟨6684985623113725084573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 142613026626426135137557 6684985623113725084573)
                ·
                  rfl

theorem cell20_43939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 6].length) (baseStart_43939 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43939 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43939 prefixEnd_43939 := by exact prefixLift 43939
  have htrace : WordTrace (prefixWord ++ tailWord_43939) baseStart_43939 baseEnd_43939 := by
    simpa [prefixWord, tailWord_43939, baseEnd_43939] using wordTrace_append hprefix tailTrace_43939
  have hstable : (prefixWord ++ tailWord_43939).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43939).length < 2 ^ (prefixWord ++ tailWord_43939).sum := by decide
  have hdescent : baseEnd_43939 < baseStart_43939 := by decide
  rcases family_descends (prefixWord ++ tailWord_43939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43966 : List Nat := [4, 2, 1, 1, 1, 2, 3, 4, 2]
def baseStart_43966 : Nat := 118140960795 + 43966 * 2 ^ 59
def prefixEnd_43966 : Nat := 4983230072969 + 3 ^ 40 * 43966 * 2
def baseEnd_43966 : Nat := 20067280405049081353609

theorem tailTrace_43966 : CollatzResearch.WordTrace tailWord_43966 prefixEnd_43966 20067280405049081353609 := by
  unfold tailWord_43966
  simp only [CollatzResearch.WordTrace]
  refine ⟨200446469840770705012969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1069047839150777093402501 200446469840770705012969)
  ·
    refine ⟨150334852380578028759727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200446469840770705012969 150334852380578028759727)
    ·
      refine ⟨225502278570867043139591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150334852380578028759727 225502278570867043139591)
      ·
        refine ⟨338253417856300564709387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225502278570867043139591 338253417856300564709387)
        ·
          refine ⟨507380126784450847064081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338253417856300564709387 507380126784450847064081)
          ·
            refine ⟨380535095088338135298061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 507380126784450847064081 380535095088338135298061)
            ·
              refine ⟨142700660658126800736773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 380535095088338135298061 142700660658126800736773)
              ·
                refine ⟨26756373873398775138145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142700660658126800736773 26756373873398775138145)
                ·
                  refine ⟨20067280405049081353609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26756373873398775138145 20067280405049081353609)
                  ·
                    rfl

theorem cell20_43966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_43966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43966 prefixEnd_43966 := by exact prefixLift 43966
  have htrace : WordTrace (prefixWord ++ tailWord_43966) baseStart_43966 baseEnd_43966 := by
    simpa [prefixWord, tailWord_43966, baseEnd_43966] using wordTrace_append hprefix tailTrace_43966
  have hstable : (prefixWord ++ tailWord_43966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43966).length < 2 ^ (prefixWord ++ tailWord_43966).sum := by decide
  have hdescent : baseEnd_43966 < baseStart_43966 := by decide
  rcases family_descends (prefixWord ++ tailWord_43966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43984 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 7]
def baseStart_43984 : Nat := 118140960795 + 43984 * 2 ^ 59
def prefixEnd_43984 : Nat := 4983230072969 + 3 ^ 40 * 43984 * 2
def baseEnd_43984 : Nat := 20075496095521018753535

theorem tailTrace_43984 : CollatzResearch.WordTrace tailWord_43984 prefixEnd_43984 20075496095521018753535 := by
  unfold tailWord_43984
  simp only [CollatzResearch.WordTrace]
  refine ⟨802114136330477357129503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1069485515107303142839337 802114136330477357129503)
  ·
    refine ⟨1203171204495716035694255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 802114136330477357129503 1203171204495716035694255)
    ·
      refine ⟨1804756806743574053541383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1203171204495716035694255 1804756806743574053541383)
      ·
        refine ⟨2707135210115361080312075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1804756806743574053541383 2707135210115361080312075)
        ·
          refine ⟨4060702815173041620468113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2707135210115361080312075 4060702815173041620468113)
          ·
            refine ⟨3045527111379781215351085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4060702815173041620468113 3045527111379781215351085)
            ·
              refine ⟨1142072666767417955756657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3045527111379781215351085 1142072666767417955756657)
              ·
                refine ⟨856554500075563466817493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1142072666767417955756657 856554500075563466817493)
                ·
                  refine ⟨20075496095521018753535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 856554500075563466817493 20075496095521018753535)
                  ·
                    rfl

theorem cell20_43984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_43984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43984 prefixEnd_43984 := by exact prefixLift 43984
  have htrace : WordTrace (prefixWord ++ tailWord_43984) baseStart_43984 baseEnd_43984 := by
    simpa [prefixWord, tailWord_43984, baseEnd_43984] using wordTrace_append hprefix tailTrace_43984
  have hstable : (prefixWord ++ tailWord_43984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43984).length < 2 ^ (prefixWord ++ tailWord_43984).sum := by decide
  have hdescent : baseEnd_43984 < baseStart_43984 := by decide
  rcases family_descends (prefixWord ++ tailWord_43984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_43990 : List Nat := [5, 2, 1, 1, 2, 2, 3, 4]
def baseStart_43990 : Nat := 118140960795 + 43990 * 2 ^ 59
def prefixEnd_43990 : Nat := 4983230072969 + 3 ^ 40 * 43990 * 2
def baseEnd_43990 : Nat := 6692744886337221517837

theorem tailTrace_43990 : CollatzResearch.WordTrace tailWord_43990 prefixEnd_43990 6692744886337221517837 := by
  unfold tailWord_43990
  simp only [CollatzResearch.WordTrace]
  refine ⟨100277944414951108686089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1069631407092811825984949 100277944414951108686089)
  ·
    refine ⟨75208458311213331514567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100277944414951108686089 75208458311213331514567)
    ·
      refine ⟨112812687466819997271851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75208458311213331514567 112812687466819997271851)
      ·
        refine ⟨169219031200229995907777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112812687466819997271851 169219031200229995907777)
        ·
          refine ⟨126914273400172496930833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169219031200229995907777 126914273400172496930833)
          ·
            refine ⟨95185705050129372698125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126914273400172496930833 95185705050129372698125)
            ·
              refine ⟨35694639393798514761797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95185705050129372698125 35694639393798514761797)
              ·
                refine ⟨6692744886337221517837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35694639393798514761797 6692744886337221517837)
                ·
                  rfl

theorem cell20_43990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_43990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_43990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_43990 prefixEnd_43990 := by exact prefixLift 43990
  have htrace : WordTrace (prefixWord ++ tailWord_43990) baseStart_43990 baseEnd_43990 := by
    simpa [prefixWord, tailWord_43990, baseEnd_43990] using wordTrace_append hprefix tailTrace_43990
  have hstable : (prefixWord ++ tailWord_43990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_43990).length < 2 ^ (prefixWord ++ tailWord_43990).sum := by decide
  have hdescent : baseEnd_43990 < baseStart_43990 := by decide
  rcases family_descends (prefixWord ++ tailWord_43990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44014 : List Nat := [4, 1, 2, 1, 5, 1, 1, 2, 3]
def baseStart_44014 : Nat := 118140960795 + 44014 * 2 ^ 59
def prefixEnd_44014 : Nat := 4983230072969 + 3 ^ 40 * 44014 * 2
def baseEnd_44014 : Nat := 20089188912974247753413

theorem tailTrace_44014 : CollatzResearch.WordTrace tailWord_44014 prefixEnd_44014 20089188912974247753413 := by
  unfold tailWord_44014
  simp only [CollatzResearch.WordTrace]
  refine ⟨200665307819033729731387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1070214975034846558567397 200665307819033729731387)
  ·
    refine ⟨300997961728550594597081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 200665307819033729731387 300997961728550594597081)
    ·
      refine ⟨225748471296412945947811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300997961728550594597081 225748471296412945947811)
      ·
        refine ⟨338622706944619418921717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225748471296412945947811 338622706944619418921717)
        ·
          refine ⟨31745878776058070523911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 338622706944619418921717 31745878776058070523911)
          ·
            refine ⟨47618818164087105785867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31745878776058070523911 47618818164087105785867)
            ·
              refine ⟨71428227246130658678801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47618818164087105785867 71428227246130658678801)
              ·
                refine ⟨53571170434597994009101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71428227246130658678801 53571170434597994009101)
                ·
                  refine ⟨20089188912974247753413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53571170434597994009101 20089188912974247753413)
                  ·
                    rfl

theorem cell20_44014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_44014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44014 prefixEnd_44014 := by exact prefixLift 44014
  have htrace : WordTrace (prefixWord ++ tailWord_44014) baseStart_44014 baseEnd_44014 := by
    simpa [prefixWord, tailWord_44014, baseEnd_44014] using wordTrace_append hprefix tailTrace_44014
  have hstable : (prefixWord ++ tailWord_44014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44014).length < 2 ^ (prefixWord ++ tailWord_44014).sum := by decide
  have hdescent : baseEnd_44014 < baseStart_44014 := by decide
  rcases family_descends (prefixWord ++ tailWord_44014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44015 : List Nat := [1, 1, 2, 1, 4, 4, 7]
def baseStart_44015 : Nat := 118140960795 + 44015 * 2 ^ 59
def prefixEnd_44015 : Nat := 4983230072969 + 3 ^ 40 * 44015 * 2
def baseEnd_44015 : Nat := 2232182815580298746675

theorem tailTrace_44015 : CollatzResearch.WordTrace tailWord_44015 prefixEnd_44015 2232182815580298746675 := by
  unfold tailWord_44015
  simp only [CollatzResearch.WordTrace]
  refine ⟨1605358935548647008637499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1070239290365764672424999 1605358935548647008637499)
  ·
    refine ⟨2408038403322970512956249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1605358935548647008637499 2408038403322970512956249)
    ·
      refine ⟨1806028802492227884717187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2408038403322970512956249 1806028802492227884717187)
      ·
        refine ⟨2709043203738341827075781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1806028802492227884717187 2709043203738341827075781)
        ·
          refine ⟨507945600700939092576709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2709043203738341827075781 507945600700939092576709)
          ·
            refine ⟨95239800131426079858133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 507945600700939092576709 95239800131426079858133)
            ·
              refine ⟨2232182815580298746675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 95239800131426079858133 2232182815580298746675)
              ·
                rfl

theorem cell20_44015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 7].length) (baseStart_44015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44015 prefixEnd_44015 := by exact prefixLift 44015
  have htrace : WordTrace (prefixWord ++ tailWord_44015) baseStart_44015 baseEnd_44015 := by
    simpa [prefixWord, tailWord_44015, baseEnd_44015] using wordTrace_append hprefix tailTrace_44015
  have hstable : (prefixWord ++ tailWord_44015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44015).length < 2 ^ (prefixWord ++ tailWord_44015).sum := by decide
  have hdescent : baseEnd_44015 < baseStart_44015 := by decide
  rcases family_descends (prefixWord ++ tailWord_44015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44021 : List Nat := [1, 3, 5, 2, 1, 1, 2, 1, 4]
def baseStart_44021 : Nat := 118140960795 + 44021 * 2 ^ 59
def prefixEnd_44021 : Nat := 4983230072969 + 3 ^ 40 * 44021 * 2
def baseEnd_44021 : Nat := 20092383903713334520051

theorem tailTrace_44021 : CollatzResearch.WordTrace tailWord_44021 prefixEnd_44021 20092383903713334520051 := by
  unfold tailWord_44021
  simp only [CollatzResearch.WordTrace]
  refine ⟨1605577773526910033355917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1070385182351273355570611 1605577773526910033355917)
  ·
    refine ⟨602091665072591262508469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1605577773526910033355917 602091665072591262508469)
    ·
      refine ⟨56446093600555430860169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 602091665072591262508469 56446093600555430860169)
      ·
        refine ⟨42334570200416573145127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56446093600555430860169 42334570200416573145127)
        ·
          refine ⟨63501855300624859717691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42334570200416573145127 63501855300624859717691)
          ·
            refine ⟨95252782950937289576537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63501855300624859717691 95252782950937289576537)
            ·
              refine ⟨71439587213202967182403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95252782950937289576537 71439587213202967182403)
              ·
                refine ⟨107159380819804450773605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71439587213202967182403 107159380819804450773605)
                ·
                  refine ⟨20092383903713334520051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107159380819804450773605 20092383903713334520051)
                  ·
                    rfl

theorem cell20_44021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 4].length) (baseStart_44021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44021 prefixEnd_44021 := by exact prefixLift 44021
  have htrace : WordTrace (prefixWord ++ tailWord_44021) baseStart_44021 baseEnd_44021 := by
    simpa [prefixWord, tailWord_44021, baseEnd_44021] using wordTrace_append hprefix tailTrace_44021
  have hstable : (prefixWord ++ tailWord_44021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44021).length < 2 ^ (prefixWord ++ tailWord_44021).sum := by decide
  have hdescent : baseEnd_44021 < baseStart_44021 := by decide
  rcases family_descends (prefixWord ++ tailWord_44021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44025 : List Nat := [1, 2, 1, 3, 1, 3, 1, 6, 2]
def baseStart_44025 : Nat := 118140960795 + 44025 * 2 ^ 59
def prefixEnd_44025 : Nat := 4983230072969 + 3 ^ 40 * 44025 * 2
def baseEnd_44025 : Nat := 20094209612707098386701

theorem tailTrace_44025 : CollatzResearch.WordTrace tailWord_44025 prefixEnd_44025 20094209612707098386701 := by
  unfold tailWord_44025
  simp only [CollatzResearch.WordTrace]
  refine ⟨1605723665512418716501529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1070482443674945811001019 1605723665512418716501529)
  ·
    refine ⟨1204292749134314037376147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1605723665512418716501529 1204292749134314037376147)
    ·
      refine ⟨1806439123701471056064221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1204292749134314037376147 1806439123701471056064221)
      ·
        refine ⟨677414671388051646024083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1806439123701471056064221 677414671388051646024083)
        ·
          refine ⟨1016122007082077469036125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 677414671388051646024083 1016122007082077469036125)
          ·
            refine ⟨381045752655779050888547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1016122007082077469036125 381045752655779050888547)
            ·
              refine ⟨571568628983668576332821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381045752655779050888547 571568628983668576332821)
              ·
                refine ⟨26792279483609464515601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 571568628983668576332821 26792279483609464515601)
                ·
                  refine ⟨20094209612707098386701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26792279483609464515601 20094209612707098386701)
                  ·
                    rfl

theorem cell20_44025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 6, 2].length) (baseStart_44025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44025 prefixEnd_44025 := by exact prefixLift 44025
  have htrace : WordTrace (prefixWord ++ tailWord_44025) baseStart_44025 baseEnd_44025 := by
    simpa [prefixWord, tailWord_44025, baseEnd_44025] using wordTrace_append hprefix tailTrace_44025
  have hstable : (prefixWord ++ tailWord_44025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44025).length < 2 ^ (prefixWord ++ tailWord_44025).sum := by decide
  have hdescent : baseEnd_44025 < baseStart_44025 := by decide
  rcases family_descends (prefixWord ++ tailWord_44025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44080 : List Nat := [2, 1, 1, 1, 2, 4, 5, 2, 2]
def baseStart_44080 : Nat := 118140960795 + 44080 * 2 ^ 59
def prefixEnd_44080 : Nat := 4983230072969 + 3 ^ 40 * 44080 * 2
def baseEnd_44080 : Nat := 20119313111371351553143

theorem tailTrace_44080 : CollatzResearch.WordTrace tailWord_44080 prefixEnd_44080 20119313111371351553143 := by
  unfold tailWord_44080
  simp only [CollatzResearch.WordTrace]
  refine ⟨803864840156581554876847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1071819786875442073169129 803864840156581554876847)
  ·
    refine ⟨1205797260234872332315271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 803864840156581554876847 1205797260234872332315271)
    ·
      refine ⟨1808695890352308498472907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1205797260234872332315271 1808695890352308498472907)
      ·
        refine ⟨2713043835528462747709361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1808695890352308498472907 2713043835528462747709361)
        ·
          refine ⟨2034782876646347060782021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2713043835528462747709361 2034782876646347060782021)
          ·
            refine ⟨381521789371190073896629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2034782876646347060782021 381521789371190073896629)
            ·
              refine ⟨35767667753549069427809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 381521789371190073896629 35767667753549069427809)
              ·
                refine ⟨26825750815161802070857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35767667753549069427809 26825750815161802070857)
                ·
                  refine ⟨20119313111371351553143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26825750815161802070857 20119313111371351553143)
                  ·
                    rfl

theorem cell20_44080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 2, 2].length) (baseStart_44080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44080 prefixEnd_44080 := by exact prefixLift 44080
  have htrace : WordTrace (prefixWord ++ tailWord_44080) baseStart_44080 baseEnd_44080 := by
    simpa [prefixWord, tailWord_44080, baseEnd_44080] using wordTrace_append hprefix tailTrace_44080
  have hstable : (prefixWord ++ tailWord_44080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44080).length < 2 ^ (prefixWord ++ tailWord_44080).sum := by decide
  have hdescent : baseEnd_44080 < baseStart_44080 := by decide
  rcases family_descends (prefixWord ++ tailWord_44080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44125 : List Nat := [1, 4, 4, 1, 3, 7]
def baseStart_44125 : Nat := 118140960795 + 44125 * 2 ^ 59
def prefixEnd_44125 : Nat := 4983230072969 + 3 ^ 40 * 44125 * 2
def baseEnd_44125 : Nat := 745920456946340557517

theorem tailTrace_44125 : CollatzResearch.WordTrace tailWord_44125 prefixEnd_44125 745920456946340557517 := by
  unfold tailWord_44125
  simp only [CollatzResearch.WordTrace]
  refine ⟨1609370965150135795141829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1072913976766757196761219 1609370965150135795141829)
  ·
    refine ⟨301757055965650461589093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1609370965150135795141829 301757055965650461589093)
    ·
      refine ⟨56579447993559461547955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 301757055965650461589093 56579447993559461547955)
      ·
        refine ⟨84869171990339192321933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56579447993559461547955 84869171990339192321933)
        ·
          refine ⟨31825939496377197120725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84869171990339192321933 31825939496377197120725)
          ·
            refine ⟨745920456946340557517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 31825939496377197120725 745920456946340557517)
            ·
              rfl

theorem cell20_44125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 7].length) (baseStart_44125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44125 prefixEnd_44125 := by exact prefixLift 44125
  have htrace : WordTrace (prefixWord ++ tailWord_44125) baseStart_44125 baseEnd_44125 := by
    simpa [prefixWord, tailWord_44125, baseEnd_44125] using wordTrace_append hprefix tailTrace_44125
  have hstable : (prefixWord ++ tailWord_44125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44125).length < 2 ^ (prefixWord ++ tailWord_44125).sum := by decide
  have hdescent : baseEnd_44125 < baseStart_44125 := by decide
  rcases family_descends (prefixWord ++ tailWord_44125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44135 : List Nat := [1, 1, 5, 1, 1, 5, 2, 2, 2]
def baseStart_44135 : Nat := 118140960795 + 44135 * 2 ^ 59
def prefixEnd_44135 : Nat := 4983230072969 + 3 ^ 40 * 44135 * 2
def baseEnd_44135 : Nat := 20144416610035604719585

theorem tailTrace_44135 : CollatzResearch.WordTrace tailWord_44135 prefixEnd_44135 20144416610035604719585 := by
  unfold tailWord_44135
  simp only [CollatzResearch.WordTrace]
  refine ⟨1609735695113907503005859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1073157130075938335337239 1609735695113907503005859)
  ·
    refine ⟨2414603542670861254508789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1609735695113907503005859 2414603542670861254508789)
    ·
      refine ⟨226369082125393242610199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2414603542670861254508789 226369082125393242610199)
      ·
        refine ⟨339553623188089863915299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226369082125393242610199 339553623188089863915299)
        ·
          refine ⟨509330434782134795872949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339553623188089863915299 509330434782134795872949)
          ·
            refine ⟨47749728260825137113089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 509330434782134795872949 47749728260825137113089)
            ·
              refine ⟨35812296195618852834817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47749728260825137113089 35812296195618852834817)
              ·
                refine ⟨26859222146714139626113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35812296195618852834817 26859222146714139626113)
                ·
                  refine ⟨20144416610035604719585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26859222146714139626113 20144416610035604719585)
                  ·
                    rfl

theorem cell20_44135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 2, 2].length) (baseStart_44135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44135 prefixEnd_44135 := by exact prefixLift 44135
  have htrace : WordTrace (prefixWord ++ tailWord_44135) baseStart_44135 baseEnd_44135 := by
    simpa [prefixWord, tailWord_44135, baseEnd_44135] using wordTrace_append hprefix tailTrace_44135
  have hstable : (prefixWord ++ tailWord_44135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44135).length < 2 ^ (prefixWord ++ tailWord_44135).sum := by decide
  have hdescent : baseEnd_44135 < baseStart_44135 := by decide
  rcases family_descends (prefixWord ++ tailWord_44135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44194 : List Nat := [3, 3, 1, 3, 2, 1, 2, 1, 4]
def baseStart_44194 : Nat := 118140960795 + 44194 * 2 ^ 59
def prefixEnd_44194 : Nat := 4983230072969 + 3 ^ 40 * 44194 * 2
def baseEnd_44194 : Nat := 20171345817693621752677

theorem tailTrace_44194 : CollatzResearch.WordTrace tailWord_44194 prefixEnd_44194 20171345817693621752677 := by
  unfold tailWord_44194
  simp only [CollatzResearch.WordTrace]
  refine ⟨402971900475040144850909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1074591734600107052935757 402971900475040144850909)
  ·
    refine ⟨151114462678140054319091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 402971900475040144850909 151114462678140054319091)
    ·
      refine ⟨226671694017210081478637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151114462678140054319091 226671694017210081478637)
      ·
        refine ⟨85001885256453780554489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226671694017210081478637 85001885256453780554489)
        ·
          refine ⟨63751413942340335415867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85001885256453780554489 63751413942340335415867)
          ·
            refine ⟨95627120913510503123801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63751413942340335415867 95627120913510503123801)
            ·
              refine ⟨71720340685132877342851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95627120913510503123801 71720340685132877342851)
              ·
                refine ⟨107580511027699316014277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71720340685132877342851 107580511027699316014277)
                ·
                  refine ⟨20171345817693621752677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107580511027699316014277 20171345817693621752677)
                  ·
                    rfl

theorem cell20_44194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_44194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44194 prefixEnd_44194 := by exact prefixLift 44194
  have htrace : WordTrace (prefixWord ++ tailWord_44194) baseStart_44194 baseEnd_44194 := by
    simpa [prefixWord, tailWord_44194, baseEnd_44194] using wordTrace_append hprefix tailTrace_44194
  have hstable : (prefixWord ++ tailWord_44194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44194).length < 2 ^ (prefixWord ++ tailWord_44194).sum := by decide
  have hdescent : baseEnd_44194 < baseStart_44194 := by decide
  rcases family_descends (prefixWord ++ tailWord_44194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44214 : List Nat := [5, 1, 3, 2, 2, 1, 2, 4]
def baseStart_44214 : Nat := 118140960795 + 44214 * 2 ^ 59
def prefixEnd_44214 : Nat := 4983230072969 + 3 ^ 40 * 44214 * 2
def baseEnd_44214 : Nat := 6726824787554147028643

theorem tailTrace_44214 : CollatzResearch.WordTrace tailWord_44214 prefixEnd_44214 6726824787554147028643 := by
  unfold tailWord_44214
  simp only [CollatzResearch.WordTrace]
  refine ⟨100788566364231499695731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1075078041218469330087797 100788566364231499695731)
  ·
    refine ⟨151182849546347249543597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100788566364231499695731 151182849546347249543597)
    ·
      refine ⟨56693568579880218578849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151182849546347249543597 56693568579880218578849)
      ·
        refine ⟨42520176434910163934137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56693568579880218578849 42520176434910163934137)
        ·
          refine ⟨31890132326182622950603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42520176434910163934137 31890132326182622950603)
          ·
            refine ⟨47835198489273934425905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31890132326182622950603 47835198489273934425905)
            ·
              refine ⟨35876398866955450819429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47835198489273934425905 35876398866955450819429)
              ·
                refine ⟨6726824787554147028643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35876398866955450819429 6726824787554147028643)
                ·
                  rfl

theorem cell20_44214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_44214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44214 prefixEnd_44214 := by exact prefixLift 44214
  have htrace : WordTrace (prefixWord ++ tailWord_44214) baseStart_44214 baseEnd_44214 := by
    simpa [prefixWord, tailWord_44214, baseEnd_44214] using wordTrace_append hprefix tailTrace_44214
  have hstable : (prefixWord ++ tailWord_44214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44214).length < 2 ^ (prefixWord ++ tailWord_44214).sum := by decide
  have hdescent : baseEnd_44214 < baseStart_44214 := by decide
  rcases family_descends (prefixWord ++ tailWord_44214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44219 : List Nat := [1, 1, 1, 1, 1, 2, 4, 3, 6]
def baseStart_44219 : Nat := 118140960795 + 44219 * 2 ^ 59
def prefixEnd_44219 : Nat := 4983230072969 + 3 ^ 40 * 44219 * 2
def baseEnd_44219 : Nat := 20182756498904645919241

theorem tailTrace_44219 : CollatzResearch.WordTrace tailWord_44219 prefixEnd_44219 20182756498904645919241 := by
  unfold tailWord_44219
  simp only [CollatzResearch.WordTrace]
  refine ⟨1612799426809589849063711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1075199617873059899375807 1612799426809589849063711)
  ·
    refine ⟨2419199140214384773595567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1612799426809589849063711 2419199140214384773595567)
    ·
      refine ⟨3628798710321577160393351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2419199140214384773595567 3628798710321577160393351)
      ·
        refine ⟨5443198065482365740590027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3628798710321577160393351 5443198065482365740590027)
        ·
          refine ⟨8164797098223548610885041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5443198065482365740590027 8164797098223548610885041)
          ·
            refine ⟨6123597823667661458163781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8164797098223548610885041 6123597823667661458163781)
            ·
              refine ⟨1148174591937686523405709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6123597823667661458163781 1148174591937686523405709)
              ·
                refine ⟨430565471976632446277141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1148174591937686523405709 430565471976632446277141)
                ·
                  refine ⟨20182756498904645919241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 430565471976632446277141 20182756498904645919241)
                  ·
                    rfl

theorem cell20_44219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 6].length) (baseStart_44219 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44219 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44219 prefixEnd_44219 := by exact prefixLift 44219
  have htrace : WordTrace (prefixWord ++ tailWord_44219) baseStart_44219 baseEnd_44219 := by
    simpa [prefixWord, tailWord_44219, baseEnd_44219] using wordTrace_append hprefix tailTrace_44219
  have hstable : (prefixWord ++ tailWord_44219).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44219).length < 2 ^ (prefixWord ++ tailWord_44219).sum := by decide
  have hdescent : baseEnd_44219 < baseStart_44219 := by decide
  rcases family_descends (prefixWord ++ tailWord_44219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44222 : List Nat := [4, 2, 1, 1, 3, 2, 1, 6]
def baseStart_44222 : Nat := 118140960795 + 44222 * 2 ^ 59
def prefixEnd_44222 : Nat := 4983230072969 + 3 ^ 40 * 44222 * 2
def baseEnd_44222 : Nat := 6728041926883322939743

theorem tailTrace_44222 : CollatzResearch.WordTrace tailWord_44222 prefixEnd_44222 6728041926883322939743 := by
  unfold tailWord_44222
  simp only [CollatzResearch.WordTrace]
  refine ⟨201613605724840170177865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1075272563865814240948613 201613605724840170177865)
  ·
    refine ⟨151210204293630127633399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201613605724840170177865 151210204293630127633399)
    ·
      refine ⟨226815306440445191450099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151210204293630127633399 226815306440445191450099)
      ·
        refine ⟨340222959660667787175149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226815306440445191450099 340222959660667787175149)
        ·
          refine ⟨127583609872750420190681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 340222959660667787175149 127583609872750420190681)
          ·
            refine ⟨95687707404562815143011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127583609872750420190681 95687707404562815143011)
            ·
              refine ⟨143531561106844222714517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95687707404562815143011 143531561106844222714517)
              ·
                refine ⟨6728041926883322939743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 143531561106844222714517 6728041926883322939743)
                ·
                  rfl

theorem cell20_44222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_44222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44222 prefixEnd_44222 := by exact prefixLift 44222
  have htrace : WordTrace (prefixWord ++ tailWord_44222) baseStart_44222 baseEnd_44222 := by
    simpa [prefixWord, tailWord_44222, baseEnd_44222] using wordTrace_append hprefix tailTrace_44222
  have hstable : (prefixWord ++ tailWord_44222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44222).length < 2 ^ (prefixWord ++ tailWord_44222).sum := by decide
  have hdescent : baseEnd_44222 < baseStart_44222 := by decide
  rcases family_descends (prefixWord ++ tailWord_44222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44228 : List Nat := [2, 3, 3, 1, 4, 1, 1, 3, 2]
def baseStart_44228 : Nat := 118140960795 + 44228 * 2 ^ 59
def prefixEnd_44228 : Nat := 4983230072969 + 3 ^ 40 * 44228 * 2
def baseEnd_44228 : Nat := 20186864344140614619205

theorem tailTrace_44228 : CollatzResearch.WordTrace tailWord_44228 prefixEnd_44228 20186864344140614619205 := by
  unfold tailWord_44228
  simp only [CollatzResearch.WordTrace]
  refine ⟨806563841888492193070669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1075418455851322924094225 806563841888492193070669)
  ·
    refine ⟨302461440708184572401501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 806563841888492193070669 302461440708184572401501)
    ·
      refine ⟨113423040265569214650563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302461440708184572401501 113423040265569214650563)
      ·
        refine ⟨170134560398353821975845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113423040265569214650563 170134560398353821975845)
        ·
          refine ⟨31900230074691341620471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170134560398353821975845 31900230074691341620471)
          ·
            refine ⟨47850345112037012430707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31900230074691341620471 47850345112037012430707)
            ·
              refine ⟨71775517668055518646061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47850345112037012430707 71775517668055518646061)
              ·
                refine ⟨26915819125520819492273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71775517668055518646061 26915819125520819492273)
                ·
                  refine ⟨20186864344140614619205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26915819125520819492273 20186864344140614619205)
                  ·
                    rfl

theorem cell20_44228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_44228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44228 prefixEnd_44228 := by exact prefixLift 44228
  have htrace : WordTrace (prefixWord ++ tailWord_44228) baseStart_44228 baseEnd_44228 := by
    simpa [prefixWord, tailWord_44228, baseEnd_44228] using wordTrace_append hprefix tailTrace_44228
  have hstable : (prefixWord ++ tailWord_44228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44228).length < 2 ^ (prefixWord ++ tailWord_44228).sum := by decide
  have hdescent : baseEnd_44228 < baseStart_44228 := by decide
  rcases family_descends (prefixWord ++ tailWord_44228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44267 : List Nat := [1, 1, 1, 1, 2, 7, 1, 3, 3]
def baseStart_44267 : Nat := 118140960795 + 44267 * 2 ^ 59
def prefixEnd_44267 : Nat := 4983230072969 + 3 ^ 40 * 44267 * 2
def baseEnd_44267 : Nat := 20204665006829812319045

theorem tailTrace_44267 : CollatzResearch.WordTrace tailWord_44267 prefixEnd_44267 20204665006829812319045 := by
  unfold tailWord_44267
  simp only [CollatzResearch.WordTrace]
  refine ⟨1614550130635694046811055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1076366753757129364540703 1614550130635694046811055)
  ·
    refine ⟨2421825195953541070216583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1614550130635694046811055 2421825195953541070216583)
    ·
      refine ⟨3632737793930311605324875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2421825195953541070216583 3632737793930311605324875)
      ·
        refine ⟨5449106690895467407987313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3632737793930311605324875 5449106690895467407987313)
        ·
          refine ⟨4086830018171600555990485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5449106690895467407987313 4086830018171600555990485)
          ·
            refine ⟨95785078550896888031027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 4086830018171600555990485 95785078550896888031027)
            ·
              refine ⟨143677617826345332046541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95785078550896888031027 143677617826345332046541)
              ·
                refine ⟨53879106684879499517453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143677617826345332046541 53879106684879499517453)
                ·
                  refine ⟨20204665006829812319045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53879106684879499517453 20204665006829812319045)
                  ·
                    rfl

theorem cell20_44267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 3].length) (baseStart_44267 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44267 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44267 prefixEnd_44267 := by exact prefixLift 44267
  have htrace : WordTrace (prefixWord ++ tailWord_44267) baseStart_44267 baseEnd_44267 := by
    simpa [prefixWord, tailWord_44267, baseEnd_44267] using wordTrace_append hprefix tailTrace_44267
  have hstable : (prefixWord ++ tailWord_44267).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44267).length < 2 ^ (prefixWord ++ tailWord_44267).sum := by decide
  have hdescent : baseEnd_44267 < baseStart_44267 := by decide
  rcases family_descends (prefixWord ++ tailWord_44267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44305 : List Nat := [1, 2, 2, 1, 1, 4, 4, 2, 3]
def baseStart_44305 : Nat := 118140960795 + 44305 * 2 ^ 59
def prefixEnd_44305 : Nat := 4983230072969 + 3 ^ 40 * 44305 * 2
def baseEnd_44305 : Nat := 20222009242270569052223

theorem tailTrace_44305 : CollatzResearch.WordTrace tailWord_44305 prefixEnd_44305 20222009242270569052223 := by
  unfold tailWord_44305
  simp only [CollatzResearch.WordTrace]
  refine ⟨1615936104498026536694369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1077290736332017691129579 1615936104498026536694369)
  ·
    refine ⟨1211952078373519902520777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1615936104498026536694369 1211952078373519902520777)
    ·
      refine ⟨908964058780139926890583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1211952078373519902520777 908964058780139926890583)
      ·
        refine ⟨1363446088170209890335875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 908964058780139926890583 1363446088170209890335875)
        ·
          refine ⟨2045169132255314835503813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1363446088170209890335875 2045169132255314835503813)
          ·
            refine ⟨383469212297871531656965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2045169132255314835503813 383469212297871531656965)
            ·
              refine ⟨71900477305850912185681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 383469212297871531656965 71900477305850912185681)
              ·
                refine ⟨53925357979388184139261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71900477305850912185681 53925357979388184139261)
                ·
                  refine ⟨20222009242270569052223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53925357979388184139261 20222009242270569052223)
                  ·
                    rfl

theorem cell20_44305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 3].length) (baseStart_44305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44305 prefixEnd_44305 := by exact prefixLift 44305
  have htrace : WordTrace (prefixWord ++ tailWord_44305) baseStart_44305 baseEnd_44305 := by
    simpa [prefixWord, tailWord_44305, baseEnd_44305] using wordTrace_append hprefix tailTrace_44305
  have hstable : (prefixWord ++ tailWord_44305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44305).length < 2 ^ (prefixWord ++ tailWord_44305).sum := by decide
  have hdescent : baseEnd_44305 < baseStart_44305 := by decide
  rcases family_descends (prefixWord ++ tailWord_44305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44342 : List Nat := [5, 1, 2, 3, 1, 1, 2, 3, 2]
def baseStart_44342 : Nat := 118140960795 + 44342 * 2 ^ 59
def prefixEnd_44342 : Nat := 4983230072969 + 3 ^ 40 * 44342 * 2
def baseEnd_44342 : Nat := 20238897050462884818739

theorem tailTrace_44342 : CollatzResearch.WordTrace tailWord_44342 prefixEnd_44342 20238897050462884818739 := by
  unfold tailWord_44342
  simp only [CollatzResearch.WordTrace]
  refine ⟨101080350335248865986955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1078190403575987903860853 101080350335248865986955)
  ·
    refine ⟨151620525502873298980433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101080350335248865986955 151620525502873298980433)
    ·
      refine ⟨113715394127154974235325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151620525502873298980433 113715394127154974235325)
      ·
        refine ⟨42643272797683115338247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113715394127154974235325 42643272797683115338247)
        ·
          refine ⟨63964909196524673007371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42643272797683115338247 63964909196524673007371)
          ·
            refine ⟨95947363794787009511057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63964909196524673007371 95947363794787009511057)
            ·
              refine ⟨71960522846090257133293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95947363794787009511057 71960522846090257133293)
              ·
                refine ⟨26985196067283846424985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71960522846090257133293 26985196067283846424985)
                ·
                  refine ⟨20238897050462884818739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26985196067283846424985 20238897050462884818739)
                  ·
                    rfl

theorem cell20_44342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_44342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44342 prefixEnd_44342 := by exact prefixLift 44342
  have htrace : WordTrace (prefixWord ++ tailWord_44342) baseStart_44342 baseEnd_44342 := by
    simpa [prefixWord, tailWord_44342, baseEnd_44342] using wordTrace_append hprefix tailTrace_44342
  have hstable : (prefixWord ++ tailWord_44342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44342).length < 2 ^ (prefixWord ++ tailWord_44342).sum := by decide
  have hdescent : baseEnd_44342 < baseStart_44342 := by decide
  rcases family_descends (prefixWord ++ tailWord_44342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44350 : List Nat := [4, 2, 1, 2, 1, 1, 1, 2, 6]
def baseStart_44350 : Nat := 118140960795 + 44350 * 2 ^ 59
def prefixEnd_44350 : Nat := 4983230072969 + 3 ^ 40 * 44350 * 2
def baseEnd_44350 : Nat := 20242548468450412552039

theorem tailTrace_44350 : CollatzResearch.WordTrace tailWord_44350 prefixEnd_44350 20242548468450412552039 := by
  unfold tailWord_44350
  simp only [CollatzResearch.WordTrace]
  refine ⟨202197173666874902760313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1078384926223332814721669 202197173666874902760313)
  ·
    refine ⟨151647880250156177070235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202197173666874902760313 151647880250156177070235)
    ·
      refine ⟨227471820375234265605353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151647880250156177070235 227471820375234265605353)
      ·
        refine ⟨170603865281425699204015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227471820375234265605353 170603865281425699204015)
        ·
          refine ⟨255905797922138548806023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170603865281425699204015 255905797922138548806023)
          ·
            refine ⟨383858696883207823209035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255905797922138548806023 383858696883207823209035)
            ·
              refine ⟨575788045324811734813553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 383858696883207823209035 575788045324811734813553)
              ·
                refine ⟨431841033993608801110165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 575788045324811734813553 431841033993608801110165)
                ·
                  refine ⟨20242548468450412552039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 431841033993608801110165 20242548468450412552039)
                  ·
                    rfl

theorem cell20_44350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_44350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44350 prefixEnd_44350 := by exact prefixLift 44350
  have htrace : WordTrace (prefixWord ++ tailWord_44350) baseStart_44350 baseEnd_44350 := by
    simpa [prefixWord, tailWord_44350, baseEnd_44350] using wordTrace_append hprefix tailTrace_44350
  have hstable : (prefixWord ++ tailWord_44350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44350).length < 2 ^ (prefixWord ++ tailWord_44350).sum := by decide
  have hdescent : baseEnd_44350 < baseStart_44350 := by decide
  rcases family_descends (prefixWord ++ tailWord_44350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44388 : List Nat := [2, 3, 1, 1, 3, 2, 2, 2, 4]
def baseStart_44388 : Nat := 118140960795 + 44388 * 2 ^ 59
def prefixEnd_44388 : Nat := 4983230072969 + 3 ^ 40 * 44388 * 2
def baseEnd_44388 : Nat := 20259892703891169285217

theorem tailTrace_44388 : CollatzResearch.WordTrace tailWord_44388 prefixEnd_44388 20259892703891169285217 := by
  unfold tailWord_44388
  simp only [CollatzResearch.WordTrace]
  refine ⟨809481681598665855982909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1079308908798221141310545 809481681598665855982909)
  ·
    refine ⟨303555630599499695993591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 809481681598665855982909 303555630599499695993591)
    ·
      refine ⟨455333445899249543990387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303555630599499695993591 455333445899249543990387)
      ·
        refine ⟨683000168848874315985581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455333445899249543990387 683000168848874315985581)
        ·
          refine ⟨256125063318327868494593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 683000168848874315985581 256125063318327868494593)
          ·
            refine ⟨192093797488745901370945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256125063318327868494593 192093797488745901370945)
            ·
              refine ⟨144070348116559426028209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192093797488745901370945 144070348116559426028209)
              ·
                refine ⟨108052761087419569521157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144070348116559426028209 108052761087419569521157)
                ·
                  refine ⟨20259892703891169285217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108052761087419569521157 20259892703891169285217)
                  ·
                    rfl

theorem cell20_44388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_44388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44388 prefixEnd_44388 := by exact prefixLift 44388
  have htrace : WordTrace (prefixWord ++ tailWord_44388) baseStart_44388 baseEnd_44388 := by
    simpa [prefixWord, tailWord_44388, baseEnd_44388] using wordTrace_append hprefix tailTrace_44388
  have hstable : (prefixWord ++ tailWord_44388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44388).length < 2 ^ (prefixWord ++ tailWord_44388).sum := by decide
  have hdescent : baseEnd_44388 < baseStart_44388 := by decide
  rcases family_descends (prefixWord ++ tailWord_44388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44391 : List Nat := [1, 1, 5, 1, 4, 2, 2, 4]
def baseStart_44391 : Nat := 118140960795 + 44391 * 2 ^ 59
def prefixEnd_44391 : Nat := 4983230072969 + 3 ^ 40 * 44391 * 2
def baseEnd_44391 : Nat := 6753753995212164061735

theorem tailTrace_44391 : CollatzResearch.WordTrace tailWord_44391 prefixEnd_44391 6753753995212164061735 := by
  unfold tailWord_44391
  simp only [CollatzResearch.WordTrace]
  refine ⟨1619072782186463224325027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1079381854790975482883351 1619072782186463224325027)
  ·
    refine ⟨2428609173279694836487541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1619072782186463224325027 2428609173279694836487541)
    ·
      refine ⟨227682109994971390920707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2428609173279694836487541 227682109994971390920707)
      ·
        refine ⟨341523164992457086381061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227682109994971390920707 341523164992457086381061)
        ·
          refine ⟨64035593436085703696449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 341523164992457086381061 64035593436085703696449)
          ·
            refine ⟨48026695077064277772337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64035593436085703696449 48026695077064277772337)
            ·
              refine ⟨36020021307798208329253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48026695077064277772337 36020021307798208329253)
              ·
                refine ⟨6753753995212164061735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36020021307798208329253 6753753995212164061735)
                ·
                  rfl

theorem cell20_44391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 4].length) (baseStart_44391 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44391 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44391 prefixEnd_44391 := by exact prefixLift 44391
  have htrace : WordTrace (prefixWord ++ tailWord_44391) baseStart_44391 baseEnd_44391 := by
    simpa [prefixWord, tailWord_44391, baseEnd_44391] using wordTrace_append hprefix tailTrace_44391
  have hstable : (prefixWord ++ tailWord_44391).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44391).length < 2 ^ (prefixWord ++ tailWord_44391).sum := by decide
  have hdescent : baseEnd_44391 < baseStart_44391 := by decide
  rcases family_descends (prefixWord ++ tailWord_44391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44402 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 7]
def baseStart_44402 : Nat := 118140960795 + 44402 * 2 ^ 59
def prefixEnd_44402 : Nat := 4983230072969 + 3 ^ 40 * 44402 * 2
def baseEnd_44402 : Nat := 20266282685369342818493

theorem tailTrace_44402 : CollatzResearch.WordTrace tailWord_44402 prefixEnd_44402 20266282685369342818493 := by
  unfold tailWord_44402
  simp only [CollatzResearch.WordTrace]
  refine ⟨404868496286653025743865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1079649323431074735316973 404868496286653025743865)
  ·
    refine ⟨303651372214989769307899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 404868496286653025743865 303651372214989769307899)
    ·
      refine ⟨455477058322484653961849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303651372214989769307899 455477058322484653961849)
      ·
        refine ⟨341607793741863490471387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 455477058322484653961849 341607793741863490471387)
        ·
          refine ⟨512411690612795235707081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341607793741863490471387 512411690612795235707081)
          ·
            refine ⟨384308767959596426780311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 512411690612795235707081 384308767959596426780311)
            ·
              refine ⟨576463151939394640170467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384308767959596426780311 576463151939394640170467)
              ·
                refine ⟨864694727909091960255701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 576463151939394640170467 864694727909091960255701)
                ·
                  refine ⟨20266282685369342818493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 864694727909091960255701 20266282685369342818493)
                  ·
                    rfl

theorem cell20_44402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_44402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44402 prefixEnd_44402 := by exact prefixLift 44402
  have htrace : WordTrace (prefixWord ++ tailWord_44402) baseStart_44402 baseEnd_44402 := by
    simpa [prefixWord, tailWord_44402, baseEnd_44402] using wordTrace_append hprefix tailTrace_44402
  have hstable : (prefixWord ++ tailWord_44402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44402).length < 2 ^ (prefixWord ++ tailWord_44402).sum := by decide
  have hdescent : baseEnd_44402 < baseStart_44402 := by decide
  rcases family_descends (prefixWord ++ tailWord_44402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44409 : List Nat := [1, 2, 1, 3, 2, 1, 2, 2, 6]
def baseStart_44409 : Nat := 118140960795 + 44409 * 2 ^ 59
def prefixEnd_44409 : Nat := 4983230072969 + 3 ^ 40 * 44409 * 2
def baseEnd_44409 : Nat := 20269477676108429585131

theorem tailTrace_44409 : CollatzResearch.WordTrace tailWord_44409 prefixEnd_44409 20269477676108429585131 := by
  unfold tailWord_44409
  simp only [CollatzResearch.WordTrace]
  refine ⟨1619729296121252298480281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1079819530747501532320187 1619729296121252298480281)
  ·
    refine ⟨1214796972090939223860211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1619729296121252298480281 1214796972090939223860211)
    ·
      refine ⟨1822195458136408835790317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1214796972090939223860211 1822195458136408835790317)
      ·
        refine ⟨683323296801153313421369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1822195458136408835790317 683323296801153313421369)
        ·
          refine ⟨512492472600864985066027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 683323296801153313421369 512492472600864985066027)
          ·
            refine ⟨768738708901297477599041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512492472600864985066027 768738708901297477599041)
            ·
              refine ⟨576554031675973108199281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 768738708901297477599041 576554031675973108199281)
              ·
                refine ⟨432415523756979831149461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 576554031675973108199281 432415523756979831149461)
                ·
                  refine ⟨20269477676108429585131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 432415523756979831149461 20269477676108429585131)
                  ·
                    rfl

theorem cell20_44409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_44409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44409 prefixEnd_44409 := by exact prefixLift 44409
  have htrace : WordTrace (prefixWord ++ tailWord_44409) baseStart_44409 baseEnd_44409 := by
    simpa [prefixWord, tailWord_44409, baseEnd_44409] using wordTrace_append hprefix tailTrace_44409
  have hstable : (prefixWord ++ tailWord_44409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44409).length < 2 ^ (prefixWord ++ tailWord_44409).sum := by decide
  have hdescent : baseEnd_44409 < baseStart_44409 := by decide
  rcases family_descends (prefixWord ++ tailWord_44409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44418 : List Nat := [3, 4, 2, 1, 1, 2, 3, 2, 2]
def baseStart_44418 : Nat := 118140960795 + 44418 * 2 ^ 59
def prefixEnd_44418 : Nat := 4983230072969 + 3 ^ 40 * 44418 * 2
def baseEnd_44418 : Nat := 20273585521344398285095

theorem tailTrace_44418 : CollatzResearch.WordTrace tailWord_44418 prefixEnd_44418 20273585521344398285095 := by
  unfold tailWord_44418
  simp only [CollatzResearch.WordTrace]
  refine ⟨405014388272161708889477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1080038368725764557038605 405014388272161708889477)
  ·
    refine ⟨75940197801030320416777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 405014388272161708889477 75940197801030320416777)
    ·
      refine ⟨56955148350772740312583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75940197801030320416777 56955148350772740312583)
      ·
        refine ⟨85432722526159110468875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56955148350772740312583 85432722526159110468875)
        ·
          refine ⟨128149083789238665703313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85432722526159110468875 128149083789238665703313)
          ·
            refine ⟨96111812841928999277485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128149083789238665703313 96111812841928999277485)
            ·
              refine ⟨36041929815723374729057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96111812841928999277485 36041929815723374729057)
              ·
                refine ⟨27031447361792531046793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36041929815723374729057 27031447361792531046793)
                ·
                  refine ⟨20273585521344398285095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27031447361792531046793 20273585521344398285095)
                  ·
                    rfl

theorem cell20_44418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_44418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44418 prefixEnd_44418 := by exact prefixLift 44418
  have htrace : WordTrace (prefixWord ++ tailWord_44418) baseStart_44418 baseEnd_44418 := by
    simpa [prefixWord, tailWord_44418, baseEnd_44418] using wordTrace_append hprefix tailTrace_44418
  have hstable : (prefixWord ++ tailWord_44418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44418).length < 2 ^ (prefixWord ++ tailWord_44418).sum := by decide
  have hdescent : baseEnd_44418 < baseStart_44418 := by decide
  rcases family_descends (prefixWord ++ tailWord_44418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44436 : List Nat := [2, 4, 2, 1, 2, 2, 1, 3, 3]
def baseStart_44436 : Nat := 118140960795 + 44436 * 2 ^ 59
def prefixEnd_44436 : Nat := 4983230072969 + 3 ^ 40 * 44436 * 2
def baseEnd_44436 : Nat := 20281801211816335685021

theorem tailTrace_44436 : CollatzResearch.WordTrace tailWord_44436 prefixEnd_44436 20281801211816335685021 := by
  unfold tailWord_44436
  simp only [CollatzResearch.WordTrace]
  refine ⟨810357033511717954856581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1080476044682290606475441 810357033511717954856581)
  ·
    refine ⟨151941943783447116535609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 810357033511717954856581 151941943783447116535609)
    ·
      refine ⟨113956457837585337401707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151941943783447116535609 113956457837585337401707)
      ·
        refine ⟨170934686756378006102561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113956457837585337401707 170934686756378006102561)
        ·
          refine ⟨128201015067283504576921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170934686756378006102561 128201015067283504576921)
          ·
            refine ⟨96150761300462628432691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128201015067283504576921 96150761300462628432691)
            ·
              refine ⟨144226141950693942649037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96150761300462628432691 144226141950693942649037)
              ·
                refine ⟨54084803231510228493389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144226141950693942649037 54084803231510228493389)
                ·
                  refine ⟨20281801211816335685021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54084803231510228493389 20281801211816335685021)
                  ·
                    rfl

theorem cell20_44436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_44436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44436 prefixEnd_44436 := by exact prefixLift 44436
  have htrace : WordTrace (prefixWord ++ tailWord_44436) baseStart_44436 baseEnd_44436 := by
    simpa [prefixWord, tailWord_44436, baseEnd_44436] using wordTrace_append hprefix tailTrace_44436
  have hstable : (prefixWord ++ tailWord_44436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44436).length < 2 ^ (prefixWord ++ tailWord_44436).sum := by decide
  have hdescent : baseEnd_44436 < baseStart_44436 := by decide
  rcases family_descends (prefixWord ++ tailWord_44436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44519 : List Nat := [1, 1, 5, 2, 1, 2, 1, 5, 2]
def baseStart_44519 : Nat := 118140960795 + 44519 * 2 ^ 59
def prefixEnd_44519 : Nat := 4983230072969 + 3 ^ 40 * 44519 * 2
def baseEnd_44519 : Nat := 20319684673436935918015

theorem tailTrace_44519 : CollatzResearch.WordTrace tailWord_44519 prefixEnd_44519 20319684673436935918015 := by
  unfold tailWord_44519
  simp only [CollatzResearch.WordTrace]
  refine ⟨1623741325722741084984611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1082494217148494056656407 1623741325722741084984611)
  ·
    refine ⟨2435611988584111627476917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1623741325722741084984611 2435611988584111627476917)
    ·
      refine ⟨228338623929760465075961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2435611988584111627476917 228338623929760465075961)
      ·
        refine ⟨171253967947320348806971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228338623929760465075961 171253967947320348806971)
        ·
          refine ⟨256880951920980523210457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171253967947320348806971 256880951920980523210457)
          ·
            refine ⟨192660713940735392407843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256880951920980523210457 192660713940735392407843)
            ·
              refine ⟨288991070911103088611765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192660713940735392407843 288991070911103088611765)
              ·
                refine ⟨27092912897915914557353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 288991070911103088611765 27092912897915914557353)
                ·
                  refine ⟨20319684673436935918015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27092912897915914557353 20319684673436935918015)
                  ·
                    rfl

theorem cell20_44519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 5, 2].length) (baseStart_44519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44519 prefixEnd_44519 := by exact prefixLift 44519
  have htrace : WordTrace (prefixWord ++ tailWord_44519) baseStart_44519 baseEnd_44519 := by
    simpa [prefixWord, tailWord_44519, baseEnd_44519] using wordTrace_append hprefix tailTrace_44519
  have hstable : (prefixWord ++ tailWord_44519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44519).length < 2 ^ (prefixWord ++ tailWord_44519).sum := by decide
  have hdescent : baseEnd_44519 < baseStart_44519 := by decide
  rcases family_descends (prefixWord ++ tailWord_44519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44561 : List Nat := [1, 2, 2, 1, 1, 2, 3, 4, 4]
def baseStart_44561 : Nat := 118140960795 + 44561 * 2 ^ 59
def prefixEnd_44561 : Nat := 4983230072969 + 3 ^ 40 * 44561 * 2
def baseEnd_44561 : Nat := 20338854617871456517843

theorem tailTrace_44561 : CollatzResearch.WordTrace tailWord_44561 prefixEnd_44561 20338854617871456517843 := by
  unfold tailWord_44561
  simp only [CollatzResearch.WordTrace]
  refine ⟨1625273191570582258013537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1083515461047054838675691 1625273191570582258013537)
  ·
    refine ⟨1218954893677936693510153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1625273191570582258013537 1218954893677936693510153)
    ·
      refine ⟨914216170258452520132615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1218954893677936693510153 914216170258452520132615)
      ·
        refine ⟨1371324255387678780198923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 914216170258452520132615 1371324255387678780198923)
        ·
          refine ⟨2056986383081518170298385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1371324255387678780198923 2056986383081518170298385)
          ·
            refine ⟨1542739787311138627723789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2056986383081518170298385 1542739787311138627723789)
            ·
              refine ⟨578527420241676985396421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1542739787311138627723789 578527420241676985396421)
              ·
                refine ⟨108473891295314434761829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 578527420241676985396421 108473891295314434761829)
                ·
                  refine ⟨20338854617871456517843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108473891295314434761829 20338854617871456517843)
                  ·
                    rfl

theorem cell20_44561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_44561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44561 prefixEnd_44561 := by exact prefixLift 44561
  have htrace : WordTrace (prefixWord ++ tailWord_44561) baseStart_44561 baseEnd_44561 := by
    simpa [prefixWord, tailWord_44561, baseEnd_44561] using wordTrace_append hprefix tailTrace_44561
  have hstable : (prefixWord ++ tailWord_44561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44561).length < 2 ^ (prefixWord ++ tailWord_44561).sum := by decide
  have hdescent : baseEnd_44561 < baseStart_44561 := by decide
  rcases family_descends (prefixWord ++ tailWord_44561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44592 : List Nat := [2, 1, 1, 1, 2, 3, 1, 6, 3]
def baseStart_44592 : Nat := 118140960795 + 44592 * 2 ^ 59
def prefixEnd_44592 : Nat := 4983230072969 + 3 ^ 40 * 44592 * 2
def baseEnd_44592 : Nat := 20353003862573126484383

theorem tailTrace_44592 : CollatzResearch.WordTrace tailWord_44592 prefixEnd_44592 20353003862573126484383 := by
  unfold tailWord_44592
  simp only [CollatzResearch.WordTrace]
  refine ⟨813201927229137276196015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1084269236305516368261353 813201927229137276196015)
  ·
    refine ⟨1219802890843705914294023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 813201927229137276196015 1219802890843705914294023)
    ·
      refine ⟨1829704336265558871441035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1219802890843705914294023 1829704336265558871441035)
      ·
        refine ⟨2744556504398338307161553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1829704336265558871441035 2744556504398338307161553)
        ·
          refine ⟨2058417378298753730371165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2744556504398338307161553 2058417378298753730371165)
          ·
            refine ⟨771906516862032648889187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2058417378298753730371165 771906516862032648889187)
            ·
              refine ⟨1157859775293048973333781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 771906516862032648889187 1157859775293048973333781)
              ·
                refine ⟨54274676966861670625021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1157859775293048973333781 54274676966861670625021)
                ·
                  refine ⟨20353003862573126484383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54274676966861670625021 20353003862573126484383)
                  ·
                    rfl

theorem cell20_44592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 3].length) (baseStart_44592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44592 prefixEnd_44592 := by exact prefixLift 44592
  have htrace : WordTrace (prefixWord ++ tailWord_44592) baseStart_44592 baseEnd_44592 := by
    simpa [prefixWord, tailWord_44592, baseEnd_44592] using wordTrace_append hprefix tailTrace_44592
  have hstable : (prefixWord ++ tailWord_44592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44592).length < 2 ^ (prefixWord ++ tailWord_44592).sum := by decide
  have hdescent : baseEnd_44592 < baseStart_44592 := by decide
  rcases family_descends (prefixWord ++ tailWord_44592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44605 : List Nat := [1, 4, 1, 3, 3, 2, 2, 1, 3]
def baseStart_44605 : Nat := 118140960795 + 44605 * 2 ^ 59
def prefixEnd_44605 : Nat := 4983230072969 + 3 ^ 40 * 44605 * 2
def baseEnd_44605 : Nat := 20358937416802859050997

theorem tailTrace_44605 : CollatzResearch.WordTrace tailWord_44605 prefixEnd_44605 20358937416802859050997 := by
  unfold tailWord_44605
  simp only [CollatzResearch.WordTrace]
  refine ⟨1626878003411177772615269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1084585335607451848410179 1626878003411177772615269)
  ·
    refine ⟨305039625639595832365363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1626878003411177772615269 305039625639595832365363)
    ·
      refine ⟨457559438459393748548045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305039625639595832365363 457559438459393748548045)
      ·
        refine ⟨171584789422272655705517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 457559438459393748548045 171584789422272655705517)
        ·
          refine ⟨64344296033352245889569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171584789422272655705517 64344296033352245889569)
          ·
            refine ⟨48258222025014184417177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64344296033352245889569 48258222025014184417177)
            ·
              refine ⟨36193666518760638312883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48258222025014184417177 36193666518760638312883)
              ·
                refine ⟨54290499778140957469325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36193666518760638312883 54290499778140957469325)
                ·
                  refine ⟨20358937416802859050997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54290499778140957469325 20358937416802859050997)
                  ·
                    rfl

theorem cell20_44605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_44605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44605 prefixEnd_44605 := by exact prefixLift 44605
  have htrace : WordTrace (prefixWord ++ tailWord_44605) baseStart_44605 baseEnd_44605 := by
    simpa [prefixWord, tailWord_44605, baseEnd_44605] using wordTrace_append hprefix tailTrace_44605
  have hstable : (prefixWord ++ tailWord_44605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44605).length < 2 ^ (prefixWord ++ tailWord_44605).sum := by decide
  have hdescent : baseEnd_44605 < baseStart_44605 := by decide
  rcases family_descends (prefixWord ++ tailWord_44605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44609 : List Nat := [1, 2, 5, 1, 1, 1, 3, 3, 3]
def baseStart_44609 : Nat := 118140960795 + 44609 * 2 ^ 59
def prefixEnd_44609 : Nat := 4983230072969 + 3 ^ 40 * 44609 * 2
def baseEnd_44609 : Nat := 20360763125796622917647

theorem tailTrace_44609 : CollatzResearch.WordTrace tailWord_44609 prefixEnd_44609 20360763125796622917647 := by
  unfold tailWord_44609
  simp only [CollatzResearch.WordTrace]
  refine ⟨1627023895396686455760881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1084682596931124303840587 1627023895396686455760881)
  ·
    refine ⟨1220267921547514841820661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1627023895396686455760881 1220267921547514841820661)
    ·
      refine ⟨114400117645079516420687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1220267921547514841820661 114400117645079516420687)
      ·
        refine ⟨171600176467619274631031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114400117645079516420687 171600176467619274631031)
        ·
          refine ⟨257400264701428911946547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171600176467619274631031 257400264701428911946547)
          ·
            refine ⟨386100397052143367919821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257400264701428911946547 386100397052143367919821)
            ·
              refine ⟨144787648894553762969933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 386100397052143367919821 144787648894553762969933)
              ·
                refine ⟨54295368335457661113725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144787648894553762969933 54295368335457661113725)
                ·
                  refine ⟨20360763125796622917647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54295368335457661113725 20360763125796622917647)
                  ·
                    rfl

theorem cell20_44609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 3].length) (baseStart_44609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44609 prefixEnd_44609 := by exact prefixLift 44609
  have htrace : WordTrace (prefixWord ++ tailWord_44609) baseStart_44609 baseEnd_44609 := by
    simpa [prefixWord, tailWord_44609, baseEnd_44609] using wordTrace_append hprefix tailTrace_44609
  have hstable : (prefixWord ++ tailWord_44609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44609).length < 2 ^ (prefixWord ++ tailWord_44609).sum := by decide
  have hdescent : baseEnd_44609 < baseStart_44609 := by decide
  rcases family_descends (prefixWord ++ tailWord_44609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44644 : List Nat := [2, 3, 1, 1, 2, 11]
def baseStart_44644 : Nat := 118140960795 + 44644 * 2 ^ 59
def prefixEnd_44644 : Nat := 4983230072969 + 3 ^ 40 * 44644 * 2
def baseEnd_44644 : Nat := 754694002944150250031

theorem tailTrace_44644 : CollatzResearch.WordTrace tailWord_44644 prefixEnd_44644 754694002944150250031 := by
  unfold tailWord_44644
  simp only [CollatzResearch.WordTrace]
  refine ⟨814150225134943716642493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1085533633513258288856657 814150225134943716642493)
  ·
    refine ⟨305306334425603893740935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 814150225134943716642493 305306334425603893740935)
    ·
      refine ⟨457959501638405840611403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305306334425603893740935 457959501638405840611403)
      ·
        refine ⟨686939252457608760917105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457959501638405840611403 686939252457608760917105)
        ·
          refine ⟨515204439343206570687829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 686939252457608760917105 515204439343206570687829)
          ·
            refine ⟨754694002944150250031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 515204439343206570687829 754694002944150250031)
            ·
              rfl

theorem cell20_44644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 11].length) (baseStart_44644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44644 prefixEnd_44644 := by exact prefixLift 44644
  have htrace : WordTrace (prefixWord ++ tailWord_44644) baseStart_44644 baseEnd_44644 := by
    simpa [prefixWord, tailWord_44644, baseEnd_44644] using wordTrace_append hprefix tailTrace_44644
  have hstable : (prefixWord ++ tailWord_44644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44644).length < 2 ^ (prefixWord ++ tailWord_44644).sum := by decide
  have hdescent : baseEnd_44644 < baseStart_44644 := by decide
  rcases family_descends (prefixWord ++ tailWord_44644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44650 : List Nat := [3, 1, 3, 2, 1, 2, 4, 2, 2]
def baseStart_44650 : Nat := 118140960795 + 44650 * 2 ^ 59
def prefixEnd_44650 : Nat := 4983230072969 + 3 ^ 40 * 44650 * 2
def baseEnd_44650 : Nat := 20379476642982702550813

theorem tailTrace_44650 : CollatzResearch.WordTrace tailWord_44650 prefixEnd_44650 20379476642982702550813 := by
  unfold tailWord_44650
  simp only [CollatzResearch.WordTrace]
  refine ⟨407129822062037614500851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1085679525498766972002269 407129822062037614500851)
  ·
    refine ⟨610694733093056421751277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 407129822062037614500851 610694733093056421751277)
    ·
      refine ⟨229010524909896158156729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 610694733093056421751277 229010524909896158156729)
      ·
        refine ⟨171757893682422118617547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229010524909896158156729 171757893682422118617547)
        ·
          refine ⟨257636840523633177926321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171757893682422118617547 257636840523633177926321)
          ·
            refine ⟨193227630392724883444741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257636840523633177926321 193227630392724883444741)
            ·
              refine ⟨36230180698635915645889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 193227630392724883444741 36230180698635915645889)
              ·
                refine ⟨27172635523976936734417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36230180698635915645889 27172635523976936734417)
                ·
                  refine ⟨20379476642982702550813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27172635523976936734417 20379476642982702550813)
                  ·
                    rfl

theorem cell20_44650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 2, 2].length) (baseStart_44650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44650 prefixEnd_44650 := by exact prefixLift 44650
  have htrace : WordTrace (prefixWord ++ tailWord_44650) baseStart_44650 baseEnd_44650 := by
    simpa [prefixWord, tailWord_44650, baseEnd_44650] using wordTrace_append hprefix tailTrace_44650
  have hstable : (prefixWord ++ tailWord_44650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44650).length < 2 ^ (prefixWord ++ tailWord_44650).sum := by decide
  have hdescent : baseEnd_44650 < baseStart_44650 := by decide
  rcases family_descends (prefixWord ++ tailWord_44650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44651 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 9]
def baseStart_44651 : Nat := 118140960795 + 44651 * 2 ^ 59
def prefixEnd_44651 : Nat := 4983230072969 + 3 ^ 40 * 44651 * 2
def baseEnd_44651 : Nat := 20379933070231143517475

theorem tailTrace_44651 : CollatzResearch.WordTrace tailWord_44651 prefixEnd_44651 20379933070231143517475 := by
  unfold tailWord_44651
  simp only [CollatzResearch.WordTrace]
  refine ⟨1628555761244527628789807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1085703840829685085859871 1628555761244527628789807)
  ·
    refine ⟨2442833641866791443184711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1628555761244527628789807 2442833641866791443184711)
    ·
      refine ⟨3664250462800187164777067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2442833641866791443184711 3664250462800187164777067)
      ·
        refine ⟨5496375694200280747165601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3664250462800187164777067 5496375694200280747165601)
        ·
          refine ⟨4122281770650210560374201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5496375694200280747165601 4122281770650210560374201)
          ·
            refine ⟨3091711327987657920280651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4122281770650210560374201 3091711327987657920280651)
            ·
              refine ⟨4637566991981486880420977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3091711327987657920280651 4637566991981486880420977)
              ·
                refine ⟨3478175243986115160315733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4637566991981486880420977 3478175243986115160315733)
                ·
                  refine ⟨20379933070231143517475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3478175243986115160315733 20379933070231143517475)
                  ·
                    rfl

theorem cell20_44651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 9].length) (baseStart_44651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44651 prefixEnd_44651 := by exact prefixLift 44651
  have htrace : WordTrace (prefixWord ++ tailWord_44651) baseStart_44651 baseEnd_44651 := by
    simpa [prefixWord, tailWord_44651, baseEnd_44651] using wordTrace_append hprefix tailTrace_44651
  have hstable : (prefixWord ++ tailWord_44651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44651).length < 2 ^ (prefixWord ++ tailWord_44651).sum := by decide
  have hdescent : baseEnd_44651 < baseStart_44651 := by decide
  rcases family_descends (prefixWord ++ tailWord_44651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44702 : List Nat := [4, 3, 1, 1, 1, 2, 3, 2, 3]
def baseStart_44702 : Nat := 118140960795 + 44702 * 2 ^ 59
def prefixEnd_44702 : Nat := 4983230072969 + 3 ^ 40 * 44702 * 2
def baseEnd_44702 : Nat := 20403210859901632817267

theorem tailTrace_44702 : CollatzResearch.WordTrace tailWord_44702 prefixEnd_44702 20403210859901632817267 := by
  unfold tailWord_44702
  simp only [CollatzResearch.WordTrace]
  refine ⟨203801985507470417362045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1086943922706508892597573 203801985507470417362045)
  ·
    refine ⟨76425744565301406510767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203801985507470417362045 76425744565301406510767)
    ·
      refine ⟨114638616847952109766151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76425744565301406510767 114638616847952109766151)
      ·
        refine ⟨171957925271928164649227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114638616847952109766151 171957925271928164649227)
        ·
          refine ⟨257936887907892246973841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171957925271928164649227 257936887907892246973841)
          ·
            refine ⟨193452665930919185230381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257936887907892246973841 193452665930919185230381)
            ·
              refine ⟨72544749724094694461393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193452665930919185230381 72544749724094694461393)
              ·
                refine ⟨54408562293071020846045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72544749724094694461393 54408562293071020846045)
                ·
                  refine ⟨20403210859901632817267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54408562293071020846045 20403210859901632817267)
                  ·
                    rfl

theorem cell20_44702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_44702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44702 prefixEnd_44702 := by exact prefixLift 44702
  have htrace : WordTrace (prefixWord ++ tailWord_44702) baseStart_44702 baseEnd_44702 := by
    simpa [prefixWord, tailWord_44702, baseEnd_44702] using wordTrace_append hprefix tailTrace_44702
  have hstable : (prefixWord ++ tailWord_44702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44702).length < 2 ^ (prefixWord ++ tailWord_44702).sum := by decide
  have hdescent : baseEnd_44702 < baseStart_44702 := by decide
  rcases family_descends (prefixWord ++ tailWord_44702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44723 : List Nat := [1, 1, 1, 2, 3, 3, 5, 1, 3]
def baseStart_44723 : Nat := 118140960795 + 44723 * 2 ^ 59
def prefixEnd_44723 : Nat := 4983230072969 + 3 ^ 40 * 44723 * 2
def baseEnd_44723 : Nat := 20412795832118893117181

theorem tailTrace_44723 : CollatzResearch.WordTrace tailWord_44723 prefixEnd_44723 20412795832118893117181 := by
  unfold tailWord_44723
  simp only [CollatzResearch.WordTrace]
  refine ⟨1631181816983683925410823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1087454544655789283607215 1631181816983683925410823)
  ·
    refine ⟨2446772725475525888116235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1631181816983683925410823 2446772725475525888116235)
    ·
      refine ⟨3670159088213288832174353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2446772725475525888116235 3670159088213288832174353)
      ·
        refine ⟨2752619316159966624130765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3670159088213288832174353 2752619316159966624130765)
        ·
          refine ⟨1032232243559987484049037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2752619316159966624130765 1032232243559987484049037)
          ·
            refine ⟨387087091334995306518389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1032232243559987484049037 387087091334995306518389)
            ·
              refine ⟨36289414812655809986099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 387087091334995306518389 36289414812655809986099)
              ·
                refine ⟨54434122218983714979149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36289414812655809986099 54434122218983714979149)
                ·
                  refine ⟨20412795832118893117181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54434122218983714979149 20412795832118893117181)
                  ·
                    rfl

theorem cell20_44723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 3].length) (baseStart_44723 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44723 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44723 prefixEnd_44723 := by exact prefixLift 44723
  have htrace : WordTrace (prefixWord ++ tailWord_44723) baseStart_44723 baseEnd_44723 := by
    simpa [prefixWord, tailWord_44723, baseEnd_44723] using wordTrace_append hprefix tailTrace_44723
  have hstable : (prefixWord ++ tailWord_44723).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44723).length < 2 ^ (prefixWord ++ tailWord_44723).sum := by decide
  have hdescent : baseEnd_44723 < baseStart_44723 := by decide
  rcases family_descends (prefixWord ++ tailWord_44723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44764 : List Nat := [2, 2, 5, 1, 2, 2, 1, 1, 4]
def baseStart_44764 : Nat := 118140960795 + 44764 * 2 ^ 59
def prefixEnd_44764 : Nat := 4983230072969 + 3 ^ 40 * 44764 * 2
def baseEnd_44764 : Nat := 20431509349304972750347

theorem tailTrace_44764 : CollatzResearch.WordTrace tailWord_44764 prefixEnd_44764 20431509349304972750347 := by
  unfold tailWord_44764
  simp only [CollatzResearch.WordTrace]
  refine ⟨816338604917573963826673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1088451473223431951768897 816338604917573963826673)
  ·
    refine ⟨612253953688180472870005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 816338604917573963826673 612253953688180472870005)
    ·
      refine ⟨57398808158266919331563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 612253953688180472870005 57398808158266919331563)
      ·
        refine ⟨86098212237400378997345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57398808158266919331563 86098212237400378997345)
        ·
          refine ⟨64573659178050284248009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86098212237400378997345 64573659178050284248009)
          ·
            refine ⟨48430244383537713186007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64573659178050284248009 48430244383537713186007)
            ·
              refine ⟨72645366575306569779011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48430244383537713186007 72645366575306569779011)
              ·
                refine ⟨108968049862959854668517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72645366575306569779011 108968049862959854668517)
                ·
                  refine ⟨20431509349304972750347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108968049862959854668517 20431509349304972750347)
                  ·
                    rfl

theorem cell20_44764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 4].length) (baseStart_44764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44764 prefixEnd_44764 := by exact prefixLift 44764
  have htrace : WordTrace (prefixWord ++ tailWord_44764) baseStart_44764 baseEnd_44764 := by
    simpa [prefixWord, tailWord_44764, baseEnd_44764] using wordTrace_append hprefix tailTrace_44764
  have hstable : (prefixWord ++ tailWord_44764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44764).length < 2 ^ (prefixWord ++ tailWord_44764).sum := by decide
  have hdescent : baseEnd_44764 < baseStart_44764 := by decide
  rcases family_descends (prefixWord ++ tailWord_44764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44768 : List Nat := [2, 1, 1, 3, 1, 2, 2, 6, 2]
def baseStart_44768 : Nat := 118140960795 + 44768 * 2 ^ 59
def prefixEnd_44768 : Nat := 4983230072969 + 3 ^ 40 * 44768 * 2
def baseEnd_44768 : Nat := 20433335058298736616997

theorem tailTrace_44768 : CollatzResearch.WordTrace tailWord_44768 prefixEnd_44768 20433335058298736616997 := by
  unfold tailWord_44768
  simp only [CollatzResearch.WordTrace]
  refine ⟨816411550910328305399479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1088548734547104407199305 816411550910328305399479)
  ·
    refine ⟨1224617326365492458099219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 816411550910328305399479 1224617326365492458099219)
    ·
      refine ⟨1836925989548238687148829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1224617326365492458099219 1836925989548238687148829)
      ·
        refine ⟨688847246080589507680811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1836925989548238687148829 688847246080589507680811)
        ·
          refine ⟨1033270869120884261521217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 688847246080589507680811 1033270869120884261521217)
          ·
            refine ⟨774953151840663196140913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1033270869120884261521217 774953151840663196140913)
            ·
              refine ⟨581214863880497397105685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 774953151840663196140913 581214863880497397105685)
              ·
                refine ⟨27244446744398315489329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 581214863880497397105685 27244446744398315489329)
                ·
                  refine ⟨20433335058298736616997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27244446744398315489329 20433335058298736616997)
                  ·
                    rfl

theorem cell20_44768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 6, 2].length) (baseStart_44768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44768 prefixEnd_44768 := by exact prefixLift 44768
  have htrace : WordTrace (prefixWord ++ tailWord_44768) baseStart_44768 baseEnd_44768 := by
    simpa [prefixWord, tailWord_44768, baseEnd_44768] using wordTrace_append hprefix tailTrace_44768
  have hstable : (prefixWord ++ tailWord_44768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44768).length < 2 ^ (prefixWord ++ tailWord_44768).sum := by decide
  have hdescent : baseEnd_44768 < baseStart_44768 := by decide
  rcases family_descends (prefixWord ++ tailWord_44768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44796 : List Nat := [2, 2, 2, 1, 3, 1, 1, 8]
def baseStart_44796 : Nat := 118140960795 + 44796 * 2 ^ 59
def prefixEnd_44796 : Nat := 4983230072969 + 3 ^ 40 * 44796 * 2
def baseEnd_44796 : Nat := 6815371673751694561183

theorem tailTrace_44796 : CollatzResearch.WordTrace tailWord_44796 prefixEnd_44796 6815371673751694561183 := by
  unfold tailWord_44796
  simp only [CollatzResearch.WordTrace]
  refine ⟨816922172859608696409121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1089229563812811595212161 816922172859608696409121)
  ·
    refine ⟨612691629644706522306841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 816922172859608696409121 612691629644706522306841)
    ·
      refine ⟨459518722233529891730131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 612691629644706522306841 459518722233529891730131)
      ·
        refine ⟨689278083350294837595197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459518722233529891730131 689278083350294837595197)
        ·
          refine ⟨258479281256360564098199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 689278083350294837595197 258479281256360564098199)
          ·
            refine ⟨387718921884540846147299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258479281256360564098199 387718921884540846147299)
            ·
              refine ⟨581578382826811269220949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 387718921884540846147299 581578382826811269220949)
              ·
                refine ⟨6815371673751694561183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 581578382826811269220949 6815371673751694561183)
                ·
                  rfl

theorem cell20_44796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 8].length) (baseStart_44796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44796 prefixEnd_44796 := by exact prefixLift 44796
  have htrace : WordTrace (prefixWord ++ tailWord_44796) baseStart_44796 baseEnd_44796 := by
    simpa [prefixWord, tailWord_44796, baseEnd_44796] using wordTrace_append hprefix tailTrace_44796
  have hstable : (prefixWord ++ tailWord_44796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44796).length < 2 ^ (prefixWord ++ tailWord_44796).sum := by decide
  have hdescent : baseEnd_44796 < baseStart_44796 := by decide
  rcases family_descends (prefixWord ++ tailWord_44796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44803 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 7]
def baseStart_44803 : Nat := 118140960795 + 44803 * 2 ^ 59
def prefixEnd_44803 : Nat := 4983230072969 + 3 ^ 40 * 44803 * 2
def baseEnd_44803 : Nat := 20449310011994170450187

theorem tailTrace_44803 : CollatzResearch.WordTrace tailWord_44803 prefixEnd_44803 20449310011994170450187 := by
  unfold tailWord_44803
  simp only [CollatzResearch.WordTrace]
  refine ⟨1634099656693857588323063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1089399771129238392215375 1634099656693857588323063)
  ·
    refine ⟨2451149485040786382484595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1634099656693857588323063 2451149485040786382484595)
    ·
      refine ⟨3676724227561179573726893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2451149485040786382484595 3676724227561179573726893)
      ·
        refine ⟨1378771585335442340147585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3676724227561179573726893 1378771585335442340147585)
        ·
          refine ⟨1034078689001581755110689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1378771585335442340147585 1034078689001581755110689)
          ·
            refine ⟨775559016751186316333017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1034078689001581755110689 775559016751186316333017)
            ·
              refine ⟨581669262563389737249763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 775559016751186316333017 581669262563389737249763)
              ·
                refine ⟨872503893845084605874645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 581669262563389737249763 872503893845084605874645)
                ·
                  refine ⟨20449310011994170450187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 872503893845084605874645 20449310011994170450187)
                  ·
                    rfl

theorem cell20_44803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 7].length) (baseStart_44803 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44803 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44803 prefixEnd_44803 := by exact prefixLift 44803
  have htrace : WordTrace (prefixWord ++ tailWord_44803) baseStart_44803 baseEnd_44803 := by
    simpa [prefixWord, tailWord_44803, baseEnd_44803] using wordTrace_append hprefix tailTrace_44803
  have hstable : (prefixWord ++ tailWord_44803).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44803).length < 2 ^ (prefixWord ++ tailWord_44803).sum := by decide
  have hdescent : baseEnd_44803 < baseStart_44803 := by decide
  rcases family_descends (prefixWord ++ tailWord_44803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44823 : List Nat := [1, 1, 3, 4, 2, 2, 1, 4, 2]
def baseStart_44823 : Nat := 118140960795 + 44823 * 2 ^ 59
def prefixEnd_44823 : Nat := 4983230072969 + 3 ^ 40 * 44823 * 2
def baseEnd_44823 : Nat := 20458438556962989783439

theorem tailTrace_44823 : CollatzResearch.WordTrace tailWord_44823 prefixEnd_44823 20458438556962989783439 := by
  unfold tailWord_44823
  simp only [CollatzResearch.WordTrace]
  refine ⟨1634829116621401004051123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1089886077747600669367415 1634829116621401004051123)
  ·
    refine ⟨2452243674932101506076685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1634829116621401004051123 2452243674932101506076685)
    ·
      refine ⟨919591378099538064778757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2452243674932101506076685 919591378099538064778757)
      ·
        refine ⟨172423383393663387146017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 919591378099538064778757 172423383393663387146017)
        ·
          refine ⟨129317537545247540359513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172423383393663387146017 129317537545247540359513)
          ·
            refine ⟨96988153158935655269635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129317537545247540359513 96988153158935655269635)
            ·
              refine ⟨145482229738403482904453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96988153158935655269635 145482229738403482904453)
              ·
                refine ⟨27277918075950653044585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145482229738403482904453 27277918075950653044585)
                ·
                  refine ⟨20458438556962989783439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27277918075950653044585 20458438556962989783439)
                  ·
                    rfl

theorem cell20_44823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 4, 2].length) (baseStart_44823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44823 prefixEnd_44823 := by exact prefixLift 44823
  have htrace : WordTrace (prefixWord ++ tailWord_44823) baseStart_44823 baseEnd_44823 := by
    simpa [prefixWord, tailWord_44823, baseEnd_44823] using wordTrace_append hprefix tailTrace_44823
  have hstable : (prefixWord ++ tailWord_44823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44823).length < 2 ^ (prefixWord ++ tailWord_44823).sum := by decide
  have hdescent : baseEnd_44823 < baseStart_44823 := by decide
  rcases family_descends (prefixWord ++ tailWord_44823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44861 : List Nat := [1, 4, 1, 4, 1, 1, 1, 5, 2]
def baseStart_44861 : Nat := 118140960795 + 44861 * 2 ^ 59
def prefixEnd_44861 : Nat := 4983230072969 + 3 ^ 40 * 44861 * 2
def baseEnd_44861 : Nat := 20475782792403746516617

theorem tailTrace_44861 : CollatzResearch.WordTrace tailWord_44861 prefixEnd_44861 20475782792403746516617 := by
  unfold tailWord_44861
  simp only [CollatzResearch.WordTrace]
  refine ⟨1636215090483733493934437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1090810060322488995956291 1636215090483733493934437)
  ·
    refine ⟨306790329465700030112707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1636215090483733493934437 306790329465700030112707)
    ·
      refine ⟨460185494198550045169061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306790329465700030112707 460185494198550045169061)
      ·
        refine ⟨86284780162228133469199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 460185494198550045169061 86284780162228133469199)
        ·
          refine ⟨129427170243342200203799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86284780162228133469199 129427170243342200203799)
          ·
            refine ⟨194140755365013300305699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129427170243342200203799 194140755365013300305699)
            ·
              refine ⟨291211133047519950458549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194140755365013300305699 291211133047519950458549)
              ·
                refine ⟨27301043723204995355489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 291211133047519950458549 27301043723204995355489)
                ·
                  refine ⟨20475782792403746516617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27301043723204995355489 20475782792403746516617)
                  ·
                    rfl

theorem cell20_44861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_44861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44861 prefixEnd_44861 := by exact prefixLift 44861
  have htrace : WordTrace (prefixWord ++ tailWord_44861) baseStart_44861 baseEnd_44861 := by
    simpa [prefixWord, tailWord_44861, baseEnd_44861] using wordTrace_append hprefix tailTrace_44861
  have hstable : (prefixWord ++ tailWord_44861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44861).length < 2 ^ (prefixWord ++ tailWord_44861).sum := by decide
  have hdescent : baseEnd_44861 < baseStart_44861 := by decide
  rcases family_descends (prefixWord ++ tailWord_44861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44872 : List Nat := [2, 1, 3, 1, 1, 5, 7]
def baseStart_44872 : Nat := 118140960795 + 44872 * 2 ^ 59
def prefixEnd_44872 : Nat := 4983230072969 + 3 ^ 40 * 44872 * 2
def baseEnd_44872 : Nat := 2275644832459621905545

theorem tailTrace_44872 : CollatzResearch.WordTrace tailWord_44872 prefixEnd_44872 2275644832459621905545 := by
  unfold tailWord_44872
  simp only [CollatzResearch.WordTrace]
  refine ⟨818308146721941186292435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1091077528962588248389913 818308146721941186292435)
  ·
    refine ⟨1227462220082911779438653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 818308146721941186292435 1227462220082911779438653)
    ·
      refine ⟨460298332531091917289495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1227462220082911779438653 460298332531091917289495)
      ·
        refine ⟨690447498796637875934243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 460298332531091917289495 690447498796637875934243)
        ·
          refine ⟨1035671248194956813901365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 690447498796637875934243 1035671248194956813901365)
          ·
            refine ⟨97094179518277201303253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1035671248194956813901365 97094179518277201303253)
            ·
              refine ⟨2275644832459621905545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 97094179518277201303253 2275644832459621905545)
              ·
                rfl

theorem cell20_44872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 7].length) (baseStart_44872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44872 prefixEnd_44872 := by exact prefixLift 44872
  have htrace : WordTrace (prefixWord ++ tailWord_44872) baseStart_44872 baseEnd_44872 := by
    simpa [prefixWord, tailWord_44872, baseEnd_44872] using wordTrace_append hprefix tailTrace_44872
  have hstable : (prefixWord ++ tailWord_44872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44872).length < 2 ^ (prefixWord ++ tailWord_44872).sum := by decide
  have hdescent : baseEnd_44872 < baseStart_44872 := by decide
  rcases family_descends (prefixWord ++ tailWord_44872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44882 : List Nat := [3, 2, 2, 1, 1, 4, 2, 1, 4]
def baseStart_44882 : Nat := 118140960795 + 44882 * 2 ^ 59
def prefixEnd_44882 : Nat := 4983230072969 + 3 ^ 40 * 44882 * 2
def baseEnd_44882 : Nat := 20485367764621006816531

theorem tailTrace_44882 : CollatzResearch.WordTrace tailWord_44882 prefixEnd_44882 20485367764621006816531 := by
  unfold tailWord_44882
  simp only [CollatzResearch.WordTrace]
  refine ⟨409245255851913520112225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1091320682271769386965933 409245255851913520112225)
  ·
    refine ⟨306933941888935140084169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 409245255851913520112225 306933941888935140084169)
    ·
      refine ⟨230200456416701355063127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306933941888935140084169 230200456416701355063127)
      ·
        refine ⟨345300684625052032594691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230200456416701355063127 345300684625052032594691)
        ·
          refine ⟨517951026937578048892037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345300684625052032594691 517951026937578048892037)
          ·
            refine ⟨97115817550795884167257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 517951026937578048892037 97115817550795884167257)
            ·
              refine ⟨72836863163096913125443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97115817550795884167257 72836863163096913125443)
              ·
                refine ⟨109255294744645369688165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72836863163096913125443 109255294744645369688165)
                ·
                  refine ⟨20485367764621006816531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109255294744645369688165 20485367764621006816531)
                  ·
                    rfl

theorem cell20_44882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_44882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44882 prefixEnd_44882 := by exact prefixLift 44882
  have htrace : WordTrace (prefixWord ++ tailWord_44882) baseStart_44882 baseEnd_44882 := by
    simpa [prefixWord, tailWord_44882, baseEnd_44882] using wordTrace_append hprefix tailTrace_44882
  have hstable : (prefixWord ++ tailWord_44882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44882).length < 2 ^ (prefixWord ++ tailWord_44882).sum := by decide
  have hdescent : baseEnd_44882 < baseStart_44882 := by decide
  rcases family_descends (prefixWord ++ tailWord_44882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44903 : List Nat := [1, 1, 5, 1, 2, 1, 1, 4, 4]
def baseStart_44903 : Nat := 118140960795 + 44903 * 2 ^ 59
def prefixEnd_44903 : Nat := 4983230072969 + 3 ^ 40 * 44903 * 2
def baseEnd_44903 : Nat := 20494952736838267116445

theorem tailTrace_44903 : CollatzResearch.WordTrace tailWord_44903 prefixEnd_44903 20494952736838267116445 := by
  unfold tailWord_44903
  simp only [CollatzResearch.WordTrace]
  refine ⟨1637746956331574666963363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1091831304221049777975575 1637746956331574666963363)
  ·
    refine ⟨2456620434497362000445045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1637746956331574666963363 2456620434497362000445045)
    ·
      refine ⟨230308165734127687541723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2456620434497362000445045 230308165734127687541723)
      ·
        refine ⟨345462248601191531312585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230308165734127687541723 345462248601191531312585)
        ·
          refine ⟨259096686450893648484439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 345462248601191531312585 259096686450893648484439)
          ·
            refine ⟨388645029676340472726659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259096686450893648484439 388645029676340472726659)
            ·
              refine ⟨582967544514510709089989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388645029676340472726659 582967544514510709089989)
              ·
                refine ⟨109306414596470757954373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 582967544514510709089989 109306414596470757954373)
                ·
                  refine ⟨20494952736838267116445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109306414596470757954373 20494952736838267116445)
                  ·
                    rfl

theorem cell20_44903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 4].length) (baseStart_44903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44903 prefixEnd_44903 := by exact prefixLift 44903
  have htrace : WordTrace (prefixWord ++ tailWord_44903) baseStart_44903 baseEnd_44903 := by
    simpa [prefixWord, tailWord_44903, baseEnd_44903] using wordTrace_append hprefix tailTrace_44903
  have hstable : (prefixWord ++ tailWord_44903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44903).length < 2 ^ (prefixWord ++ tailWord_44903).sum := by decide
  have hdescent : baseEnd_44903 < baseStart_44903 := by decide
  rcases family_descends (prefixWord ++ tailWord_44903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44906 : List Nat := [3, 1, 3, 4, 1, 1, 1, 6]
def baseStart_44906 : Nat := 118140960795 + 44906 * 2 ^ 59
def prefixEnd_44906 : Nat := 4983230072969 + 3 ^ 40 * 44906 * 2
def baseEnd_44906 : Nat := 6832107339527863338811

theorem tailTrace_44906 : CollatzResearch.WordTrace tailWord_44906 prefixEnd_44906 6832107339527863338811 := by
  unfold tailWord_44906
  simp only [CollatzResearch.WordTrace]
  refine ⟨409464093830176544830643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1091904250213804119548381 409464093830176544830643)
  ·
    refine ⟨614196140745264817245965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 409464093830176544830643 614196140745264817245965)
    ·
      refine ⟨230323552779474306467237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 614196140745264817245965 230323552779474306467237)
      ·
        refine ⟨43185666146151432462607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 230323552779474306467237 43185666146151432462607)
        ·
          refine ⟨64778499219227148693911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43185666146151432462607 64778499219227148693911)
          ·
            refine ⟨97167748828840723040867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64778499219227148693911 97167748828840723040867)
            ·
              refine ⟨145751623243261084561301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97167748828840723040867 145751623243261084561301)
              ·
                refine ⟨6832107339527863338811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 145751623243261084561301 6832107339527863338811)
                ·
                  rfl

theorem cell20_44906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_44906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44906 prefixEnd_44906 := by exact prefixLift 44906
  have htrace : WordTrace (prefixWord ++ tailWord_44906) baseStart_44906 baseEnd_44906 := by
    simpa [prefixWord, tailWord_44906, baseEnd_44906] using wordTrace_append hprefix tailTrace_44906
  have hstable : (prefixWord ++ tailWord_44906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44906).length < 2 ^ (prefixWord ++ tailWord_44906).sum := by decide
  have hdescent : baseEnd_44906 < baseStart_44906 := by decide
  rcases family_descends (prefixWord ++ tailWord_44906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44937 : List Nat := [1, 2, 1, 1, 5, 1, 5, 2, 2]
def baseStart_44937 : Nat := 118140960795 + 44937 * 2 ^ 59
def prefixEnd_44937 : Nat := 4983230072969 + 3 ^ 40 * 44937 * 2
def baseEnd_44937 : Nat := 20510471263285259982973

theorem tailTrace_44937 : CollatzResearch.WordTrace tailWord_44937 prefixEnd_44937 20510471263285259982973 := by
  unfold tailWord_44937
  simp only [CollatzResearch.WordTrace]
  refine ⟨1638987038208398473701065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1092658025472265649134043 1638987038208398473701065)
  ·
    refine ⟨1229240278656298855275799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1638987038208398473701065 1229240278656298855275799)
    ·
      refine ⟨1843860417984448282913699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1229240278656298855275799 1843860417984448282913699)
      ·
        refine ⟨2765790626976672424370549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1843860417984448282913699 2765790626976672424370549)
        ·
          refine ⟨259292871279063039784739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2765790626976672424370549 259292871279063039784739)
          ·
            refine ⟨388939306918594559677109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259292871279063039784739 388939306918594559677109)
            ·
              refine ⟨36463060023618239969729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 388939306918594559677109 36463060023618239969729)
              ·
                refine ⟨27347295017713679977297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36463060023618239969729 27347295017713679977297)
                ·
                  refine ⟨20510471263285259982973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27347295017713679977297 20510471263285259982973)
                  ·
                    rfl

theorem cell20_44937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 2, 2].length) (baseStart_44937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44937 prefixEnd_44937 := by exact prefixLift 44937
  have htrace : WordTrace (prefixWord ++ tailWord_44937) baseStart_44937 baseEnd_44937 := by
    simpa [prefixWord, tailWord_44937, baseEnd_44937] using wordTrace_append hprefix tailTrace_44937
  have hstable : (prefixWord ++ tailWord_44937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44937).length < 2 ^ (prefixWord ++ tailWord_44937).sum := by decide
  have hdescent : baseEnd_44937 < baseStart_44937 := by decide
  rcases family_descends (prefixWord ++ tailWord_44937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44951 : List Nat := [1, 1, 3, 3, 1, 3, 4, 1, 3]
def baseStart_44951 : Nat := 118140960795 + 44951 * 2 ^ 59
def prefixEnd_44951 : Nat := 4983230072969 + 3 ^ 40 * 44951 * 2
def baseEnd_44951 : Nat := 20516861244763433516249

theorem tailTrace_44951 : CollatzResearch.WordTrace tailWord_44951 prefixEnd_44951 20516861244763433516249 := by
  unfold tailWord_44951
  simp only [CollatzResearch.WordTrace]
  refine ⟨1639497660157678864710707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1092998440105119243140471 1639497660157678864710707)
  ·
    refine ⟨2459246490236518297066061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1639497660157678864710707 2459246490236518297066061)
    ·
      refine ⟨922217433838694361399773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2459246490236518297066061 922217433838694361399773)
      ·
        refine ⟨345831537689510385524915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 922217433838694361399773 345831537689510385524915)
        ·
          refine ⟨518747306534265578287373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345831537689510385524915 518747306534265578287373)
          ·
            refine ⟨194530239950349591857765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 518747306534265578287373 194530239950349591857765)
            ·
              refine ⟨36474419990690548473331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 194530239950349591857765 36474419990690548473331)
              ·
                refine ⟨54711629986035822709997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36474419990690548473331 54711629986035822709997)
                ·
                  refine ⟨20516861244763433516249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54711629986035822709997 20516861244763433516249)
                  ·
                    rfl

theorem cell20_44951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 3].length) (baseStart_44951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44951 prefixEnd_44951 := by exact prefixLift 44951
  have htrace : WordTrace (prefixWord ++ tailWord_44951) baseStart_44951 baseEnd_44951 := by
    simpa [prefixWord, tailWord_44951, baseEnd_44951] using wordTrace_append hprefix tailTrace_44951
  have hstable : (prefixWord ++ tailWord_44951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44951).length < 2 ^ (prefixWord ++ tailWord_44951).sum := by decide
  have hdescent : baseEnd_44951 < baseStart_44951 := by decide
  rcases family_descends (prefixWord ++ tailWord_44951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44988 : List Nat := [2, 2, 2, 5, 2, 1, 2, 2, 2]
def baseStart_44988 : Nat := 118140960795 + 44988 * 2 ^ 59
def prefixEnd_44988 : Nat := 4983230072969 + 3 ^ 40 * 44988 * 2
def baseEnd_44988 : Nat := 20533749052955749282765

theorem tailTrace_44988 : CollatzResearch.WordTrace tailWord_44988 prefixEnd_44988 20533749052955749282765 := by
  unfold tailWord_44988
  simp only [CollatzResearch.WordTrace]
  refine ⟨820423580511817091903809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1093898107349089455871745 820423580511817091903809)
  ·
    refine ⟨615317685383862818927857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 820423580511817091903809 615317685383862818927857)
    ·
      refine ⟨461488264037897114195893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 615317685383862818927857 461488264037897114195893)
      ·
        refine ⟨43264524753552854455865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 461488264037897114195893 43264524753552854455865)
        ·
          refine ⟨32448393565164640841899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43264524753552854455865 32448393565164640841899)
          ·
            refine ⟨48672590347746961262849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32448393565164640841899 48672590347746961262849)
            ·
              refine ⟨36504442760810220947137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48672590347746961262849 36504442760810220947137)
              ·
                refine ⟨27378332070607665710353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36504442760810220947137 27378332070607665710353)
                ·
                  refine ⟨20533749052955749282765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27378332070607665710353 20533749052955749282765)
                  ·
                    rfl

theorem cell20_44988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 2, 2].length) (baseStart_44988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44988 prefixEnd_44988 := by exact prefixLift 44988
  have htrace : WordTrace (prefixWord ++ tailWord_44988) baseStart_44988 baseEnd_44988 := by
    simpa [prefixWord, tailWord_44988, baseEnd_44988] using wordTrace_append hprefix tailTrace_44988
  have hstable : (prefixWord ++ tailWord_44988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44988).length < 2 ^ (prefixWord ++ tailWord_44988).sum := by decide
  have hdescent : baseEnd_44988 < baseStart_44988 := by decide
  rcases family_descends (prefixWord ++ tailWord_44988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_44989 : List Nat := [1, 4, 1, 2, 3, 2, 2, 2, 3]
def baseStart_44989 : Nat := 118140960795 + 44989 * 2 ^ 59
def prefixEnd_44989 : Nat := 4983230072969 + 3 ^ 40 * 44989 * 2
def baseEnd_44989 : Nat := 20534205480204190249427

theorem tailTrace_44989 : CollatzResearch.WordTrace tailWord_44989 prefixEnd_44989 20534205480204190249427 := by
  unfold tailWord_44989
  simp only [CollatzResearch.WordTrace]
  refine ⟨1640883634020011354594021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1093922422680007569729347 1640883634020011354594021)
  ·
    refine ⟨307665681378752128986379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1640883634020011354594021 307665681378752128986379)
    ·
      refine ⟨461498522068128193479569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307665681378752128986379 461498522068128193479569)
      ·
        refine ⟨346123891551096145109677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 461498522068128193479569 346123891551096145109677)
        ·
          refine ⟨129796459331661054416129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 346123891551096145109677 129796459331661054416129)
          ·
            refine ⟨97347344498745790812097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129796459331661054416129 97347344498745790812097)
            ·
              refine ⟨73010508374059343109073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97347344498745790812097 73010508374059343109073)
              ·
                refine ⟨54757881280544507331805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73010508374059343109073 54757881280544507331805)
                ·
                  refine ⟨20534205480204190249427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54757881280544507331805 20534205480204190249427)
                  ·
                    rfl

theorem cell20_44989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_44989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_44989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_44989 prefixEnd_44989 := by exact prefixLift 44989
  have htrace : WordTrace (prefixWord ++ tailWord_44989) baseStart_44989 baseEnd_44989 := by
    simpa [prefixWord, tailWord_44989, baseEnd_44989] using wordTrace_append hprefix tailTrace_44989
  have hstable : (prefixWord ++ tailWord_44989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_44989).length < 2 ^ (prefixWord ++ tailWord_44989).sum := by decide
  have hdescent : baseEnd_44989 < baseStart_44989 := by decide
  rcases family_descends (prefixWord ++ tailWord_44989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45048 : List Nat := [2, 1, 2, 1, 1, 3, 5, 2, 3]
def baseStart_45048 : Nat := 118140960795 + 45048 * 2 ^ 59
def prefixEnd_45048 : Nat := 4983230072969 + 3 ^ 40 * 45048 * 2
def baseEnd_45048 : Nat := 20561134687862207282519

theorem tailTrace_45048 : CollatzResearch.WordTrace tailWord_45048 prefixEnd_45048 20561134687862207282519 := by
  unfold tailWord_45048
  simp only [CollatzResearch.WordTrace]
  refine ⟨821517770403132215495899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1095357027204176287327865 821517770403132215495899)
  ·
    refine ⟨1232276655604698323243849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 821517770403132215495899 1232276655604698323243849)
    ·
      refine ⟨924207491703523742432887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1232276655604698323243849 924207491703523742432887)
      ·
        refine ⟨1386311237555285613649331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 924207491703523742432887 1386311237555285613649331)
        ·
          refine ⟨2079466856332928420473997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1386311237555285613649331 2079466856332928420473997)
          ·
            refine ⟨779800071124848157677749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2079466856332928420473997 779800071124848157677749)
            ·
              refine ⟨73106256667954514782289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 779800071124848157677749 73106256667954514782289)
              ·
                refine ⟨54829692500965886086717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73106256667954514782289 54829692500965886086717)
                ·
                  refine ⟨20561134687862207282519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54829692500965886086717 20561134687862207282519)
                  ·
                    rfl

theorem cell20_45048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 3].length) (baseStart_45048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_45048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_45048 prefixEnd_45048 := by exact prefixLift 45048
  have htrace : WordTrace (prefixWord ++ tailWord_45048) baseStart_45048 baseEnd_45048 := by
    simpa [prefixWord, tailWord_45048, baseEnd_45048] using wordTrace_append hprefix tailTrace_45048
  have hstable : (prefixWord ++ tailWord_45048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45048).length < 2 ^ (prefixWord ++ tailWord_45048).sum := by decide
  have hdescent : baseEnd_45048 < baseStart_45048 := by decide
  rcases family_descends (prefixWord ++ tailWord_45048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45079 : List Nat := [1, 1, 3, 5, 2, 1, 1, 6]
def baseStart_45079 : Nat := 118140960795 + 45079 * 2 ^ 59
def prefixEnd_45079 : Nat := 4983230072969 + 3 ^ 40 * 45079 * 2
def baseEnd_45079 : Nat := 6858427977521292416353

theorem tailTrace_45079 : CollatzResearch.WordTrace tailWord_45079 prefixEnd_45079 6858427977521292416353 := by
  unfold tailWord_45079
  simp only [CollatzResearch.WordTrace]
  refine ⟨1644166203693956725370291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1096110802462637816913527 1644166203693956725370291)
  ·
    refine ⟨2466249305540935088055437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1644166203693956725370291 2466249305540935088055437)
    ·
      refine ⟨924843489577850658020789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2466249305540935088055437 924843489577850658020789)
      ·
        refine ⟨86704077147923499189449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 924843489577850658020789 86704077147923499189449)
        ·
          refine ⟨65028057860942624392087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86704077147923499189449 65028057860942624392087)
          ·
            refine ⟨97542086791413936588131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65028057860942624392087 97542086791413936588131)
            ·
              refine ⟨146313130187120904882197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97542086791413936588131 146313130187120904882197)
              ·
                refine ⟨6858427977521292416353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 146313130187120904882197 6858427977521292416353)
                ·
                  rfl

theorem cell20_45079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 6].length) (baseStart_45079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_45079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_45079 prefixEnd_45079 := by exact prefixLift 45079
  have htrace : WordTrace (prefixWord ++ tailWord_45079) baseStart_45079 baseEnd_45079 := by
    simpa [prefixWord, tailWord_45079, baseEnd_45079] using wordTrace_append hprefix tailTrace_45079
  have hstable : (prefixWord ++ tailWord_45079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45079).length < 2 ^ (prefixWord ++ tailWord_45079).sum := by decide
  have hdescent : baseEnd_45079 < baseStart_45079 := by decide
  rcases family_descends (prefixWord ++ tailWord_45079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45096 : List Nat := [2, 1, 5, 3, 1, 2, 6]
def baseStart_45096 : Nat := 118140960795 + 45096 * 2 ^ 59
def prefixEnd_45096 : Nat := 4983230072969 + 3 ^ 40 * 45096 * 2
def baseEnd_45096 : Nat := 2287004799531930409147

theorem tailTrace_45096 : CollatzResearch.WordTrace tailWord_45096 prefixEnd_45096 2287004799531930409147 := by
  unfold tailWord_45096
  simp only [CollatzResearch.WordTrace]
  refine ⟨822393122316184314369571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1096524163088245752492761 822393122316184314369571)
  ·
    refine ⟨1233589683474276471554357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 822393122316184314369571 1233589683474276471554357)
    ·
      refine ⟨115649032825713419208221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1233589683474276471554357 115649032825713419208221)
      ·
        refine ⟨43368387309642532203083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115649032825713419208221 43368387309642532203083)
        ·
          refine ⟨65052580964463798304625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43368387309642532203083 65052580964463798304625)
          ·
            refine ⟨48789435723347848728469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65052580964463798304625 48789435723347848728469)
            ·
              refine ⟨2287004799531930409147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48789435723347848728469 2287004799531930409147)
              ·
                rfl

theorem cell20_45096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 6].length) (baseStart_45096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_45096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_45096 prefixEnd_45096 := by exact prefixLift 45096
  have htrace : WordTrace (prefixWord ++ tailWord_45096) baseStart_45096 baseEnd_45096 := by
    simpa [prefixWord, tailWord_45096, baseEnd_45096] using wordTrace_append hprefix tailTrace_45096
  have hstable : (prefixWord ++ tailWord_45096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45096).length < 2 ^ (prefixWord ++ tailWord_45096).sum := by decide
  have hdescent : baseEnd_45096 < baseStart_45096 := by decide
  rcases family_descends (prefixWord ++ tailWord_45096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45107 : List Nat := [1, 1, 1, 2, 4, 1, 4, 1, 5]
def baseStart_45107 : Nat := 118140960795 + 45107 * 2 ^ 59
def prefixEnd_45107 : Nat := 4983230072969 + 3 ^ 40 * 45107 * 2
def baseEnd_45107 : Nat := 20588063895520224315611

theorem tailTrace_45107 : CollatzResearch.WordTrace tailWord_45107 prefixEnd_45107 20588063895520224315611 := by
  unfold tailWord_45107
  simp only [CollatzResearch.WordTrace]
  refine ⟨1645187447592517507389575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1096791631728345004926383 1645187447592517507389575)
  ·
    refine ⟨2467781171388776261084363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1645187447592517507389575 2467781171388776261084363)
    ·
      refine ⟨3701671757083164391626545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2467781171388776261084363 3701671757083164391626545)
      ·
        refine ⟨2776253817812373293719909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3701671757083164391626545 2776253817812373293719909)
        ·
          refine ⟨520547590839819992572483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2776253817812373293719909 520547590839819992572483)
          ·
            refine ⟨780821386259729988858725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520547590839819992572483 780821386259729988858725)
            ·
              refine ⟨146404009923699372911011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 780821386259729988858725 146404009923699372911011)
              ·
                refine ⟨219606014885549059366517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146404009923699372911011 219606014885549059366517)
                ·
                  refine ⟨20588063895520224315611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 219606014885549059366517 20588063895520224315611)
                  ·
                    rfl

theorem cell20_45107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 5].length) (baseStart_45107 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_45107 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_45107 prefixEnd_45107 := by exact prefixLift 45107
  have htrace : WordTrace (prefixWord ++ tailWord_45107) baseStart_45107 baseEnd_45107 := by
    simpa [prefixWord, tailWord_45107, baseEnd_45107] using wordTrace_append hprefix tailTrace_45107
  have hstable : (prefixWord ++ tailWord_45107).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45107).length < 2 ^ (prefixWord ++ tailWord_45107).sum := by decide
  have hdescent : baseEnd_45107 < baseStart_45107 := by decide
  rcases family_descends (prefixWord ++ tailWord_45107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45206 : List Nat := [5, 3, 2, 1, 1, 1, 7]
def baseStart_45206 : Nat := 118140960795 + 45206 * 2 ^ 59
def prefixEnd_45206 : Nat := 4983230072969 + 3 ^ 40 * 45206 * 2
def baseEnd_45206 : Nat := 2292583354790653335023

theorem tailTrace_45206 : CollatzResearch.WordTrace tailWord_45206 prefixEnd_45206 2292583354790653335023 := by
  unfold tailWord_45206
  simp only [CollatzResearch.WordTrace]
  refine ⟨103049892139616088452717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1099198849489238276828981 103049892139616088452717)
  ·
    refine ⟨38643709552356033169769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103049892139616088452717 38643709552356033169769)
    ·
      refine ⟨28982782164267024877327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38643709552356033169769 28982782164267024877327)
      ·
        refine ⟨43474173246400537315991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28982782164267024877327 43474173246400537315991)
        ·
          refine ⟨65211259869600805973987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43474173246400537315991 65211259869600805973987)
          ·
            refine ⟨97816889804401208960981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65211259869600805973987 97816889804401208960981)
            ·
              refine ⟨2292583354790653335023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 97816889804401208960981 2292583354790653335023)
              ·
                rfl

theorem cell20_45206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 7].length) (baseStart_45206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_45206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_45206 prefixEnd_45206 := by exact prefixLift 45206
  have htrace : WordTrace (prefixWord ++ tailWord_45206) baseStart_45206 baseEnd_45206 := by
    simpa [prefixWord, tailWord_45206, baseEnd_45206] using wordTrace_append hprefix tailTrace_45206
  have hstable : (prefixWord ++ tailWord_45206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45206).length < 2 ^ (prefixWord ++ tailWord_45206).sum := by decide
  have hdescent : baseEnd_45206 < baseStart_45206 := by decide
  rcases family_descends (prefixWord ++ tailWord_45206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45217 : List Nat := [1, 2, 3, 3, 1, 4, 1, 2, 3]
def baseStart_45217 : Nat := 118140960795 + 45217 * 2 ^ 59
def prefixEnd_45217 : Nat := 4983230072969 + 3 ^ 40 * 45217 * 2
def baseEnd_45217 : Nat := 20638270892848730648495

theorem tailTrace_45217 : CollatzResearch.WordTrace tailWord_45217 prefixEnd_45217 20638270892848730648495 := by
  unfold tailWord_45217
  simp only [CollatzResearch.WordTrace]
  refine ⟨1649199477194006293893905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1099466318129337529262603 1649199477194006293893905)
  ·
    refine ⟨1236899607895504720420429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1649199477194006293893905 1236899607895504720420429)
    ·
      refine ⟨463837352960814270157661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1236899607895504720420429 463837352960814270157661)
      ·
        refine ⟨173939007360305351309123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 463837352960814270157661 173939007360305351309123)
        ·
          refine ⟨260908511040458026963685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173939007360305351309123 260908511040458026963685)
          ·
            refine ⟨48920345820085880055691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 260908511040458026963685 48920345820085880055691)
            ·
              refine ⟨73380518730128820083537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48920345820085880055691 73380518730128820083537)
              ·
                refine ⟨55035389047596615062653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73380518730128820083537 55035389047596615062653)
                ·
                  refine ⟨20638270892848730648495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55035389047596615062653 20638270892848730648495)
                  ·
                    rfl

theorem cell20_45217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 3].length) (baseStart_45217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_45217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_45217 prefixEnd_45217 := by exact prefixLift 45217
  have htrace : WordTrace (prefixWord ++ tailWord_45217) baseStart_45217 baseEnd_45217 := by
    simpa [prefixWord, tailWord_45217, baseEnd_45217] using wordTrace_append hprefix tailTrace_45217
  have hstable : (prefixWord ++ tailWord_45217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45217).length < 2 ^ (prefixWord ++ tailWord_45217).sum := by decide
  have hdescent : baseEnd_45217 < baseStart_45217 := by decide
  rcases family_descends (prefixWord ++ tailWord_45217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45221 : List Nat := [1, 3, 1, 2, 1, 3, 3, 1, 5]
def baseStart_45221 : Nat := 118140960795 + 45221 * 2 ^ 59
def prefixEnd_45221 : Nat := 4983230072969 + 3 ^ 40 * 45221 * 2
def baseEnd_45221 : Nat := 20640096601842494515145

theorem tailTrace_45221 : CollatzResearch.WordTrace tailWord_45221 prefixEnd_45221 20640096601842494515145 := by
  unfold tailWord_45221
  simp only [CollatzResearch.WordTrace]
  refine ⟨1649345369179514977039517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1099563579453009984693011 1649345369179514977039517)
  ·
    refine ⟨618504513442318116389819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1649345369179514977039517 618504513442318116389819)
    ·
      refine ⟨927756770163477174584729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 618504513442318116389819 927756770163477174584729)
      ·
        refine ⟨695817577622607880938547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 927756770163477174584729 695817577622607880938547)
        ·
          refine ⟨1043726366433911821407821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695817577622607880938547 1043726366433911821407821)
          ·
            refine ⟨391397387412716933027933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1043726366433911821407821 391397387412716933027933)
            ·
              refine ⟨146774020279768849885475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 391397387412716933027933 146774020279768849885475)
              ·
                refine ⟨220161030419653274828213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146774020279768849885475 220161030419653274828213)
                ·
                  refine ⟨20640096601842494515145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 220161030419653274828213 20640096601842494515145)
                  ·
                    rfl

theorem cell20_45221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_45221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_45221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_45221 prefixEnd_45221 := by exact prefixLift 45221
  have htrace : WordTrace (prefixWord ++ tailWord_45221) baseStart_45221 baseEnd_45221 := by
    simpa [prefixWord, tailWord_45221, baseEnd_45221] using wordTrace_append hprefix tailTrace_45221
  have hstable : (prefixWord ++ tailWord_45221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45221).length < 2 ^ (prefixWord ++ tailWord_45221).sum := by decide
  have hdescent : baseEnd_45221 < baseStart_45221 := by decide
  rcases family_descends (prefixWord ++ tailWord_45221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45235 : List Nat := [1, 1, 1, 2, 3, 2, 1, 9]
def baseStart_45235 : Nat := 118140960795 + 45235 * 2 ^ 59
def prefixEnd_45235 : Nat := 4983230072969 + 3 ^ 40 * 45235 * 2
def baseEnd_45235 : Nat := 6882162194440222682807

theorem tailTrace_45235 : CollatzResearch.WordTrace tailWord_45235 prefixEnd_45235 6882162194440222682807 := by
  unfold tailWord_45235
  simp only [CollatzResearch.WordTrace]
  refine ⟨1649855991128795368049159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1099903994085863578699439 1649855991128795368049159)
  ·
    refine ⟨2474783986693193052073739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1649855991128795368049159 2474783986693193052073739)
    ·
      refine ⟨3712175980039789578110609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2474783986693193052073739 3712175980039789578110609)
      ·
        refine ⟨2784131985029842183582957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3712175980039789578110609 2784131985029842183582957)
        ·
          refine ⟨1044049494386190818843609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2784131985029842183582957 1044049494386190818843609)
          ·
            refine ⟨783037120789643114132707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1044049494386190818843609 783037120789643114132707)
            ·
              refine ⟨1174555681184464671199061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 783037120789643114132707 1174555681184464671199061)
              ·
                refine ⟨6882162194440222682807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1174555681184464671199061 6882162194440222682807)
                ·
                  rfl

theorem cell20_45235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 9].length) (baseStart_45235 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_45235 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_45235 prefixEnd_45235 := by exact prefixLift 45235
  have htrace : WordTrace (prefixWord ++ tailWord_45235) baseStart_45235 baseEnd_45235 := by
    simpa [prefixWord, tailWord_45235, baseEnd_45235] using wordTrace_append hprefix tailTrace_45235
  have hstable : (prefixWord ++ tailWord_45235).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45235).length < 2 ^ (prefixWord ++ tailWord_45235).sum := by decide
  have hdescent : baseEnd_45235 < baseStart_45235 := by decide
  rcases family_descends (prefixWord ++ tailWord_45235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45269 : List Nat := [1, 3, 2, 4, 2, 2, 6]
def baseStart_45269 : Nat := 118140960795 + 45269 * 2 ^ 59
def prefixEnd_45269 : Nat := 4983230072969 + 3 ^ 40 * 45269 * 2
def baseEnd_45269 : Nat := 2295778345529740101661

theorem tailTrace_45269 : CollatzResearch.WordTrace tailWord_45269 prefixEnd_45269 2295778345529740101661 := by
  unfold tailWord_45269
  simp only [CollatzResearch.WordTrace]
  refine ⟨1651096073005619174786861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1100730715337079449857907 1651096073005619174786861)
  ·
    refine ⟨619161027377107190545073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1651096073005619174786861 619161027377107190545073)
    ·
      refine ⟨464370770532830392908805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 619161027377107190545073 464370770532830392908805)
      ·
        refine ⟨87069519474905698670401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 464370770532830392908805 87069519474905698670401)
        ·
          refine ⟨65302139606179274002801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87069519474905698670401 65302139606179274002801)
          ·
            refine ⟨48976604704634455502101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65302139606179274002801 48976604704634455502101)
            ·
              refine ⟨2295778345529740101661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48976604704634455502101 2295778345529740101661)
              ·
                rfl

theorem cell20_45269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 6].length) (baseStart_45269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_45269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_45269 prefixEnd_45269 := by exact prefixLift 45269
  have htrace : WordTrace (prefixWord ++ tailWord_45269) baseStart_45269 baseEnd_45269 := by
    simpa [prefixWord, tailWord_45269, baseEnd_45269] using wordTrace_append hprefix tailTrace_45269
  have hstable : (prefixWord ++ tailWord_45269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45269).length < 2 ^ (prefixWord ++ tailWord_45269).sum := by decide
  have hdescent : baseEnd_45269 < baseStart_45269 := by decide
  rcases family_descends (prefixWord ++ tailWord_45269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45273 : List Nat := [1, 2, 1, 2, 3, 1, 10]
def baseStart_45273 : Nat := 118140960795 + 45273 * 2 ^ 59
def prefixEnd_45273 : Nat := 4983230072969 + 3 ^ 40 * 45273 * 2
def baseEnd_45273 : Nat := 2295981202084602753511

theorem tailTrace_45273 : CollatzResearch.WordTrace tailWord_45273 prefixEnd_45273 2295981202084602753511 := by
  unfold tailWord_45273
  simp only [CollatzResearch.WordTrace]
  refine ⟨1651241964991127857932473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1100827976660751905288315 1651241964991127857932473)
  ·
    refine ⟨1238431473743345893449355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1651241964991127857932473 1238431473743345893449355)
    ·
      refine ⟨1857647210615018840174033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1238431473743345893449355 1857647210615018840174033)
      ·
        refine ⟨1393235407961264130130525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1857647210615018840174033 1393235407961264130130525)
        ·
          refine ⟨522463277985474048798947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1393235407961264130130525 522463277985474048798947)
          ·
            refine ⟨783694916978211073198421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522463277985474048798947 783694916978211073198421)
            ·
              refine ⟨2295981202084602753511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 783694916978211073198421 2295981202084602753511)
              ·
                rfl

theorem cell20_45273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 10].length) (baseStart_45273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_45273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_45273 prefixEnd_45273 := by exact prefixLift 45273
  have htrace : WordTrace (prefixWord ++ tailWord_45273) baseStart_45273 baseEnd_45273 := by
    simpa [prefixWord, tailWord_45273, baseEnd_45273] using wordTrace_append hprefix tailTrace_45273
  have hstable : (prefixWord ++ tailWord_45273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45273).length < 2 ^ (prefixWord ++ tailWord_45273).sum := by decide
  have hdescent : baseEnd_45273 < baseStart_45273 := by decide
  rcases family_descends (prefixWord ++ tailWord_45273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45290 : List Nat := [3, 1, 3, 1, 1, 2, 4, 5]
def baseStart_45290 : Nat := 118140960795 + 45290 * 2 ^ 59
def prefixEnd_45290 : Nat := 4983230072969 + 3 ^ 40 * 45290 * 2
def baseEnd_45290 : Nat := 6890530027328307071621

theorem tailTrace_45290 : CollatzResearch.WordTrace tailWord_45290 prefixEnd_45290 6890530027328307071621 := by
  unfold tailWord_45290
  simp only [CollatzResearch.WordTrace]
  refine ⟨412965501482384940325331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1101241337286359840867549 412965501482384940325331)
  ·
    refine ⟨619448252223577410487997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 412965501482384940325331 619448252223577410487997)
    ·
      refine ⟨232293094583841528932999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 619448252223577410487997 232293094583841528932999)
      ·
        refine ⟨348439641875762293399499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232293094583841528932999 348439641875762293399499)
        ·
          refine ⟨522659462813643440099249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348439641875762293399499 522659462813643440099249)
          ·
            refine ⟨391994597110232580074437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 522659462813643440099249 391994597110232580074437)
            ·
              refine ⟨73498986958168608763957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 391994597110232580074437 73498986958168608763957)
              ·
                refine ⟨6890530027328307071621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73498986958168608763957 6890530027328307071621)
                ·
                  rfl

theorem cell20_45290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_45290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_45290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_45290 prefixEnd_45290 := by exact prefixLift 45290
  have htrace : WordTrace (prefixWord ++ tailWord_45290) baseStart_45290 baseEnd_45290 := by
    simpa [prefixWord, tailWord_45290, baseEnd_45290] using wordTrace_append hprefix tailTrace_45290
  have hstable : (prefixWord ++ tailWord_45290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45290).length < 2 ^ (prefixWord ++ tailWord_45290).sum := by decide
  have hdescent : baseEnd_45290 < baseStart_45290 := by decide
  rcases family_descends (prefixWord ++ tailWord_45290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45293 : List Nat := [1, 5, 1, 2, 3, 1, 1, 3, 3]
def baseStart_45293 : Nat := 118140960795 + 45293 * 2 ^ 59
def prefixEnd_45293 : Nat := 4983230072969 + 3 ^ 40 * 45293 * 2
def baseEnd_45293 : Nat := 20672959363730244114851

theorem tailTrace_45293 : CollatzResearch.WordTrace tailWord_45293 prefixEnd_45293 20672959363730244114851 := by
  unfold tailWord_45293
  simp only [CollatzResearch.WordTrace]
  refine ⟨1651971424918671273660533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1101314283279114182440355 1651971424918671273660533)
  ·
    refine ⟨154872321086125431905675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1651971424918671273660533 154872321086125431905675)
    ·
      refine ⟨232308481629188147858513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154872321086125431905675 232308481629188147858513)
      ·
        refine ⟨174231361221891110893885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232308481629188147858513 174231361221891110893885)
        ·
          refine ⟨65336760458209166585207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174231361221891110893885 65336760458209166585207)
          ·
            refine ⟨98005140687313749877811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65336760458209166585207 98005140687313749877811)
            ·
              refine ⟨147007711030970624816717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98005140687313749877811 147007711030970624816717)
              ·
                refine ⟨55127891636613984306269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147007711030970624816717 55127891636613984306269)
                ·
                  refine ⟨20672959363730244114851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55127891636613984306269 20672959363730244114851)
                  ·
                    rfl

theorem cell20_45293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_45293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_45293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_45293 prefixEnd_45293 := by exact prefixLift 45293
  have htrace : WordTrace (prefixWord ++ tailWord_45293) baseStart_45293 baseEnd_45293 := by
    simpa [prefixWord, tailWord_45293, baseEnd_45293] using wordTrace_append hprefix tailTrace_45293
  have hstable : (prefixWord ++ tailWord_45293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45293).length < 2 ^ (prefixWord ++ tailWord_45293).sum := by decide
  have hdescent : baseEnd_45293 < baseStart_45293 := by decide
  rcases family_descends (prefixWord ++ tailWord_45293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45304 : List Nat := [2, 1, 2, 1, 1, 2, 1, 6, 4]
def baseStart_45304 : Nat := 118140960795 + 45304 * 2 ^ 59
def prefixEnd_45304 : Nat := 4983230072969 + 3 ^ 40 * 45304 * 2
def baseEnd_45304 : Nat := 20677980063463094748139

theorem tailTrace_45304 : CollatzResearch.WordTrace tailWord_45304 prefixEnd_45304 20677980063463094748139 := by
  unfold tailWord_45304
  simp only [CollatzResearch.WordTrace]
  refine ⟨826186313939410076155483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1101581751919213434873977 826186313939410076155483)
  ·
    refine ⟨1239279470909115114233225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 826186313939410076155483 1239279470909115114233225)
    ·
      refine ⟨929459603181836335674919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1239279470909115114233225 929459603181836335674919)
      ·
        refine ⟨1394189404772754503512379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 929459603181836335674919 1394189404772754503512379)
        ·
          refine ⟨2091284107159131755268569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1394189404772754503512379 2091284107159131755268569)
          ·
            refine ⟨1568463080369348816451427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2091284107159131755268569 1568463080369348816451427)
            ·
              refine ⟨2352694620554023224677141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1568463080369348816451427 2352694620554023224677141)
              ·
                refine ⟨110282560338469838656741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2352694620554023224677141 110282560338469838656741)
                ·
                  refine ⟨20677980063463094748139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110282560338469838656741 20677980063463094748139)
                  ·
                    rfl

theorem cell20_45304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_45304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_45304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_45304 prefixEnd_45304 := by exact prefixLift 45304
  have htrace : WordTrace (prefixWord ++ tailWord_45304) baseStart_45304 baseEnd_45304 := by
    simpa [prefixWord, tailWord_45304, baseEnd_45304] using wordTrace_append hprefix tailTrace_45304
  have hstable : (prefixWord ++ tailWord_45304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45304).length < 2 ^ (prefixWord ++ tailWord_45304).sum := by decide
  have hdescent : baseEnd_45304 < baseStart_45304 := by decide
  rcases family_descends (prefixWord ++ tailWord_45304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45311 : List Nat := [1, 1, 2, 2, 1, 4, 1, 8]
def baseStart_45311 : Nat := 118140960795 + 45311 * 2 ^ 59
def prefixEnd_45311 : Nat := 4983230072969 + 3 ^ 40 * 45311 * 2
def baseEnd_45311 : Nat := 6893725018067393838259

theorem tailTrace_45311 : CollatzResearch.WordTrace tailWord_45311 prefixEnd_45311 6893725018067393838259 := by
  unfold tailWord_45311
  simp only [CollatzResearch.WordTrace]
  refine ⟨1652627938853460347815787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1101751959235640231877191 1652627938853460347815787)
  ·
    refine ⟨2478941908280190521723681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1652627938853460347815787 2478941908280190521723681)
    ·
      refine ⟨1859206431210142891292761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2478941908280190521723681 1859206431210142891292761)
      ·
        refine ⟨1394404823407607168469571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1859206431210142891292761 1394404823407607168469571)
        ·
          refine ⟨2091607235111410752704357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1394404823407607168469571 2091607235111410752704357)
          ·
            refine ⟨392176356583389516132067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2091607235111410752704357 392176356583389516132067)
            ·
              refine ⟨588264534875084274198101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 392176356583389516132067 588264534875084274198101)
              ·
                refine ⟨6893725018067393838259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 588264534875084274198101 6893725018067393838259)
                ·
                  rfl

theorem cell20_45311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 8].length) (baseStart_45311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_45311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_45311 prefixEnd_45311 := by exact prefixLift 45311
  have htrace : WordTrace (prefixWord ++ tailWord_45311) baseStart_45311 baseEnd_45311 := by
    simpa [prefixWord, tailWord_45311, baseEnd_45311] using wordTrace_append hprefix tailTrace_45311
  have hstable : (prefixWord ++ tailWord_45311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45311).length < 2 ^ (prefixWord ++ tailWord_45311).sum := by decide
  have hdescent : baseEnd_45311 < baseStart_45311 := by decide
  rcases family_descends (prefixWord ++ tailWord_45311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45449 : List Nat := [1, 2, 1, 1, 6, 1, 2, 1, 5]
def baseStart_45449 : Nat := 118140960795 + 45449 * 2 ^ 59
def prefixEnd_45449 : Nat := 4983230072969 + 3 ^ 40 * 45449 * 2
def baseEnd_45449 : Nat := 20744162014487034914213

theorem tailTrace_45449 : CollatzResearch.WordTrace tailWord_45449 prefixEnd_45449 20744162014487034914213 := by
  unfold tailWord_45449
  simp only [CollatzResearch.WordTrace]
  refine ⟨1657661212353509916339401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1105107474902339944226267 1657661212353509916339401)
  ·
    refine ⟨1243245909265132437254551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1657661212353509916339401 1243245909265132437254551)
    ·
      refine ⟨1864868863897698655881827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1243245909265132437254551 1864868863897698655881827)
      ·
        refine ⟨2797303295846547983822741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1864868863897698655881827 2797303295846547983822741)
        ·
          refine ⟨131123591992806936741691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2797303295846547983822741 131123591992806936741691)
          ·
            refine ⟨196685387989210405112537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131123591992806936741691 196685387989210405112537)
            ·
              refine ⟨147514040991907803834403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196685387989210405112537 147514040991907803834403)
              ·
                refine ⟨221271061487861705751605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147514040991907803834403 221271061487861705751605)
                ·
                  refine ⟨20744162014487034914213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 221271061487861705751605 20744162014487034914213)
                  ·
                    rfl

theorem cell20_45449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_45449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_45449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_45449 prefixEnd_45449 := by exact prefixLift 45449
  have htrace : WordTrace (prefixWord ++ tailWord_45449) baseStart_45449 baseEnd_45449 := by
    simpa [prefixWord, tailWord_45449, baseEnd_45449] using wordTrace_append hprefix tailTrace_45449
  have hstable : (prefixWord ++ tailWord_45449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45449).length < 2 ^ (prefixWord ++ tailWord_45449).sum := by decide
  have hdescent : baseEnd_45449 < baseStart_45449 := by decide
  rcases family_descends (prefixWord ++ tailWord_45449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45463 : List Nat := [1, 1, 3, 3, 1, 1, 3, 7]
def baseStart_45463 : Nat := 118140960795 + 45463 * 2 ^ 59
def prefixEnd_45463 : Nat := 4983230072969 + 3 ^ 40 * 45463 * 2
def baseEnd_45463 : Nat := 6916850665321736149163

theorem tailTrace_45463 : CollatzResearch.WordTrace tailWord_45463 prefixEnd_45463 6916850665321736149163 := by
  unfold tailWord_45463
  simp only [CollatzResearch.WordTrace]
  refine ⟨1658171834302790307349043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1105447889535193538232695 1658171834302790307349043)
  ·
    refine ⟨2487257751454185461023565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1658171834302790307349043 2487257751454185461023565)
    ·
      refine ⟨932721656795319547883837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2487257751454185461023565 932721656795319547883837)
      ·
        refine ⟨349770621298244830456439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 932721656795319547883837 349770621298244830456439)
        ·
          refine ⟨524655931947367245684659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349770621298244830456439 524655931947367245684659)
          ·
            refine ⟨786983897921050868526989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524655931947367245684659 786983897921050868526989)
            ·
              refine ⟨295118961720394075697621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 786983897921050868526989 295118961720394075697621)
              ·
                refine ⟨6916850665321736149163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 295118961720394075697621 6916850665321736149163)
                ·
                  rfl

theorem cell20_45463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 7].length) (baseStart_45463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_45463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_45463 prefixEnd_45463 := by exact prefixLift 45463
  have htrace : WordTrace (prefixWord ++ tailWord_45463) baseStart_45463 baseEnd_45463 := by
    simpa [prefixWord, tailWord_45463, baseEnd_45463] using wordTrace_append hprefix tailTrace_45463
  have hstable : (prefixWord ++ tailWord_45463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45463).length < 2 ^ (prefixWord ++ tailWord_45463).sum := by decide
  have hdescent : baseEnd_45463 < baseStart_45463 := by decide
  rcases family_descends (prefixWord ++ tailWord_45463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45466 : List Nat := [3, 1, 1, 4, 1, 3, 1, 3, 3]
def baseStart_45466 : Nat := 118140960795 + 45466 * 2 ^ 59
def prefixEnd_45466 : Nat := 4983230072969 + 3 ^ 40 * 45466 * 2
def baseEnd_45466 : Nat := 20751921277710531347477

theorem tailTrace_45466 : CollatzResearch.WordTrace tailWord_45466 prefixEnd_45466 20751921277710531347477 := by
  unfold tailWord_45466
  simp only [CollatzResearch.WordTrace]
  refine ⟨414570313322980454927063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1105520835527947879805501 414570313322980454927063)
  ·
    refine ⟨621855469984470682390595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 414570313322980454927063 621855469984470682390595)
    ·
      refine ⟨932783204976706023585893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 621855469984470682390595 932783204976706023585893)
      ·
        refine ⟨174896850933132379422355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 932783204976706023585893 174896850933132379422355)
        ·
          refine ⟨262345276399698569133533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174896850933132379422355 262345276399698569133533)
          ·
            refine ⟨98379478649886963425075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 262345276399698569133533 98379478649886963425075)
            ·
              refine ⟨147569217974830445137613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98379478649886963425075 147569217974830445137613)
              ·
                refine ⟨55338456740561416926605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147569217974830445137613 55338456740561416926605)
                ·
                  refine ⟨20751921277710531347477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55338456740561416926605 20751921277710531347477)
                  ·
                    rfl

theorem cell20_45466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_45466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_45466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_45466 prefixEnd_45466 := by exact prefixLift 45466
  have htrace : WordTrace (prefixWord ++ tailWord_45466) baseStart_45466 baseEnd_45466 := by
    simpa [prefixWord, tailWord_45466, baseEnd_45466] using wordTrace_append hprefix tailTrace_45466
  have hstable : (prefixWord ++ tailWord_45466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45466).length < 2 ^ (prefixWord ++ tailWord_45466).sum := by decide
  have hdescent : baseEnd_45466 < baseStart_45466 := by decide
  rcases family_descends (prefixWord ++ tailWord_45466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45501 : List Nat := [1, 4, 1, 2, 2, 10]
def baseStart_45501 : Nat := 118140960795 + 45501 * 2 ^ 59
def prefixEnd_45501 : Nat := 4983230072969 + 3 ^ 40 * 45501 * 2
def baseEnd_45501 : Nat := 769181341903924636321

theorem tailTrace_45501 : CollatzResearch.WordTrace tailWord_45501 prefixEnd_45501 769181341903924636321 := by
  unfold tailWord_45501
  simp only [CollatzResearch.WordTrace]
  refine ⟨1659557808165122797232357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1106371872110081864821571 1659557808165122797232357)
  ·
    refine ⟨311167089030960524481067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1659557808165122797232357 311167089030960524481067)
    ·
      refine ⟨466750633546440786721601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311167089030960524481067 466750633546440786721601)
      ·
        refine ⟨350062975159830590041201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466750633546440786721601 350062975159830590041201)
        ·
          refine ⟨262547231369872942530901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 350062975159830590041201 262547231369872942530901)
          ·
            refine ⟨769181341903924636321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 262547231369872942530901 769181341903924636321)
            ·
              rfl

theorem cell20_45501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 10].length) (baseStart_45501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_45501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_45501 prefixEnd_45501 := by exact prefixLift 45501
  have htrace : WordTrace (prefixWord ++ tailWord_45501) baseStart_45501 baseEnd_45501 := by
    simpa [prefixWord, tailWord_45501, baseEnd_45501] using wordTrace_append hprefix tailTrace_45501
  have hstable : (prefixWord ++ tailWord_45501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45501).length < 2 ^ (prefixWord ++ tailWord_45501).sum := by decide
  have hdescent : baseEnd_45501 < baseStart_45501 := by decide
  rcases family_descends (prefixWord ++ tailWord_45501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45594 : List Nat := [3, 1, 1, 3, 1, 1, 6, 4]
def baseStart_45594 : Nat := 118140960795 + 45594 * 2 ^ 59
def prefixEnd_45594 : Nat := 4983230072969 + 3 ^ 40 * 45594 * 2
def baseEnd_45594 : Nat := 6936781321836991693429

theorem tailTrace_45594 : CollatzResearch.WordTrace tailWord_45594 prefixEnd_45594 6936781321836991693429 := by
  unfold tailWord_45594
  simp only [CollatzResearch.WordTrace]
  refine ⟨415737449207049920091959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1108633197885466453578557 415737449207049920091959)
  ·
    refine ⟨623606173810574880137939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 415737449207049920091959 623606173810574880137939)
    ·
      refine ⟨935409260715862320206909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 623606173810574880137939 935409260715862320206909)
      ·
        refine ⟨350778472768448370077591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 935409260715862320206909 350778472768448370077591)
        ·
          refine ⟨526167709152672555116387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350778472768448370077591 526167709152672555116387)
          ·
            refine ⟨789251563729008832674581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526167709152672555116387 789251563729008832674581)
            ·
              refine ⟨36996167049797289031621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 789251563729008832674581 36996167049797289031621)
              ·
                refine ⟨6936781321836991693429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36996167049797289031621 6936781321836991693429)
                ·
                  rfl

theorem cell20_45594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_45594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_45594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_45594 prefixEnd_45594 := by exact prefixLift 45594
  have htrace : WordTrace (prefixWord ++ tailWord_45594) baseStart_45594 baseEnd_45594 := by
    simpa [prefixWord, tailWord_45594, baseEnd_45594] using wordTrace_append hprefix tailTrace_45594
  have hstable : (prefixWord ++ tailWord_45594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45594).length < 2 ^ (prefixWord ++ tailWord_45594).sum := by decide
  have hdescent : baseEnd_45594 < baseStart_45594 := by decide
  rcases family_descends (prefixWord ++ tailWord_45594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45600 : List Nat := [2, 1, 1, 6, 3, 1, 1, 3, 2]
def baseStart_45600 : Nat := 118140960795 + 45600 * 2 ^ 59
def prefixEnd_45600 : Nat := 4983230072969 + 3 ^ 40 * 45600 * 2
def baseEnd_45600 : Nat := 20813082529001620880263

theorem tailTrace_45600 : CollatzResearch.WordTrace tailWord_45600 prefixEnd_45600 20813082529001620880263 := by
  unfold tailWord_45600
  simp only [CollatzResearch.WordTrace]
  refine ⟨831584317403231352543127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1108779089870975136724169 831584317403231352543127)
  ·
    refine ⟨1247376476104847028814691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 831584317403231352543127 1247376476104847028814691)
    ·
      refine ⟨1871064714157270543222037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1247376476104847028814691 1871064714157270543222037)
      ·
        refine ⟨87706158476122056713533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1871064714157270543222037 87706158476122056713533)
        ·
          refine ⟨32889809428545771267575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87706158476122056713533 32889809428545771267575)
          ·
            refine ⟨49334714142818656901363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32889809428545771267575 49334714142818656901363)
            ·
              refine ⟨74002071214227985352045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49334714142818656901363 74002071214227985352045)
              ·
                refine ⟨27750776705335494507017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74002071214227985352045 27750776705335494507017)
                ·
                  refine ⟨20813082529001620880263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27750776705335494507017 20813082529001620880263)
                  ·
                    rfl

theorem cell20_45600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 3, 2].length) (baseStart_45600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_45600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_45600 prefixEnd_45600 := by exact prefixLift 45600
  have htrace : WordTrace (prefixWord ++ tailWord_45600) baseStart_45600 baseEnd_45600 := by
    simpa [prefixWord, tailWord_45600, baseEnd_45600] using wordTrace_append hprefix tailTrace_45600
  have hstable : (prefixWord ++ tailWord_45600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45600).length < 2 ^ (prefixWord ++ tailWord_45600).sum := by decide
  have hdescent : baseEnd_45600 < baseStart_45600 := by decide
  rcases family_descends (prefixWord ++ tailWord_45600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45646 : List Nat := [4, 1, 1, 1, 1, 2, 2, 4, 4]
def baseStart_45646 : Nat := 118140960795 + 45646 * 2 ^ 59
def prefixEnd_45646 : Nat := 4983230072969 + 3 ^ 40 * 45646 * 2
def baseEnd_45646 : Nat := 20834078182429905346741

theorem tailTrace_45646 : CollatzResearch.WordTrace tailWord_45646 prefixEnd_45646 20834078182429905346741 := by
  unfold tailWord_45646
  simp only [CollatzResearch.WordTrace]
  refine ⟨208105799079976570157599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1109897595093208374173861 208105799079976570157599)
  ·
    refine ⟨312158698619964855236399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208105799079976570157599 312158698619964855236399)
    ·
      refine ⟨468238047929947282854599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 312158698619964855236399 468238047929947282854599)
      ·
        refine ⟨702357071894920924281899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 468238047929947282854599 702357071894920924281899)
        ·
          refine ⟨1053535607842381386422849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 702357071894920924281899 1053535607842381386422849)
          ·
            refine ⟨790151705881786039817137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1053535607842381386422849 790151705881786039817137)
            ·
              refine ⟨592613779411339529862853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 790151705881786039817137 592613779411339529862853)
              ·
                refine ⟨111115083639626161849285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 592613779411339529862853 111115083639626161849285)
                ·
                  refine ⟨20834078182429905346741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111115083639626161849285 20834078182429905346741)
                  ·
                    rfl

theorem cell20_45646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_45646 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_45646 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_45646 prefixEnd_45646 := by exact prefixLift 45646
  have htrace : WordTrace (prefixWord ++ tailWord_45646) baseStart_45646 baseEnd_45646 := by
    simpa [prefixWord, tailWord_45646, baseEnd_45646] using wordTrace_append hprefix tailTrace_45646
  have hstable : (prefixWord ++ tailWord_45646).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45646).length < 2 ^ (prefixWord ++ tailWord_45646).sum := by decide
  have hdescent : baseEnd_45646 < baseStart_45646 := by decide
  rcases family_descends (prefixWord ++ tailWord_45646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45653 : List Nat := [1, 3, 2, 2, 1, 1, 4, 6]
def baseStart_45653 : Nat := 118140960795 + 45653 * 2 ^ 59
def prefixEnd_45653 : Nat := 4983230072969 + 3 ^ 40 * 45653 * 2
def baseEnd_45653 : Nat := 6945757724389664037793

theorem tailTrace_45653 : CollatzResearch.WordTrace tailWord_45653 prefixEnd_45653 6945757724389664037793 := by
  unfold tailWord_45653
  simp only [CollatzResearch.WordTrace]
  refine ⟨1665101703614452756765613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1110067802409635171177075 1665101703614452756765613)
  ·
    refine ⟨624413138855419783787105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1665101703614452756765613 624413138855419783787105)
    ·
      refine ⟨468309854141564837840329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 624413138855419783787105 468309854141564837840329)
      ·
        refine ⟨351232390606173628380247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 468309854141564837840329 351232390606173628380247)
        ·
          refine ⟨526848585909260442570371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351232390606173628380247 526848585909260442570371)
          ·
            refine ⟨790272878863890663855557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526848585909260442570371 790272878863890663855557)
            ·
              refine ⟨148176164786979499472917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 790272878863890663855557 148176164786979499472917)
              ·
                refine ⟨6945757724389664037793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 148176164786979499472917 6945757724389664037793)
                ·
                  rfl

theorem cell20_45653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 6].length) (baseStart_45653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_45653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_45653 prefixEnd_45653 := by exact prefixLift 45653
  have htrace : WordTrace (prefixWord ++ tailWord_45653) baseStart_45653 baseEnd_45653 := by
    simpa [prefixWord, tailWord_45653, baseEnd_45653] using wordTrace_append hprefix tailTrace_45653
  have hstable : (prefixWord ++ tailWord_45653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45653).length < 2 ^ (prefixWord ++ tailWord_45653).sum := by decide
  have hdescent : baseEnd_45653 < baseStart_45653 := by decide
  rcases family_descends (prefixWord ++ tailWord_45653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45680 : List Nat := [2, 1, 1, 1, 7, 1, 1, 4, 2]
def baseStart_45680 : Nat := 118140960795 + 45680 * 2 ^ 59
def prefixEnd_45680 : Nat := 4983230072969 + 3 ^ 40 * 45680 * 2
def baseEnd_45680 : Nat := 20849596708876898213269

theorem tailTrace_45680 : CollatzResearch.WordTrace tailWord_45680 prefixEnd_45680 20849596708876898213269 := by
  unfold tailWord_45680
  simp only [CollatzResearch.WordTrace]
  refine ⟨833043237258318183999247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1110724316344424245332329 833043237258318183999247)
  ·
    refine ⟨1249564855887477275998871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 833043237258318183999247 1249564855887477275998871)
    ·
      refine ⟨1874347283831215913998307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1249564855887477275998871 1874347283831215913998307)
      ·
        refine ⟨2811520925746823870997461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1874347283831215913998307 2811520925746823870997461)
        ·
          refine ⟨65895021697191184476503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 2811520925746823870997461 65895021697191184476503)
          ·
            refine ⟨98842532545786776714755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65895021697191184476503 98842532545786776714755)
            ·
              refine ⟨148263798818680165072133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98842532545786776714755 148263798818680165072133)
              ·
                refine ⟨27799462278502530951025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 148263798818680165072133 27799462278502530951025)
                ·
                  refine ⟨20849596708876898213269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27799462278502530951025 20849596708876898213269)
                  ·
                    rfl

theorem cell20_45680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 4, 2].length) (baseStart_45680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_45680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_45680 prefixEnd_45680 := by exact prefixLift 45680
  have htrace : WordTrace (prefixWord ++ tailWord_45680) baseStart_45680 baseEnd_45680 := by
    simpa [prefixWord, tailWord_45680, baseEnd_45680] using wordTrace_append hprefix tailTrace_45680
  have hstable : (prefixWord ++ tailWord_45680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45680).length < 2 ^ (prefixWord ++ tailWord_45680).sum := by decide
  have hdescent : baseEnd_45680 < baseStart_45680 := by decide
  rcases family_descends (prefixWord ++ tailWord_45680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45749 : List Nat := [1, 3, 3, 3, 1, 2, 3, 1, 3]
def baseStart_45749 : Nat := 118140960795 + 45749 * 2 ^ 59
def prefixEnd_45749 : Nat := 4983230072969 + 3 ^ 40 * 45749 * 2
def baseEnd_45749 : Nat := 20881090189019324912987

theorem tailTrace_45749 : CollatzResearch.WordTrace tailWord_45749 prefixEnd_45749 20881090189019324912987 := by
  unfold tailWord_45749
  simp only [CollatzResearch.WordTrace]
  refine ⟨1668603111266661152260301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1112402074177774101506867 1668603111266661152260301)
  ·
    refine ⟨625726166724997932097613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1668603111266661152260301 625726166724997932097613)
    ·
      refine ⟨234647312521874224536605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 625726166724997932097613 234647312521874224536605)
      ·
        refine ⟨87992742195702834201227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234647312521874224536605 87992742195702834201227)
        ·
          refine ⟨131989113293554251301841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87992742195702834201227 131989113293554251301841)
          ·
            refine ⟨98991834970165688476381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131989113293554251301841 98991834970165688476381)
            ·
              refine ⟨37121938113812133178643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98991834970165688476381 37121938113812133178643)
              ·
                refine ⟨55682907170718199767965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37121938113812133178643 55682907170718199767965)
                ·
                  refine ⟨20881090189019324912987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55682907170718199767965 20881090189019324912987)
                  ·
                    rfl

theorem cell20_45749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 3].length) (baseStart_45749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_45749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_45749 prefixEnd_45749 := by exact prefixLift 45749
  have htrace : WordTrace (prefixWord ++ tailWord_45749) baseStart_45749 baseEnd_45749 := by
    simpa [prefixWord, tailWord_45749, baseEnd_45749] using wordTrace_append hprefix tailTrace_45749
  have hstable : (prefixWord ++ tailWord_45749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45749).length < 2 ^ (prefixWord ++ tailWord_45749).sum := by decide
  have hdescent : baseEnd_45749 < baseStart_45749 := by decide
  rcases family_descends (prefixWord ++ tailWord_45749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45760 : List Nat := [2, 1, 1, 2, 4, 2, 2, 2, 4]
def baseStart_45760 : Nat := 118140960795 + 45760 * 2 ^ 59
def prefixEnd_45760 : Nat := 4983230072969 + 3 ^ 40 * 45760 * 2
def baseEnd_45760 : Nat := 20886110888752175546275

theorem tailTrace_45760 : CollatzResearch.WordTrace tailWord_45760 prefixEnd_45760 20886110888752175546275 := by
  unfold tailWord_45760
  simp only [CollatzResearch.WordTrace]
  refine ⟨834502157113405015455367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1112669542817873353940489 834502157113405015455367)
  ·
    refine ⟨1251753235670107523183051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 834502157113405015455367 1251753235670107523183051)
    ·
      refine ⟨1877629853505161284774577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1251753235670107523183051 1877629853505161284774577)
      ·
        refine ⟨1408222390128870963580933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1877629853505161284774577 1408222390128870963580933)
        ·
          refine ⟨264041698149163305671425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1408222390128870963580933 264041698149163305671425)
          ·
            refine ⟨198031273611872479253569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264041698149163305671425 198031273611872479253569)
            ·
              refine ⟨148523455208904359440177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198031273611872479253569 148523455208904359440177)
              ·
                refine ⟨111392591406678269580133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148523455208904359440177 111392591406678269580133)
                ·
                  refine ⟨20886110888752175546275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111392591406678269580133 20886110888752175546275)
                  ·
                    rfl

theorem cell20_45760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_45760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_45760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_45760 prefixEnd_45760 := by exact prefixLift 45760
  have htrace : WordTrace (prefixWord ++ tailWord_45760) baseStart_45760 baseEnd_45760 := by
    simpa [prefixWord, tailWord_45760, baseEnd_45760] using wordTrace_append hprefix tailTrace_45760
  have hstable : (prefixWord ++ tailWord_45760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45760).length < 2 ^ (prefixWord ++ tailWord_45760).sum := by decide
  have hdescent : baseEnd_45760 < baseStart_45760 := by decide
  rcases family_descends (prefixWord ++ tailWord_45760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45822 : List Nat := [4, 2, 2, 1, 2, 1, 2, 6]
def baseStart_45822 : Nat := 118140960795 + 45822 * 2 ^ 59
def prefixEnd_45822 : Nat := 4983230072969 + 3 ^ 40 * 45822 * 2
def baseEnd_45822 : Nat := 6971469792718505159785

theorem tailTrace_45822 : CollatzResearch.WordTrace tailWord_45822 prefixEnd_45822 6971469792718505159785 := by
  unfold tailWord_45822
  simp only [CollatzResearch.WordTrace]
  refine ⟨208908205000274327458465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1114177093334796413111813 208908205000274327458465)
  ·
    refine ⟨156681153750205745593849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208908205000274327458465 156681153750205745593849)
    ·
      refine ⟨117510865312654309195387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156681153750205745593849 117510865312654309195387)
      ·
        refine ⟨176266297968981463793081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117510865312654309195387 176266297968981463793081)
        ·
          refine ⟨132199723476736097844811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176266297968981463793081 132199723476736097844811)
          ·
            refine ⟨198299585215104146767217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132199723476736097844811 198299585215104146767217)
            ·
              refine ⟨148724688911328110075413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198299585215104146767217 148724688911328110075413)
              ·
                refine ⟨6971469792718505159785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 148724688911328110075413 6971469792718505159785)
                ·
                  rfl

theorem cell20_45822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_45822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_45822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_45822 prefixEnd_45822 := by exact prefixLift 45822
  have htrace : WordTrace (prefixWord ++ tailWord_45822) baseStart_45822 baseEnd_45822 := by
    simpa [prefixWord, tailWord_45822, baseEnd_45822] using wordTrace_append hprefix tailTrace_45822
  have hstable : (prefixWord ++ tailWord_45822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45822).length < 2 ^ (prefixWord ++ tailWord_45822).sum := by decide
  have hdescent : baseEnd_45822 < baseStart_45822 := by decide
  rcases family_descends (prefixWord ++ tailWord_45822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45874 : List Nat := [3, 2, 1, 1, 3, 1, 3, 2, 4]
def baseStart_45874 : Nat := 118140960795 + 45874 * 2 ^ 59
def prefixEnd_45874 : Nat := 4983230072969 + 3 ^ 40 * 45874 * 2
def baseEnd_45874 : Nat := 20938143595074445745809

theorem tailTrace_45874 : CollatzResearch.WordTrace tailWord_45874 prefixEnd_45874 20938143595074445745809 := by
  unfold tailWord_45874
  simp only [CollatzResearch.WordTrace]
  refine ⟨418290558953451875140169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1115441490542538333707117 418290558953451875140169)
  ·
    refine ⟨313717919215088906355127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 418290558953451875140169 313717919215088906355127)
    ·
      refine ⟨470576878822633359532691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313717919215088906355127 470576878822633359532691)
      ·
        refine ⟨705865318233950039299037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470576878822633359532691 705865318233950039299037)
        ·
          refine ⟨264699494337731264737139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 705865318233950039299037 264699494337731264737139)
          ·
            refine ⟨397049241506596897105709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264699494337731264737139 397049241506596897105709)
            ·
              refine ⟨148893465564973836414641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 397049241506596897105709 148893465564973836414641)
              ·
                refine ⟨111670099173730377310981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148893465564973836414641 111670099173730377310981)
                ·
                  refine ⟨20938143595074445745809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111670099173730377310981 20938143595074445745809)
                  ·
                    rfl

theorem cell20_45874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_45874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_45874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_45874 prefixEnd_45874 := by exact prefixLift 45874
  have htrace : WordTrace (prefixWord ++ tailWord_45874) baseStart_45874 baseEnd_45874 := by
    simpa [prefixWord, tailWord_45874, baseEnd_45874] using wordTrace_append hprefix tailTrace_45874
  have hstable : (prefixWord ++ tailWord_45874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45874).length < 2 ^ (prefixWord ++ tailWord_45874).sum := by decide
  have hdescent : baseEnd_45874 < baseStart_45874 := by decide
  rcases family_descends (prefixWord ++ tailWord_45874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45891 : List Nat := [1, 1, 1, 3, 1, 4, 4, 3, 2]
def baseStart_45891 : Nat := 118140960795 + 45891 * 2 ^ 59
def prefixEnd_45891 : Nat := 4983230072969 + 3 ^ 40 * 45891 * 2
def baseEnd_45891 : Nat := 20945902858297942179073

theorem tailTrace_45891 : CollatzResearch.WordTrace tailWord_45891 prefixEnd_45891 20945902858297942179073 := by
  unfold tailWord_45891
  simp only [CollatzResearch.WordTrace]
  refine ⟨1673782276752219403929527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1115854851168146269286351 1673782276752219403929527)
  ·
    refine ⟨2510673415128329105894291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1673782276752219403929527 2510673415128329105894291)
    ·
      refine ⟨3766010122692493658841437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2510673415128329105894291 3766010122692493658841437)
      ·
        refine ⟨1412253796009685122065539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3766010122692493658841437 1412253796009685122065539)
        ·
          refine ⟨2118380694014527683098309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1412253796009685122065539 2118380694014527683098309)
          ·
            refine ⟨397196380127723940580933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2118380694014527683098309 397196380127723940580933)
            ·
              refine ⟨74474321273948238858925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 397196380127723940580933 74474321273948238858925)
              ·
                refine ⟨27927870477730589572097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74474321273948238858925 27927870477730589572097)
                ·
                  refine ⟨20945902858297942179073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27927870477730589572097 20945902858297942179073)
                  ·
                    rfl

theorem cell20_45891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 3, 2].length) (baseStart_45891 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_45891 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_45891 prefixEnd_45891 := by exact prefixLift 45891
  have htrace : WordTrace (prefixWord ++ tailWord_45891) baseStart_45891 baseEnd_45891 := by
    simpa [prefixWord, tailWord_45891, baseEnd_45891] using wordTrace_append hprefix tailTrace_45891
  have hstable : (prefixWord ++ tailWord_45891).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45891).length < 2 ^ (prefixWord ++ tailWord_45891).sum := by decide
  have hdescent : baseEnd_45891 < baseStart_45891 := by decide
  rcases family_descends (prefixWord ++ tailWord_45891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45895 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 8]
def baseStart_45895 : Nat := 118140960795 + 45895 * 2 ^ 59
def prefixEnd_45895 : Nat := 4983230072969 + 3 ^ 40 * 45895 * 2
def baseEnd_45895 : Nat := 20947728567291706045723

theorem tailTrace_45895 : CollatzResearch.WordTrace tailWord_45895 prefixEnd_45895 20947728567291706045723 := by
  unfold tailWord_45895
  simp only [CollatzResearch.WordTrace]
  refine ⟨1673928168737728087075139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1115952112491818724716759 1673928168737728087075139)
  ·
    refine ⟨2510892253106592130612709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1673928168737728087075139 2510892253106592130612709)
    ·
      refine ⟨470792297457486024489883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2510892253106592130612709 470792297457486024489883)
      ·
        refine ⟨706188446186229036734825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470792297457486024489883 706188446186229036734825)
        ·
          refine ⟨529641334639671777551119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 706188446186229036734825 529641334639671777551119)
          ·
            refine ⟨794462001959507666326679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529641334639671777551119 794462001959507666326679)
            ·
              refine ⟨1191693002939261499490019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 794462001959507666326679 1191693002939261499490019)
              ·
                refine ⟨1787539504408892249235029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1191693002939261499490019 1787539504408892249235029)
                ·
                  refine ⟨20947728567291706045723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1787539504408892249235029 20947728567291706045723)
                  ·
                    rfl

theorem cell20_45895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 8].length) (baseStart_45895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_45895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_45895 prefixEnd_45895 := by exact prefixLift 45895
  have htrace : WordTrace (prefixWord ++ tailWord_45895) baseStart_45895 baseEnd_45895 := by
    simpa [prefixWord, tailWord_45895, baseEnd_45895] using wordTrace_append hprefix tailTrace_45895
  have hstable : (prefixWord ++ tailWord_45895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45895).length < 2 ^ (prefixWord ++ tailWord_45895).sum := by decide
  have hdescent : baseEnd_45895 < baseStart_45895 := by decide
  rcases family_descends (prefixWord ++ tailWord_45895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45905 : List Nat := [1, 2, 2, 1, 6, 1, 1, 1, 5]
def baseStart_45905 : Nat := 118140960795 + 45905 * 2 ^ 59
def prefixEnd_45905 : Nat := 4983230072969 + 3 ^ 40 * 45905 * 2
def baseEnd_45905 : Nat := 20952292839776115712349

theorem tailTrace_45905 : CollatzResearch.WordTrace tailWord_45905 prefixEnd_45905 20952292839776115712349 := by
  unfold tailWord_45905
  simp only [CollatzResearch.WordTrace]
  refine ⟨1674292898701499794939169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1116195265800999863292779 1674292898701499794939169)
  ·
    refine ⟨1255719674026124846204377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1674292898701499794939169 1255719674026124846204377)
    ·
      refine ⟨941789755519593634653283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1255719674026124846204377 941789755519593634653283)
      ·
        refine ⟨1412684633279390451979925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 941789755519593634653283 1412684633279390451979925)
        ·
          refine ⟨66219592184971427436559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1412684633279390451979925 66219592184971427436559)
          ·
            refine ⟨99329388277457141154839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66219592184971427436559 99329388277457141154839)
            ·
              refine ⟨148994082416185711732259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99329388277457141154839 148994082416185711732259)
              ·
                refine ⟨223491123624278567598389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148994082416185711732259 223491123624278567598389)
                ·
                  refine ⟨20952292839776115712349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 223491123624278567598389 20952292839776115712349)
                  ·
                    rfl

theorem cell20_45905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 5].length) (baseStart_45905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_45905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_45905 prefixEnd_45905 := by exact prefixLift 45905
  have htrace : WordTrace (prefixWord ++ tailWord_45905) baseStart_45905 baseEnd_45905 := by
    simpa [prefixWord, tailWord_45905, baseEnd_45905] using wordTrace_append hprefix tailTrace_45905
  have hstable : (prefixWord ++ tailWord_45905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45905).length < 2 ^ (prefixWord ++ tailWord_45905).sum := by decide
  have hdescent : baseEnd_45905 < baseStart_45905 := by decide
  rcases family_descends (prefixWord ++ tailWord_45905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45957 : List Nat := [1, 3, 1, 1, 3, 5, 6]
def baseStart_45957 : Nat := 118140960795 + 45957 * 2 ^ 59
def prefixEnd_45957 : Nat := 4983230072969 + 3 ^ 40 * 45957 * 2
def baseEnd_45957 : Nat := 2330669672966116219867

theorem tailTrace_45957 : CollatzResearch.WordTrace tailWord_45957 prefixEnd_45957 2330669672966116219867 := by
  unfold tailWord_45957
  simp only [CollatzResearch.WordTrace]
  refine ⟨1676189494513112675832125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1117459663008741783888083 1676189494513112675832125)
  ·
    refine ⟨628571060442417253437047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1676189494513112675832125 628571060442417253437047)
    ·
      refine ⟨942856590663625880155571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 628571060442417253437047 942856590663625880155571)
      ·
        refine ⟨1414284885995438820233357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 942856590663625880155571 1414284885995438820233357)
        ·
          refine ⟨530356832248289557587509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1414284885995438820233357 530356832248289557587509)
          ·
            refine ⟨49720953023277146023829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 530356832248289557587509 49720953023277146023829)
            ·
              refine ⟨2330669672966116219867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49720953023277146023829 2330669672966116219867)
              ·
                rfl

theorem cell20_45957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 6].length) (baseStart_45957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_45957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_45957 prefixEnd_45957 := by exact prefixLift 45957
  have htrace : WordTrace (prefixWord ++ tailWord_45957) baseStart_45957 baseEnd_45957 := by
    simpa [prefixWord, tailWord_45957, baseEnd_45957] using wordTrace_append hprefix tailTrace_45957
  have hstable : (prefixWord ++ tailWord_45957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45957).length < 2 ^ (prefixWord ++ tailWord_45957).sum := by decide
  have hdescent : baseEnd_45957 < baseStart_45957 := by decide
  rcases family_descends (prefixWord ++ tailWord_45957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45964 : List Nat := [2, 2, 1, 2, 1, 2, 4, 1, 5]
def baseStart_45964 : Nat := 118140960795 + 45964 * 2 ^ 59
def prefixEnd_45964 : Nat := 4983230072969 + 3 ^ 40 * 45964 * 2
def baseEnd_45964 : Nat := 20979222047434132745441

theorem tailTrace_45964 : CollatzResearch.WordTrace tailWord_45964 prefixEnd_45964 20979222047434132745441 := by
  unfold tailWord_45964
  simp only [CollatzResearch.WordTrace]
  refine ⟨838222402743876435668473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1117629870325168580891297 838222402743876435668473)
  ·
    refine ⟨628666802057907326751355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 838222402743876435668473 628666802057907326751355)
    ·
      refine ⟨943000203086860990127033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 628666802057907326751355 943000203086860990127033)
      ·
        refine ⟨707250152315145742595275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 943000203086860990127033 707250152315145742595275)
        ·
          refine ⟨1060875228472718613892913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 707250152315145742595275 1060875228472718613892913)
          ·
            refine ⟨795656421354538960419685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1060875228472718613892913 795656421354538960419685)
            ·
              refine ⟨149185579003976055078691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 795656421354538960419685 149185579003976055078691)
              ·
                refine ⟨223778368505964082618037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149185579003976055078691 223778368505964082618037)
                ·
                  refine ⟨20979222047434132745441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 223778368505964082618037 20979222047434132745441)
                  ·
                    rfl

theorem cell20_45964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_45964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_45964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_45964 prefixEnd_45964 := by exact prefixLift 45964
  have htrace : WordTrace (prefixWord ++ tailWord_45964) baseStart_45964 baseEnd_45964 := by
    simpa [prefixWord, tailWord_45964, baseEnd_45964] using wordTrace_append hprefix tailTrace_45964
  have hstable : (prefixWord ++ tailWord_45964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45964).length < 2 ^ (prefixWord ++ tailWord_45964).sum := by decide
  have hdescent : baseEnd_45964 < baseStart_45964 := by decide
  rcases family_descends (prefixWord ++ tailWord_45964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45971 : List Nat := [1, 1, 1, 2, 1, 2, 1, 7, 4]
def baseStart_45971 : Nat := 118140960795 + 45971 * 2 ^ 59
def prefixEnd_45971 : Nat := 4983230072969 + 3 ^ 40 * 45971 * 2
def baseEnd_45971 : Nat := 20982417038173219512079

theorem tailTrace_45971 : CollatzResearch.WordTrace tailWord_45971 prefixEnd_45971 20982417038173219512079 := by
  unfold tailWord_45971
  simp only [CollatzResearch.WordTrace]
  refine ⟨1676700116462393066841767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1117800077641595377894511 1676700116462393066841767)
  ·
    refine ⟨2515050174693589600262651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1676700116462393066841767 2515050174693589600262651)
    ·
      refine ⟨3772575262040384400393977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2515050174693589600262651 3772575262040384400393977)
      ·
        refine ⟨2829431446530288300295483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3772575262040384400393977 2829431446530288300295483)
        ·
          refine ⟨4244147169795432450443225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2829431446530288300295483 4244147169795432450443225)
          ·
            refine ⟨3183110377346574337832419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4244147169795432450443225 3183110377346574337832419)
            ·
              refine ⟨4774665566019861506748629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3183110377346574337832419 4774665566019861506748629)
              ·
                refine ⟨111906224203590504064421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4774665566019861506748629 111906224203590504064421)
                ·
                  refine ⟨20982417038173219512079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111906224203590504064421 20982417038173219512079)
                  ·
                    rfl

theorem cell20_45971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 4].length) (baseStart_45971 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_45971 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_45971 prefixEnd_45971 := by exact prefixLift 45971
  have htrace : WordTrace (prefixWord ++ tailWord_45971) baseStart_45971 baseEnd_45971 := by
    simpa [prefixWord, tailWord_45971, baseEnd_45971] using wordTrace_append hprefix tailTrace_45971
  have hstable : (prefixWord ++ tailWord_45971).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45971).length < 2 ^ (prefixWord ++ tailWord_45971).sum := by decide
  have hdescent : baseEnd_45971 < baseStart_45971 := by decide
  rcases family_descends (prefixWord ++ tailWord_45971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_45981 : List Nat := [1, 4, 2, 1, 2, 1, 3, 3, 3]
def baseStart_45981 : Nat := 118140960795 + 45981 * 2 ^ 59
def prefixEnd_45981 : Nat := 4983230072969 + 3 ^ 40 * 45981 * 2
def baseEnd_45981 : Nat := 20986981310657629178705

theorem tailTrace_45981 : CollatzResearch.WordTrace tailWord_45981 prefixEnd_45981 20986981310657629178705 := by
  unfold tailWord_45981
  simp only [CollatzResearch.WordTrace]
  refine ⟨1677064846426164774705797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1118043230950776516470531 1677064846426164774705797)
  ·
    refine ⟨314449658704905895257337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1677064846426164774705797 314449658704905895257337)
    ·
      refine ⟨235837244028679421443003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314449658704905895257337 235837244028679421443003)
      ·
        refine ⟨353755866043019132164505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235837244028679421443003 353755866043019132164505)
        ·
          refine ⟨265316899532264349123379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353755866043019132164505 265316899532264349123379)
          ·
            refine ⟨397975349298396523685069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265316899532264349123379 397975349298396523685069)
            ·
              refine ⟨149240755986898696381901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 397975349298396523685069 149240755986898696381901)
              ·
                refine ⟨55965283495087011143213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149240755986898696381901 55965283495087011143213)
                ·
                  refine ⟨20986981310657629178705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55965283495087011143213 20986981310657629178705)
                  ·
                    rfl

theorem cell20_45981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_45981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_45981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_45981 prefixEnd_45981 := by exact prefixLift 45981
  have htrace : WordTrace (prefixWord ++ tailWord_45981) baseStart_45981 baseEnd_45981 := by
    simpa [prefixWord, tailWord_45981, baseEnd_45981] using wordTrace_append hprefix tailTrace_45981
  have hstable : (prefixWord ++ tailWord_45981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_45981).length < 2 ^ (prefixWord ++ tailWord_45981).sum := by decide
  have hdescent : baseEnd_45981 < baseStart_45981 := by decide
  rcases family_descends (prefixWord ++ tailWord_45981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46005 : List Nat := [1, 3, 3, 2, 1, 1, 2, 5, 2]
def baseStart_46005 : Nat := 118140960795 + 46005 * 2 ^ 59
def prefixEnd_46005 : Nat := 4983230072969 + 3 ^ 40 * 46005 * 2
def baseEnd_46005 : Nat := 20997935564620212378607

theorem tailTrace_46005 : CollatzResearch.WordTrace tailWord_46005 prefixEnd_46005 20997935564620212378607 := by
  unfold tailWord_46005
  simp only [CollatzResearch.WordTrace]
  refine ⟨1677940198339216873579469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1118626798892811249052979 1677940198339216873579469)
  ·
    refine ⟨629227574377206327592301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1677940198339216873579469 629227574377206327592301)
    ·
      refine ⟨235960340391452372847113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 629227574377206327592301 235960340391452372847113)
      ·
        refine ⟨176970255293589279635335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235960340391452372847113 176970255293589279635335)
        ·
          refine ⟨265455382940383919453003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176970255293589279635335 265455382940383919453003)
          ·
            refine ⟨398183074410575879179505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265455382940383919453003 398183074410575879179505)
            ·
              refine ⟨298637305807931909384629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 398183074410575879179505 298637305807931909384629)
              ·
                refine ⟨27997247419493616504809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 298637305807931909384629 27997247419493616504809)
                ·
                  refine ⟨20997935564620212378607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27997247419493616504809 20997935564620212378607)
                  ·
                    rfl

theorem cell20_46005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 5, 2].length) (baseStart_46005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46005 prefixEnd_46005 := by exact prefixLift 46005
  have htrace : WordTrace (prefixWord ++ tailWord_46005) baseStart_46005 baseEnd_46005 := by
    simpa [prefixWord, tailWord_46005, baseEnd_46005] using wordTrace_append hprefix tailTrace_46005
  have hstable : (prefixWord ++ tailWord_46005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46005).length < 2 ^ (prefixWord ++ tailWord_46005).sum := by decide
  have hdescent : baseEnd_46005 < baseStart_46005 := by decide
  rcases family_descends (prefixWord ++ tailWord_46005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46016 : List Nat := [2, 1, 1, 2, 3, 11]
def baseStart_46016 : Nat := 118140960795 + 46016 * 2 ^ 59
def prefixEnd_46016 : Nat := 4983230072969 + 3 ^ 40 * 46016 * 2
def baseEnd_46016 : Nat := 777887269050113444885

theorem tailTrace_46016 : CollatzResearch.WordTrace tailWord_46016 prefixEnd_46016 777887269050113444885 := by
  unfold tailWord_46016
  simp only [CollatzResearch.WordTrace]
  refine ⟨839170700649682876114951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1118894267532910501486601 839170700649682876114951)
  ·
    refine ⟨1258756050974524314172427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 839170700649682876114951 1258756050974524314172427)
    ·
      refine ⟨1888134076461786471258641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1258756050974524314172427 1888134076461786471258641)
      ·
        refine ⟨1416100557346339853443981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1888134076461786471258641 1416100557346339853443981)
        ·
          refine ⟨531037709004877445041493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1416100557346339853443981 531037709004877445041493)
          ·
            refine ⟨777887269050113444885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 531037709004877445041493 777887269050113444885)
            ·
              rfl

theorem cell20_46016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 11].length) (baseStart_46016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46016 prefixEnd_46016 := by exact prefixLift 46016
  have htrace : WordTrace (prefixWord ++ tailWord_46016) baseStart_46016 baseEnd_46016 := by
    simpa [prefixWord, tailWord_46016, baseEnd_46016] using wordTrace_append hprefix tailTrace_46016
  have hstable : (prefixWord ++ tailWord_46016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46016).length < 2 ^ (prefixWord ++ tailWord_46016).sum := by decide
  have hdescent : baseEnd_46016 < baseStart_46016 := by decide
  rcases family_descends (prefixWord ++ tailWord_46016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46081 : List Nat := [1, 2, 4, 1, 2, 2, 2, 4, 2]
def baseStart_46081 : Nat := 118140960795 + 46081 * 2 ^ 59
def prefixEnd_46081 : Nat := 4983230072969 + 3 ^ 40 * 46081 * 2
def baseEnd_46081 : Nat := 21032624035501725844963

theorem tailTrace_46081 : CollatzResearch.WordTrace tailWord_46081 prefixEnd_46081 21032624035501725844963 := by
  unfold tailWord_46081
  simp only [CollatzResearch.WordTrace]
  refine ⟨1680712146063881853346097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1120474764042587902230731 1680712146063881853346097)
  ·
    refine ⟨1260534109547911390009573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1680712146063881853346097 1260534109547911390009573)
    ·
      refine ⟨236350145540233385626795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1260534109547911390009573 236350145540233385626795)
      ·
        refine ⟨354525218310350078440193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236350145540233385626795 354525218310350078440193)
        ·
          refine ⟨265893913732762558830145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 354525218310350078440193 265893913732762558830145)
          ·
            refine ⟨199420435299571919122609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265893913732762558830145 199420435299571919122609)
            ·
              refine ⟨149565326474678939341957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199420435299571919122609 149565326474678939341957)
              ·
                refine ⟨28043498714002301126617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 149565326474678939341957 28043498714002301126617)
                ·
                  refine ⟨21032624035501725844963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28043498714002301126617 21032624035501725844963)
                  ·
                    rfl

theorem cell20_46081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 4, 2].length) (baseStart_46081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46081 prefixEnd_46081 := by exact prefixLift 46081
  have htrace : WordTrace (prefixWord ++ tailWord_46081) baseStart_46081 baseEnd_46081 := by
    simpa [prefixWord, tailWord_46081, baseEnd_46081] using wordTrace_append hprefix tailTrace_46081
  have hstable : (prefixWord ++ tailWord_46081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46081).length < 2 ^ (prefixWord ++ tailWord_46081).sum := by decide
  have hdescent : baseEnd_46081 < baseStart_46081 := by decide
  rcases family_descends (prefixWord ++ tailWord_46081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46136 : List Nat := [2, 1, 2, 1, 5, 2, 3, 2, 2]
def baseStart_46136 : Nat := 118140960795 + 46136 * 2 ^ 59
def prefixEnd_46136 : Nat := 4983230072969 + 3 ^ 40 * 46136 * 2
def baseEnd_46136 : Nat := 21057727534165979011405

theorem tailTrace_46136 : CollatzResearch.WordTrace tailWord_46136 prefixEnd_46136 21057727534165979011405 := by
  unfold tailWord_46136
  simp only [CollatzResearch.WordTrace]
  refine ⟨841359080432313123299131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1121812107243084164398841 841359080432313123299131)
  ·
    refine ⟨1262038620648469684948697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 841359080432313123299131 1262038620648469684948697)
    ·
      refine ⟨946528965486352263711523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1262038620648469684948697 946528965486352263711523)
      ·
        refine ⟨1419793448229528395567285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 946528965486352263711523 1419793448229528395567285)
        ·
          refine ⟨133105635771518287084433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1419793448229528395567285 133105635771518287084433)
          ·
            refine ⟨99829226828638715313325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133105635771518287084433 99829226828638715313325)
            ·
              refine ⟨37435960060739518242497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99829226828638715313325 37435960060739518242497)
              ·
                refine ⟨28076970045554638681873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37435960060739518242497 28076970045554638681873)
                ·
                  refine ⟨21057727534165979011405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28076970045554638681873 21057727534165979011405)
                  ·
                    rfl

theorem cell20_46136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 2, 2].length) (baseStart_46136 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46136 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46136 prefixEnd_46136 := by exact prefixLift 46136
  have htrace : WordTrace (prefixWord ++ tailWord_46136) baseStart_46136 baseEnd_46136 := by
    simpa [prefixWord, tailWord_46136, baseEnd_46136] using wordTrace_append hprefix tailTrace_46136
  have hstable : (prefixWord ++ tailWord_46136).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46136).length < 2 ^ (prefixWord ++ tailWord_46136).sum := by decide
  have hdescent : baseEnd_46136 < baseStart_46136 := by decide
  rcases family_descends (prefixWord ++ tailWord_46136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46140 : List Nat := [2, 2, 2, 2, 2, 2, 3, 1, 4]
def baseStart_46140 : Nat := 118140960795 + 46140 * 2 ^ 59
def prefixEnd_46140 : Nat := 4983230072969 + 3 ^ 40 * 46140 * 2
def baseEnd_46140 : Nat := 21059553243159742878055

theorem tailTrace_46140 : CollatzResearch.WordTrace tailWord_46140 prefixEnd_46140 21059553243159742878055 := by
  unfold tailWord_46140
  simp only [CollatzResearch.WordTrace]
  refine ⟨841432026425067464871937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1121909368566756619829249 841432026425067464871937)
  ·
    refine ⟨631074019818800598653953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 841432026425067464871937 631074019818800598653953)
    ·
      refine ⟨473305514864100448990465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 631074019818800598653953 473305514864100448990465)
      ·
        refine ⟨354979136148075336742849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 473305514864100448990465 354979136148075336742849)
        ·
          refine ⟨266234352111056502557137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 354979136148075336742849 266234352111056502557137)
          ·
            refine ⟨199675764083292376917853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266234352111056502557137 199675764083292376917853)
            ·
              refine ⟨74878411531234641344195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199675764083292376917853 74878411531234641344195)
              ·
                refine ⟨112317617296851962016293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74878411531234641344195 112317617296851962016293)
                ·
                  refine ⟨21059553243159742878055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112317617296851962016293 21059553243159742878055)
                  ·
                    rfl

theorem cell20_46140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_46140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46140 prefixEnd_46140 := by exact prefixLift 46140
  have htrace : WordTrace (prefixWord ++ tailWord_46140) baseStart_46140 baseEnd_46140 := by
    simpa [prefixWord, tailWord_46140, baseEnd_46140] using wordTrace_append hprefix tailTrace_46140
  have hstable : (prefixWord ++ tailWord_46140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46140).length < 2 ^ (prefixWord ++ tailWord_46140).sum := by decide
  have hdescent : baseEnd_46140 < baseStart_46140 := by decide
  rcases family_descends (prefixWord ++ tailWord_46140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46161 : List Nat := [1, 2, 2, 1, 3, 1, 2, 4, 4]
def baseStart_46161 : Nat := 118140960795 + 46161 * 2 ^ 59
def prefixEnd_46161 : Nat := 4983230072969 + 3 ^ 40 * 46161 * 2
def baseEnd_46161 : Nat := 21069138215377003177969

theorem tailTrace_46161 : CollatzResearch.WordTrace tailWord_46161 prefixEnd_46161 21069138215377003177969 := by
  unfold tailWord_46161
  simp only [CollatzResearch.WordTrace]
  refine ⟨1683629985774055516258337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1122419990516037010838891 1683629985774055516258337)
  ·
    refine ⟨1262722489330541637193753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1683629985774055516258337 1262722489330541637193753)
    ·
      refine ⟨947041866997906227895315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1262722489330541637193753 947041866997906227895315)
      ·
        refine ⟨1420562800496859341842973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 947041866997906227895315 1420562800496859341842973)
        ·
          refine ⟨532711050186322253191115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1420562800496859341842973 532711050186322253191115)
          ·
            refine ⟨799066575279483379786673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 532711050186322253191115 799066575279483379786673)
            ·
              refine ⟨599299931459612534840005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 799066575279483379786673 599299931459612534840005)
              ·
                refine ⟨112368737148677350282501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 599299931459612534840005 112368737148677350282501)
                ·
                  refine ⟨21069138215377003177969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112368737148677350282501 21069138215377003177969)
                  ·
                    rfl

theorem cell20_46161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_46161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46161 prefixEnd_46161 := by exact prefixLift 46161
  have htrace : WordTrace (prefixWord ++ tailWord_46161) baseStart_46161 baseEnd_46161 := by
    simpa [prefixWord, tailWord_46161, baseEnd_46161] using wordTrace_append hprefix tailTrace_46161
  have hstable : (prefixWord ++ tailWord_46161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46161).length < 2 ^ (prefixWord ++ tailWord_46161).sum := by decide
  have hdescent : baseEnd_46161 < baseStart_46161 := by decide
  rcases family_descends (prefixWord ++ tailWord_46161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46168 : List Nat := [2, 1, 2, 2, 1, 3, 1, 8]
def baseStart_46168 : Nat := 118140960795 + 46168 * 2 ^ 59
def prefixEnd_46168 : Nat := 4983230072969 + 3 ^ 40 * 46168 * 2
def baseEnd_46168 : Nat := 7024111068705363314869

theorem tailTrace_46168 : CollatzResearch.WordTrace tailWord_46168 prefixEnd_46168 7024111068705363314869 := by
  unfold tailWord_46168
  simp only [CollatzResearch.WordTrace]
  refine ⟨841942648374347855881579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1122590197832463807842105 841942648374347855881579)
  ·
    refine ⟨1262913972561521783822369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 841942648374347855881579 1262913972561521783822369)
    ·
      refine ⟨947185479421141337866777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1262913972561521783822369 947185479421141337866777)
      ·
        refine ⟨710389109565856003400083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 947185479421141337866777 710389109565856003400083)
        ·
          refine ⟨1065583664348784005100125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 710389109565856003400083 1065583664348784005100125)
          ·
            refine ⟨399593874130794001912547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1065583664348784005100125 399593874130794001912547)
            ·
              refine ⟨599390811196191002868821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 399593874130794001912547 599390811196191002868821)
              ·
                refine ⟨7024111068705363314869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 599390811196191002868821 7024111068705363314869)
                ·
                  rfl

theorem cell20_46168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 8].length) (baseStart_46168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46168 prefixEnd_46168 := by exact prefixLift 46168
  have htrace : WordTrace (prefixWord ++ tailWord_46168) baseStart_46168 baseEnd_46168 := by
    simpa [prefixWord, tailWord_46168, baseEnd_46168] using wordTrace_append hprefix tailTrace_46168
  have hstable : (prefixWord ++ tailWord_46168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46168).length < 2 ^ (prefixWord ++ tailWord_46168).sum := by decide
  have hdescent : baseEnd_46168 < baseStart_46168 := by decide
  rcases family_descends (prefixWord ++ tailWord_46168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46199 : List Nat := [1, 1, 3, 1, 1, 4, 2, 3, 4]
def baseStart_46199 : Nat := 118140960795 + 46199 * 2 ^ 59
def prefixEnd_46199 : Nat := 4983230072969 + 3 ^ 40 * 46199 * 2
def baseEnd_46199 : Nat := 21086482450817759911147

theorem tailTrace_46199 : CollatzResearch.WordTrace tailWord_46199 prefixEnd_46199 21086482450817759911147 := by
  unfold tailWord_46199
  simp only [CollatzResearch.WordTrace]
  refine ⟨1685015959636388006141651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1123343973090925337427767 1685015959636388006141651)
  ·
    refine ⟨2527523939454582009212477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1685015959636388006141651 2527523939454582009212477)
    ·
      refine ⟨947821477295468253454679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2527523939454582009212477 947821477295468253454679)
      ·
        refine ⟨1421732215943202380182019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 947821477295468253454679 1421732215943202380182019)
        ·
          refine ⟨2132598323914803570273029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1421732215943202380182019 2132598323914803570273029)
          ·
            refine ⟨399862185734025669426193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2132598323914803570273029 399862185734025669426193)
            ·
              refine ⟨299896639300519252069645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 399862185734025669426193 299896639300519252069645)
              ·
                refine ⟨112461239737694719526117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 299896639300519252069645 112461239737694719526117)
                ·
                  refine ⟨21086482450817759911147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112461239737694719526117 21086482450817759911147)
                  ·
                    rfl

theorem cell20_46199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 4].length) (baseStart_46199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46199 prefixEnd_46199 := by exact prefixLift 46199
  have htrace : WordTrace (prefixWord ++ tailWord_46199) baseStart_46199 baseEnd_46199 := by
    simpa [prefixWord, tailWord_46199, baseEnd_46199] using wordTrace_append hprefix tailTrace_46199
  have hstable : (prefixWord ++ tailWord_46199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46199).length < 2 ^ (prefixWord ++ tailWord_46199).sum := by decide
  have hdescent : baseEnd_46199 < baseStart_46199 := by decide
  rcases family_descends (prefixWord ++ tailWord_46199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46209 : List Nat := [1, 2, 4, 2, 2, 1, 2, 3, 3]
def baseStart_46209 : Nat := 118140960795 + 46209 * 2 ^ 59
def prefixEnd_46209 : Nat := 4983230072969 + 3 ^ 40 * 46209 * 2
def baseEnd_46209 : Nat := 21091046723302169577773

theorem tailTrace_46209 : CollatzResearch.WordTrace tailWord_46209 prefixEnd_46209 21091046723302169577773 := by
  unfold tailWord_46209
  simp only [CollatzResearch.WordTrace]
  refine ⟨1685380689600159714005681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1123587126400106476003787 1685380689600159714005681)
  ·
    refine ⟨1264035517200119785504261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1685380689600159714005681 1264035517200119785504261)
    ·
      refine ⟨237006659475022459782049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1264035517200119785504261 237006659475022459782049)
      ·
        refine ⟨177754994606266844836537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237006659475022459782049 177754994606266844836537)
        ·
          refine ⟨133316245954700133627403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177754994606266844836537 133316245954700133627403)
          ·
            refine ⟨199974368932050200441105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133316245954700133627403 199974368932050200441105)
            ·
              refine ⟨149980776699037650330829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199974368932050200441105 149980776699037650330829)
              ·
                refine ⟨56242791262139118874061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149980776699037650330829 56242791262139118874061)
                ·
                  refine ⟨21091046723302169577773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56242791262139118874061 21091046723302169577773)
                  ·
                    rfl

theorem cell20_46209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 3].length) (baseStart_46209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46209 prefixEnd_46209 := by exact prefixLift 46209
  have htrace : WordTrace (prefixWord ++ tailWord_46209) baseStart_46209 baseEnd_46209 := by
    simpa [prefixWord, tailWord_46209, baseEnd_46209] using wordTrace_append hprefix tailTrace_46209
  have hstable : (prefixWord ++ tailWord_46209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46209).length < 2 ^ (prefixWord ++ tailWord_46209).sum := by decide
  have hdescent : baseEnd_46209 < baseStart_46209 := by decide
  rcases family_descends (prefixWord ++ tailWord_46209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46237 : List Nat := [1, 4, 2, 1, 1, 2, 1, 2, 6]
def baseStart_46237 : Nat := 118140960795 + 46237 * 2 ^ 59
def prefixEnd_46237 : Nat := 4983230072969 + 3 ^ 40 * 46237 * 2
def baseEnd_46237 : Nat := 21103826686258516644325

theorem tailTrace_46237 : CollatzResearch.WordTrace tailWord_46237 prefixEnd_46237 21103826686258516644325 := by
  unfold tailWord_46237
  simp only [CollatzResearch.WordTrace]
  refine ⟨1686401933498720496024965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1124267955665813664016643 1686401933498720496024965)
  ·
    refine ⟨316200362531010093004681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1686401933498720496024965 316200362531010093004681)
    ·
      refine ⟨237150271898257569753511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316200362531010093004681 237150271898257569753511)
      ·
        refine ⟨355725407847386354630267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237150271898257569753511 355725407847386354630267)
        ·
          refine ⟨533588111771079531945401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355725407847386354630267 533588111771079531945401)
          ·
            refine ⟨400191083828309648959051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 533588111771079531945401 400191083828309648959051)
            ·
              refine ⟨600286625742464473438577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 400191083828309648959051 600286625742464473438577)
              ·
                refine ⟨450214969306848355078933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 600286625742464473438577 450214969306848355078933)
                ·
                  refine ⟨21103826686258516644325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 450214969306848355078933 21103826686258516644325)
                  ·
                    rfl

theorem cell20_46237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_46237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46237 prefixEnd_46237 := by exact prefixLift 46237
  have htrace : WordTrace (prefixWord ++ tailWord_46237) baseStart_46237 baseEnd_46237 := by
    simpa [prefixWord, tailWord_46237, baseEnd_46237] using wordTrace_append hprefix tailTrace_46237
  have hstable : (prefixWord ++ tailWord_46237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46237).length < 2 ^ (prefixWord ++ tailWord_46237).sum := by decide
  have hdescent : baseEnd_46237 < baseStart_46237 := by decide
  rcases family_descends (prefixWord ++ tailWord_46237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46247 : List Nat := [1, 1, 6, 2, 1, 2, 1, 1, 5]
def baseStart_46247 : Nat := 118140960795 + 46247 * 2 ^ 59
def prefixEnd_46247 : Nat := 4983230072969 + 3 ^ 40 * 46247 * 2
def baseEnd_46247 : Nat := 21108390958742926310951

theorem tailTrace_46247 : CollatzResearch.WordTrace tailWord_46247 prefixEnd_46247 21108390958742926310951 := by
  unfold tailWord_46247
  simp only [CollatzResearch.WordTrace]
  refine ⟨1686766663462492203888995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1124511108974994802592663 1686766663462492203888995)
  ·
    refine ⟨2530149995193738305833493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1686766663462492203888995 2530149995193738305833493)
    ·
      refine ⟨118600781024706483085945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2530149995193738305833493 118600781024706483085945)
      ·
        refine ⟨88950585768529862314459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118600781024706483085945 88950585768529862314459)
        ·
          refine ⟨133425878652794793471689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88950585768529862314459 133425878652794793471689)
          ·
            refine ⟨100069408989596095103767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133425878652794793471689 100069408989596095103767)
            ·
              refine ⟨150104113484394142655651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100069408989596095103767 150104113484394142655651)
              ·
                refine ⟨225156170226591213983477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150104113484394142655651 225156170226591213983477)
                ·
                  refine ⟨21108390958742926310951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 225156170226591213983477 21108390958742926310951)
                  ·
                    rfl

theorem cell20_46247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 5].length) (baseStart_46247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46247 prefixEnd_46247 := by exact prefixLift 46247
  have htrace : WordTrace (prefixWord ++ tailWord_46247) baseStart_46247 baseEnd_46247 := by
    simpa [prefixWord, tailWord_46247, baseEnd_46247] using wordTrace_append hprefix tailTrace_46247
  have hstable : (prefixWord ++ tailWord_46247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46247).length < 2 ^ (prefixWord ++ tailWord_46247).sum := by decide
  have hdescent : baseEnd_46247 < baseStart_46247 := by decide
  rcases family_descends (prefixWord ++ tailWord_46247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46250 : List Nat := [3, 1, 5, 1, 1, 1, 2, 4, 2]
def baseStart_46250 : Nat := 118140960795 + 46250 * 2 ^ 59
def prefixEnd_46250 : Nat := 4983230072969 + 3 ^ 40 * 46250 * 2
def baseEnd_46250 : Nat := 21109760240488249210939

theorem tailTrace_46250 : CollatzResearch.WordTrace tailWord_46250 prefixEnd_46250 21109760240488249210939 := by
  unfold tailWord_46250
  simp only [CollatzResearch.WordTrace]
  refine ⟨421719020612905929062051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1124584054967749144165469 421719020612905929062051)
  ·
    refine ⟨632578530919358893593077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 421719020612905929062051 632578530919358893593077)
    ·
      refine ⟨59304237273689896274351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 632578530919358893593077 59304237273689896274351)
      ·
        refine ⟨88956355910534844411527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59304237273689896274351 88956355910534844411527)
        ·
          refine ⟨133434533865802266617291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88956355910534844411527 133434533865802266617291)
          ·
            refine ⟨200151800798703399925937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133434533865802266617291 200151800798703399925937)
            ·
              refine ⟨150113850599027549944453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200151800798703399925937 150113850599027549944453)
              ·
                refine ⟨28146346987317665614585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150113850599027549944453 28146346987317665614585)
                ·
                  refine ⟨21109760240488249210939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28146346987317665614585 21109760240488249210939)
                  ·
                    rfl

theorem cell20_46250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 4, 2].length) (baseStart_46250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46250 prefixEnd_46250 := by exact prefixLift 46250
  have htrace : WordTrace (prefixWord ++ tailWord_46250) baseStart_46250 baseEnd_46250 := by
    simpa [prefixWord, tailWord_46250, baseEnd_46250] using wordTrace_append hprefix tailTrace_46250
  have hstable : (prefixWord ++ tailWord_46250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46250).length < 2 ^ (prefixWord ++ tailWord_46250).sum := by decide
  have hdescent : baseEnd_46250 < baseStart_46250 := by decide
  rcases family_descends (prefixWord ++ tailWord_46250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46309 : List Nat := [1, 3, 1, 4, 3, 2, 1, 1, 4]
def baseStart_46309 : Nat := 118140960795 + 46309 * 2 ^ 59
def prefixEnd_46309 : Nat := 4983230072969 + 3 ^ 40 * 46309 * 2
def baseEnd_46309 : Nat := 21136689448146266244031

theorem tailTrace_46309 : CollatzResearch.WordTrace tailWord_46309 prefixEnd_46309 21136689448146266244031 := by
  unfold tailWord_46309
  simp only [CollatzResearch.WordTrace]
  refine ⟨1689027989237876792645981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1126018659491917861763987 1689027989237876792645981)
  ·
    refine ⟨633385495964203797242243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1689027989237876792645981 633385495964203797242243)
    ·
      refine ⟨950078243946305695863365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 633385495964203797242243 950078243946305695863365)
      ·
        refine ⟨178139670739932317974381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 950078243946305695863365 178139670739932317974381)
        ·
          refine ⟨66802376527474619240393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178139670739932317974381 66802376527474619240393)
          ·
            refine ⟨50101782395605964430295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66802376527474619240393 50101782395605964430295)
            ·
              refine ⟨75152673593408946645443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50101782395605964430295 75152673593408946645443)
              ·
                refine ⟨112729010390113419968165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75152673593408946645443 112729010390113419968165)
                ·
                  refine ⟨21136689448146266244031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112729010390113419968165 21136689448146266244031)
                  ·
                    rfl

theorem cell20_46309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 4].length) (baseStart_46309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46309 prefixEnd_46309 := by exact prefixLift 46309
  have htrace : WordTrace (prefixWord ++ tailWord_46309) baseStart_46309 baseEnd_46309 := by
    simpa [prefixWord, tailWord_46309, baseEnd_46309] using wordTrace_append hprefix tailTrace_46309
  have hstable : (prefixWord ++ tailWord_46309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46309).length < 2 ^ (prefixWord ++ tailWord_46309).sum := by decide
  have hdescent : baseEnd_46309 < baseStart_46309 := by decide
  rcases family_descends (prefixWord ++ tailWord_46309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46319 : List Nat := [1, 1, 2, 1, 8, 1, 2, 1, 3]
def baseStart_46319 : Nat := 118140960795 + 46319 * 2 ^ 59
def prefixEnd_46319 : Nat := 4983230072969 + 3 ^ 40 * 46319 * 2
def baseEnd_46319 : Nat := 21141253720630675910657

theorem tailTrace_46319 : CollatzResearch.WordTrace tailWord_46319 prefixEnd_46319 21141253720630675910657 := by
  unfold tailWord_46319
  simp only [CollatzResearch.WordTrace]
  refine ⟨1689392719201648500510011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1126261812801099000340007 1689392719201648500510011)
  ·
    refine ⟨2534089078802472750765017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1689392719201648500510011 2534089078802472750765017)
    ·
      refine ⟨1900566809101854563073763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2534089078802472750765017 1900566809101854563073763)
      ·
        refine ⟨2850850213652781844610645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1900566809101854563073763 2850850213652781844610645)
        ·
          refine ⟨33408400941243537241531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 2850850213652781844610645 33408400941243537241531)
          ·
            refine ⟨50112601411865305862297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33408400941243537241531 50112601411865305862297)
            ·
              refine ⟨37584451058898979396723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50112601411865305862297 37584451058898979396723)
              ·
                refine ⟨56376676588348469095085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37584451058898979396723 56376676588348469095085)
                ·
                  refine ⟨21141253720630675910657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56376676588348469095085 21141253720630675910657)
                  ·
                    rfl

theorem cell20_46319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 3].length) (baseStart_46319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46319 prefixEnd_46319 := by exact prefixLift 46319
  have htrace : WordTrace (prefixWord ++ tailWord_46319) baseStart_46319 baseEnd_46319 := by
    simpa [prefixWord, tailWord_46319, baseEnd_46319] using wordTrace_append hprefix tailTrace_46319
  have hstable : (prefixWord ++ tailWord_46319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46319).length < 2 ^ (prefixWord ++ tailWord_46319).sum := by decide
  have hdescent : baseEnd_46319 < baseStart_46319 := by decide
  rcases family_descends (prefixWord ++ tailWord_46319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46323 : List Nat := [1, 1, 1, 2, 2, 5, 4, 1, 3]
def baseStart_46323 : Nat := 118140960795 + 46323 * 2 ^ 59
def prefixEnd_46323 : Nat := 4983230072969 + 3 ^ 40 * 46323 * 2
def baseEnd_46323 : Nat := 21143079429624439777307

theorem tailTrace_46323 : CollatzResearch.WordTrace tailWord_46323 prefixEnd_46323 21143079429624439777307 := by
  unfold tailWord_46323
  simp only [CollatzResearch.WordTrace]
  refine ⟨1689538611187157183655623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1126359074124771455770415 1689538611187157183655623)
  ·
    refine ⟨2534307916780735775483435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1689538611187157183655623 2534307916780735775483435)
    ·
      refine ⟨3801461875171103663225153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2534307916780735775483435 3801461875171103663225153)
      ·
        refine ⟨2851096406378327747418865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3801461875171103663225153 2851096406378327747418865)
        ·
          refine ⟨2138322304783745810564149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2851096406378327747418865 2138322304783745810564149)
          ·
            refine ⟨200467716073476169740389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2138322304783745810564149 200467716073476169740389)
            ·
              refine ⟨37587696763776781826323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 200467716073476169740389 37587696763776781826323)
              ·
                refine ⟨56381545145665172739485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37587696763776781826323 56381545145665172739485)
                ·
                  refine ⟨21143079429624439777307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56381545145665172739485 21143079429624439777307)
                  ·
                    rfl

theorem cell20_46323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 3].length) (baseStart_46323 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46323 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46323 prefixEnd_46323 := by exact prefixLift 46323
  have htrace : WordTrace (prefixWord ++ tailWord_46323) baseStart_46323 baseEnd_46323 := by
    simpa [prefixWord, tailWord_46323, baseEnd_46323] using wordTrace_append hprefix tailTrace_46323
  have hstable : (prefixWord ++ tailWord_46323).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46323).length < 2 ^ (prefixWord ++ tailWord_46323).sum := by decide
  have hdescent : baseEnd_46323 < baseStart_46323 := by decide
  rcases family_descends (prefixWord ++ tailWord_46323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46354 : List Nat := [3, 2, 4, 2, 1, 8]
def baseStart_46354 : Nat := 118140960795 + 46354 * 2 ^ 59
def prefixEnd_46354 : Nat := 4983230072969 + 3 ^ 40 * 46354 * 2
def baseEnd_46354 : Nat := 783601062012078138661

theorem tailTrace_46354 : CollatzResearch.WordTrace tailWord_46354 prefixEnd_46354 783601062012078138661 := by
  unfold tailWord_46354
  simp only [CollatzResearch.WordTrace]
  refine ⟨422667318518712369508529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1127112849383232985356077 422667318518712369508529)
  ·
    refine ⟨317000488889034277131397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 422667318518712369508529 317000488889034277131397)
    ·
      refine ⟨59437591666693926962137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 317000488889034277131397 59437591666693926962137)
      ·
        refine ⟨44578193750020445221603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59437591666693926962137 44578193750020445221603)
        ·
          refine ⟨66867290625030667832405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44578193750020445221603 66867290625030667832405)
          ·
            refine ⟨783601062012078138661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 66867290625030667832405 783601062012078138661)
            ·
              rfl

theorem cell20_46354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 8].length) (baseStart_46354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46354 prefixEnd_46354 := by exact prefixLift 46354
  have htrace : WordTrace (prefixWord ++ tailWord_46354) baseStart_46354 baseEnd_46354 := by
    simpa [prefixWord, tailWord_46354, baseEnd_46354] using wordTrace_append hprefix tailTrace_46354
  have hstable : (prefixWord ++ tailWord_46354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46354).length < 2 ^ (prefixWord ++ tailWord_46354).sum := by decide
  have hdescent : baseEnd_46354 < baseStart_46354 := by decide
  rcases family_descends (prefixWord ++ tailWord_46354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46389 : List Nat := [1, 3, 3, 1, 2, 2, 1, 1, 6]
def baseStart_46389 : Nat := 118140960795 + 46389 * 2 ^ 59
def prefixEnd_46389 : Nat := 4983230072969 + 3 ^ 40 * 46389 * 2
def baseEnd_46389 : Nat := 21173203628021543577037

theorem tailTrace_46389 : CollatzResearch.WordTrace tailWord_46389 prefixEnd_46389 21173203628021543577037 := by
  unfold tailWord_46389
  simp only [CollatzResearch.WordTrace]
  refine ⟨1691945828948050455558221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1127963885965366970372147 1691945828948050455558221)
  ·
    refine ⟨634479685855518920834333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1691945828948050455558221 634479685855518920834333)
    ·
      refine ⟨237929882195819595312875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 634479685855518920834333 237929882195819595312875)
      ·
        refine ⟨356894823293729392969313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237929882195819595312875 356894823293729392969313)
        ·
          refine ⟨267671117470297044726985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356894823293729392969313 267671117470297044726985)
          ·
            refine ⟨200753338102722783545239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267671117470297044726985 200753338102722783545239)
            ·
              refine ⟨301130007154084175317859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200753338102722783545239 301130007154084175317859)
              ·
                refine ⟨451695010731126262976789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301130007154084175317859 451695010731126262976789)
                ·
                  refine ⟨21173203628021543577037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 451695010731126262976789 21173203628021543577037)
                  ·
                    rfl

theorem cell20_46389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_46389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46389 prefixEnd_46389 := by exact prefixLift 46389
  have htrace : WordTrace (prefixWord ++ tailWord_46389) baseStart_46389 baseEnd_46389 := by
    simpa [prefixWord, tailWord_46389, baseEnd_46389] using wordTrace_append hprefix tailTrace_46389
  have hstable : (prefixWord ++ tailWord_46389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46389).length < 2 ^ (prefixWord ++ tailWord_46389).sum := by decide
  have hdescent : baseEnd_46389 < baseStart_46389 := by decide
  rcases family_descends (prefixWord ++ tailWord_46389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46403 : List Nat := [1, 1, 1, 3, 1, 3, 1, 4, 5]
def baseStart_46403 : Nat := 118140960795 + 46403 * 2 ^ 59
def prefixEnd_46403 : Nat := 4983230072969 + 3 ^ 40 * 46403 * 2
def baseEnd_46403 : Nat := 21179593609499717110313

theorem tailTrace_46403 : CollatzResearch.WordTrace tailWord_46403 prefixEnd_46403 21179593609499717110313 := by
  unfold tailWord_46403
  simp only [CollatzResearch.WordTrace]
  refine ⟨1692456450897330846567863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1128304300598220564378575 1692456450897330846567863)
  ·
    refine ⟨2538684676345996269851795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1692456450897330846567863 2538684676345996269851795)
    ·
      refine ⟨3808027014518994404777693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2538684676345996269851795 3808027014518994404777693)
      ·
        refine ⟨1428010130444622901791635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3808027014518994404777693 1428010130444622901791635)
        ·
          refine ⟨2142015195666934352687453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1428010130444622901791635 2142015195666934352687453)
          ·
            refine ⟨803255698375100382257795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2142015195666934352687453 803255698375100382257795)
            ·
              refine ⟨1204883547562650573386693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 803255698375100382257795 1204883547562650573386693)
              ·
                refine ⟨225915665167996982510005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1204883547562650573386693 225915665167996982510005)
                ·
                  refine ⟨21179593609499717110313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 225915665167996982510005 21179593609499717110313)
                  ·
                    rfl

theorem cell20_46403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 5].length) (baseStart_46403 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46403 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46403 prefixEnd_46403 := by exact prefixLift 46403
  have htrace : WordTrace (prefixWord ++ tailWord_46403) baseStart_46403 baseEnd_46403 := by
    simpa [prefixWord, tailWord_46403, baseEnd_46403] using wordTrace_append hprefix tailTrace_46403
  have hstable : (prefixWord ++ tailWord_46403).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46403).length < 2 ^ (prefixWord ++ tailWord_46403).sum := by decide
  have hdescent : baseEnd_46403 < baseStart_46403 := by decide
  rcases family_descends (prefixWord ++ tailWord_46403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46420 : List Nat := [2, 4, 1, 1, 2, 1, 3, 1, 5]
def baseStart_46420 : Nat := 118140960795 + 46420 * 2 ^ 59
def prefixEnd_46420 : Nat := 4983230072969 + 3 ^ 40 * 46420 * 2
def baseEnd_46420 : Nat := 21187352872723213543577

theorem tailTrace_46420 : CollatzResearch.WordTrace tailWord_46420 prefixEnd_46420 21187352872723213543577 := by
  unfold tailWord_46420
  simp only [CollatzResearch.WordTrace]
  refine ⟨846538245917871374968357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1128717661223828499957809 846538245917871374968357)
  ·
    refine ⟨158725921109600882806567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 846538245917871374968357 158725921109600882806567)
    ·
      refine ⟨238088881664401324209851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158725921109600882806567 238088881664401324209851)
      ·
        refine ⟨357133322496601986314777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238088881664401324209851 357133322496601986314777)
        ·
          refine ⟨267849991872451489736083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357133322496601986314777 267849991872451489736083)
          ·
            refine ⟨401774987808677234604125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267849991872451489736083 401774987808677234604125)
            ·
              refine ⟨150665620428253962976547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 401774987808677234604125 150665620428253962976547)
              ·
                refine ⟨225998430642380944464821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150665620428253962976547 225998430642380944464821)
                ·
                  refine ⟨21187352872723213543577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 225998430642380944464821 21187352872723213543577)
                  ·
                    rfl

theorem cell20_46420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_46420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46420 prefixEnd_46420 := by exact prefixLift 46420
  have htrace : WordTrace (prefixWord ++ tailWord_46420) baseStart_46420 baseEnd_46420 := by
    simpa [prefixWord, tailWord_46420, baseEnd_46420] using wordTrace_append hprefix tailTrace_46420
  have hstable : (prefixWord ++ tailWord_46420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46420).length < 2 ^ (prefixWord ++ tailWord_46420).sum := by decide
  have hdescent : baseEnd_46420 < baseStart_46420 := by decide
  rcases family_descends (prefixWord ++ tailWord_46420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46437 : List Nat := [1, 3, 1, 3, 1, 2, 5, 1, 3]
def baseStart_46437 : Nat := 118140960795 + 46437 * 2 ^ 59
def prefixEnd_46437 : Nat := 4983230072969 + 3 ^ 40 * 46437 * 2
def baseEnd_46437 : Nat := 21195112135946709976841

theorem tailTrace_46437 : CollatzResearch.WordTrace tailWord_46437 prefixEnd_46437 21195112135946709976841 := by
  unfold tailWord_46437
  simp only [CollatzResearch.WordTrace]
  refine ⟨1693696532774154653305565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1129131021849436435537043 1693696532774154653305565)
  ·
    refine ⟨635136199790307994989587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1693696532774154653305565 635136199790307994989587)
    ·
      refine ⟨952704299685461992484381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 635136199790307994989587 952704299685461992484381)
      ·
        refine ⟨357264112382048247181643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 952704299685461992484381 357264112382048247181643)
        ·
          refine ⟨535896168573072370772465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357264112382048247181643 535896168573072370772465)
          ·
            refine ⟨401922126429804278079349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 535896168573072370772465 401922126429804278079349)
            ·
              refine ⟨37680199352794151069939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 401922126429804278079349 37680199352794151069939)
              ·
                refine ⟨56520299029191226604909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37680199352794151069939 56520299029191226604909)
                ·
                  refine ⟨21195112135946709976841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56520299029191226604909 21195112135946709976841)
                  ·
                    rfl

theorem cell20_46437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 3].length) (baseStart_46437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46437 prefixEnd_46437 := by exact prefixLift 46437
  have htrace : WordTrace (prefixWord ++ tailWord_46437) baseStart_46437 baseEnd_46437 := by
    simpa [prefixWord, tailWord_46437, baseEnd_46437] using wordTrace_append hprefix tailTrace_46437
  have hstable : (prefixWord ++ tailWord_46437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46437).length < 2 ^ (prefixWord ++ tailWord_46437).sum := by decide
  have hdescent : baseEnd_46437 < baseStart_46437 := by decide
  rcases family_descends (prefixWord ++ tailWord_46437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46472 : List Nat := [2, 1, 3, 3, 1, 2, 8]
def baseStart_46472 : Nat := 118140960795 + 46472 * 2 ^ 59
def prefixEnd_46472 : Nat := 4983230072969 + 3 ^ 40 * 46472 * 2
def baseEnd_46472 : Nat := 2356787454404682645559

theorem tailTrace_46472 : CollatzResearch.WordTrace tailWord_46472 prefixEnd_46472 2356787454404682645559 := by
  unfold tailWord_46472
  simp only [CollatzResearch.WordTrace]
  refine ⟨847486543823677815414835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1129982058431570420553113 847486543823677815414835)
  ·
    refine ⟨1271229815735516723122253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 847486543823677815414835 1271229815735516723122253)
    ·
      refine ⟨476711180900818771170845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1271229815735516723122253 476711180900818771170845)
      ·
        refine ⟨178766692837807039189067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 476711180900818771170845 178766692837807039189067)
        ·
          refine ⟨268150039256710558783601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178766692837807039189067 268150039256710558783601)
          ·
            refine ⟨201112529442532919087701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268150039256710558783601 201112529442532919087701)
            ·
              refine ⟨2356787454404682645559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 201112529442532919087701 2356787454404682645559)
              ·
                rfl

theorem cell20_46472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 8].length) (baseStart_46472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46472 prefixEnd_46472 := by exact prefixLift 46472
  have htrace : WordTrace (prefixWord ++ tailWord_46472) baseStart_46472 baseEnd_46472 := by
    simpa [prefixWord, tailWord_46472, baseEnd_46472] using wordTrace_append hprefix tailTrace_46472
  have hstable : (prefixWord ++ tailWord_46472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46472).length < 2 ^ (prefixWord ++ tailWord_46472).sum := by decide
  have hdescent : baseEnd_46472 < baseStart_46472 := by decide
  rcases family_descends (prefixWord ++ tailWord_46472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46478 : List Nat := [4, 1, 1, 4, 3, 1, 1, 1, 4]
def baseStart_46478 : Nat := 118140960795 + 46478 * 2 ^ 59
def prefixEnd_46478 : Nat := 4983230072969 + 3 ^ 40 * 46478 * 2
def baseEnd_46478 : Nat := 21213825653132789610007

theorem tailTrace_46478 : CollatzResearch.WordTrace tailWord_46478 prefixEnd_46478 21213825653132789610007 := by
  unfold tailWord_46478
  simp only [CollatzResearch.WordTrace]
  refine ⟨211898990703202331943511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1130127950417079103698725 211898990703202331943511)
  ·
    refine ⟨317848486054803497915267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211898990703202331943511 317848486054803497915267)
    ·
      refine ⟨476772729082205246872901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317848486054803497915267 476772729082205246872901)
      ·
        refine ⟨89394886702913483788669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 476772729082205246872901 89394886702913483788669)
        ·
          refine ⟨33523082513592556420751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89394886702913483788669 33523082513592556420751)
          ·
            refine ⟨50284623770388834631127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33523082513592556420751 50284623770388834631127)
            ·
              refine ⟨75426935655583251946691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50284623770388834631127 75426935655583251946691)
              ·
                refine ⟨113140403483374877920037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75426935655583251946691 113140403483374877920037)
                ·
                  refine ⟨21213825653132789610007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113140403483374877920037 21213825653132789610007)
                  ·
                    rfl

theorem cell20_46478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_46478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46478 prefixEnd_46478 := by exact prefixLift 46478
  have htrace : WordTrace (prefixWord ++ tailWord_46478) baseStart_46478 baseEnd_46478 := by
    simpa [prefixWord, tailWord_46478, baseEnd_46478] using wordTrace_append hprefix tailTrace_46478
  have hstable : (prefixWord ++ tailWord_46478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46478).length < 2 ^ (prefixWord ++ tailWord_46478).sum := by decide
  have hdescent : baseEnd_46478 < baseStart_46478 := by decide
  rcases family_descends (prefixWord ++ tailWord_46478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46492 : List Nat := [2, 2, 3, 4, 1, 1, 1, 3, 3]
def baseStart_46492 : Nat := 118140960795 + 46492 * 2 ^ 59
def prefixEnd_46492 : Nat := 4983230072969 + 3 ^ 40 * 46492 * 2
def baseEnd_46492 : Nat := 21220215634610963143283

theorem tailTrace_46492 : CollatzResearch.WordTrace tailWord_46492 prefixEnd_46492 21220215634610963143283 := by
  unfold tailWord_46492
  simp only [CollatzResearch.WordTrace]
  refine ⟨847851273787449523278865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1130468365049932697705153 847851273787449523278865)
  ·
    refine ⟨635888455340587142459149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 847851273787449523278865 635888455340587142459149)
    ·
      refine ⟨238458170752720178422181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 635888455340587142459149 238458170752720178422181)
      ·
        refine ⟨44710907016135033454159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 238458170752720178422181 44710907016135033454159)
        ·
          refine ⟨67066360524202550181239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44710907016135033454159 67066360524202550181239)
          ·
            refine ⟨100599540786303825271859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67066360524202550181239 100599540786303825271859)
            ·
              refine ⟨150899311179455737907789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100599540786303825271859 150899311179455737907789)
              ·
                refine ⟨56587241692295901715421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150899311179455737907789 56587241692295901715421)
                ·
                  refine ⟨21220215634610963143283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56587241692295901715421 21220215634610963143283)
                  ·
                    rfl

theorem cell20_46492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 3].length) (baseStart_46492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46492 prefixEnd_46492 := by exact prefixLift 46492
  have htrace : WordTrace (prefixWord ++ tailWord_46492) baseStart_46492 baseEnd_46492 := by
    simpa [prefixWord, tailWord_46492, baseEnd_46492] using wordTrace_append hprefix tailTrace_46492
  have hstable : (prefixWord ++ tailWord_46492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46492).length < 2 ^ (prefixWord ++ tailWord_46492).sum := by decide
  have hdescent : baseEnd_46492 < baseStart_46492 := by decide
  rcases family_descends (prefixWord ++ tailWord_46492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46496 : List Nat := [2, 1, 1, 4, 1, 2, 3, 3, 3]
def baseStart_46496 : Nat := 118140960795 + 46496 * 2 ^ 59
def prefixEnd_46496 : Nat := 4983230072969 + 3 ^ 40 * 46496 * 2
def baseEnd_46496 : Nat := 21222041343604727009933

theorem tailTrace_46496 : CollatzResearch.WordTrace tailWord_46496 prefixEnd_46496 21222041343604727009933 := by
  unfold tailWord_46496
  simp only [CollatzResearch.WordTrace]
  refine ⟨847924219780203864851671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1130565626373605153135561 847924219780203864851671)
  ·
    refine ⟨1271886329670305797277507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 847924219780203864851671 1271886329670305797277507)
    ·
      refine ⟨1907829494505458695916261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1271886329670305797277507 1907829494505458695916261)
      ·
        refine ⟨357718030219773505484299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1907829494505458695916261 357718030219773505484299)
        ·
          refine ⟨536577045329660258226449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357718030219773505484299 536577045329660258226449)
          ·
            refine ⟨402432783997245193669837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 536577045329660258226449 402432783997245193669837)
            ·
              refine ⟨150912293998966947626189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 402432783997245193669837 150912293998966947626189)
              ·
                refine ⟨56592110249612605359821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150912293998966947626189 56592110249612605359821)
                ·
                  refine ⟨21222041343604727009933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56592110249612605359821 21222041343604727009933)
                  ·
                    rfl

theorem cell20_46496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 3].length) (baseStart_46496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46496 prefixEnd_46496 := by exact prefixLift 46496
  have htrace : WordTrace (prefixWord ++ tailWord_46496) baseStart_46496 baseEnd_46496 := by
    simpa [prefixWord, tailWord_46496, baseEnd_46496] using wordTrace_append hprefix tailTrace_46496
  have hstable : (prefixWord ++ tailWord_46496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46496).length < 2 ^ (prefixWord ++ tailWord_46496).sum := by decide
  have hdescent : baseEnd_46496 < baseStart_46496 := by decide
  rcases family_descends (prefixWord ++ tailWord_46496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46503 : List Nat := [1, 1, 6, 1, 1, 1, 2, 1, 6]
def baseStart_46503 : Nat := 118140960795 + 46503 * 2 ^ 59
def prefixEnd_46503 : Nat := 4983230072969 + 3 ^ 40 * 46503 * 2
def baseEnd_46503 : Nat := 21225236334343813776571

theorem tailTrace_46503 : CollatzResearch.WordTrace tailWord_46503 prefixEnd_46503 21225236334343813776571 := by
  unfold tailWord_46503
  simp only [CollatzResearch.WordTrace]
  refine ⟨1696103750535047925208163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1130735833690031950138775 1696103750535047925208163)
  ·
    refine ⟨2544155625802571887812245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1696103750535047925208163 2544155625802571887812245)
    ·
      refine ⟨119257294959495557241199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2544155625802571887812245 119257294959495557241199)
      ·
        refine ⟨178885942439243335861799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119257294959495557241199 178885942439243335861799)
        ·
          refine ⟨268328913658865003792699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178885942439243335861799 268328913658865003792699)
          ·
            refine ⟨402493370488297505689049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268328913658865003792699 402493370488297505689049)
            ·
              refine ⟨301870027866223129266787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 402493370488297505689049 301870027866223129266787)
              ·
                refine ⟨452805041799334693900181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301870027866223129266787 452805041799334693900181)
                ·
                  refine ⟨21225236334343813776571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 452805041799334693900181 21225236334343813776571)
                  ·
                    rfl

theorem cell20_46503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 6].length) (baseStart_46503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46503 prefixEnd_46503 := by exact prefixLift 46503
  have htrace : WordTrace (prefixWord ++ tailWord_46503) baseStart_46503 baseEnd_46503 := by
    simpa [prefixWord, tailWord_46503, baseEnd_46503] using wordTrace_append hprefix tailTrace_46503
  have hstable : (prefixWord ++ tailWord_46503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46503).length < 2 ^ (prefixWord ++ tailWord_46503).sum := by decide
  have hdescent : baseEnd_46503 < baseStart_46503 := by decide
  rcases family_descends (prefixWord ++ tailWord_46503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46589 : List Nat := [1, 4, 1, 1, 1, 6, 1, 2, 3]
def baseStart_46589 : Nat := 118140960795 + 46589 * 2 ^ 59
def prefixEnd_46589 : Nat := 4983230072969 + 3 ^ 40 * 46589 * 2
def baseEnd_46589 : Nat := 21264489077709736909553

theorem tailTrace_46589 : CollatzResearch.WordTrace tailWord_46589 prefixEnd_46589 21264489077709736909553 := by
  unfold tailWord_46589
  simp only [CollatzResearch.WordTrace]
  refine ⟨1699240428223484612838821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1132826952148989741892547 1699240428223484612838821)
  ·
    refine ⟨318607580291903364907279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1699240428223484612838821 318607580291903364907279)
    ·
      refine ⟨477911370437855047360919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318607580291903364907279 477911370437855047360919)
      ·
        refine ⟨716867055656782571041379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477911370437855047360919 716867055656782571041379)
        ·
          refine ⟨1075300583485173856562069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 716867055656782571041379 1075300583485173856562069)
          ·
            refine ⟨50404714850867524526347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1075300583485173856562069 50404714850867524526347)
            ·
              refine ⟨75607072276301286789521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50404714850867524526347 75607072276301286789521)
              ·
                refine ⟨56705304207225965092141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75607072276301286789521 56705304207225965092141)
                ·
                  refine ⟨21264489077709736909553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56705304207225965092141 21264489077709736909553)
                  ·
                    rfl

theorem cell20_46589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_46589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46589 prefixEnd_46589 := by exact prefixLift 46589
  have htrace : WordTrace (prefixWord ++ tailWord_46589) baseStart_46589 baseEnd_46589 := by
    simpa [prefixWord, tailWord_46589, baseEnd_46589] using wordTrace_append hprefix tailTrace_46589
  have hstable : (prefixWord ++ tailWord_46589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46589).length < 2 ^ (prefixWord ++ tailWord_46589).sum := by decide
  have hdescent : baseEnd_46589 < baseStart_46589 := by decide
  rcases family_descends (prefixWord ++ tailWord_46589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46606 : List Nat := [4, 1, 1, 2, 4, 1, 3, 1, 3]
def baseStart_46606 : Nat := 118140960795 + 46606 * 2 ^ 59
def prefixEnd_46606 : Nat := 4983230072969 + 3 ^ 40 * 46606 * 2
def baseEnd_46606 : Nat := 21272248340933233342817

theorem tailTrace_46606 : CollatzResearch.WordTrace tailWord_46606 prefixEnd_46606 21272248340933233342817 := by
  unfold tailWord_46606
  simp only [CollatzResearch.WordTrace]
  refine ⟨212482558645237064525959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1133240312774597677471781 212482558645237064525959)
  ·
    refine ⟨318723837967855596788939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212482558645237064525959 318723837967855596788939)
    ·
      refine ⟨478085756951783395183409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318723837967855596788939 478085756951783395183409)
      ·
        refine ⟨358564317713837546387557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 478085756951783395183409 358564317713837546387557)
        ·
          refine ⟨67230809571344539947667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 358564317713837546387557 67230809571344539947667)
          ·
            refine ⟨100846214357016809921501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67230809571344539947667 100846214357016809921501)
            ·
              refine ⟨37817330383881303720563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100846214357016809921501 37817330383881303720563)
              ·
                refine ⟨56725995575821955580845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37817330383881303720563 56725995575821955580845)
                ·
                  refine ⟨21272248340933233342817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56725995575821955580845 21272248340933233342817)
                  ·
                    rfl

theorem cell20_46606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_46606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46606 prefixEnd_46606 := by exact prefixLift 46606
  have htrace : WordTrace (prefixWord ++ tailWord_46606) baseStart_46606 baseEnd_46606 := by
    simpa [prefixWord, tailWord_46606, baseEnd_46606] using wordTrace_append hprefix tailTrace_46606
  have hstable : (prefixWord ++ tailWord_46606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46606).length < 2 ^ (prefixWord ++ tailWord_46606).sum := by decide
  have hdescent : baseEnd_46606 < baseStart_46606 := by decide
  rcases family_descends (prefixWord ++ tailWord_46606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46655 : List Nat := [1, 1, 2, 2, 3, 3, 3, 1, 4]
def baseStart_46655 : Nat := 118140960795 + 46655 * 2 ^ 59
def prefixEnd_46655 : Nat := 4983230072969 + 3 ^ 40 * 46655 * 2
def baseEnd_46655 : Nat := 21294613276106840709283

theorem tailTrace_46655 : CollatzResearch.WordTrace tailWord_46655 prefixEnd_46655 21294613276106840709283 := by
  unfold tailWord_46655
  simp only [CollatzResearch.WordTrace]
  refine ⟨1701647645984377884741419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1134431763989585256494279 1701647645984377884741419)
  ·
    refine ⟨2552471468976566827112129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1701647645984377884741419 2552471468976566827112129)
    ·
      refine ⟨1914353601732425120334097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2552471468976566827112129 1914353601732425120334097)
      ·
        refine ⟨1435765201299318840250573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1914353601732425120334097 1435765201299318840250573)
        ·
          refine ⟨538411950487244565093965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1435765201299318840250573 538411950487244565093965)
          ·
            refine ⟨201904481432716711910237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 538411950487244565093965 201904481432716711910237)
            ·
              refine ⟨75714180537268766966339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 201904481432716711910237 75714180537268766966339)
              ·
                refine ⟨113571270805903150449509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75714180537268766966339 113571270805903150449509)
                ·
                  refine ⟨21294613276106840709283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113571270805903150449509 21294613276106840709283)
                  ·
                    rfl

theorem cell20_46655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 4].length) (baseStart_46655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46655 prefixEnd_46655 := by exact prefixLift 46655
  have htrace : WordTrace (prefixWord ++ tailWord_46655) baseStart_46655 baseEnd_46655 := by
    simpa [prefixWord, tailWord_46655, baseEnd_46655] using wordTrace_append hprefix tailTrace_46655
  have hstable : (prefixWord ++ tailWord_46655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46655).length < 2 ^ (prefixWord ++ tailWord_46655).sum := by decide
  have hdescent : baseEnd_46655 < baseStart_46655 := by decide
  rcases family_descends (prefixWord ++ tailWord_46655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46706 : List Nat := [3, 2, 1, 2, 3, 3, 2, 2, 2]
def baseStart_46706 : Nat := 118140960795 + 46706 * 2 ^ 59
def prefixEnd_46706 : Nat := 4983230072969 + 3 ^ 40 * 46706 * 2
def baseEnd_46706 : Nat := 21317891065777330009075

theorem tailTrace_46706 : CollatzResearch.WordTrace tailWord_46706 prefixEnd_46706 21317891065777330009075 := by
  unfold tailWord_46706
  simp only [CollatzResearch.WordTrace]
  refine ⟨425876942199903398711993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1135671845866409063231981 425876942199903398711993)
  ·
    refine ⟨319407706649927549033995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 425876942199903398711993 319407706649927549033995)
    ·
      refine ⟨479111559974891323550993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319407706649927549033995 479111559974891323550993)
      ·
        refine ⟨359333669981168492663245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 479111559974891323550993 359333669981168492663245)
        ·
          refine ⟨134750126242938184748717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 359333669981168492663245 134750126242938184748717)
          ·
            refine ⟨50531297341101819280769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134750126242938184748717 50531297341101819280769)
            ·
              refine ⟨37898473005826364460577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50531297341101819280769 37898473005826364460577)
              ·
                refine ⟨28423854754369773345433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37898473005826364460577 28423854754369773345433)
                ·
                  refine ⟨21317891065777330009075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28423854754369773345433 21317891065777330009075)
                  ·
                    rfl

theorem cell20_46706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_46706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46706 prefixEnd_46706 := by exact prefixLift 46706
  have htrace : WordTrace (prefixWord ++ tailWord_46706) baseStart_46706 baseEnd_46706 := by
    simpa [prefixWord, tailWord_46706, baseEnd_46706] using wordTrace_append hprefix tailTrace_46706
  have hstable : (prefixWord ++ tailWord_46706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46706).length < 2 ^ (prefixWord ++ tailWord_46706).sum := by decide
  have hdescent : baseEnd_46706 < baseStart_46706 := by decide
  rcases family_descends (prefixWord ++ tailWord_46706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46717 : List Nat := [1, 4, 1, 1, 4, 3, 1, 5]
def baseStart_46717 : Nat := 118140960795 + 46717 * 2 ^ 59
def prefixEnd_46717 : Nat := 4983230072969 + 3 ^ 40 * 46717 * 2
def baseEnd_46717 : Nat := 7107637255170060214121

theorem tailTrace_46717 : CollatzResearch.WordTrace tailWord_46717 prefixEnd_46717 7107637255170060214121 := by
  unfold tailWord_46717
  simp only [CollatzResearch.WordTrace]
  refine ⟨1703908971759762473498405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1135939314506508315665603 1703908971759762473498405)
  ·
    refine ⟨319482932204955463780951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1703908971759762473498405 319482932204955463780951)
    ·
      refine ⟨479224398307433195671427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319482932204955463780951 479224398307433195671427)
      ·
        refine ⟨718836597461149793507141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479224398307433195671427 718836597461149793507141)
        ·
          refine ⟨134781862023965586282589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 718836597461149793507141 134781862023965586282589)
          ·
            refine ⟨50543198258987094855971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134781862023965586282589 50543198258987094855971)
            ·
              refine ⟨75814797388480642283957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50543198258987094855971 75814797388480642283957)
              ·
                refine ⟨7107637255170060214121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75814797388480642283957 7107637255170060214121)
                ·
                  rfl

theorem cell20_46717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 5].length) (baseStart_46717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46717 prefixEnd_46717 := by exact prefixLift 46717
  have htrace : WordTrace (prefixWord ++ tailWord_46717) baseStart_46717 baseEnd_46717 := by
    simpa [prefixWord, tailWord_46717, baseEnd_46717] using wordTrace_append hprefix tailTrace_46717
  have hstable : (prefixWord ++ tailWord_46717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46717).length < 2 ^ (prefixWord ++ tailWord_46717).sum := by decide
  have hdescent : baseEnd_46717 < baseStart_46717 := by decide
  rcases family_descends (prefixWord ++ tailWord_46717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46821 : List Nat := [1, 3, 1, 4, 1, 1, 1, 3, 5]
def baseStart_46821 : Nat := 118140960795 + 46821 * 2 ^ 59
def prefixEnd_46821 : Nat := 4983230072969 + 3 ^ 40 * 46821 * 2
def baseEnd_46821 : Nat := 21370380199348041175271

theorem tailTrace_46821 : CollatzResearch.WordTrace tailWord_46821 prefixEnd_46821 21370380199348041175271 := by
  unfold tailWord_46821
  simp only [CollatzResearch.WordTrace]
  refine ⟨1707702163382988235284317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1138468108921992156856211 1707702163382988235284317)
  ·
    refine ⟨640388311268620588231619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1707702163382988235284317 640388311268620588231619)
    ·
      refine ⟨960582466902930882347429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 640388311268620588231619 960582466902930882347429)
      ·
        refine ⟨180109212544299540440143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 960582466902930882347429 180109212544299540440143)
        ·
          refine ⟨270163818816449310660215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180109212544299540440143 270163818816449310660215)
          ·
            refine ⟨405245728224673965990323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270163818816449310660215 405245728224673965990323)
            ·
              refine ⟨607868592337010948985485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 405245728224673965990323 607868592337010948985485)
              ·
                refine ⟨227950722126379105869557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 607868592337010948985485 227950722126379105869557)
                ·
                  refine ⟨21370380199348041175271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 227950722126379105869557 21370380199348041175271)
                  ·
                    rfl

theorem cell20_46821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_46821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46821 prefixEnd_46821 := by exact prefixLift 46821
  have htrace : WordTrace (prefixWord ++ tailWord_46821) baseStart_46821 baseEnd_46821 := by
    simpa [prefixWord, tailWord_46821, baseEnd_46821] using wordTrace_append hprefix tailTrace_46821
  have hstable : (prefixWord ++ tailWord_46821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46821).length < 2 ^ (prefixWord ++ tailWord_46821).sum := by decide
  have hdescent : baseEnd_46821 < baseStart_46821 := by decide
  rcases family_descends (prefixWord ++ tailWord_46821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46824 : List Nat := [2, 1, 4, 1, 3, 3, 1, 1, 4]
def baseStart_46824 : Nat := 118140960795 + 46824 * 2 ^ 59
def prefixEnd_46824 : Nat := 4983230072969 + 3 ^ 40 * 46824 * 2
def baseEnd_46824 : Nat := 21371749481093364075259

theorem tailTrace_46824 : CollatzResearch.WordTrace tailWord_46824 prefixEnd_46824 21371749481093364075259 := by
  unfold tailWord_46824
  simp only [CollatzResearch.WordTrace]
  refine ⟨853905791186059873821763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1138541054914746498429017 853905791186059873821763)
  ·
    refine ⟨1280858686779089810732645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 853905791186059873821763 1280858686779089810732645)
    ·
      refine ⟨240161003771079339512371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1280858686779089810732645 240161003771079339512371)
      ·
        refine ⟨360241505656619009268557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240161003771079339512371 360241505656619009268557)
        ·
          refine ⟨135090564621232128475709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 360241505656619009268557 135090564621232128475709)
          ·
            refine ⟨50658961732962048178391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135090564621232128475709 50658961732962048178391)
            ·
              refine ⟨75988442599443072267587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50658961732962048178391 75988442599443072267587)
              ·
                refine ⟨113982663899164608401381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75988442599443072267587 113982663899164608401381)
                ·
                  refine ⟨21371749481093364075259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113982663899164608401381 21371749481093364075259)
                  ·
                    rfl

theorem cell20_46824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 4].length) (baseStart_46824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46824 prefixEnd_46824 := by exact prefixLift 46824
  have htrace : WordTrace (prefixWord ++ tailWord_46824) baseStart_46824 baseEnd_46824 := by
    simpa [prefixWord, tailWord_46824, baseEnd_46824] using wordTrace_append hprefix tailTrace_46824
  have hstable : (prefixWord ++ tailWord_46824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46824).length < 2 ^ (prefixWord ++ tailWord_46824).sum := by decide
  have hdescent : baseEnd_46824 < baseStart_46824 := by decide
  rcases family_descends (prefixWord ++ tailWord_46824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46835 : List Nat := [1, 1, 1, 2, 2, 3, 3, 7]
def baseStart_46835 : Nat := 118140960795 + 46835 * 2 ^ 59
def prefixEnd_46835 : Nat := 4983230072969 + 3 ^ 40 * 46835 * 2
def baseEnd_46835 : Nat := 7125590060275404902849

theorem tailTrace_46835 : CollatzResearch.WordTrace tailWord_46835 prefixEnd_46835 7125590060275404902849 := by
  unfold tailWord_46835
  simp only [CollatzResearch.WordTrace]
  refine ⟨1708212785332268626293959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1138808523554845750862639 1708212785332268626293959)
  ·
    refine ⟨2562319177998402939440939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1708212785332268626293959 2562319177998402939440939)
    ·
      refine ⟨3843478766997604409161409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2562319177998402939440939 3843478766997604409161409)
      ·
        refine ⟨2882609075248203306871057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3843478766997604409161409 2882609075248203306871057)
        ·
          refine ⟨2161956806436152480153293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2882609075248203306871057 2161956806436152480153293)
          ·
            refine ⟨810733802413557180057485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2161956806436152480153293 810733802413557180057485)
            ·
              refine ⟨304025175905083942521557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 810733802413557180057485 304025175905083942521557)
              ·
                refine ⟨7125590060275404902849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 304025175905083942521557 7125590060275404902849)
                ·
                  rfl

theorem cell20_46835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 7].length) (baseStart_46835 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46835 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46835 prefixEnd_46835 := by exact prefixLift 46835
  have htrace : WordTrace (prefixWord ++ tailWord_46835) baseStart_46835 baseEnd_46835 := by
    simpa [prefixWord, tailWord_46835, baseEnd_46835] using wordTrace_append hprefix tailTrace_46835
  have hstable : (prefixWord ++ tailWord_46835).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46835).length < 2 ^ (prefixWord ++ tailWord_46835).sum := by decide
  have hdescent : baseEnd_46835 < baseStart_46835 := by decide
  rcases family_descends (prefixWord ++ tailWord_46835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46852 : List Nat := [2, 3, 2, 2, 1, 2, 2, 6]
def baseStart_46852 : Nat := 118140960795 + 46852 * 2 ^ 59
def prefixEnd_46852 : Nat := 4983230072969 + 3 ^ 40 * 46852 * 2
def baseEnd_46852 : Nat := 7128176481349903713937

theorem tailTrace_46852 : CollatzResearch.WordTrace tailWord_46852 prefixEnd_46852 7128176481349903713937 := by
  unfold tailWord_46852
  simp only [CollatzResearch.WordTrace]
  refine ⟨854416413135340264831405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1139221884180453686441873 854416413135340264831405)
  ·
    refine ⟨320406154925752599311777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 854416413135340264831405 320406154925752599311777)
    ·
      refine ⟨240304616194314449483833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320406154925752599311777 240304616194314449483833)
      ·
        refine ⟨180228462145735837112875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240304616194314449483833 180228462145735837112875)
        ·
          refine ⟨270342693218603755669313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180228462145735837112875 270342693218603755669313)
          ·
            refine ⟨202757019913952816751985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270342693218603755669313 202757019913952816751985)
            ·
              refine ⟨152067764935464612563989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202757019913952816751985 152067764935464612563989)
              ·
                refine ⟨7128176481349903713937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 152067764935464612563989 7128176481349903713937)
                ·
                  rfl

theorem cell20_46852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 6].length) (baseStart_46852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46852 prefixEnd_46852 := by exact prefixLift 46852
  have htrace : WordTrace (prefixWord ++ tailWord_46852) baseStart_46852 baseEnd_46852 := by
    simpa [prefixWord, tailWord_46852, baseEnd_46852] using wordTrace_append hprefix tailTrace_46852
  have hstable : (prefixWord ++ tailWord_46852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46852).length < 2 ^ (prefixWord ++ tailWord_46852).sum := by decide
  have hdescent : baseEnd_46852 < baseStart_46852 := by decide
  rcases family_descends (prefixWord ++ tailWord_46852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46876 : List Nat := [2, 2, 3, 1, 1, 2, 4, 2, 3]
def baseStart_46876 : Nat := 118140960795 + 46876 * 2 ^ 59
def prefixEnd_46876 : Nat := 4983230072969 + 3 ^ 40 * 46876 * 2
def baseEnd_46876 : Nat := 21395483698012294341713

theorem tailTrace_46876 : CollatzResearch.WordTrace tailWord_46876 prefixEnd_46876 21395483698012294341713 := by
  unfold tailWord_46876
  simp only [CollatzResearch.WordTrace]
  refine ⟨854854089091866314268241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1139805452122488419024321 854854089091866314268241)
  ·
    refine ⟨641140566818899735701181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 854854089091866314268241 641140566818899735701181)
    ·
      refine ⟨240427712557087400887943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 641140566818899735701181 240427712557087400887943)
      ·
        refine ⟨360641568835631101331915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240427712557087400887943 360641568835631101331915)
        ·
          refine ⟨540962353253446651997873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360641568835631101331915 540962353253446651997873)
          ·
            refine ⟨405721764940084988998405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 540962353253446651997873 405721764940084988998405)
            ·
              refine ⟨76072830926265935437201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 405721764940084988998405 76072830926265935437201)
              ·
                refine ⟨57054623194699451577901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76072830926265935437201 57054623194699451577901)
                ·
                  refine ⟨21395483698012294341713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57054623194699451577901 21395483698012294341713)
                  ·
                    rfl

theorem cell20_46876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_46876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46876 prefixEnd_46876 := by exact prefixLift 46876
  have htrace : WordTrace (prefixWord ++ tailWord_46876) baseStart_46876 baseEnd_46876 := by
    simpa [prefixWord, tailWord_46876, baseEnd_46876] using wordTrace_append hprefix tailTrace_46876
  have hstable : (prefixWord ++ tailWord_46876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46876).length < 2 ^ (prefixWord ++ tailWord_46876).sum := by decide
  have hdescent : baseEnd_46876 < baseStart_46876 := by decide
  rcases family_descends (prefixWord ++ tailWord_46876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46900 : List Nat := [2, 5, 1, 1, 2, 2, 1, 2, 4]
def baseStart_46900 : Nat := 118140960795 + 46900 * 2 ^ 59
def prefixEnd_46900 : Nat := 4983230072969 + 3 ^ 40 * 46900 * 2
def baseEnd_46900 : Nat := 21406437951974877541615

theorem tailTrace_46900 : CollatzResearch.WordTrace tailWord_46900 prefixEnd_46900 21406437951974877541615 := by
  unfold tailWord_46900
  simp only [CollatzResearch.WordTrace]
  refine ⟨855291765048392363705077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1140389020064523151606769 855291765048392363705077)
  ·
    refine ⟨80183602973286784097351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 855291765048392363705077 80183602973286784097351)
    ·
      refine ⟨120275404459930176146027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80183602973286784097351 120275404459930176146027)
      ·
        refine ⟨180413106689895264219041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120275404459930176146027 180413106689895264219041)
        ·
          refine ⟨135309830017421448164281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180413106689895264219041 135309830017421448164281)
          ·
            refine ⟨101482372513066086123211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135309830017421448164281 101482372513066086123211)
            ·
              refine ⟨152223558769599129184817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101482372513066086123211 152223558769599129184817)
              ·
                refine ⟨114167669077199346888613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152223558769599129184817 114167669077199346888613)
                ·
                  refine ⟨21406437951974877541615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114167669077199346888613 21406437951974877541615)
                  ·
                    rfl

theorem cell20_46900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_46900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46900 prefixEnd_46900 := by exact prefixLift 46900
  have htrace : WordTrace (prefixWord ++ tailWord_46900) baseStart_46900 baseEnd_46900 := by
    simpa [prefixWord, tailWord_46900, baseEnd_46900] using wordTrace_append hprefix tailTrace_46900
  have hstable : (prefixWord ++ tailWord_46900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46900).length < 2 ^ (prefixWord ++ tailWord_46900).sum := by decide
  have hdescent : baseEnd_46900 < baseStart_46900 := by decide
  rcases family_descends (prefixWord ++ tailWord_46900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46904 : List Nat := [2, 1, 2, 1, 3, 3, 1, 1, 6]
def baseStart_46904 : Nat := 118140960795 + 46904 * 2 ^ 59
def prefixEnd_46904 : Nat := 4983230072969 + 3 ^ 40 * 46904 * 2
def baseEnd_46904 : Nat := 21408263660968641408265

theorem tailTrace_46904 : CollatzResearch.WordTrace tailWord_46904 prefixEnd_46904 21408263660968641408265 := by
  unfold tailWord_46904
  simp only [CollatzResearch.WordTrace]
  refine ⟨855364711041146705277883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1140486281388195607037177 855364711041146705277883)
  ·
    refine ⟨1283047066561720057916825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 855364711041146705277883 1283047066561720057916825)
    ·
      refine ⟨962285299921290043437619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1283047066561720057916825 962285299921290043437619)
      ·
        refine ⟨1443427949881935065156429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 962285299921290043437619 1443427949881935065156429)
        ·
          refine ⟨541285481205725649433661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1443427949881935065156429 541285481205725649433661)
          ·
            refine ⟨202982055452147118537623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 541285481205725649433661 202982055452147118537623)
            ·
              refine ⟨304473083178220677806435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202982055452147118537623 304473083178220677806435)
              ·
                refine ⟨456709624767331016709653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304473083178220677806435 456709624767331016709653)
                ·
                  refine ⟨21408263660968641408265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 456709624767331016709653 21408263660968641408265)
                  ·
                    rfl

theorem cell20_46904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_46904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46904 prefixEnd_46904 := by exact prefixLift 46904
  have htrace : WordTrace (prefixWord ++ tailWord_46904) baseStart_46904 baseEnd_46904 := by
    simpa [prefixWord, tailWord_46904, baseEnd_46904] using wordTrace_append hprefix tailTrace_46904
  have hstable : (prefixWord ++ tailWord_46904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46904).length < 2 ^ (prefixWord ++ tailWord_46904).sum := by decide
  have hdescent : baseEnd_46904 < baseStart_46904 := by decide
  rcases family_descends (prefixWord ++ tailWord_46904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46949 : List Nat := [1, 3, 1, 3, 1, 1, 1, 9]
def baseStart_46949 : Nat := 118140960795 + 46949 * 2 ^ 59
def prefixEnd_46949 : Nat := 4983230072969 + 3 ^ 40 * 46949 * 2
def baseEnd_46949 : Nat := 7142934295716161636027

theorem tailTrace_46949 : CollatzResearch.WordTrace tailWord_46949 prefixEnd_46949 7142934295716161636027 := by
  unfold tailWord_46949
  simp only [CollatzResearch.WordTrace]
  refine ⟨1712370706919266095943901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1141580471279510730629267 1712370706919266095943901)
  ·
    refine ⟨642139015094724785978963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1712370706919266095943901 642139015094724785978963)
    ·
      refine ⟨963208522642087178968445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 642139015094724785978963 963208522642087178968445)
      ·
        refine ⟨361203195990782692113167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 963208522642087178968445 361203195990782692113167)
        ·
          refine ⟨541804793986174038169751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361203195990782692113167 541804793986174038169751)
          ·
            refine ⟨812707190979261057254627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541804793986174038169751 812707190979261057254627)
            ·
              refine ⟨1219060786468891585881941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 812707190979261057254627 1219060786468891585881941)
              ·
                refine ⟨7142934295716161636027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1219060786468891585881941 7142934295716161636027)
                ·
                  rfl

theorem cell20_46949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 9].length) (baseStart_46949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46949 prefixEnd_46949 := by exact prefixLift 46949
  have htrace : WordTrace (prefixWord ++ tailWord_46949) baseStart_46949 baseEnd_46949 := by
    simpa [prefixWord, tailWord_46949, baseEnd_46949] using wordTrace_append hprefix tailTrace_46949
  have hstable : (prefixWord ++ tailWord_46949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46949).length < 2 ^ (prefixWord ++ tailWord_46949).sum := by decide
  have hdescent : baseEnd_46949 < baseStart_46949 := by decide
  rcases family_descends (prefixWord ++ tailWord_46949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46980 : List Nat := [2, 3, 2, 1, 1, 1, 2, 2, 6]
def baseStart_46980 : Nat := 118140960795 + 46980 * 2 ^ 59
def prefixEnd_46980 : Nat := 4983230072969 + 3 ^ 40 * 46980 * 2
def baseEnd_46980 : Nat := 21442952131850154874621

theorem tailTrace_46980 : CollatzResearch.WordTrace tailWord_46980 prefixEnd_46980 21442952131850154874621 := by
  unfold tailWord_46980
  simp only [CollatzResearch.WordTrace]
  refine ⟨856750684903479195161197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1142334246537972260214929 856750684903479195161197)
  ·
    refine ⟨321281506838804698185449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 856750684903479195161197 321281506838804698185449)
    ·
      refine ⟨240961130129103523639087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321281506838804698185449 240961130129103523639087)
      ·
        refine ⟨361441695193655285458631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240961130129103523639087 361441695193655285458631)
        ·
          refine ⟨542162542790482928187947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361441695193655285458631 542162542790482928187947)
          ·
            refine ⟨813243814185724392281921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542162542790482928187947 813243814185724392281921)
            ·
              refine ⟨609932860639293294211441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 813243814185724392281921 609932860639293294211441)
              ·
                refine ⟨457449645479469970658581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 609932860639293294211441 457449645479469970658581)
                ·
                  refine ⟨21442952131850154874621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 457449645479469970658581 21442952131850154874621)
                  ·
                    rfl

theorem cell20_46980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_46980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46980 prefixEnd_46980 := by exact prefixLift 46980
  have htrace : WordTrace (prefixWord ++ tailWord_46980) baseStart_46980 baseEnd_46980 := by
    simpa [prefixWord, tailWord_46980, baseEnd_46980] using wordTrace_append hprefix tailTrace_46980
  have hstable : (prefixWord ++ tailWord_46980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46980).length < 2 ^ (prefixWord ++ tailWord_46980).sum := by decide
  have hdescent : baseEnd_46980 < baseStart_46980 := by decide
  rcases family_descends (prefixWord ++ tailWord_46980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_46983 : List Nat := [1, 1, 4, 2, 5, 1, 6]
def baseStart_46983 : Nat := 118140960795 + 46983 * 2 ^ 59
def prefixEnd_46983 : Nat := 4983230072969 + 3 ^ 40 * 46983 * 2
def baseEnd_46983 : Nat := 2382702379288386419401

theorem tailTrace_46983 : CollatzResearch.WordTrace tailWord_46983 prefixEnd_46983 2382702379288386419401 := by
  unfold tailWord_46983
  simp only [CollatzResearch.WordTrace]
  refine ⟨1713610788796089902681603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1142407192530726601787735 1713610788796089902681603)
  ·
    refine ⟨2570416183194134854022405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1713610788796089902681603 2570416183194134854022405)
    ·
      refine ⟨481953034348900285129201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2570416183194134854022405 481953034348900285129201)
      ·
        refine ⟨361464775761675213846901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 481953034348900285129201 361464775761675213846901)
        ·
          refine ⟨33887322727657051298147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 361464775761675213846901 33887322727657051298147)
          ·
            refine ⟨50830984091485576947221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33887322727657051298147 50830984091485576947221)
            ·
              refine ⟨2382702379288386419401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50830984091485576947221 2382702379288386419401)
              ·
                rfl

theorem cell20_46983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 6].length) (baseStart_46983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_46983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_46983 prefixEnd_46983 := by exact prefixLift 46983
  have htrace : WordTrace (prefixWord ++ tailWord_46983) baseStart_46983 baseEnd_46983 := by
    simpa [prefixWord, tailWord_46983, baseEnd_46983] using wordTrace_append hprefix tailTrace_46983
  have hstable : (prefixWord ++ tailWord_46983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_46983).length < 2 ^ (prefixWord ++ tailWord_46983).sum := by decide
  have hdescent : baseEnd_46983 < baseStart_46983 := by decide
  rcases family_descends (prefixWord ++ tailWord_46983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47004 : List Nat := [2, 2, 3, 3, 1, 1, 1, 7]
def baseStart_47004 : Nat := 118140960795 + 47004 * 2 ^ 59
def prefixEnd_47004 : Nat := 4983230072969 + 3 ^ 40 * 47004 * 2
def baseEnd_47004 : Nat := 7151302128604246024841

theorem tailTrace_47004 : CollatzResearch.WordTrace tailWord_47004 prefixEnd_47004 7151302128604246024841 := by
  unfold tailWord_47004
  simp only [CollatzResearch.WordTrace]
  refine ⟨857188360860005244598033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1142917814480006992797377 857188360860005244598033)
  ·
    refine ⟨642891270645003933448525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 857188360860005244598033 642891270645003933448525)
    ·
      refine ⟨241084226491876475043197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 642891270645003933448525 241084226491876475043197)
      ·
        refine ⟨90406584934453678141199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241084226491876475043197 90406584934453678141199)
        ·
          refine ⟨135609877401680517211799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90406584934453678141199 135609877401680517211799)
          ·
            refine ⟨203414816102520775817699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135609877401680517211799 203414816102520775817699)
            ·
              refine ⟨305122224153781163726549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203414816102520775817699 305122224153781163726549)
              ·
                refine ⟨7151302128604246024841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 305122224153781163726549 7151302128604246024841)
                ·
                  rfl

theorem cell20_47004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 7].length) (baseStart_47004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47004 prefixEnd_47004 := by exact prefixLift 47004
  have htrace : WordTrace (prefixWord ++ tailWord_47004) baseStart_47004 baseEnd_47004 := by
    simpa [prefixWord, tailWord_47004, baseEnd_47004] using wordTrace_append hprefix tailTrace_47004
  have hstable : (prefixWord ++ tailWord_47004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47004).length < 2 ^ (prefixWord ++ tailWord_47004).sum := by decide
  have hdescent : baseEnd_47004 < baseStart_47004 := by decide
  rcases family_descends (prefixWord ++ tailWord_47004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47052 : List Nat := [2, 2, 1, 4, 1, 3, 1, 4, 2]
def baseStart_47052 : Nat := 118140960795 + 47052 * 2 ^ 59
def prefixEnd_47052 : Nat := 4983230072969 + 3 ^ 40 * 47052 * 2
def baseEnd_47052 : Nat := 21475814893737904474327

theorem tailTrace_47052 : CollatzResearch.WordTrace tailWord_47052 prefixEnd_47052 21475814893737904474327 := by
  unfold tailWord_47052
  simp only [CollatzResearch.WordTrace]
  refine ⟨858063712773057343471705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1144084950364076457962273 858063712773057343471705)
  ·
    refine ⟨643547784579793007603779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 858063712773057343471705 643547784579793007603779)
    ·
      refine ⟨965321676869689511405669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 643547784579793007603779 965321676869689511405669)
      ·
        refine ⟨180997814413066783388563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 965321676869689511405669 180997814413066783388563)
        ·
          refine ⟨271496721619600175082845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180997814413066783388563 271496721619600175082845)
          ·
            refine ⟨101811270607350065656067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 271496721619600175082845 101811270607350065656067)
            ·
              refine ⟨152716905911025098484101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101811270607350065656067 152716905911025098484101)
              ·
                refine ⟨28634419858317205965769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152716905911025098484101 28634419858317205965769)
                ·
                  refine ⟨21475814893737904474327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28634419858317205965769 21475814893737904474327)
                  ·
                    rfl

theorem cell20_47052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 4, 2].length) (baseStart_47052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47052 prefixEnd_47052 := by exact prefixLift 47052
  have htrace : WordTrace (prefixWord ++ tailWord_47052) baseStart_47052 baseEnd_47052 := by
    simpa [prefixWord, tailWord_47052, baseEnd_47052] using wordTrace_append hprefix tailTrace_47052
  have hstable : (prefixWord ++ tailWord_47052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47052).length < 2 ^ (prefixWord ++ tailWord_47052).sum := by decide
  have hdescent : baseEnd_47052 < baseStart_47052 := by decide
  rcases family_descends (prefixWord ++ tailWord_47052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47111 : List Nat := [1, 1, 4, 3, 1, 3, 2, 1, 4]
def baseStart_47111 : Nat := 118140960795 + 47111 * 2 ^ 59
def prefixEnd_47111 : Nat := 4983230072969 + 3 ^ 40 * 47111 * 2
def baseEnd_47111 : Nat := 21502744101395921507419

theorem tailTrace_47111 : CollatzResearch.WordTrace tailWord_47111 prefixEnd_47111 21502744101395921507419 := by
  unfold tailWord_47111
  simp only [CollatzResearch.WordTrace]
  refine ⟨1718279332332367763341187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1145519554888245175560791 1718279332332367763341187)
  ·
    refine ⟨2577418998498551645011781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1718279332332367763341187 2577418998498551645011781)
    ·
      refine ⟨483266062218478433439709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2577418998498551645011781 483266062218478433439709)
      ·
        refine ⟨181224773331929412539891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 483266062218478433439709 181224773331929412539891)
        ·
          refine ⟨271837159997894118809837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181224773331929412539891 271837159997894118809837)
          ·
            refine ⟨101938934999210294553689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 271837159997894118809837 101938934999210294553689)
            ·
              refine ⟨76454201249407720915267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101938934999210294553689 76454201249407720915267)
              ·
                refine ⟨114681301874111581372901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76454201249407720915267 114681301874111581372901)
                ·
                  refine ⟨21502744101395921507419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114681301874111581372901 21502744101395921507419)
                  ·
                    rfl

theorem cell20_47111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 4].length) (baseStart_47111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47111 prefixEnd_47111 := by exact prefixLift 47111
  have htrace : WordTrace (prefixWord ++ tailWord_47111) baseStart_47111 baseEnd_47111 := by
    simpa [prefixWord, tailWord_47111, baseEnd_47111] using wordTrace_append hprefix tailTrace_47111
  have hstable : (prefixWord ++ tailWord_47111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47111).length < 2 ^ (prefixWord ++ tailWord_47111).sum := by decide
  have hdescent : baseEnd_47111 < baseStart_47111 := by decide
  rcases family_descends (prefixWord ++ tailWord_47111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47139 : List Nat := [1, 1, 1, 4, 3, 1, 3, 6]
def baseStart_47139 : Nat := 118140960795 + 47139 * 2 ^ 59
def prefixEnd_47139 : Nat := 4983230072969 + 3 ^ 40 * 47139 * 2
def baseEnd_47139 : Nat := 7171841354784089524657

theorem tailTrace_47139 : CollatzResearch.WordTrace tailWord_47139 prefixEnd_47139 7171841354784089524657 := by
  unfold tailWord_47139
  simp only [CollatzResearch.WordTrace]
  refine ⟨1719300576230928545360471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1146200384153952363573647 1719300576230928545360471)
  ·
    refine ⟨2578950864346392818040707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1719300576230928545360471 2578950864346392818040707)
    ·
      refine ⟨3868426296519589227061061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2578950864346392818040707 3868426296519589227061061)
      ·
        refine ⟨725329930597422980073949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3868426296519589227061061 725329930597422980073949)
        ·
          refine ⟨271998723974033617527731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 725329930597422980073949 271998723974033617527731)
          ·
            refine ⟨407998085961050426291597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271998723974033617527731 407998085961050426291597)
            ·
              refine ⟨152999282235393909859349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 407998085961050426291597 152999282235393909859349)
              ·
                refine ⟨7171841354784089524657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 152999282235393909859349 7171841354784089524657)
                ·
                  rfl

theorem cell20_47139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 6].length) (baseStart_47139 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47139 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47139 prefixEnd_47139 := by exact prefixLift 47139
  have htrace : WordTrace (prefixWord ++ tailWord_47139) baseStart_47139 baseEnd_47139 := by
    simpa [prefixWord, tailWord_47139, baseEnd_47139] using wordTrace_append hprefix tailTrace_47139
  have hstable : (prefixWord ++ tailWord_47139).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47139).length < 2 ^ (prefixWord ++ tailWord_47139).sum := by decide
  have hdescent : baseEnd_47139 < baseStart_47139 := by decide
  rcases family_descends (prefixWord ++ tailWord_47139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47177 : List Nat := [1, 2, 1, 1, 2, 2, 6, 5]
def baseStart_47177 : Nat := 118140960795 + 47177 * 2 ^ 59
def prefixEnd_47177 : Nat := 4983230072969 + 3 ^ 40 * 47177 * 2
def baseEnd_47177 : Nat := 7177622766597675102383

theorem tailTrace_47177 : CollatzResearch.WordTrace tailWord_47177 prefixEnd_47177 7177622766597675102383 := by
  unfold tailWord_47177
  simp only [CollatzResearch.WordTrace]
  refine ⟨1720686550093261035243785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1147124366728840690162523 1720686550093261035243785)
  ·
    refine ⟨1290514912569945776432839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1720686550093261035243785 1290514912569945776432839)
    ·
      refine ⟨1935772368854918664649259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1290514912569945776432839 1935772368854918664649259)
      ·
        refine ⟨2903658553282377996973889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1935772368854918664649259 2903658553282377996973889)
        ·
          refine ⟨2177743914961783497730417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2903658553282377996973889 2177743914961783497730417)
          ·
            refine ⟨1633307936221337623297813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2177743914961783497730417 1633307936221337623297813)
            ·
              refine ⟨76561309510375201092085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1633307936221337623297813 76561309510375201092085)
              ·
                refine ⟨7177622766597675102383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76561309510375201092085 7177622766597675102383)
                ·
                  rfl

theorem cell20_47177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 5].length) (baseStart_47177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47177 prefixEnd_47177 := by exact prefixLift 47177
  have htrace : WordTrace (prefixWord ++ tailWord_47177) baseStart_47177 baseEnd_47177 := by
    simpa [prefixWord, tailWord_47177, baseEnd_47177] using wordTrace_append hprefix tailTrace_47177
  have hstable : (prefixWord ++ tailWord_47177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47177).length < 2 ^ (prefixWord ++ tailWord_47177).sum := by decide
  have hdescent : baseEnd_47177 < baseStart_47177 := by decide
  rcases family_descends (prefixWord ++ tailWord_47177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47180 : List Nat := [2, 2, 1, 3, 1, 1, 6, 1, 3]
def baseStart_47180 : Nat := 118140960795 + 47180 * 2 ^ 59
def prefixEnd_47180 : Nat := 4983230072969 + 3 ^ 40 * 47180 * 2
def baseEnd_47180 : Nat := 21534237581538348207137

theorem tailTrace_47180 : CollatzResearch.WordTrace tailWord_47180 prefixEnd_47180 21534237581538348207137 := by
  unfold tailWord_47180
  simp only [CollatzResearch.WordTrace]
  refine ⟨860397984541196273801497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1147197312721595031735329 860397984541196273801497)
  ·
    refine ⟨645298488405897205351123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 860397984541196273801497 645298488405897205351123)
    ·
      refine ⟨967947732608845808026685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 645298488405897205351123 967947732608845808026685)
      ·
        refine ⟨362980399728317178010007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 967947732608845808026685 362980399728317178010007)
        ·
          refine ⟨544470599592475767015011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362980399728317178010007 544470599592475767015011)
          ·
            refine ⟨816705899388713650522517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544470599592475767015011 816705899388713650522517)
            ·
              refine ⟨38283089033845952368243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 816705899388713650522517 38283089033845952368243)
              ·
                refine ⟨57424633550768928552365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38283089033845952368243 57424633550768928552365)
                ·
                  refine ⟨21534237581538348207137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57424633550768928552365 21534237581538348207137)
                  ·
                    rfl

theorem cell20_47180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 3].length) (baseStart_47180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47180 prefixEnd_47180 := by exact prefixLift 47180
  have htrace : WordTrace (prefixWord ++ tailWord_47180) baseStart_47180 baseEnd_47180 := by
    simpa [prefixWord, tailWord_47180, baseEnd_47180] using wordTrace_append hprefix tailTrace_47180
  have hstable : (prefixWord ++ tailWord_47180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47180).length < 2 ^ (prefixWord ++ tailWord_47180).sum := by decide
  have hdescent : baseEnd_47180 < baseStart_47180 := by decide
  rcases family_descends (prefixWord ++ tailWord_47180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47218 : List Nat := [3, 2, 1, 2, 2, 3, 2, 2, 3]
def baseStart_47218 : Nat := 118140960795 + 47218 * 2 ^ 59
def prefixEnd_47218 : Nat := 4983230072969 + 3 ^ 40 * 47218 * 2
def baseEnd_47218 : Nat := 21551581816979104940315

theorem tailTrace_47218 : CollatzResearch.WordTrace tailWord_47218 prefixEnd_47218 21551581816979104940315 := by
  unfold tailWord_47218
  simp only [CollatzResearch.WordTrace]
  refine ⟨430545485736181259371577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1148121295296483358324205 430545485736181259371577)
  ·
    refine ⟨322909114302135944528683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 430545485736181259371577 322909114302135944528683)
    ·
      refine ⟨484363671453203916793025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322909114302135944528683 484363671453203916793025)
      ·
        refine ⟨363272753589902937594769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 484363671453203916793025 363272753589902937594769)
        ·
          refine ⟨272454565192427203196077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 363272753589902937594769 272454565192427203196077)
          ·
            refine ⟨102170461947160201198529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 272454565192427203196077 102170461947160201198529)
            ·
              refine ⟨76627846460370150898897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102170461947160201198529 76627846460370150898897)
              ·
                refine ⟨57470884845277613174173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76627846460370150898897 57470884845277613174173)
                ·
                  refine ⟨21551581816979104940315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57470884845277613174173 21551581816979104940315)
                  ·
                    rfl

theorem cell20_47218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_47218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47218 prefixEnd_47218 := by exact prefixLift 47218
  have htrace : WordTrace (prefixWord ++ tailWord_47218) baseStart_47218 baseEnd_47218 := by
    simpa [prefixWord, tailWord_47218, baseEnd_47218] using wordTrace_append hprefix tailTrace_47218
  have hstable : (prefixWord ++ tailWord_47218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47218).length < 2 ^ (prefixWord ++ tailWord_47218).sum := by decide
  have hdescent : baseEnd_47218 < baseStart_47218 := by decide
  rcases family_descends (prefixWord ++ tailWord_47218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47239 : List Nat := [1, 1, 4, 2, 1, 1, 4, 3, 3]
def baseStart_47239 : Nat := 118140960795 + 47239 * 2 ^ 59
def prefixEnd_47239 : Nat := 4983230072969 + 3 ^ 40 * 47239 * 2
def baseEnd_47239 : Nat := 21561166789196365240229

theorem tailTrace_47239 : CollatzResearch.WordTrace tailWord_47239 prefixEnd_47239 21561166789196365240229 := by
  unfold tailWord_47239
  simp only [CollatzResearch.WordTrace]
  refine ⟨1722947875868645624000771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1148631917245763749333847 1722947875868645624000771)
  ·
    refine ⟨2584421813802968436001157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1722947875868645624000771 2584421813802968436001157)
    ·
      refine ⟨484579090088056581750217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2584421813802968436001157 484579090088056581750217)
      ·
        refine ⟨363434317566042436312663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 484579090088056581750217 363434317566042436312663)
        ·
          refine ⟨545151476349063654468995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363434317566042436312663 545151476349063654468995)
          ·
            refine ⟨817727214523595481703493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545151476349063654468995 817727214523595481703493)
            ·
              refine ⟨153323852723174152819405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 817727214523595481703493 153323852723174152819405)
              ·
                refine ⟨57496444771190307307277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153323852723174152819405 57496444771190307307277)
                ·
                  refine ⟨21561166789196365240229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57496444771190307307277 21561166789196365240229)
                  ·
                    rfl

theorem cell20_47239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 3].length) (baseStart_47239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47239 prefixEnd_47239 := by exact prefixLift 47239
  have htrace : WordTrace (prefixWord ++ tailWord_47239) baseStart_47239 baseEnd_47239 := by
    simpa [prefixWord, tailWord_47239, baseEnd_47239] using wordTrace_append hprefix tailTrace_47239
  have hstable : (prefixWord ++ tailWord_47239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47239).length < 2 ^ (prefixWord ++ tailWord_47239).sum := by decide
  have hdescent : baseEnd_47239 < baseStart_47239 := by decide
  rcases family_descends (prefixWord ++ tailWord_47239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47305 : List Nat := [1, 2, 1, 1, 2, 1, 1, 5, 6]
def baseStart_47305 : Nat := 118140960795 + 47305 * 2 ^ 59
def prefixEnd_47305 : Nat := 4983230072969 + 3 ^ 40 * 47305 * 2
def baseEnd_47305 : Nat := 21591290987593469039959

theorem tailTrace_47305 : CollatzResearch.WordTrace tailWord_47305 prefixEnd_47305 21591290987593469039959 := by
  unfold tailWord_47305
  simp only [CollatzResearch.WordTrace]
  refine ⟨1725355093629538895903369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1150236729086359263935579 1725355093629538895903369)
  ·
    refine ⟨1294016320222154171927527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1725355093629538895903369 1294016320222154171927527)
    ·
      refine ⟨1941024480333231257891291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1294016320222154171927527 1941024480333231257891291)
      ·
        refine ⟨2911536720499846886836937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1941024480333231257891291 2911536720499846886836937)
        ·
          refine ⟨2183652540374885165127703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2911536720499846886836937 2183652540374885165127703)
          ·
            refine ⟨3275478810562327747691555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2183652540374885165127703 3275478810562327747691555)
            ·
              refine ⟨4913218215843491621537333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3275478810562327747691555 4913218215843491621537333)
              ·
                refine ⟨460614207735327339519125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4913218215843491621537333 460614207735327339519125)
                ·
                  refine ⟨21591290987593469039959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 460614207735327339519125 21591290987593469039959)
                  ·
                    rfl

theorem cell20_47305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_47305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47305 prefixEnd_47305 := by exact prefixLift 47305
  have htrace : WordTrace (prefixWord ++ tailWord_47305) baseStart_47305 baseEnd_47305 := by
    simpa [prefixWord, tailWord_47305, baseEnd_47305] using wordTrace_append hprefix tailTrace_47305
  have hstable : (prefixWord ++ tailWord_47305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47305).length < 2 ^ (prefixWord ++ tailWord_47305).sum := by decide
  have hdescent : baseEnd_47305 < baseStart_47305 := by decide
  rcases family_descends (prefixWord ++ tailWord_47305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47335 : List Nat := [1, 1, 5, 3, 1, 2, 3, 2, 2]
def baseStart_47335 : Nat := 118140960795 + 47335 * 2 ^ 59
def prefixEnd_47335 : Nat := 4983230072969 + 3 ^ 40 * 47335 * 2
def baseEnd_47335 : Nat := 21604983805046698039837

theorem tailTrace_47335 : CollatzResearch.WordTrace tailWord_47335 prefixEnd_47335 21604983805046698039837 := by
  unfold tailWord_47335
  simp only [CollatzResearch.WordTrace]
  refine ⟨1726449283520854019495459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1150966189013902679663639 1726449283520854019495459)
  ·
    refine ⟨2589673925281281029243189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1726449283520854019495459 2589673925281281029243189)
    ·
      refine ⟨242781930495120096491549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2589673925281281029243189 242781930495120096491549)
      ·
        refine ⟨91043223935670036184331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242781930495120096491549 91043223935670036184331)
        ·
          refine ⟨136564835903505054276497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91043223935670036184331 136564835903505054276497)
          ·
            refine ⟨102423626927628790707373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136564835903505054276497 102423626927628790707373)
            ·
              refine ⟨38408860097860796515265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102423626927628790707373 38408860097860796515265)
              ·
                refine ⟨28806645073395597386449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38408860097860796515265 28806645073395597386449)
                ·
                  refine ⟨21604983805046698039837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28806645073395597386449 21604983805046698039837)
                  ·
                    rfl

theorem cell20_47335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 2, 2].length) (baseStart_47335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47335 prefixEnd_47335 := by exact prefixLift 47335
  have htrace : WordTrace (prefixWord ++ tailWord_47335) baseStart_47335 baseEnd_47335 := by
    simpa [prefixWord, tailWord_47335, baseEnd_47335] using wordTrace_append hprefix tailTrace_47335
  have hstable : (prefixWord ++ tailWord_47335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47335).length < 2 ^ (prefixWord ++ tailWord_47335).sum := by decide
  have hdescent : baseEnd_47335 < baseStart_47335 := by decide
  rcases family_descends (prefixWord ++ tailWord_47335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47346 : List Nat := [3, 2, 1, 3, 2, 2, 2, 5]
def baseStart_47346 : Nat := 118140960795 + 47346 * 2 ^ 59
def prefixEnd_47346 : Nat := 4983230072969 + 3 ^ 40 * 47346 * 2
def baseEnd_47346 : Nat := 7203334834926516224375

theorem tailTrace_47346 : CollatzResearch.WordTrace tailWord_47346 prefixEnd_47346 7203334834926516224375 := by
  unfold tailWord_47346
  simp only [CollatzResearch.WordTrace]
  refine ⟨431712621620250724536473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1151233657654001932097261 431712621620250724536473)
  ·
    refine ⟨323784466215188043402355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 431712621620250724536473 323784466215188043402355)
    ·
      refine ⟨485676699322782065103533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323784466215188043402355 485676699322782065103533)
      ·
        refine ⟨182128762246043274413825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 485676699322782065103533 182128762246043274413825)
        ·
          refine ⟨136596571684532455810369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182128762246043274413825 136596571684532455810369)
          ·
            refine ⟨102447428763399341857777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136596571684532455810369 102447428763399341857777)
            ·
              refine ⟨76835571572549506393333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102447428763399341857777 76835571572549506393333)
              ·
                refine ⟨7203334834926516224375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76835571572549506393333 7203334834926516224375)
                ·
                  rfl

theorem cell20_47346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_47346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47346 prefixEnd_47346 := by exact prefixLift 47346
  have htrace : WordTrace (prefixWord ++ tailWord_47346) baseStart_47346 baseEnd_47346 := by
    simpa [prefixWord, tailWord_47346, baseEnd_47346] using wordTrace_append hprefix tailTrace_47346
  have hstable : (prefixWord ++ tailWord_47346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47346).length < 2 ^ (prefixWord ++ tailWord_47346).sum := by decide
  have hdescent : baseEnd_47346 < baseStart_47346 := by decide
  rcases family_descends (prefixWord ++ tailWord_47346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47390 : List Nat := [4, 3, 2, 1, 1, 1, 4, 2, 2]
def baseStart_47390 : Nat := 118140960795 + 47390 * 2 ^ 59
def prefixEnd_47390 : Nat := 4983230072969 + 3 ^ 40 * 47390 * 2
def baseEnd_47390 : Nat := 21630087303710951206279

theorem tailTrace_47390 : CollatzResearch.WordTrace tailWord_47390 prefixEnd_47390 21630087303710951206279 := by
  unfold tailWord_47390
  simp only [CollatzResearch.WordTrace]
  refine ⟨216056912290199801593453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1152303532214398941831749 216056912290199801593453)
  ·
    refine ⟨81021342108824925597545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216056912290199801593453 81021342108824925597545)
    ·
      refine ⟨60766006581618694198159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81021342108824925597545 60766006581618694198159)
      ·
        refine ⟨91149009872428041297239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60766006581618694198159 91149009872428041297239)
        ·
          refine ⟨136723514808642061945859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91149009872428041297239 136723514808642061945859)
          ·
            refine ⟨205085272212963092918789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136723514808642061945859 205085272212963092918789)
            ·
              refine ⟨38453488539930579922273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 205085272212963092918789 38453488539930579922273)
              ·
                refine ⟨28840116404947934941705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38453488539930579922273 28840116404947934941705)
                ·
                  refine ⟨21630087303710951206279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28840116404947934941705 21630087303710951206279)
                  ·
                    rfl

theorem cell20_47390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_47390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47390 prefixEnd_47390 := by exact prefixLift 47390
  have htrace : WordTrace (prefixWord ++ tailWord_47390) baseStart_47390 baseEnd_47390 := by
    simpa [prefixWord, tailWord_47390, baseEnd_47390] using wordTrace_append hprefix tailTrace_47390
  have hstable : (prefixWord ++ tailWord_47390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47390).length < 2 ^ (prefixWord ++ tailWord_47390).sum := by decide
  have hdescent : baseEnd_47390 < baseStart_47390 := by decide
  rcases family_descends (prefixWord ++ tailWord_47390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47391 : List Nat := [1, 1, 2, 4, 3, 1, 1, 4, 3]
def baseStart_47391 : Nat := 118140960795 + 47391 * 2 ^ 59
def prefixEnd_47391 : Nat := 4983230072969 + 3 ^ 40 * 47391 * 2
def baseEnd_47391 : Nat := 21630543730959392172941

theorem tailTrace_47391 : CollatzResearch.WordTrace tailWord_47391 prefixEnd_47391 21630543730959392172941 := by
  unfold tailWord_47391
  simp only [CollatzResearch.WordTrace]
  refine ⟨1728491771317975583534027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1152327847545317055689351 1728491771317975583534027)
  ·
    refine ⟨2592737656976963375301041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1728491771317975583534027 2592737656976963375301041)
    ·
      refine ⟨1944553242732722531475781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2592737656976963375301041 1944553242732722531475781)
      ·
        refine ⟨364603733012385474651709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1944553242732722531475781 364603733012385474651709)
        ·
          refine ⟨136726399879644552994391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 364603733012385474651709 136726399879644552994391)
          ·
            refine ⟨205089599819466829491587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136726399879644552994391 205089599819466829491587)
            ·
              refine ⟨307634399729200244237381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205089599819466829491587 307634399729200244237381)
              ·
                refine ⟨57681449949225045794509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 307634399729200244237381 57681449949225045794509)
                ·
                  refine ⟨21630543730959392172941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57681449949225045794509 21630543730959392172941)
                  ·
                    rfl

theorem cell20_47391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 3].length) (baseStart_47391 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47391 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47391 prefixEnd_47391 := by exact prefixLift 47391
  have htrace : WordTrace (prefixWord ++ tailWord_47391) baseStart_47391 baseEnd_47391 := by
    simpa [prefixWord, tailWord_47391, baseEnd_47391] using wordTrace_append hprefix tailTrace_47391
  have hstable : (prefixWord ++ tailWord_47391).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47391).length < 2 ^ (prefixWord ++ tailWord_47391).sum := by decide
  have hdescent : baseEnd_47391 < baseStart_47391 := by decide
  rcases family_descends (prefixWord ++ tailWord_47391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47394 : List Nat := [3, 3, 1, 1, 3, 2, 1, 4, 2]
def baseStart_47394 : Nat := 118140960795 + 47394 * 2 ^ 59
def prefixEnd_47394 : Nat := 4983230072969 + 3 ^ 40 * 47394 * 2
def baseEnd_47394 : Nat := 21631913012704715072929

theorem tailTrace_47394 : CollatzResearch.WordTrace tailWord_47394 prefixEnd_47394 21631913012704715072929 := by
  unfold tailWord_47394
  simp only [CollatzResearch.WordTrace]
  refine ⟨432150297576776773973309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1152400793538071397262157 432150297576776773973309)
  ·
    refine ⟨162056361591291290239991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 432150297576776773973309 162056361591291290239991)
    ·
      refine ⟨243084542386936935359987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162056361591291290239991 243084542386936935359987)
      ·
        refine ⟨364626813580405403039981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243084542386936935359987 364626813580405403039981)
        ·
          refine ⟨136735055092652026139993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 364626813580405403039981 136735055092652026139993)
          ·
            refine ⟨102551291319489019604995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136735055092652026139993 102551291319489019604995)
            ·
              refine ⟨153826936979233529407493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102551291319489019604995 153826936979233529407493)
              ·
                refine ⟨28842550683606286763905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153826936979233529407493 28842550683606286763905)
                ·
                  refine ⟨21631913012704715072929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28842550683606286763905 21631913012704715072929)
                  ·
                    rfl

theorem cell20_47394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_47394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47394 prefixEnd_47394 := by exact prefixLift 47394
  have htrace : WordTrace (prefixWord ++ tailWord_47394) baseStart_47394 baseEnd_47394 := by
    simpa [prefixWord, tailWord_47394, baseEnd_47394] using wordTrace_append hprefix tailTrace_47394
  have hstable : (prefixWord ++ tailWord_47394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47394).length < 2 ^ (prefixWord ++ tailWord_47394).sum := by decide
  have hdescent : baseEnd_47394 < baseStart_47394 := by decide
  rcases family_descends (prefixWord ++ tailWord_47394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47474 : List Nat := [3, 2, 1, 2, 1, 3, 2, 2, 4]
def baseStart_47474 : Nat := 118140960795 + 47474 * 2 ^ 59
def prefixEnd_47474 : Nat := 4983230072969 + 3 ^ 40 * 47474 * 2
def baseEnd_47474 : Nat := 21668427192579992405935

theorem tailTrace_47474 : CollatzResearch.WordTrace tailWord_47474 prefixEnd_47474 21668427192579992405935 := by
  unfold tailWord_47474
  simp only [CollatzResearch.WordTrace]
  refine ⟨432879757504320189701369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1154346020011520505870317 432879757504320189701369)
  ·
    refine ⟨324659818128240142276027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 432879757504320189701369 324659818128240142276027)
    ·
      refine ⟨486989727192360213414041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324659818128240142276027 486989727192360213414041)
      ·
        refine ⟨365242295394270160060531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 486989727192360213414041 365242295394270160060531)
        ·
          refine ⟨547863443091405240090797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365242295394270160060531 547863443091405240090797)
          ·
            refine ⟨205448791159276965034049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 547863443091405240090797 205448791159276965034049)
            ·
              refine ⟨154086593369457723775537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205448791159276965034049 154086593369457723775537)
              ·
                refine ⟨115564945027093292831653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154086593369457723775537 115564945027093292831653)
                ·
                  refine ⟨21668427192579992405935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115564945027093292831653 21668427192579992405935)
                  ·
                    rfl

theorem cell20_47474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_47474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47474 prefixEnd_47474 := by exact prefixLift 47474
  have htrace : WordTrace (prefixWord ++ tailWord_47474) baseStart_47474 baseEnd_47474 := by
    simpa [prefixWord, tailWord_47474, baseEnd_47474] using wordTrace_append hprefix tailTrace_47474
  have hstable : (prefixWord ++ tailWord_47474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47474).length < 2 ^ (prefixWord ++ tailWord_47474).sum := by decide
  have hdescent : baseEnd_47474 < baseStart_47474 := by decide
  rcases family_descends (prefixWord ++ tailWord_47474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47477 : List Nat := [1, 3, 4, 1, 2, 3, 2, 4]
def baseStart_47477 : Nat := 118140960795 + 47477 * 2 ^ 59
def prefixEnd_47477 : Nat := 4983230072969 + 3 ^ 40 * 47477 * 2
def baseEnd_47477 : Nat := 7223265491441771768641

theorem tailTrace_47477 : CollatzResearch.WordTrace tailWord_47477 prefixEnd_47477 7223265491441771768641 := by
  unfold tailWord_47477
  simp only [CollatzResearch.WordTrace]
  refine ⟨1731628449006412271164685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1154418966004274847443123 1731628449006412271164685)
  ·
    refine ⟨649360668377404601686757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1731628449006412271164685 649360668377404601686757)
    ·
      refine ⟨121755125320763362816267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 649360668377404601686757 121755125320763362816267)
      ·
        refine ⟨182632687981145044224401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121755125320763362816267 182632687981145044224401)
        ·
          refine ⟨136974515985858783168301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182632687981145044224401 136974515985858783168301)
          ·
            refine ⟨51365443494697043688113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136974515985858783168301 51365443494697043688113)
            ·
              refine ⟨38524082621022782766085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51365443494697043688113 38524082621022782766085)
              ·
                refine ⟨7223265491441771768641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38524082621022782766085 7223265491441771768641)
                ·
                  rfl

theorem cell20_47477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 4].length) (baseStart_47477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47477 prefixEnd_47477 := by exact prefixLift 47477
  have htrace : WordTrace (prefixWord ++ tailWord_47477) baseStart_47477 baseEnd_47477 := by
    simpa [prefixWord, tailWord_47477, baseEnd_47477] using wordTrace_append hprefix tailTrace_47477
  have hstable : (prefixWord ++ tailWord_47477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47477).length < 2 ^ (prefixWord ++ tailWord_47477).sum := by decide
  have hdescent : baseEnd_47477 < baseStart_47477 := by decide
  rcases family_descends (prefixWord ++ tailWord_47477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47508 : List Nat := [2, 4, 2, 1, 3, 2, 1, 1, 4]
def baseStart_47508 : Nat := 118140960795 + 47508 * 2 ^ 59
def prefixEnd_47508 : Nat := 4983230072969 + 3 ^ 40 * 47508 * 2
def baseEnd_47508 : Nat := 21683945719026985272463

theorem tailTrace_47508 : CollatzResearch.WordTrace tailWord_47508 prefixEnd_47508 21683945719026985272463 := by
  unfold tailWord_47508
  simp only [CollatzResearch.WordTrace]
  refine ⟨866379555947052282771589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1155172741262736377028785 866379555947052282771589)
  ·
    refine ⟨162446166740072303019673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 866379555947052282771589 162446166740072303019673)
    ·
      refine ⟨121834625055054227264755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162446166740072303019673 121834625055054227264755)
      ·
        refine ⟨182751937582581340897133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121834625055054227264755 182751937582581340897133)
        ·
          refine ⟨68531976593468002836425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182751937582581340897133 68531976593468002836425)
          ·
            refine ⟨51398982445101002127319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68531976593468002836425 51398982445101002127319)
            ·
              refine ⟨77098473667651503190979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51398982445101002127319 77098473667651503190979)
              ·
                refine ⟨115647710501477254786469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77098473667651503190979 115647710501477254786469)
                ·
                  refine ⟨21683945719026985272463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115647710501477254786469 21683945719026985272463)
                  ·
                    rfl

theorem cell20_47508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_47508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47508 prefixEnd_47508 := by exact prefixLift 47508
  have htrace : WordTrace (prefixWord ++ tailWord_47508) baseStart_47508 baseEnd_47508 := by
    simpa [prefixWord, tailWord_47508, baseEnd_47508] using wordTrace_append hprefix tailTrace_47508
  have hstable : (prefixWord ++ tailWord_47508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47508).length < 2 ^ (prefixWord ++ tailWord_47508).sum := by decide
  have hdescent : baseEnd_47508 < baseStart_47508 := by decide
  rcases family_descends (prefixWord ++ tailWord_47508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47518 : List Nat := [4, 3, 1, 2, 1, 3, 2, 1, 3]
def baseStart_47518 : Nat := 118140960795 + 47518 * 2 ^ 59
def prefixEnd_47518 : Nat := 4983230072969 + 3 ^ 40 * 47518 * 2
def baseEnd_47518 : Nat := 21688509991511394939089

theorem tailTrace_47518 : CollatzResearch.WordTrace tailWord_47518 prefixEnd_47518 21688509991511394939089 := by
  unfold tailWord_47518
  simp only [CollatzResearch.WordTrace]
  refine ⟨216640480232234534175901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1155415894571917515604805 216640480232234534175901)
  ·
    refine ⟨81240180087087950315963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216640480232234534175901 81240180087087950315963)
    ·
      refine ⟨121860270130631925473945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81240180087087950315963 121860270130631925473945)
      ·
        refine ⟨91395202597973944105459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121860270130631925473945 91395202597973944105459)
        ·
          refine ⟨137092803896960916158189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91395202597973944105459 137092803896960916158189)
          ·
            refine ⟨51409801461360343559321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137092803896960916158189 51409801461360343559321)
            ·
              refine ⟨38557351096020257669491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51409801461360343559321 38557351096020257669491)
              ·
                refine ⟨57836026644030386504237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38557351096020257669491 57836026644030386504237)
                ·
                  refine ⟨21688509991511394939089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57836026644030386504237 21688509991511394939089)
                  ·
                    rfl

theorem cell20_47518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_47518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47518 prefixEnd_47518 := by exact prefixLift 47518
  have htrace : WordTrace (prefixWord ++ tailWord_47518) baseStart_47518 baseEnd_47518 := by
    simpa [prefixWord, tailWord_47518, baseEnd_47518] using wordTrace_append hprefix tailTrace_47518
  have hstable : (prefixWord ++ tailWord_47518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47518).length < 2 ^ (prefixWord ++ tailWord_47518).sum := by decide
  have hdescent : baseEnd_47518 < baseStart_47518 := by decide
  rcases family_descends (prefixWord ++ tailWord_47518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47519 : List Nat := [1, 1, 2, 5, 1, 1, 4, 5]
def baseStart_47519 : Nat := 118140960795 + 47519 * 2 ^ 59
def prefixEnd_47519 : Nat := 4983230072969 + 3 ^ 40 * 47519 * 2
def baseEnd_47519 : Nat := 7229655472919945301917

theorem tailTrace_47519 : CollatzResearch.WordTrace tailWord_47519 prefixEnd_47519 7229655472919945301917 := by
  unfold tailWord_47519
  simp only [CollatzResearch.WordTrace]
  refine ⟨1733160314854253444193611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1155440209902835629462407 1733160314854253444193611)
  ·
    refine ⟨2599740472281380166290417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1733160314854253444193611 2599740472281380166290417)
    ·
      refine ⟨1949805354211035124717813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2599740472281380166290417 1949805354211035124717813)
      ·
        refine ⟨182794251957284542942295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1949805354211035124717813 182794251957284542942295)
        ·
          refine ⟨274191377935926814413443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182794251957284542942295 274191377935926814413443)
          ·
            refine ⟨411287066903890221620165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274191377935926814413443 411287066903890221620165)
            ·
              refine ⟨77116325044479416553781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 411287066903890221620165 77116325044479416553781)
              ·
                refine ⟨7229655472919945301917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77116325044479416553781 7229655472919945301917)
                ·
                  rfl

theorem cell20_47519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 5].length) (baseStart_47519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47519 prefixEnd_47519 := by exact prefixLift 47519
  have htrace : WordTrace (prefixWord ++ tailWord_47519) baseStart_47519 baseEnd_47519 := by
    simpa [prefixWord, tailWord_47519, baseEnd_47519] using wordTrace_append hprefix tailTrace_47519
  have hstable : (prefixWord ++ tailWord_47519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47519).length < 2 ^ (prefixWord ++ tailWord_47519).sum := by decide
  have hdescent : baseEnd_47519 < baseStart_47519 := by decide
  rcases family_descends (prefixWord ++ tailWord_47519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47553 : List Nat := [1, 2, 7, 1, 1, 8]
def baseStart_47553 : Nat := 118140960795 + 47553 * 2 ^ 59
def prefixEnd_47553 : Nat := 4983230072969 + 3 ^ 40 * 47553 * 2
def baseEnd_47553 : Nat := 803869812785438102677

theorem tailTrace_47553 : CollatzResearch.WordTrace tailWord_47553 prefixEnd_47553 803869812785438102677 := by
  unfold tailWord_47553
  simp only [CollatzResearch.WordTrace]
  refine ⟨1734400396731077250931313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1156266931154051500620875 1734400396731077250931313)
  ·
    refine ⟨1300800297548307938198485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1734400396731077250931313 1300800297548307938198485)
    ·
      refine ⟨30487506973788467301527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 1300800297548307938198485 30487506973788467301527)
      ·
        refine ⟨45731260460682700952291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30487506973788467301527 45731260460682700952291)
        ·
          refine ⟨68596890691024051428437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45731260460682700952291 68596890691024051428437)
          ·
            refine ⟨803869812785438102677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 68596890691024051428437 803869812785438102677)
            ·
              rfl

theorem cell20_47553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 8].length) (baseStart_47553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47553 prefixEnd_47553 := by exact prefixLift 47553
  have htrace : WordTrace (prefixWord ++ tailWord_47553) baseStart_47553 baseEnd_47553 := by
    simpa [prefixWord, tailWord_47553, baseEnd_47553] using wordTrace_append hprefix tailTrace_47553
  have hstable : (prefixWord ++ tailWord_47553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47553).length < 2 ^ (prefixWord ++ tailWord_47553).sum := by decide
  have hdescent : baseEnd_47553 < baseStart_47553 := by decide
  rcases family_descends (prefixWord ++ tailWord_47553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47570 : List Nat := [3, 2, 2, 4, 2, 1, 1, 5]
def baseStart_47570 : Nat := 118140960795 + 47570 * 2 ^ 59
def prefixEnd_47570 : Nat := 4983230072969 + 3 ^ 40 * 47570 * 2
def baseEnd_47570 : Nat := 7237414736143441735181

theorem tailTrace_47570 : CollatzResearch.WordTrace tailWord_47570 prefixEnd_47570 7237414736143441735181 := by
  unfold tailWord_47570
  simp only [CollatzResearch.WordTrace]
  refine ⟨433755109417372288575041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1156680291779659436200109 433755109417372288575041)
  ·
    refine ⟨325316332063029216431281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 433755109417372288575041 325316332063029216431281)
    ·
      refine ⟨243987249047271912323461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325316332063029216431281 243987249047271912323461)
      ·
        refine ⟨45747609196363483560649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 243987249047271912323461 45747609196363483560649)
        ·
          refine ⟨34310706897272612670487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45747609196363483560649 34310706897272612670487)
          ·
            refine ⟨51466060345908919005731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34310706897272612670487 51466060345908919005731)
            ·
              refine ⟨77199090518863378508597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51466060345908919005731 77199090518863378508597)
              ·
                refine ⟨7237414736143441735181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77199090518863378508597 7237414736143441735181)
                ·
                  rfl

theorem cell20_47570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 5].length) (baseStart_47570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47570 prefixEnd_47570 := by exact prefixLift 47570
  have htrace : WordTrace (prefixWord ++ tailWord_47570) baseStart_47570 baseEnd_47570 := by
    simpa [prefixWord, tailWord_47570, baseEnd_47570] using wordTrace_append hprefix tailTrace_47570
  have hstable : (prefixWord ++ tailWord_47570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47570).length < 2 ^ (prefixWord ++ tailWord_47570).sum := by decide
  have hdescent : baseEnd_47570 < baseStart_47570 := by decide
  rcases family_descends (prefixWord ++ tailWord_47570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47581 : List Nat := [1, 4, 3, 1, 1, 1, 1, 5, 3]
def baseStart_47581 : Nat := 118140960795 + 47581 * 2 ^ 59
def prefixEnd_47581 : Nat := 4983230072969 + 3 ^ 40 * 47581 * 2
def baseEnd_47581 : Nat := 21717264908163175838831

theorem tailTrace_47581 : CollatzResearch.WordTrace tailWord_47581 prefixEnd_47581 21717264908163175838831 := by
  unfold tailWord_47581
  simp only [CollatzResearch.WordTrace]
  refine ⟨1735421640629638032950597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1156947760419758688633731 1735421640629638032950597)
  ·
    refine ⟨325391557618057131178237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1735421640629638032950597 325391557618057131178237)
    ·
      refine ⟨122021834106771424191839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 325391557618057131178237 122021834106771424191839)
      ·
        refine ⟨183032751160157136287759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122021834106771424191839 183032751160157136287759)
        ·
          refine ⟨274549126740235704431639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183032751160157136287759 274549126740235704431639)
          ·
            refine ⟨411823690110353556647459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274549126740235704431639 411823690110353556647459)
            ·
              refine ⟨617735535165530334971189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411823690110353556647459 617735535165530334971189)
              ·
                refine ⟨57912706421768468903549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 617735535165530334971189 57912706421768468903549)
                ·
                  refine ⟨21717264908163175838831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57912706421768468903549 21717264908163175838831)
                  ·
                    rfl

theorem cell20_47581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_47581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47581 prefixEnd_47581 := by exact prefixLift 47581
  have htrace : WordTrace (prefixWord ++ tailWord_47581) baseStart_47581 baseEnd_47581 := by
    simpa [prefixWord, tailWord_47581, baseEnd_47581] using wordTrace_append hprefix tailTrace_47581
  have hstable : (prefixWord ++ tailWord_47581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47581).length < 2 ^ (prefixWord ++ tailWord_47581).sum := by decide
  have hdescent : baseEnd_47581 < baseStart_47581 := by decide
  rcases family_descends (prefixWord ++ tailWord_47581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47595 : List Nat := [1, 1, 1, 1, 2, 3, 7, 4]
def baseStart_47595 : Nat := 118140960795 + 47595 * 2 ^ 59
def prefixEnd_47595 : Nat := 4983230072969 + 3 ^ 40 * 47595 * 2
def baseEnd_47595 : Nat := 7241218296547116457369

theorem tailTrace_47595 : CollatzResearch.WordTrace tailWord_47595 prefixEnd_47595 7241218296547116457369 := by
  unfold tailWord_47595
  simp only [CollatzResearch.WordTrace]
  refine ⟨1735932262578918423960239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1157288175052612282640159 1735932262578918423960239)
  ·
    refine ⟨2603898393868377635940359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1735932262578918423960239 2603898393868377635940359)
    ·
      refine ⟨3905847590802566453910539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2603898393868377635940359 3905847590802566453910539)
      ·
        refine ⟨5858771386203849680865809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3905847590802566453910539 5858771386203849680865809)
        ·
          refine ⟨4394078539652887260649357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5858771386203849680865809 4394078539652887260649357)
          ·
            refine ⟨1647779452369832722743509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4394078539652887260649357 1647779452369832722743509)
            ·
              refine ⟨38619830914917954439301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1647779452369832722743509 38619830914917954439301)
              ·
                refine ⟨7241218296547116457369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38619830914917954439301 7241218296547116457369)
                ·
                  rfl

theorem cell20_47595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 4].length) (baseStart_47595 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47595 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47595 prefixEnd_47595 := by exact prefixLift 47595
  have htrace : WordTrace (prefixWord ++ tailWord_47595) baseStart_47595 baseEnd_47595 := by
    simpa [prefixWord, tailWord_47595, baseEnd_47595] using wordTrace_append hprefix tailTrace_47595
  have hstable : (prefixWord ++ tailWord_47595).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47595).length < 2 ^ (prefixWord ++ tailWord_47595).sum := by decide
  have hdescent : baseEnd_47595 < baseStart_47595 := by decide
  rcases family_descends (prefixWord ++ tailWord_47595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47626 : List Nat := [3, 1, 2, 2, 2, 1, 4, 1, 4]
def baseStart_47626 : Nat := 118140960795 + 47626 * 2 ^ 59
def prefixEnd_47626 : Nat := 4983230072969 + 3 ^ 40 * 47626 * 2
def baseEnd_47626 : Nat := 21737804134343019338647

theorem tailTrace_47626 : CollatzResearch.WordTrace tailWord_47626 prefixEnd_47626 21737804134343019338647 := by
  unfold tailWord_47626
  simp only [CollatzResearch.WordTrace]
  refine ⟨434265731366652679584683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1158041950311073812225821 434265731366652679584683)
  ·
    refine ⟨651398597049979019377025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 434265731366652679584683 651398597049979019377025)
    ·
      refine ⟨488548947787484264532769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 651398597049979019377025 488548947787484264532769)
      ·
        refine ⟨366411710840613198399577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 488548947787484264532769 366411710840613198399577)
        ·
          refine ⟨274808783130459898799683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366411710840613198399577 274808783130459898799683)
          ·
            refine ⟨412213174695689848199525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274808783130459898799683 412213174695689848199525)
            ·
              refine ⟨77289970255441846537411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 412213174695689848199525 77289970255441846537411)
              ·
                refine ⟨115934955383162769806117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77289970255441846537411 115934955383162769806117)
                ·
                  refine ⟨21737804134343019338647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115934955383162769806117 21737804134343019338647)
                  ·
                    rfl

theorem cell20_47626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_47626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47626 prefixEnd_47626 := by exact prefixLift 47626
  have htrace : WordTrace (prefixWord ++ tailWord_47626) baseStart_47626 baseEnd_47626 := by
    simpa [prefixWord, tailWord_47626, baseEnd_47626] using wordTrace_append hprefix tailTrace_47626
  have hstable : (prefixWord ++ tailWord_47626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47626).length < 2 ^ (prefixWord ++ tailWord_47626).sum := by decide
  have hdescent : baseEnd_47626 < baseStart_47626 := by decide
  rcases family_descends (prefixWord ++ tailWord_47626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47681 : List Nat := [1, 2, 5, 1, 1, 4, 1, 1, 4]
def baseStart_47681 : Nat := 118140960795 + 47681 * 2 ^ 59
def prefixEnd_47681 : Nat := 4983230072969 + 3 ^ 40 * 47681 * 2
def baseEnd_47681 : Nat := 21762907633007272505089

theorem tailTrace_47681 : CollatzResearch.WordTrace tailWord_47681 prefixEnd_47681 21762907633007272505089 := by
  unfold tailWord_47681
  simp only [CollatzResearch.WordTrace]
  refine ⟨1739068940267355111590897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1159379293511570074393931 1739068940267355111590897)
  ·
    refine ⟨1304301705200516333693173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1739068940267355111590897 1304301705200516333693173)
    ·
      refine ⟨122278284862548406283735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1304301705200516333693173 122278284862548406283735)
      ·
        refine ⟨183417427293822609425603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122278284862548406283735 183417427293822609425603)
        ·
          refine ⟨275126140940733914138405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183417427293822609425603 275126140940733914138405)
          ·
            refine ⟨51586151426387608900951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 275126140940733914138405 51586151426387608900951)
            ·
              refine ⟨77379227139581413351427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51586151426387608900951 77379227139581413351427)
              ·
                refine ⟨116068840709372120027141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77379227139581413351427 116068840709372120027141)
                ·
                  refine ⟨21762907633007272505089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116068840709372120027141 21762907633007272505089)
                  ·
                    rfl

theorem cell20_47681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 4].length) (baseStart_47681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47681 prefixEnd_47681 := by exact prefixLift 47681
  have htrace : WordTrace (prefixWord ++ tailWord_47681) baseStart_47681 baseEnd_47681 := by
    simpa [prefixWord, tailWord_47681, baseEnd_47681] using wordTrace_append hprefix tailTrace_47681
  have hstable : (prefixWord ++ tailWord_47681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47681).length < 2 ^ (prefixWord ++ tailWord_47681).sum := by decide
  have hdescent : baseEnd_47681 < baseStart_47681 := by decide
  rcases family_descends (prefixWord ++ tailWord_47681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47684 : List Nat := [2, 3, 5, 1, 1, 1, 2, 5]
def baseStart_47684 : Nat := 118140960795 + 47684 * 2 ^ 59
def prefixEnd_47684 : Nat := 4983230072969 + 3 ^ 40 * 47684 * 2
def baseEnd_47684 : Nat := 7254758971584198468359

theorem tailTrace_47684 : CollatzResearch.WordTrace tailWord_47684 prefixEnd_47684 7254758971584198468359 := by
  unfold tailWord_47684
  simp only [CollatzResearch.WordTrace]
  refine ⟨869589179628243311975053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1159452239504324415966737 869589179628243311975053)
  ·
    refine ⟨326095942360591241990645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 869589179628243311975053 326095942360591241990645)
    ·
      refine ⟨30571494596305428936623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 326095942360591241990645 30571494596305428936623)
      ·
        refine ⟨45857241894458143404935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30571494596305428936623 45857241894458143404935)
        ·
          refine ⟨68785862841687215107403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45857241894458143404935 68785862841687215107403)
          ·
            refine ⟨103178794262530822661105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68785862841687215107403 103178794262530822661105)
            ·
              refine ⟨77384095696898116995829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103178794262530822661105 77384095696898116995829)
              ·
                refine ⟨7254758971584198468359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77384095696898116995829 7254758971584198468359)
                ·
                  rfl

theorem cell20_47684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 5].length) (baseStart_47684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47684 prefixEnd_47684 := by exact prefixLift 47684
  have htrace : WordTrace (prefixWord ++ tailWord_47684) baseStart_47684 baseEnd_47684 := by
    simpa [prefixWord, tailWord_47684, baseEnd_47684] using wordTrace_append hprefix tailTrace_47684
  have hstable : (prefixWord ++ tailWord_47684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47684).length < 2 ^ (prefixWord ++ tailWord_47684).sum := by decide
  have hdescent : baseEnd_47684 < baseStart_47684 := by decide
  rcases family_descends (prefixWord ++ tailWord_47684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47695 : List Nat := [1, 1, 2, 1, 1, 2, 8, 1, 3]
def baseStart_47695 : Nat := 118140960795 + 47695 * 2 ^ 59
def prefixEnd_47695 : Nat := 4983230072969 + 3 ^ 40 * 47695 * 2
def baseEnd_47695 : Nat := 21769297614485446038365

theorem tailTrace_47695 : CollatzResearch.WordTrace tailWord_47695 prefixEnd_47695 21769297614485446038365 := by
  unfold tailWord_47695
  simp only [CollatzResearch.WordTrace]
  refine ⟨1739579562216635502600539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1159719708144423668400359 1739579562216635502600539)
  ·
    refine ⟨2609369343324953253900809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1739579562216635502600539 2609369343324953253900809)
    ·
      refine ⟨1957027007493714940425607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2609369343324953253900809 1957027007493714940425607)
      ·
        refine ⟨2935540511240572410638411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1957027007493714940425607 2935540511240572410638411)
        ·
          refine ⟨4403310766860858615957617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2935540511240572410638411 4403310766860858615957617)
          ·
            refine ⟨3302483075145643961968213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4403310766860858615957617 3302483075145643961968213)
            ·
              refine ⟨38700973536863015179315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3302483075145643961968213 38700973536863015179315)
              ·
                refine ⟨58051460305294522768973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38700973536863015179315 58051460305294522768973)
                ·
                  refine ⟨21769297614485446038365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58051460305294522768973 21769297614485446038365)
                  ·
                    rfl

theorem cell20_47695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 3].length) (baseStart_47695 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47695 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47695 prefixEnd_47695 := by exact prefixLift 47695
  have htrace : WordTrace (prefixWord ++ tailWord_47695) baseStart_47695 baseEnd_47695 := by
    simpa [prefixWord, tailWord_47695, baseEnd_47695] using wordTrace_append hprefix tailTrace_47695
  have hstable : (prefixWord ++ tailWord_47695).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47695).length < 2 ^ (prefixWord ++ tailWord_47695).sum := by decide
  have hdescent : baseEnd_47695 < baseStart_47695 := by decide
  rcases family_descends (prefixWord ++ tailWord_47695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47730 : List Nat := [3, 2, 1, 2, 12]
def baseStart_47730 : Nat := 118140960795 + 47730 * 2 ^ 59
def prefixEnd_47730 : Nat := 4983230072969 + 3 ^ 40 * 47730 * 2
def baseEnd_47730 : Nat := 268953982323220739155

theorem tailTrace_47730 : CollatzResearch.WordTrace tailWord_47730 prefixEnd_47730 268953982323220739155 := by
  unfold tailWord_47730
  simp only [CollatzResearch.WordTrace]
  refine ⟨435214029272459120031161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1160570744726557653416429 435214029272459120031161)
  ·
    refine ⟨326410521954344340023371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 435214029272459120031161 326410521954344340023371)
    ·
      refine ⟨489615782931516510035057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326410521954344340023371 489615782931516510035057)
      ·
        refine ⟨367211837198637382526293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 489615782931516510035057 367211837198637382526293)
        ·
          refine ⟨268953982323220739155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 367211837198637382526293 268953982323220739155)
          ·
            rfl

theorem cell20_47730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 12].length) (baseStart_47730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47730 prefixEnd_47730 := by exact prefixLift 47730
  have htrace : WordTrace (prefixWord ++ tailWord_47730) baseStart_47730 baseEnd_47730 := by
    simpa [prefixWord, tailWord_47730, baseEnd_47730] using wordTrace_append hprefix tailTrace_47730
  have hstable : (prefixWord ++ tailWord_47730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47730).length < 2 ^ (prefixWord ++ tailWord_47730).sum := by decide
  have hdescent : baseEnd_47730 < baseStart_47730 := by decide
  rcases family_descends (prefixWord ++ tailWord_47730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47774 : List Nat := [4, 3, 1, 1, 1, 1, 4, 3, 2]
def baseStart_47774 : Nat := 118140960795 + 47774 * 2 ^ 59
def prefixEnd_47774 : Nat := 4983230072969 + 3 ^ 40 * 47774 * 2
def baseEnd_47774 : Nat := 21805355367112282404709

theorem tailTrace_47774 : CollatzResearch.WordTrace tailWord_47774 prefixEnd_47774 21805355367112282404709 := by
  unfold tailWord_47774
  simp only [CollatzResearch.WordTrace]
  refine ⟨217807616116303999340797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1161640619286954663150917 217807616116303999340797)
  ·
    refine ⟨81677856043613999752799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217807616116303999340797 81677856043613999752799)
    ·
      refine ⟨122516784065420999629199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81677856043613999752799 122516784065420999629199)
      ·
        refine ⟨183775176098131499443799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122516784065420999629199 183775176098131499443799)
        ·
          refine ⟨275662764147197249165699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183775176098131499443799 275662764147197249165699)
          ·
            refine ⟨413494146220795873748549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275662764147197249165699 413494146220795873748549)
            ·
              refine ⟨77530152416399226327853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 413494146220795873748549 77530152416399226327853)
              ·
                refine ⟨29073807156149709872945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77530152416399226327853 29073807156149709872945)
                ·
                  refine ⟨21805355367112282404709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29073807156149709872945 21805355367112282404709)
                  ·
                    rfl

theorem cell20_47774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_47774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47774 prefixEnd_47774 := by exact prefixLift 47774
  have htrace : WordTrace (prefixWord ++ tailWord_47774) baseStart_47774 baseEnd_47774 := by
    simpa [prefixWord, tailWord_47774, baseEnd_47774] using wordTrace_append hprefix tailTrace_47774
  have hstable : (prefixWord ++ tailWord_47774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47774).length < 2 ^ (prefixWord ++ tailWord_47774).sum := by decide
  have hdescent : baseEnd_47774 < baseStart_47774 := by decide
  rcases family_descends (prefixWord ++ tailWord_47774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47813 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 9]
def baseStart_47813 : Nat := 118140960795 + 47813 * 2 ^ 59
def prefixEnd_47813 : Nat := 4983230072969 + 3 ^ 40 * 47813 * 2
def baseEnd_47813 : Nat := 21823156029801480104549

theorem tailTrace_47813 : CollatzResearch.WordTrace tailWord_47813 prefixEnd_47813 21823156029801480104549 := by
  unfold tailWord_47813
  simp only [CollatzResearch.WordTrace]
  refine ⟨1743883375789141655396093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1162588917192761103597395 1743883375789141655396093)
  ·
    refine ⟨653956265920928120773535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1743883375789141655396093 653956265920928120773535)
    ·
      refine ⟨980934398881392181160303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 653956265920928120773535 980934398881392181160303)
      ·
        refine ⟨1471401598322088271740455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 980934398881392181160303 1471401598322088271740455)
        ·
          refine ⟨2207102397483132407610683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1471401598322088271740455 2207102397483132407610683)
          ·
            refine ⟨3310653596224698611416025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2207102397483132407610683 3310653596224698611416025)
            ·
              refine ⟨2482990197168523958562019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3310653596224698611416025 2482990197168523958562019)
              ·
                refine ⟨3724485295752785937843029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2482990197168523958562019 3724485295752785937843029)
                ·
                  refine ⟨21823156029801480104549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3724485295752785937843029 21823156029801480104549)
                  ·
                    rfl

theorem cell20_47813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_47813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47813 prefixEnd_47813 := by exact prefixLift 47813
  have htrace : WordTrace (prefixWord ++ tailWord_47813) baseStart_47813 baseEnd_47813 := by
    simpa [prefixWord, tailWord_47813, baseEnd_47813] using wordTrace_append hprefix tailTrace_47813
  have hstable : (prefixWord ++ tailWord_47813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47813).length < 2 ^ (prefixWord ++ tailWord_47813).sum := by decide
  have hdescent : baseEnd_47813 < baseStart_47813 := by decide
  rcases family_descends (prefixWord ++ tailWord_47813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47829 : List Nat := [1, 3, 2, 5, 1, 2, 1, 3, 2]
def baseStart_47829 : Nat := 118140960795 + 47829 * 2 ^ 59
def prefixEnd_47829 : Nat := 4983230072969 + 3 ^ 40 * 47829 * 2
def baseEnd_47829 : Nat := 21830458865776535571151

theorem tailTrace_47829 : CollatzResearch.WordTrace tailWord_47829 prefixEnd_47829 21830458865776535571151 := by
  unfold tailWord_47829
  simp only [CollatzResearch.WordTrace]
  refine ⟨1744466943731176387978541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1162977962487450925319027 1744466943731176387978541)
  ·
    refine ⟨654175103899191145491953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1744466943731176387978541 654175103899191145491953)
    ·
      refine ⟨490631327924393359118965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 654175103899191145491953 490631327924393359118965)
      ·
        refine ⟨45996686992911877417403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 490631327924393359118965 45996686992911877417403)
        ·
          refine ⟨68995030489367816126105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45996686992911877417403 68995030489367816126105)
          ·
            refine ⟨51746272867025862094579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68995030489367816126105 51746272867025862094579)
            ·
              refine ⟨77619409300538793141869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51746272867025862094579 77619409300538793141869)
              ·
                refine ⟨29107278487702047428201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77619409300538793141869 29107278487702047428201)
                ·
                  refine ⟨21830458865776535571151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29107278487702047428201 21830458865776535571151)
                  ·
                    rfl

theorem cell20_47829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 3, 2].length) (baseStart_47829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47829 prefixEnd_47829 := by exact prefixLift 47829
  have htrace : WordTrace (prefixWord ++ tailWord_47829) baseStart_47829 baseEnd_47829 := by
    simpa [prefixWord, tailWord_47829, baseEnd_47829] using wordTrace_append hprefix tailTrace_47829
  have hstable : (prefixWord ++ tailWord_47829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47829).length < 2 ^ (prefixWord ++ tailWord_47829).sum := by decide
  have hdescent : baseEnd_47829 < baseStart_47829 := by decide
  rcases family_descends (prefixWord ++ tailWord_47829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47844 : List Nat := [2, 3, 1, 1, 1, 4, 8]
def baseStart_47844 : Nat := 118140960795 + 47844 * 2 ^ 59
def prefixEnd_47844 : Nat := 4983230072969 + 3 ^ 40 * 47844 * 2
def baseEnd_47844 : Nat := 2426367252722572230121

theorem tailTrace_47844 : CollatzResearch.WordTrace tailWord_47844 prefixEnd_47844 2426367252722572230121 := by
  unfold tailWord_47844
  simp only [CollatzResearch.WordTrace]
  refine ⟨872507019338416974887293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1163342692451222633183057 872507019338416974887293)
  ·
    refine ⟨327190132251906365582735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 872507019338416974887293 327190132251906365582735)
    ·
      refine ⟨490785198377859548374103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327190132251906365582735 490785198377859548374103)
      ·
        refine ⟨736177797566789322561155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490785198377859548374103 736177797566789322561155)
        ·
          refine ⟨1104266696350183983841733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 736177797566789322561155 1104266696350183983841733)
          ·
            refine ⟨207050005565659496970325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1104266696350183983841733 207050005565659496970325)
            ·
              refine ⟨2426367252722572230121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 207050005565659496970325 2426367252722572230121)
              ·
                rfl

theorem cell20_47844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 8].length) (baseStart_47844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47844 prefixEnd_47844 := by exact prefixLift 47844
  have htrace : WordTrace (prefixWord ++ tailWord_47844) baseStart_47844 baseEnd_47844 := by
    simpa [prefixWord, tailWord_47844, baseEnd_47844] using wordTrace_append hprefix tailTrace_47844
  have hstable : (prefixWord ++ tailWord_47844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47844).length < 2 ^ (prefixWord ++ tailWord_47844).sum := by decide
  have hdescent : baseEnd_47844 < baseStart_47844 := by decide
  rcases family_descends (prefixWord ++ tailWord_47844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47854 : List Nat := [4, 1, 2, 1, 1, 3, 3, 1, 4]
def baseStart_47854 : Nat := 118140960795 + 47854 * 2 ^ 59
def prefixEnd_47854 : Nat := 4983230072969 + 3 ^ 40 * 47854 * 2
def baseEnd_47854 : Nat := 21841869546987559737715

theorem tailTrace_47854 : CollatzResearch.WordTrace tailWord_47854 prefixEnd_47854 21841869546987559737715 := by
  unfold tailWord_47854
  simp only [CollatzResearch.WordTrace]
  refine ⟨218172346080075707204827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1163585845760403771759077 218172346080075707204827)
  ·
    refine ⟨327258519120113560807241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218172346080075707204827 327258519120113560807241)
    ·
      refine ⟨245443889340085170605431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327258519120113560807241 245443889340085170605431)
      ·
        refine ⟨368165834010127755908147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245443889340085170605431 368165834010127755908147)
        ·
          refine ⟨552248751015191633862221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368165834010127755908147 552248751015191633862221)
          ·
            refine ⟨207093281630696862698333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 552248751015191633862221 207093281630696862698333)
            ·
              refine ⟨77659980611511323511875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 207093281630696862698333 77659980611511323511875)
              ·
                refine ⟨116489970917266985267813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77659980611511323511875 116489970917266985267813)
                ·
                  refine ⟨21841869546987559737715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116489970917266985267813 21841869546987559737715)
                  ·
                    rfl

theorem cell20_47854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_47854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47854 prefixEnd_47854 := by exact prefixLift 47854
  have htrace : WordTrace (prefixWord ++ tailWord_47854) baseStart_47854 baseEnd_47854 := by
    simpa [prefixWord, tailWord_47854, baseEnd_47854] using wordTrace_append hprefix tailTrace_47854
  have hstable : (prefixWord ++ tailWord_47854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47854).length < 2 ^ (prefixWord ++ tailWord_47854).sum := by decide
  have hdescent : baseEnd_47854 < baseStart_47854 := by decide
  rcases family_descends (prefixWord ++ tailWord_47854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47882 : List Nat := [3, 1, 2, 2, 1, 2, 1, 8]
def baseStart_47882 : Nat := 118140960795 + 47882 * 2 ^ 59
def prefixEnd_47882 : Nat := 4983230072969 + 3 ^ 40 * 47882 * 2
def baseEnd_47882 : Nat := 7284883169981302268089

theorem tailTrace_47882 : CollatzResearch.WordTrace tailWord_47882 prefixEnd_47882 7284883169981302268089 := by
  unfold tailWord_47882
  simp only [CollatzResearch.WordTrace]
  refine ⟨436600003134791609914475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1164266675026110959771933 436600003134791609914475)
  ·
    refine ⟨654900004702187414871713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 436600003134791609914475 654900004702187414871713)
    ·
      refine ⟨491175003526640561153785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 654900004702187414871713 491175003526640561153785)
      ·
        refine ⟨368381252644980420865339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 491175003526640561153785 368381252644980420865339)
        ·
          refine ⟨552571878967470631298009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368381252644980420865339 552571878967470631298009)
          ·
            refine ⟨414428909225602973473507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 552571878967470631298009 414428909225602973473507)
            ·
              refine ⟨621643363838404460210261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414428909225602973473507 621643363838404460210261)
              ·
                refine ⟨7284883169981302268089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 621643363838404460210261 7284883169981302268089)
                ·
                  rfl

theorem cell20_47882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_47882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47882 prefixEnd_47882 := by exact prefixLift 47882
  have htrace : WordTrace (prefixWord ++ tailWord_47882) baseStart_47882 baseEnd_47882 := by
    simpa [prefixWord, tailWord_47882, baseEnd_47882] using wordTrace_append hprefix tailTrace_47882
  have hstable : (prefixWord ++ tailWord_47882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47882).length < 2 ^ (prefixWord ++ tailWord_47882).sum := by decide
  have hdescent : baseEnd_47882 < baseStart_47882 := by decide
  rcases family_descends (prefixWord ++ tailWord_47882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47889 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 7]
def baseStart_47889 : Nat := 118140960795 + 47889 * 2 ^ 59
def prefixEnd_47889 : Nat := 4983230072969 + 3 ^ 40 * 47889 * 2
def baseEnd_47889 : Nat := 21857844500682993570905

theorem tailTrace_47889 : CollatzResearch.WordTrace tailWord_47889 prefixEnd_47889 21857844500682993570905 := by
  unfold tailWord_47889
  simp only [CollatzResearch.WordTrace]
  refine ⟨1746655323513806635162721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1164436882342537756775147 1746655323513806635162721)
  ·
    refine ⟨1309991492635354976372041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1746655323513806635162721 1309991492635354976372041)
    ·
      refine ⟨982493619476516232279031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1309991492635354976372041 982493619476516232279031)
      ·
        refine ⟨1473740429214774348418547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 982493619476516232279031 1473740429214774348418547)
        ·
          refine ⟨2210610643822161522627821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1473740429214774348418547 2210610643822161522627821)
          ·
            refine ⟨828978991433310570985433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2210610643822161522627821 828978991433310570985433)
            ·
              refine ⟨621734243574982928239075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 828978991433310570985433 621734243574982928239075)
              ·
                refine ⟨932601365362474392358613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 621734243574982928239075 932601365362474392358613)
                ·
                  refine ⟨21857844500682993570905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 932601365362474392358613 21857844500682993570905)
                  ·
                    rfl

theorem cell20_47889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_47889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47889 prefixEnd_47889 := by exact prefixLift 47889
  have htrace : WordTrace (prefixWord ++ tailWord_47889) baseStart_47889 baseEnd_47889 := by
    simpa [prefixWord, tailWord_47889, baseEnd_47889] using wordTrace_append hprefix tailTrace_47889
  have hstable : (prefixWord ++ tailWord_47889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47889).length < 2 ^ (prefixWord ++ tailWord_47889).sum := by decide
  have hdescent : baseEnd_47889 < baseStart_47889 := by decide
  rcases family_descends (prefixWord ++ tailWord_47889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47930 : List Nat := [3, 1, 1, 1, 6, 1, 1, 2, 4]
def baseStart_47930 : Nat := 118140960795 + 47930 * 2 ^ 59
def prefixEnd_47930 : Nat := 4983230072969 + 3 ^ 40 * 47930 * 2
def baseEnd_47930 : Nat := 21876558017869073204071

theorem tailTrace_47930 : CollatzResearch.WordTrace tailWord_47930 prefixEnd_47930 21876558017869073204071 := by
  unfold tailWord_47930
  simp only [CollatzResearch.WordTrace]
  refine ⟨437037679091317659351311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1165433810910180424936829 437037679091317659351311)
  ·
    refine ⟨655556518636976489026967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 437037679091317659351311 655556518636976489026967)
    ·
      refine ⟨983334777955464733540451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 655556518636976489026967 983334777955464733540451)
      ·
        refine ⟨1475002166933197100310677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 983334777955464733540451 1475002166933197100310677)
        ·
          refine ⟨69140726574993614077063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1475002166933197100310677 69140726574993614077063)
          ·
            refine ⟨103711089862490421115595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69140726574993614077063 103711089862490421115595)
            ·
              refine ⟨155566634793735631673393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103711089862490421115595 155566634793735631673393)
              ·
                refine ⟨116674976095301723755045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155566634793735631673393 116674976095301723755045)
                ·
                  refine ⟨21876558017869073204071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116674976095301723755045 21876558017869073204071)
                  ·
                    rfl

theorem cell20_47930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_47930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47930 prefixEnd_47930 := by exact prefixLift 47930
  have htrace : WordTrace (prefixWord ++ tailWord_47930) baseStart_47930 baseEnd_47930 := by
    simpa [prefixWord, tailWord_47930, baseEnd_47930] using wordTrace_append hprefix tailTrace_47930
  have hstable : (prefixWord ++ tailWord_47930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47930).length < 2 ^ (prefixWord ++ tailWord_47930).sum := by decide
  have hdescent : baseEnd_47930 < baseStart_47930 := by decide
  rcases family_descends (prefixWord ++ tailWord_47930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47961 : List Nat := [1, 2, 1, 2, 2, 6, 1, 2, 3]
def baseStart_47961 : Nat := 118140960795 + 47961 * 2 ^ 59
def prefixEnd_47961 : Nat := 4983230072969 + 3 ^ 40 * 47961 * 2
def baseEnd_47961 : Nat := 21890707262570743170611

theorem tailTrace_47961 : CollatzResearch.WordTrace tailWord_47961 prefixEnd_47961 21890707262570743170611 := by
  unfold tailWord_47961
  simp only [CollatzResearch.WordTrace]
  refine ⟨1749281379252962931783737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1166187586168641954522491 1749281379252962931783737)
  ·
    refine ⟨1311961034439722198837803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1749281379252962931783737 1311961034439722198837803)
    ·
      refine ⟨1967941551659583298256705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1311961034439722198837803 1967941551659583298256705)
      ·
        refine ⟨1475956163744687473692529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1967941551659583298256705 1475956163744687473692529)
        ·
          refine ⟨1106967122808515605269397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1475956163744687473692529 1106967122808515605269397)
          ·
            refine ⟨51889083881649168997003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1106967122808515605269397 51889083881649168997003)
            ·
              refine ⟨77833625822473753495505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51889083881649168997003 77833625822473753495505)
              ·
                refine ⟨58375219366855315121629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77833625822473753495505 58375219366855315121629)
                ·
                  refine ⟨21890707262570743170611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58375219366855315121629 21890707262570743170611)
                  ·
                    rfl

theorem cell20_47961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 3].length) (baseStart_47961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47961 prefixEnd_47961 := by exact prefixLift 47961
  have htrace : WordTrace (prefixWord ++ tailWord_47961) baseStart_47961 baseEnd_47961 := by
    simpa [prefixWord, tailWord_47961, baseEnd_47961] using wordTrace_append hprefix tailTrace_47961
  have hstable : (prefixWord ++ tailWord_47961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47961).length < 2 ^ (prefixWord ++ tailWord_47961).sum := by decide
  have hdescent : baseEnd_47961 < baseStart_47961 := by decide
  rcases family_descends (prefixWord ++ tailWord_47961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47968 : List Nat := [2, 1, 1, 3, 3, 1, 1, 6, 2]
def baseStart_47968 : Nat := 118140960795 + 47968 * 2 ^ 59
def prefixEnd_47968 : Nat := 4983230072969 + 3 ^ 40 * 47968 * 2
def baseEnd_47968 : Nat := 21893902253309829937249

theorem tailTrace_47968 : CollatzResearch.WordTrace tailWord_47968 prefixEnd_47968 21893902253309829937249 := by
  unfold tailWord_47968
  simp only [CollatzResearch.WordTrace]
  refine ⟨874768345113801563644279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1166357793485068751525705 874768345113801563644279)
  ·
    refine ⟨1312152517670702345466419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 874768345113801563644279 1312152517670702345466419)
    ·
      refine ⟨1968228776506053518199629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1312152517670702345466419 1968228776506053518199629)
      ·
        refine ⟨738085791189770069324861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1968228776506053518199629 738085791189770069324861)
        ·
          refine ⟨276782171696163775996823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 738085791189770069324861 276782171696163775996823)
          ·
            refine ⟨415173257544245663995235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276782171696163775996823 415173257544245663995235)
            ·
              refine ⟨622759886316368495992853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415173257544245663995235 622759886316368495992853)
              ·
                refine ⟨29191869671079773249665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 622759886316368495992853 29191869671079773249665)
                ·
                  refine ⟨21893902253309829937249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29191869671079773249665 21893902253309829937249)
                  ·
                    rfl

theorem cell20_47968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 6, 2].length) (baseStart_47968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47968 prefixEnd_47968 := by exact prefixLift 47968
  have htrace : WordTrace (prefixWord ++ tailWord_47968) baseStart_47968 baseEnd_47968 := by
    simpa [prefixWord, tailWord_47968, baseEnd_47968] using wordTrace_append hprefix tailTrace_47968
  have hstable : (prefixWord ++ tailWord_47968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47968).length < 2 ^ (prefixWord ++ tailWord_47968).sum := by decide
  have hdescent : baseEnd_47968 < baseStart_47968 := by decide
  rcases family_descends (prefixWord ++ tailWord_47968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_47998 : List Nat := [4, 2, 3, 1, 3, 1, 1, 3, 2]
def baseStart_47998 : Nat := 118140960795 + 47998 * 2 ^ 59
def prefixEnd_47998 : Nat := 4983230072969 + 3 ^ 40 * 47998 * 2
def baseEnd_47998 : Nat := 21907595070763058937127

theorem tailTrace_47998 : CollatzResearch.WordTrace tailWord_47998 prefixEnd_47998 21907595070763058937127 := by
  unfold tailWord_47998
  simp only [CollatzResearch.WordTrace]
  refine ⟨218828860014864781360081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1167087253412612167253765 218828860014864781360081)
  ·
    refine ⟨164121645011148586020061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 218828860014864781360081 164121645011148586020061)
    ·
      refine ⟨61545616879180719757523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164121645011148586020061 61545616879180719757523)
      ·
        refine ⟨92318425318771079636285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61545616879180719757523 92318425318771079636285)
        ·
          refine ⟨34619409494539154863607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92318425318771079636285 34619409494539154863607)
          ·
            refine ⟨51929114241808732295411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34619409494539154863607 51929114241808732295411)
            ·
              refine ⟨77893671362713098443117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51929114241808732295411 77893671362713098443117)
              ·
                refine ⟨29210126761017411916169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77893671362713098443117 29210126761017411916169)
                ·
                  refine ⟨21907595070763058937127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29210126761017411916169 21907595070763058937127)
                  ·
                    rfl

theorem cell20_47998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_47998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_47998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_47998 prefixEnd_47998 := by exact prefixLift 47998
  have htrace : WordTrace (prefixWord ++ tailWord_47998) baseStart_47998 baseEnd_47998 := by
    simpa [prefixWord, tailWord_47998, baseEnd_47998] using wordTrace_append hprefix tailTrace_47998
  have hstable : (prefixWord ++ tailWord_47998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_47998).length < 2 ^ (prefixWord ++ tailWord_47998).sum := by decide
  have hdescent : baseEnd_47998 < baseStart_47998 := by decide
  rcases family_descends (prefixWord ++ tailWord_47998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48003 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 7]
def baseStart_48003 : Nat := 118140960795 + 48003 * 2 ^ 59
def prefixEnd_48003 : Nat := 4983230072969 + 3 ^ 40 * 48003 * 2
def baseEnd_48003 : Nat := 21909877207005263770439

theorem tailTrace_48003 : CollatzResearch.WordTrace tailWord_48003 prefixEnd_48003 21909877207005263770439 := by
  unfold tailWord_48003
  simp only [CollatzResearch.WordTrace]
  refine ⟨1750813245100804104812663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1167208830067202736541775 1750813245100804104812663)
  ·
    refine ⟨2626219867651206157218995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1750813245100804104812663 2626219867651206157218995)
    ·
      refine ⟨3939329801476809235828493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2626219867651206157218995 3939329801476809235828493)
      ·
        refine ⟨1477248675553803463435685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3939329801476809235828493 1477248675553803463435685)
        ·
          refine ⟨276984126666338149394191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1477248675553803463435685 276984126666338149394191)
          ·
            refine ⟨415476189999507224091287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276984126666338149394191 415476189999507224091287)
            ·
              refine ⟨623214284999260836136931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415476189999507224091287 623214284999260836136931)
              ·
                refine ⟨934821427498891254205397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 623214284999260836136931 934821427498891254205397)
                ·
                  refine ⟨21909877207005263770439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 934821427498891254205397 21909877207005263770439)
                  ·
                    rfl

theorem cell20_48003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 7].length) (baseStart_48003 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48003 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48003 prefixEnd_48003 := by exact prefixLift 48003
  have htrace : WordTrace (prefixWord ++ tailWord_48003) baseStart_48003 baseEnd_48003 := by
    simpa [prefixWord, tailWord_48003, baseEnd_48003] using wordTrace_append hprefix tailTrace_48003
  have hstable : (prefixWord ++ tailWord_48003).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48003).length < 2 ^ (prefixWord ++ tailWord_48003).sum := by decide
  have hdescent : baseEnd_48003 < baseStart_48003 := by decide
  rcases family_descends (prefixWord ++ tailWord_48003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48020 : List Nat := [2, 4, 2, 1, 1, 1, 1, 3, 5]
def baseStart_48020 : Nat := 118140960795 + 48020 * 2 ^ 59
def prefixEnd_48020 : Nat := 4983230072969 + 3 ^ 40 * 48020 * 2
def baseEnd_48020 : Nat := 21917636470228760203703

theorem tailTrace_48020 : CollatzResearch.WordTrace tailWord_48020 prefixEnd_48020 21917636470228760203703 := by
  unfold tailWord_48020
  simp only [CollatzResearch.WordTrace]
  refine ⟨875716643019608004090757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1167622190692810672121009 875716643019608004090757)
  ·
    refine ⟨164196870566176500767017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 875716643019608004090757 164196870566176500767017)
    ·
      refine ⟨123147652924632375575263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164196870566176500767017 123147652924632375575263)
      ·
        refine ⟨184721479386948563362895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123147652924632375575263 184721479386948563362895)
        ·
          refine ⟨277082219080422845044343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184721479386948563362895 277082219080422845044343)
          ·
            refine ⟨415623328620634267566515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277082219080422845044343 415623328620634267566515)
            ·
              refine ⟨623434992930951401349773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415623328620634267566515 623434992930951401349773)
              ·
                refine ⟨233788122349106775506165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 623434992930951401349773 233788122349106775506165)
                ·
                  refine ⟨21917636470228760203703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 233788122349106775506165 21917636470228760203703)
                  ·
                    rfl

theorem cell20_48020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_48020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48020 prefixEnd_48020 := by exact prefixLift 48020
  have htrace : WordTrace (prefixWord ++ tailWord_48020) baseStart_48020 baseEnd_48020 := by
    simpa [prefixWord, tailWord_48020, baseEnd_48020] using wordTrace_append hprefix tailTrace_48020
  have hstable : (prefixWord ++ tailWord_48020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48020).length < 2 ^ (prefixWord ++ tailWord_48020).sum := by decide
  have hdescent : baseEnd_48020 < baseStart_48020 := by decide
  rcases family_descends (prefixWord ++ tailWord_48020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48023 : List Nat := [1, 1, 3, 3, 1, 2, 5, 2, 2]
def baseStart_48023 : Nat := 118140960795 + 48023 * 2 ^ 59
def prefixEnd_48023 : Nat := 4983230072969 + 3 ^ 40 * 48023 * 2
def baseEnd_48023 : Nat := 21919005751974083103691

theorem tailTrace_48023 : CollatzResearch.WordTrace tailWord_48023 prefixEnd_48023 21919005751974083103691 := by
  unfold tailWord_48023
  simp only [CollatzResearch.WordTrace]
  refine ⟨1751542705028347520540723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1167695136685565013693815 1751542705028347520540723)
  ·
    refine ⟨2627314057542521280811085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1751542705028347520540723 2627314057542521280811085)
    ·
      refine ⟨985242771578445480304157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2627314057542521280811085 985242771578445480304157)
      ·
        refine ⟨369466039341917055114059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 985242771578445480304157 369466039341917055114059)
        ·
          refine ⟨554199059012875582671089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369466039341917055114059 554199059012875582671089)
          ·
            refine ⟨415649294259656687003317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 554199059012875582671089 415649294259656687003317)
            ·
              refine ⟨38967121336842814406561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 415649294259656687003317 38967121336842814406561)
              ·
                refine ⟨29225341002632110804921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38967121336842814406561 29225341002632110804921)
                ·
                  refine ⟨21919005751974083103691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29225341002632110804921 21919005751974083103691)
                  ·
                    rfl

theorem cell20_48023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 2, 2].length) (baseStart_48023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48023 prefixEnd_48023 := by exact prefixLift 48023
  have htrace : WordTrace (prefixWord ++ tailWord_48023) baseStart_48023 baseEnd_48023 := by
    simpa [prefixWord, tailWord_48023, baseEnd_48023] using wordTrace_append hprefix tailTrace_48023
  have hstable : (prefixWord ++ tailWord_48023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48023).length < 2 ^ (prefixWord ++ tailWord_48023).sum := by decide
  have hdescent : baseEnd_48023 < baseStart_48023 := by decide
  rcases family_descends (prefixWord ++ tailWord_48023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48068 : List Nat := [2, 3, 3, 3, 2, 7]
def baseStart_48068 : Nat := 118140960795 + 48068 * 2 ^ 59
def prefixEnd_48068 : Nat := 4983230072969 + 3 ^ 40 * 48068 * 2
def baseEnd_48068 : Nat := 812575739931626911241

theorem tailTrace_48068 : CollatzResearch.WordTrace tailWord_48068 prefixEnd_48068 812575739931626911241 := by
  unfold tailWord_48068
  simp only [CollatzResearch.WordTrace]
  refine ⟨876591994932660102964429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1168789326576880137285905 876591994932660102964429)
  ·
    refine ⟨328721998099747538611661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 876591994932660102964429 328721998099747538611661)
    ·
      refine ⟨123270749287405326979373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 328721998099747538611661 123270749287405326979373)
      ·
        refine ⟨46226530982776997617265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123270749287405326979373 46226530982776997617265)
        ·
          refine ⟨34669898237082748212949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46226530982776997617265 34669898237082748212949)
          ·
            refine ⟨812575739931626911241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 34669898237082748212949 812575739931626911241)
            ·
              rfl

theorem cell20_48068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 7].length) (baseStart_48068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48068 prefixEnd_48068 := by exact prefixLift 48068
  have htrace : WordTrace (prefixWord ++ tailWord_48068) baseStart_48068 baseEnd_48068 := by
    simpa [prefixWord, tailWord_48068, baseEnd_48068] using wordTrace_append hprefix tailTrace_48068
  have hstable : (prefixWord ++ tailWord_48068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48068).length < 2 ^ (prefixWord ++ tailWord_48068).sum := by decide
  have hdescent : baseEnd_48068 < baseStart_48068 := by decide
  rcases family_descends (prefixWord ++ tailWord_48068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48070 : List Nat := [6, 1, 3, 1, 1, 2, 2, 2, 2]
def baseStart_48070 : Nat := 118140960795 + 48070 * 2 ^ 59
def prefixEnd_48070 : Nat := 4983230072969 + 3 ^ 40 * 48070 * 2
def baseEnd_48070 : Nat := 21940457832650808536833

theorem tailTrace_48070 : CollatzResearch.WordTrace tailWord_48070 prefixEnd_48070 21940457832650808536833 := by
  unfold tailWord_48070
  simp only [CollatzResearch.WordTrace]
  refine ⟨54789279245564829609427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1168837957238716365001109 54789279245564829609427)
  ·
    refine ⟨82183918868347244414141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54789279245564829609427 82183918868347244414141)
    ·
      refine ⟨30818969575630216655303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82183918868347244414141 30818969575630216655303)
      ·
        refine ⟨46228454363445324982955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30818969575630216655303 46228454363445324982955)
        ·
          refine ⟨69342681545167987474433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46228454363445324982955 69342681545167987474433)
          ·
            refine ⟨52007011158875990605825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69342681545167987474433 52007011158875990605825)
            ·
              refine ⟨39005258369156992954369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52007011158875990605825 39005258369156992954369)
              ·
                refine ⟨29253943776867744715777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39005258369156992954369 29253943776867744715777)
                ·
                  refine ⟨21940457832650808536833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29253943776867744715777 21940457832650808536833)
                  ·
                    rfl

theorem cell20_48070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_48070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48070 prefixEnd_48070 := by exact prefixLift 48070
  have htrace : WordTrace (prefixWord ++ tailWord_48070) baseStart_48070 baseEnd_48070 := by
    simpa [prefixWord, tailWord_48070, baseEnd_48070] using wordTrace_append hprefix tailTrace_48070
  have hstable : (prefixWord ++ tailWord_48070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48070).length < 2 ^ (prefixWord ++ tailWord_48070).sum := by decide
  have hdescent : baseEnd_48070 < baseStart_48070 := by decide
  rcases family_descends (prefixWord ++ tailWord_48070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48072 : List Nat := [2, 1, 3, 1, 5, 8]
def baseStart_48072 : Nat := 118140960795 + 48072 * 2 ^ 59
def prefixEnd_48072 : Nat := 4983230072969 + 3 ^ 40 * 48072 * 2
def baseEnd_48072 : Nat := 812643358783247795191

theorem tailTrace_48072 : CollatzResearch.WordTrace tailWord_48072 prefixEnd_48072 812643358783247795191 := by
  unfold tailWord_48072
  simp only [CollatzResearch.WordTrace]
  refine ⟨876664940925414444537235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1168886587900552592716313 876664940925414444537235)
  ·
    refine ⟨1314997411388121666805853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 876664940925414444537235 1314997411388121666805853)
    ·
      refine ⟨493124029270545625052195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1314997411388121666805853 493124029270545625052195)
      ·
        refine ⟨739686043905818437578293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493124029270545625052195 739686043905818437578293)
        ·
          refine ⟨69345566616170478522965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 739686043905818437578293 69345566616170478522965)
          ·
            refine ⟨812643358783247795191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 69345566616170478522965 812643358783247795191)
            ·
              rfl

theorem cell20_48072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 8].length) (baseStart_48072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48072 prefixEnd_48072 := by exact prefixLift 48072
  have htrace : WordTrace (prefixWord ++ tailWord_48072) baseStart_48072 baseEnd_48072 := by
    simpa [prefixWord, tailWord_48072, baseEnd_48072] using wordTrace_append hprefix tailTrace_48072
  have hstable : (prefixWord ++ tailWord_48072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48072).length < 2 ^ (prefixWord ++ tailWord_48072).sum := by decide
  have hdescent : baseEnd_48072 < baseStart_48072 := by decide
  rcases family_descends (prefixWord ++ tailWord_48072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48078 : List Nat := [4, 1, 1, 1, 2, 5, 2, 2, 2]
def baseStart_48078 : Nat := 118140960795 + 48078 * 2 ^ 59
def prefixEnd_48078 : Nat := 4983230072969 + 3 ^ 40 * 48078 * 2
def baseEnd_48078 : Nat := 21944109250638336270133

theorem tailTrace_48078 : CollatzResearch.WordTrace tailWord_48078 prefixEnd_48078 21944109250638336270133 := by
  unfold tailWord_48078
  simp only [CollatzResearch.WordTrace]
  refine ⟨219193589978636489224111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1169032479886061275861925 219193589978636489224111)
  ·
    refine ⟨328790384967954733836167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219193589978636489224111 328790384967954733836167)
    ·
      refine ⟨493185577451932100754251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328790384967954733836167 493185577451932100754251)
      ·
        refine ⟨739778366177898151131377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493185577451932100754251 739778366177898151131377)
        ·
          refine ⟨554833774633423613348533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 739778366177898151131377 554833774633423613348533)
          ·
            refine ⟨52015666371883463751425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 554833774633423613348533 52015666371883463751425)
            ·
              refine ⟨39011749778912597813569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52015666371883463751425 39011749778912597813569)
              ·
                refine ⟨29258812334184448360177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39011749778912597813569 29258812334184448360177)
                ·
                  refine ⟨21944109250638336270133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29258812334184448360177 21944109250638336270133)
                  ·
                    rfl

theorem cell20_48078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_48078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48078 prefixEnd_48078 := by exact prefixLift 48078
  have htrace : WordTrace (prefixWord ++ tailWord_48078) baseStart_48078 baseEnd_48078 := by
    simpa [prefixWord, tailWord_48078, baseEnd_48078] using wordTrace_append hprefix tailTrace_48078
  have hstable : (prefixWord ++ tailWord_48078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48078).length < 2 ^ (prefixWord ++ tailWord_48078).sum := by decide
  have hdescent : baseEnd_48078 < baseStart_48078 := by decide
  rcases family_descends (prefixWord ++ tailWord_48078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48089 : List Nat := [1, 2, 1, 2, 5, 3, 1, 5]
def baseStart_48089 : Nat := 118140960795 + 48089 * 2 ^ 59
def prefixEnd_48089 : Nat := 4983230072969 + 3 ^ 40 * 48089 * 2
def baseEnd_48089 : Nat := 7316376650123728967807

theorem tailTrace_48089 : CollatzResearch.WordTrace tailWord_48089 prefixEnd_48089 7316376650123728967807 := by
  unfold tailWord_48089
  simp only [CollatzResearch.WordTrace]
  refine ⟨1753949922789240792443321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1169299948526160528295547 1753949922789240792443321)
  ·
    refine ⟨1315462442091930594332491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1753949922789240792443321 1315462442091930594332491)
    ·
      refine ⟨1973193663137895891498737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1315462442091930594332491 1973193663137895891498737)
      ·
        refine ⟨1479895247353421918624053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1973193663137895891498737 1479895247353421918624053)
        ·
          refine ⟨138740179439383304871005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1479895247353421918624053 138740179439383304871005)
          ·
            refine ⟨52027567289768739326627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138740179439383304871005 52027567289768739326627)
            ·
              refine ⟨78041350934653108989941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52027567289768739326627 78041350934653108989941)
              ·
                refine ⟨7316376650123728967807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78041350934653108989941 7316376650123728967807)
                ·
                  rfl

theorem cell20_48089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 5].length) (baseStart_48089 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48089 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48089 prefixEnd_48089 := by exact prefixLift 48089
  have htrace : WordTrace (prefixWord ++ tailWord_48089) baseStart_48089 baseEnd_48089 := by
    simpa [prefixWord, tailWord_48089, baseEnd_48089] using wordTrace_append hprefix tailTrace_48089
  have hstable : (prefixWord ++ tailWord_48089).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48089).length < 2 ^ (prefixWord ++ tailWord_48089).sum := by decide
  have hdescent : baseEnd_48089 < baseStart_48089 := by decide
  rcases family_descends (prefixWord ++ tailWord_48089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48103 : List Nat := [1, 1, 5, 2, 2, 1, 1, 1, 6]
def baseStart_48103 : Nat := 118140960795 + 48103 * 2 ^ 59
def prefixEnd_48103 : Nat := 4983230072969 + 3 ^ 40 * 48103 * 2
def baseEnd_48103 : Nat := 21955519931849360436697

theorem tailTrace_48103 : CollatzResearch.WordTrace tailWord_48103 prefixEnd_48103 21955519931849360436697 := by
  unfold tailWord_48103
  simp only [CollatzResearch.WordTrace]
  refine ⟨1754460544738521183452963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1169640363159014122301975 1754460544738521183452963)
  ·
    refine ⟨2631690817107781775179445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1754460544738521183452963 2631690817107781775179445)
    ·
      refine ⟨246721014103854541423073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2631690817107781775179445 246721014103854541423073)
      ·
        refine ⟨185040760577890906067305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246721014103854541423073 185040760577890906067305)
        ·
          refine ⟨138780570433418179550479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185040760577890906067305 138780570433418179550479)
          ·
            refine ⟨208170855650127269325719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138780570433418179550479 208170855650127269325719)
            ·
              refine ⟨312256283475190903988579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208170855650127269325719 312256283475190903988579)
              ·
                refine ⟨468384425212786355982869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312256283475190903988579 468384425212786355982869)
                ·
                  refine ⟨21955519931849360436697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 468384425212786355982869 21955519931849360436697)
                  ·
                    rfl

theorem cell20_48103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 6].length) (baseStart_48103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48103 prefixEnd_48103 := by exact prefixLift 48103
  have htrace : WordTrace (prefixWord ++ tailWord_48103) baseStart_48103 baseEnd_48103 := by
    simpa [prefixWord, tailWord_48103, baseEnd_48103] using wordTrace_append hprefix tailTrace_48103
  have hstable : (prefixWord ++ tailWord_48103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48103).length < 2 ^ (prefixWord ++ tailWord_48103).sum := by decide
  have hdescent : baseEnd_48103 < baseStart_48103 := by decide
  rcases family_descends (prefixWord ++ tailWord_48103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48130 : List Nat := [3, 4, 1, 3, 1, 1, 1, 1, 5]
def baseStart_48130 : Nat := 118140960795 + 48130 * 2 ^ 59
def prefixEnd_48130 : Nat := 4983230072969 + 3 ^ 40 * 48130 * 2
def baseEnd_48130 : Nat := 21967843467557266536587

theorem tailTrace_48130 : CollatzResearch.WordTrace tailWord_48130 prefixEnd_48130 21967843467557266536587 := by
  unfold tailWord_48130
  simp only [CollatzResearch.WordTrace]
  refine ⟨438861328910176198671461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1170296877093803196457229 438861328910176198671461)
  ·
    refine ⟨82286499170658037250899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 438861328910176198671461 82286499170658037250899)
    ·
      refine ⟨123429748755987055876349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82286499170658037250899 123429748755987055876349)
      ·
        refine ⟨46286155783495145953631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123429748755987055876349 46286155783495145953631)
        ·
          refine ⟨69429233675242718930447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46286155783495145953631 69429233675242718930447)
          ·
            refine ⟨104143850512864078395671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69429233675242718930447 104143850512864078395671)
            ·
              refine ⟨156215775769296117593507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104143850512864078395671 156215775769296117593507)
              ·
                refine ⟨234323663653944176390261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156215775769296117593507 234323663653944176390261)
                ·
                  refine ⟨21967843467557266536587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 234323663653944176390261 21967843467557266536587)
                  ·
                    rfl

theorem cell20_48130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_48130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48130 prefixEnd_48130 := by exact prefixLift 48130
  have htrace : WordTrace (prefixWord ++ tailWord_48130) baseStart_48130 baseEnd_48130 := by
    simpa [prefixWord, tailWord_48130, baseEnd_48130] using wordTrace_append hprefix tailTrace_48130
  have hstable : (prefixWord ++ tailWord_48130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48130).length < 2 ^ (prefixWord ++ tailWord_48130).sum := by decide
  have hdescent : baseEnd_48130 < baseStart_48130 := by decide
  rcases family_descends (prefixWord ++ tailWord_48130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48254 : List Nat := [4, 2, 4, 1, 1, 2, 1, 5]
def baseStart_48254 : Nat := 118140960795 + 48254 * 2 ^ 59
def prefixEnd_48254 : Nat := 4983230072969 + 3 ^ 40 * 48254 * 2
def baseEnd_48254 : Nat := 7341480148787982134249

theorem tailTrace_48254 : CollatzResearch.WordTrace tailWord_48254 prefixEnd_48254 7341480148787982134249 := by
  unfold tailWord_48254
  simp only [CollatzResearch.WordTrace]
  refine ⟨219995995898934246524977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1173311978127649314799877 219995995898934246524977)
  ·
    refine ⟨164996996924200684893733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219995995898934246524977 164996996924200684893733)
    ·
      refine ⟨30936936923287628417575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164996996924200684893733 30936936923287628417575)
      ·
        refine ⟨46405405384931442626363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30936936923287628417575 46405405384931442626363)
        ·
          refine ⟨69608108077397163939545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46405405384931442626363 69608108077397163939545)
          ·
            refine ⟨52206081058047872954659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69608108077397163939545 52206081058047872954659)
            ·
              refine ⟨78309121587071809431989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52206081058047872954659 78309121587071809431989)
              ·
                refine ⟨7341480148787982134249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78309121587071809431989 7341480148787982134249)
                ·
                  rfl

theorem cell20_48254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_48254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48254 prefixEnd_48254 := by exact prefixLift 48254
  have htrace : WordTrace (prefixWord ++ tailWord_48254) baseStart_48254 baseEnd_48254 := by
    simpa [prefixWord, tailWord_48254, baseEnd_48254] using wordTrace_append hprefix tailTrace_48254
  have hstable : (prefixWord ++ tailWord_48254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48254).length < 2 ^ (prefixWord ++ tailWord_48254).sum := by decide
  have hdescent : baseEnd_48254 < baseStart_48254 := by decide
  rcases family_descends (prefixWord ++ tailWord_48254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48279 : List Nat := [1, 1, 3, 3, 3, 2, 3, 4]
def baseStart_48279 : Nat := 118140960795 + 48279 * 2 ^ 59
def prefixEnd_48279 : Nat := 4983230072969 + 3 ^ 40 * 48279 * 2
def baseEnd_48279 : Nat := 7345283709191656856437

theorem tailTrace_48279 : CollatzResearch.WordTrace tailWord_48279 prefixEnd_48279 7345283709191656856437 := by
  unfold tailWord_48279
  simp only [CollatzResearch.WordTrace]
  refine ⟨1760879792100903241859891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1173919861400602161239927 1760879792100903241859891)
  ·
    refine ⟨2641319688151354862789837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1760879792100903241859891 2641319688151354862789837)
    ·
      refine ⟨990494883056758073546189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2641319688151354862789837 990494883056758073546189)
      ·
        refine ⟨371435581146284277579821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 990494883056758073546189 371435581146284277579821)
        ·
          refine ⟨139288342929856604092433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 371435581146284277579821 139288342929856604092433)
          ·
            refine ⟨104466257197392453069325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139288342929856604092433 104466257197392453069325)
            ·
              refine ⟨39174846449022169900997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104466257197392453069325 39174846449022169900997)
              ·
                refine ⟨7345283709191656856437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39174846449022169900997 7345283709191656856437)
                ·
                  rfl

theorem cell20_48279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 4].length) (baseStart_48279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48279 prefixEnd_48279 := by exact prefixLift 48279
  have htrace : WordTrace (prefixWord ++ tailWord_48279) baseStart_48279 baseEnd_48279 := by
    simpa [prefixWord, tailWord_48279, baseEnd_48279] using wordTrace_append hprefix tailTrace_48279
  have hstable : (prefixWord ++ tailWord_48279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48279).length < 2 ^ (prefixWord ++ tailWord_48279).sum := by decide
  have hdescent : baseEnd_48279 < baseStart_48279 := by decide
  rcases family_descends (prefixWord ++ tailWord_48279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48334 : List Nat := [4, 1, 1, 1, 5, 2, 2, 4]
def baseStart_48334 : Nat := 118140960795 + 48334 * 2 ^ 59
def prefixEnd_48334 : Nat := 4983230072969 + 3 ^ 40 * 48334 * 2
def baseEnd_48334 : Nat := 7353651542079741245251

theorem tailTrace_48334 : CollatzResearch.WordTrace tailWord_48334 prefixEnd_48334 7353651542079741245251 := by
  unfold tailWord_48334
  simp only [CollatzResearch.WordTrace]
  refine ⟨220360725862705954389007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1175257204601098423408037 220360725862705954389007)
  ·
    refine ⟨330541088794058931583511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220360725862705954389007 330541088794058931583511)
    ·
      refine ⟨495811633191088397375267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330541088794058931583511 495811633191088397375267)
      ·
        refine ⟨743717449786632596062901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495811633191088397375267 743717449786632596062901)
        ·
          refine ⟨69723510917496805880897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 743717449786632596062901 69723510917496805880897)
          ·
            refine ⟨52292633188122604410673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69723510917496805880897 52292633188122604410673)
            ·
              refine ⟨39219474891091953308005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52292633188122604410673 39219474891091953308005)
              ·
                refine ⟨7353651542079741245251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39219474891091953308005 7353651542079741245251)
                ·
                  rfl

theorem cell20_48334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_48334 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48334 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48334 prefixEnd_48334 := by exact prefixLift 48334
  have htrace : WordTrace (prefixWord ++ tailWord_48334) baseStart_48334 baseEnd_48334 := by
    simpa [prefixWord, tailWord_48334, baseEnd_48334] using wordTrace_append hprefix tailTrace_48334
  have hstable : (prefixWord ++ tailWord_48334).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48334).length < 2 ^ (prefixWord ++ tailWord_48334).sum := by decide
  have hdescent : baseEnd_48334 < baseStart_48334 := by decide
  rcases family_descends (prefixWord ++ tailWord_48334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48338 : List Nat := [3, 2, 2, 2, 1, 1, 3, 6]
def baseStart_48338 : Nat := 118140960795 + 48338 * 2 ^ 59
def prefixEnd_48338 : Nat := 4983230072969 + 3 ^ 40 * 48338 * 2
def baseEnd_48338 : Nat := 7354260111744329200801

theorem tailTrace_48338 : CollatzResearch.WordTrace tailWord_48338 prefixEnd_48338 7354260111744329200801 := by
  unfold tailWord_48338
  simp only [CollatzResearch.WordTrace]
  refine ⟨440757924721789079564417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1175354465924770878838445 440757924721789079564417)
  ·
    refine ⟨330568443541341809673313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 440757924721789079564417 330568443541341809673313)
    ·
      refine ⟨247926332656006357254985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330568443541341809673313 247926332656006357254985)
      ·
        refine ⟨185944749492004767941239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247926332656006357254985 185944749492004767941239)
        ·
          refine ⟨278917124238007151911859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185944749492004767941239 278917124238007151911859)
          ·
            refine ⟨418375686357010727867789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278917124238007151911859 418375686357010727867789)
            ·
              refine ⟨156890882383879022950421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 418375686357010727867789 156890882383879022950421)
              ·
                refine ⟨7354260111744329200801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 156890882383879022950421 7354260111744329200801)
                ·
                  rfl

theorem cell20_48338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_48338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48338 prefixEnd_48338 := by exact prefixLift 48338
  have htrace : WordTrace (prefixWord ++ tailWord_48338) baseStart_48338 baseEnd_48338 := by
    simpa [prefixWord, tailWord_48338, baseEnd_48338] using wordTrace_append hprefix tailTrace_48338
  have hstable : (prefixWord ++ tailWord_48338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48338).length < 2 ^ (prefixWord ++ tailWord_48338).sum := by decide
  have hdescent : baseEnd_48338 < baseStart_48338 := by decide
  rcases family_descends (prefixWord ++ tailWord_48338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48344 : List Nat := [2, 1, 2, 2, 6, 1, 1, 3, 2]
def baseStart_48344 : Nat := 118140960795 + 48344 * 2 ^ 59
def prefixEnd_48344 : Nat := 4983230072969 + 3 ^ 40 * 48344 * 2
def baseEnd_48344 : Nat := 22065518898723633402379

theorem tailTrace_48344 : CollatzResearch.WordTrace tailWord_48344 prefixEnd_48344 22065518898723633402379 := by
  unfold tailWord_48344
  simp only [CollatzResearch.WordTrace]
  refine ⟨881625268432709671488043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1175500357910279561984057 881625268432709671488043)
  ·
    refine ⟨1322437902649064507232065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 881625268432709671488043 1322437902649064507232065)
    ·
      refine ⟨991828426986798380424049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1322437902649064507232065 991828426986798380424049)
      ·
        refine ⟨743871320240098785318037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 991828426986798380424049 743871320240098785318037)
        ·
          refine ⟨34868968136254630561783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 743871320240098785318037 34868968136254630561783)
          ·
            refine ⟨52303452204381945842675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34868968136254630561783 52303452204381945842675)
            ·
              refine ⟨78455178306572918764013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52303452204381945842675 78455178306572918764013)
              ·
                refine ⟨29420691864964844536505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78455178306572918764013 29420691864964844536505)
                ·
                  refine ⟨22065518898723633402379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29420691864964844536505 22065518898723633402379)
                  ·
                    rfl

theorem cell20_48344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 3, 2].length) (baseStart_48344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48344 prefixEnd_48344 := by exact prefixLift 48344
  have htrace : WordTrace (prefixWord ++ tailWord_48344) baseStart_48344 baseEnd_48344 := by
    simpa [prefixWord, tailWord_48344, baseEnd_48344] using wordTrace_append hprefix tailTrace_48344
  have hstable : (prefixWord ++ tailWord_48344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48344).length < 2 ^ (prefixWord ++ tailWord_48344).sum := by decide
  have hdescent : baseEnd_48344 < baseStart_48344 := by decide
  rcases family_descends (prefixWord ++ tailWord_48344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48428 : List Nat := [2, 2, 1, 1, 1, 3, 1, 5, 4]
def baseStart_48428 : Nat := 118140960795 + 48428 * 2 ^ 59
def prefixEnd_48428 : Nat := 4983230072969 + 3 ^ 40 * 48428 * 2
def baseEnd_48428 : Nat := 22103858787592674602035

theorem tailTrace_48428 : CollatzResearch.WordTrace tailWord_48428 prefixEnd_48428 22103858787592674602035 := by
  unfold tailWord_48428
  simp only [CollatzResearch.WordTrace]
  refine ⟨883157134280550844516969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1177542845707401126022625 883157134280550844516969)
  ·
    refine ⟨662367850710413133387727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 883157134280550844516969 662367850710413133387727)
    ·
      refine ⟨993551776065619700081591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 662367850710413133387727 993551776065619700081591)
      ·
        refine ⟨1490327664098429550122387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 993551776065619700081591 1490327664098429550122387)
        ·
          refine ⟨2235491496147644325183581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1490327664098429550122387 2235491496147644325183581)
          ·
            refine ⟨838309311055366621943843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2235491496147644325183581 838309311055366621943843)
            ·
              refine ⟨1257463966583049932915765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 838309311055366621943843 1257463966583049932915765)
              ·
                refine ⟨117887246867160931210853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1257463966583049932915765 117887246867160931210853)
                ·
                  refine ⟨22103858787592674602035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117887246867160931210853 22103858787592674602035)
                  ·
                    rfl

theorem cell20_48428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_48428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48428 prefixEnd_48428 := by exact prefixLift 48428
  have htrace : WordTrace (prefixWord ++ tailWord_48428) baseStart_48428 baseEnd_48428 := by
    simpa [prefixWord, tailWord_48428, baseEnd_48428] using wordTrace_append hprefix tailTrace_48428
  have hstable : (prefixWord ++ tailWord_48428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48428).length < 2 ^ (prefixWord ++ tailWord_48428).sum := by decide
  have hdescent : baseEnd_48428 < baseStart_48428 := by decide
  rcases family_descends (prefixWord ++ tailWord_48428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48462 : List Nat := [4, 1, 1, 1, 1, 1, 6, 3, 2]
def baseStart_48462 : Nat := 118140960795 + 48462 * 2 ^ 59
def prefixEnd_48462 : Nat := 4983230072969 + 3 ^ 40 * 48462 * 2
def baseEnd_48462 : Nat := 22119377314039667468563

theorem tailTrace_48462 : CollatzResearch.WordTrace tailWord_48462 prefixEnd_48462 22119377314039667468563 := by
  unfold tailWord_48462
  simp only [CollatzResearch.WordTrace]
  refine ⟨220944293804740686971455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1178369566958616997181093 220944293804740686971455)
  ·
    refine ⟨331416440707111030457183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220944293804740686971455 331416440707111030457183)
    ·
      refine ⟨497124661060666545685775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331416440707111030457183 497124661060666545685775)
      ·
        refine ⟨745686991590999818528663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497124661060666545685775 745686991590999818528663)
        ·
          refine ⟨1118530487386499727792995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 745686991590999818528663 1118530487386499727792995)
          ·
            refine ⟨1677795731079749591689493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1118530487386499727792995 1677795731079749591689493)
            ·
              refine ⟨78646674894363262110445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1677795731079749591689493 78646674894363262110445)
              ·
                refine ⟨29492503085386223291417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78646674894363262110445 29492503085386223291417)
                ·
                  refine ⟨22119377314039667468563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29492503085386223291417 22119377314039667468563)
                  ·
                    rfl

theorem cell20_48462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_48462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48462 prefixEnd_48462 := by exact prefixLift 48462
  have htrace : WordTrace (prefixWord ++ tailWord_48462) baseStart_48462 baseEnd_48462 := by
    simpa [prefixWord, tailWord_48462, baseEnd_48462] using wordTrace_append hprefix tailTrace_48462
  have hstable : (prefixWord ++ tailWord_48462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48462).length < 2 ^ (prefixWord ++ tailWord_48462).sum := by decide
  have hdescent : baseEnd_48462 < baseStart_48462 := by decide
  rcases family_descends (prefixWord ++ tailWord_48462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48466 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 8]
def baseStart_48466 : Nat := 118140960795 + 48466 * 2 ^ 59
def prefixEnd_48466 : Nat := 4983230072969 + 3 ^ 40 * 48466 * 2
def baseEnd_48466 : Nat := 22121203023033431335213

theorem tailTrace_48466 : CollatzResearch.WordTrace tailWord_48466 prefixEnd_48466 22121203023033431335213 := by
  unfold tailWord_48466
  simp only [CollatzResearch.WordTrace]
  refine ⟨441925060605858544729313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1178466828282289452611501 441925060605858544729313)
  ·
    refine ⟨331443795454393908546985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 441925060605858544729313 331443795454393908546985)
    ·
      refine ⟨248582846590795431410239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 331443795454393908546985 248582846590795431410239)
      ·
        refine ⟨372874269886193147115359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248582846590795431410239 372874269886193147115359)
        ·
          refine ⟨559311404829289720673039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372874269886193147115359 559311404829289720673039)
          ·
            refine ⟨838967107243934581009559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 559311404829289720673039 838967107243934581009559)
            ·
              refine ⟨1258450660865901871514339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 838967107243934581009559 1258450660865901871514339)
              ·
                refine ⟨1887675991298852807271509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1258450660865901871514339 1887675991298852807271509)
                ·
                  refine ⟨22121203023033431335213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1887675991298852807271509 22121203023033431335213)
                  ·
                    rfl

theorem cell20_48466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_48466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48466 prefixEnd_48466 := by exact prefixLift 48466
  have htrace : WordTrace (prefixWord ++ tailWord_48466) baseStart_48466 baseEnd_48466 := by
    simpa [prefixWord, tailWord_48466, baseEnd_48466] using wordTrace_append hprefix tailTrace_48466
  have hstable : (prefixWord ++ tailWord_48466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48466).length < 2 ^ (prefixWord ++ tailWord_48466).sum := by decide
  have hdescent : baseEnd_48466 < baseStart_48466 := by decide
  rcases family_descends (prefixWord ++ tailWord_48466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48483 : List Nat := [1, 1, 1, 5, 2, 3, 2, 1, 4]
def baseStart_48483 : Nat := 118140960795 + 48483 * 2 ^ 59
def prefixEnd_48483 : Nat := 4983230072969 + 3 ^ 40 * 48483 * 2
def baseEnd_48483 : Nat := 22128962286256927768477

theorem tailTrace_48483 : CollatzResearch.WordTrace tailWord_48483 prefixEnd_48483 22128962286256927768477 := by
  unfold tailWord_48483
  simp only [CollatzResearch.WordTrace]
  refine ⟨1768320283361846082286103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1178880188907897388190735 1768320283361846082286103)
  ·
    refine ⟨2652480425042769123429155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1768320283361846082286103 2652480425042769123429155)
    ·
      refine ⟨3978720637564153685143733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2652480425042769123429155 3978720637564153685143733)
      ·
        refine ⟨373005059771639407982225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3978720637564153685143733 373005059771639407982225)
        ·
          refine ⟨279753794828729555986669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 373005059771639407982225 279753794828729555986669)
          ·
            refine ⟨104907673060773583495001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 279753794828729555986669 104907673060773583495001)
            ·
              refine ⟨78680754795580187621251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104907673060773583495001 78680754795580187621251)
              ·
                refine ⟨118021132193370281431877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78680754795580187621251 118021132193370281431877)
                ·
                  refine ⟨22128962286256927768477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118021132193370281431877 22128962286256927768477)
                  ·
                    rfl

theorem cell20_48483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 4].length) (baseStart_48483 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48483 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48483 prefixEnd_48483 := by exact prefixLift 48483
  have htrace : WordTrace (prefixWord ++ tailWord_48483) baseStart_48483 baseEnd_48483 := by
    simpa [prefixWord, tailWord_48483, baseEnd_48483] using wordTrace_append hprefix tailTrace_48483
  have hstable : (prefixWord ++ tailWord_48483).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48483).length < 2 ^ (prefixWord ++ tailWord_48483).sum := by decide
  have hdescent : baseEnd_48483 < baseStart_48483 := by decide
  rcases family_descends (prefixWord ++ tailWord_48483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48493 : List Nat := [1, 5, 1, 1, 1, 4, 3, 1, 3]
def baseStart_48493 : Nat := 118140960795 + 48493 * 2 ^ 59
def prefixEnd_48493 : Nat := 4983230072969 + 3 ^ 40 * 48493 * 2
def baseEnd_48493 : Nat := 22133526558741337435103

theorem tailTrace_48493 : CollatzResearch.WordTrace tailWord_48493 prefixEnd_48493 22133526558741337435103 := by
  unfold tailWord_48493
  simp only [CollatzResearch.WordTrace]
  refine ⟨1768685013325617790150133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1179123342217078526766755 1768685013325617790150133)
  ·
    refine ⟨165814219999276667826575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1768685013325617790150133 165814219999276667826575)
    ·
      refine ⟨248721329998915001739863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165814219999276667826575 248721329998915001739863)
      ·
        refine ⟨373081994998372502609795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248721329998915001739863 373081994998372502609795)
        ·
          refine ⟨559622992497558753914693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373081994998372502609795 559622992497558753914693)
          ·
            refine ⟨104929311093292266359005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 559622992497558753914693 104929311093292266359005)
            ·
              refine ⟨39348491659984599884627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104929311093292266359005 39348491659984599884627)
              ·
                refine ⟨59022737489976899826941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39348491659984599884627 59022737489976899826941)
                ·
                  refine ⟨22133526558741337435103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59022737489976899826941 22133526558741337435103)
                  ·
                    rfl

theorem cell20_48493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_48493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48493 prefixEnd_48493 := by exact prefixLift 48493
  have htrace : WordTrace (prefixWord ++ tailWord_48493) baseStart_48493 baseEnd_48493 := by
    simpa [prefixWord, tailWord_48493, baseEnd_48493] using wordTrace_append hprefix tailTrace_48493
  have hstable : (prefixWord ++ tailWord_48493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48493).length < 2 ^ (prefixWord ++ tailWord_48493).sum := by decide
  have hdescent : baseEnd_48493 < baseStart_48493 := by decide
  rcases family_descends (prefixWord ++ tailWord_48493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48497 : List Nat := [1, 2, 2, 2, 1, 2, 2, 5, 3]
def baseStart_48497 : Nat := 118140960795 + 48497 * 2 ^ 59
def prefixEnd_48497 : Nat := 4983230072969 + 3 ^ 40 * 48497 * 2
def baseEnd_48497 : Nat := 22135352267735101301753

theorem tailTrace_48497 : CollatzResearch.WordTrace tailWord_48497 prefixEnd_48497 22135352267735101301753 := by
  unfold tailWord_48497
  simp only [CollatzResearch.WordTrace]
  refine ⟨1768830905311126473295745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1179220603540750982197163 1768830905311126473295745)
  ·
    refine ⟨1326623178983344854971809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1768830905311126473295745 1326623178983344854971809)
    ·
      refine ⟨994967384237508641228857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1326623178983344854971809 994967384237508641228857)
      ·
        refine ⟨746225538178131480921643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 994967384237508641228857 746225538178131480921643)
        ·
          refine ⟨1119338307267197221382465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 746225538178131480921643 1119338307267197221382465)
          ·
            refine ⟨839503730450397916036849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1119338307267197221382465 839503730450397916036849)
            ·
              refine ⟨629627797837798437027637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 839503730450397916036849 629627797837798437027637)
              ·
                refine ⟨59027606047293603471341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 629627797837798437027637 59027606047293603471341)
                ·
                  refine ⟨22135352267735101301753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59027606047293603471341 22135352267735101301753)
                  ·
                    rfl

theorem cell20_48497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 3].length) (baseStart_48497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48497 prefixEnd_48497 := by exact prefixLift 48497
  have htrace : WordTrace (prefixWord ++ tailWord_48497) baseStart_48497 baseEnd_48497 := by
    simpa [prefixWord, tailWord_48497, baseEnd_48497] using wordTrace_append hprefix tailTrace_48497
  have hstable : (prefixWord ++ tailWord_48497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48497).length < 2 ^ (prefixWord ++ tailWord_48497).sum := by decide
  have hdescent : baseEnd_48497 < baseStart_48497 := by decide
  rcases family_descends (prefixWord ++ tailWord_48497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48535 : List Nat := [1, 1, 3, 3, 1, 1, 1, 6, 3]
def baseStart_48535 : Nat := 118140960795 + 48535 * 2 ^ 59
def prefixEnd_48535 : Nat := 4983230072969 + 3 ^ 40 * 48535 * 2
def baseEnd_48535 : Nat := 22152696503175858034931

theorem tailTrace_48535 : CollatzResearch.WordTrace tailWord_48535 prefixEnd_48535 22152696503175858034931 := by
  unfold tailWord_48535
  simp only [CollatzResearch.WordTrace]
  refine ⟨1770216879173458963179059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1180144586115639308786039 1770216879173458963179059)
  ·
    refine ⟨2655325318760188444768589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1770216879173458963179059 2655325318760188444768589)
    ·
      refine ⟨995746994535070666788221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2655325318760188444768589 995746994535070666788221)
      ·
        refine ⟨373405122950651500045583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 995746994535070666788221 373405122950651500045583)
        ·
          refine ⟨560107684425977250068375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373405122950651500045583 560107684425977250068375)
          ·
            refine ⟨840161526638965875102563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 560107684425977250068375 840161526638965875102563)
            ·
              refine ⟨1260242289958448812653845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 840161526638965875102563 1260242289958448812653845)
              ·
                refine ⟨59073857341802288093149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1260242289958448812653845 59073857341802288093149)
                ·
                  refine ⟨22152696503175858034931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59073857341802288093149 22152696503175858034931)
                  ·
                    rfl

theorem cell20_48535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 3].length) (baseStart_48535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48535 prefixEnd_48535 := by exact prefixLift 48535
  have htrace : WordTrace (prefixWord ++ tailWord_48535) baseStart_48535 baseEnd_48535 := by
    simpa [prefixWord, tailWord_48535, baseEnd_48535] using wordTrace_append hprefix tailTrace_48535
  have hstable : (prefixWord ++ tailWord_48535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48535).length < 2 ^ (prefixWord ++ tailWord_48535).sum := by decide
  have hdescent : baseEnd_48535 < baseStart_48535 := by decide
  rcases family_descends (prefixWord ++ tailWord_48535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48717 : List Nat := [1, 6, 1, 1, 4, 1, 2, 1, 3]
def baseStart_48717 : Nat := 118140960795 + 48717 * 2 ^ 59
def prefixEnd_48717 : Nat := 4983230072969 + 3 ^ 40 * 48717 * 2
def baseEnd_48717 : Nat := 22235766262392113967521

theorem tailTrace_48717 : CollatzResearch.WordTrace tailWord_48717 prefixEnd_48717 22235766262392113967521 := by
  unfold tailWord_48717
  simp only [CollatzResearch.WordTrace]
  refine ⟨1776854964514104046304405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1184569976342736030869603 1776854964514104046304405)
  ·
    refine ⟨83290076461598627170519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1776854964514104046304405 83290076461598627170519)
    ·
      refine ⟨124935114692397940755779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83290076461598627170519 124935114692397940755779)
      ·
        refine ⟨187402672038596911133669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124935114692397940755779 187402672038596911133669)
        ·
          refine ⟨35138001007236920837563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187402672038596911133669 35138001007236920837563)
          ·
            refine ⟨52707001510855381256345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35138001007236920837563 52707001510855381256345)
            ·
              refine ⟨39530251133141535942259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52707001510855381256345 39530251133141535942259)
              ·
                refine ⟨59295376699712303913389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39530251133141535942259 59295376699712303913389)
                ·
                  refine ⟨22235766262392113967521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59295376699712303913389 22235766262392113967521)
                  ·
                    rfl

theorem cell20_48717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_48717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48717 prefixEnd_48717 := by exact prefixLift 48717
  have htrace : WordTrace (prefixWord ++ tailWord_48717) baseStart_48717 baseEnd_48717 := by
    simpa [prefixWord, tailWord_48717, baseEnd_48717] using wordTrace_append hprefix tailTrace_48717
  have hstable : (prefixWord ++ tailWord_48717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48717).length < 2 ^ (prefixWord ++ tailWord_48717).sum := by decide
  have hdescent : baseEnd_48717 < baseStart_48717 := by decide
  rcases family_descends (prefixWord ++ tailWord_48717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48739 : List Nat := [1, 1, 1, 5, 1, 3, 2, 6]
def baseStart_48739 : Nat := 118140960795 + 48739 * 2 ^ 59
def prefixEnd_48739 : Nat := 4983230072969 + 3 ^ 40 * 48739 * 2
def baseEnd_48739 : Nat := 7415269220619271744699

theorem tailTrace_48739 : CollatzResearch.WordTrace tailWord_48739 prefixEnd_48739 7415269220619271744699 := by
  unfold tailWord_48739
  simp only [CollatzResearch.WordTrace]
  refine ⟨1777657370434401803605271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1185104913622934535736847 1777657370434401803605271)
  ·
    refine ⟨2666486055651602705407907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1777657370434401803605271 2666486055651602705407907)
    ·
      refine ⟨3999729083477404058111861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2666486055651602705407907 3999729083477404058111861)
      ·
        refine ⟨374974601576006630447987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3999729083477404058111861 374974601576006630447987)
        ·
          refine ⟨562461902364009945671981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374974601576006630447987 562461902364009945671981)
          ·
            refine ⟨210923213386503729626993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 562461902364009945671981 210923213386503729626993)
            ·
              refine ⟨158192410039877797220245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210923213386503729626993 158192410039877797220245)
              ·
                refine ⟨7415269220619271744699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 158192410039877797220245 7415269220619271744699)
                ·
                  rfl

theorem cell20_48739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 6].length) (baseStart_48739 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48739 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48739 prefixEnd_48739 := by exact prefixLift 48739
  have htrace : WordTrace (prefixWord ++ tailWord_48739) baseStart_48739 baseEnd_48739 := by
    simpa [prefixWord, tailWord_48739, baseEnd_48739] using wordTrace_append hprefix tailTrace_48739
  have hstable : (prefixWord ++ tailWord_48739).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48739).length < 2 ^ (prefixWord ++ tailWord_48739).sum := by decide
  have hdescent : baseEnd_48739 < baseStart_48739 := by decide
  rcases family_descends (prefixWord ++ tailWord_48739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48763 : List Nat := [1, 1, 1, 1, 1, 4, 6, 2, 3]
def baseStart_48763 : Nat := 118140960795 + 48763 * 2 ^ 59
def prefixEnd_48763 : Nat := 4983230072969 + 3 ^ 40 * 48763 * 2
def baseEnd_48763 : Nat := 22256761915820398433999

theorem tailTrace_48763 : CollatzResearch.WordTrace tailWord_48763 prefixEnd_48763 22256761915820398433999 := by
  unfold tailWord_48763
  simp only [CollatzResearch.WordTrace]
  refine ⟨1778532722347453902478943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1185688481564969268319295 1778532722347453902478943)
  ·
    refine ⟨2667799083521180853718415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1778532722347453902478943 2667799083521180853718415)
    ·
      refine ⟨4001698625281771280577623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2667799083521180853718415 4001698625281771280577623)
      ·
        refine ⟨6002547937922656920866435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4001698625281771280577623 6002547937922656920866435)
        ·
          refine ⟨9003821906883985381299653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6002547937922656920866435 9003821906883985381299653)
          ·
            refine ⟨1688216607540747258993685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9003821906883985381299653 1688216607540747258993685)
            ·
              refine ⟨79135153478472527765329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1688216607540747258993685 79135153478472527765329)
              ·
                refine ⟨59351365108854395823997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79135153478472527765329 59351365108854395823997)
                ·
                  refine ⟨22256761915820398433999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59351365108854395823997 22256761915820398433999)
                  ·
                    rfl

theorem cell20_48763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 3].length) (baseStart_48763 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48763 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48763 prefixEnd_48763 := by exact prefixLift 48763
  have htrace : WordTrace (prefixWord ++ tailWord_48763) baseStart_48763 baseEnd_48763 := by
    simpa [prefixWord, tailWord_48763, baseEnd_48763] using wordTrace_append hprefix tailTrace_48763
  have hstable : (prefixWord ++ tailWord_48763).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48763).length < 2 ^ (prefixWord ++ tailWord_48763).sum := by decide
  have hdescent : baseEnd_48763 < baseStart_48763 := by decide
  rcases family_descends (prefixWord ++ tailWord_48763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48777 : List Nat := [1, 2, 1, 1, 4, 1, 5, 5]
def baseStart_48777 : Nat := 118140960795 + 48777 * 2 ^ 59
def prefixEnd_48777 : Nat := 4983230072969 + 3 ^ 40 * 48777 * 2
def baseEnd_48777 : Nat := 7421050632432857322425

theorem tailTrace_48777 : CollatzResearch.WordTrace tailWord_48777 prefixEnd_48777 7421050632432857322425 := by
  unfold tailWord_48777
  simp only [CollatzResearch.WordTrace]
  refine ⟨1779043344296734293488585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1186028896197822862325723 1779043344296734293488585)
  ·
    refine ⟨1334282508222550720116439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1779043344296734293488585 1334282508222550720116439)
    ·
      refine ⟨2001423762333826080174659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1334282508222550720116439 2001423762333826080174659)
      ·
        refine ⟨3002135643500739120261989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2001423762333826080174659 3002135643500739120261989)
        ·
          refine ⟨562900433156388585049123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3002135643500739120261989 562900433156388585049123)
          ·
            refine ⟨844350649734582877573685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562900433156388585049123 844350649734582877573685)
            ·
              refine ⟨79157873412617144772533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 844350649734582877573685 79157873412617144772533)
              ·
                refine ⟨7421050632432857322425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79157873412617144772533 7421050632432857322425)
                ·
                  rfl

theorem cell20_48777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 5].length) (baseStart_48777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48777 prefixEnd_48777 := by exact prefixLift 48777
  have htrace : WordTrace (prefixWord ++ tailWord_48777) baseStart_48777 baseEnd_48777 := by
    simpa [prefixWord, tailWord_48777, baseEnd_48777] using wordTrace_append hprefix tailTrace_48777
  have hstable : (prefixWord ++ tailWord_48777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48777).length < 2 ^ (prefixWord ++ tailWord_48777).sum := by decide
  have hdescent : baseEnd_48777 < baseStart_48777 := by decide
  rcases family_descends (prefixWord ++ tailWord_48777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
