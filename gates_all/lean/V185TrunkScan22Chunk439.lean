import V185TrunkScan22Chunk438

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3914307 : List Nat := [1, 1, 1, 3, 1, 2, 1, 7, 5]
def baseStart_3914307 : Nat := 118140960795 + 3914307 * 2 ^ 59
def prefixEnd_3914307 : Nat := 4983230072969 + 3 ^ 40 * 3914307 * 2
def baseEnd_3914307 : Nat := 446649093390827108791319

theorem tailTrace_3914307 : CollatzResearch.WordTrace tailWord_3914307 prefixEnd_3914307 446649093390827108791319 := by
  unfold tailWord_3914307
  simp only [CollatzResearch.WordTrace]
  refine ⟨142766505030141724257877175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95177670020094482838584783 142766505030141724257877175)
  ·
    refine ⟨214149757545212586386815763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142766505030141724257877175 214149757545212586386815763)
    ·
      refine ⟨321224636317818879580223645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214149757545212586386815763 321224636317818879580223645)
      ·
        refine ⟨120459238619182079842583867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321224636317818879580223645 120459238619182079842583867)
        ·
          refine ⟨180688857928773119763875801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120459238619182079842583867 180688857928773119763875801)
          ·
            refine ⟨135516643446579839822906851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180688857928773119763875801 135516643446579839822906851)
            ·
              refine ⟨203274965169869759734360277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135516643446579839822906851 203274965169869759734360277)
              ·
                refine ⟨4764256996168822493774069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 203274965169869759734360277 4764256996168822493774069)
                ·
                  refine ⟨446649093390827108791319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4764256996168822493774069 446649093390827108791319)
                  ·
                    rfl

theorem cell22_3914307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 5].length) (baseStart_3914307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914307 prefixEnd_3914307 := by exact prefixLift 3914307
  have htrace : WordTrace (prefixWord ++ tailWord_3914307) baseStart_3914307 baseEnd_3914307 := by
    simpa [prefixWord, tailWord_3914307, baseEnd_3914307] using wordTrace_append hprefix tailTrace_3914307
  have hstable : (prefixWord ++ tailWord_3914307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914307).length < 2 ^ (prefixWord ++ tailWord_3914307).sum := by decide
  have hdescent : baseEnd_3914307 < baseStart_3914307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914433 : List Nat := [1, 2, 6, 2, 1, 1, 1, 1, 1, 6]
def baseStart_3914433 : Nat := 118140960795 + 3914433 * 2 ^ 59
def prefixEnd_3914433 : Nat := 4983230072969 + 3 ^ 40 * 3914433 * 2
def baseEnd_3914433 : Nat := 1339990412547458997723571

theorem tailTrace_3914433 : CollatzResearch.WordTrace tailWord_3914433 prefixEnd_3914433 1339990412547458997723571 := by
  unfold tailWord_3914433
  simp only [CollatzResearch.WordTrace]
  refine ⟨142771100627685247776963953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95180733751790165184642635 142771100627685247776963953)
  ·
    refine ⟨107078325470763935832722965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142771100627685247776963953 107078325470763935832722965)
    ·
      refine ⟨5019296506442059492158889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 107078325470763935832722965 5019296506442059492158889)
      ·
        refine ⟨3764472379831544619119167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5019296506442059492158889 3764472379831544619119167)
        ·
          refine ⟨5646708569747316928678751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3764472379831544619119167 5646708569747316928678751)
          ·
            refine ⟨8470062854620975393018127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5646708569747316928678751 8470062854620975393018127)
            ·
              refine ⟨12705094281931463089527191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8470062854620975393018127 12705094281931463089527191)
              ·
                refine ⟨19057641422897194634290787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12705094281931463089527191 19057641422897194634290787)
                ·
                  refine ⟨28586462134345791951436181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19057641422897194634290787 28586462134345791951436181)
                  ·
                    refine ⟨1339990412547458997723571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28586462134345791951436181 1339990412547458997723571)
                    ·
                      rfl

theorem cell22_3914433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_3914433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914433 prefixEnd_3914433 := by exact prefixLift 3914433
  have htrace : WordTrace (prefixWord ++ tailWord_3914433) baseStart_3914433 baseEnd_3914433 := by
    simpa [prefixWord, tailWord_3914433, baseEnd_3914433] using wordTrace_append hprefix tailTrace_3914433
  have hstable : (prefixWord ++ tailWord_3914433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914433).length < 2 ^ (prefixWord ++ tailWord_3914433).sum := by decide
  have hdescent : baseEnd_3914433 < baseStart_3914433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914452 : List Nat := [2, 4, 1, 3, 3, 1, 1, 2, 2, 3]
def baseStart_3914452 : Nat := 118140960795 + 3914452 * 2 ^ 59
def prefixEnd_3914452 : Nat := 4983230072969 + 3 ^ 40 * 3914452 * 2
def baseEnd_3914452 : Nat := 1339996916635749281498513

theorem tailTrace_3914452 : CollatzResearch.WordTrace tailWord_3914452 prefixEnd_3914452 1339996916635749281498513 := by
  unfold tailWord_3914452
  simp only [CollatzResearch.WordTrace]
  refine ⟨71385896807308207010952805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95181195743077609347937073 71385896807308207010952805)
  ·
    refine ⟨13384855651370288814553651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71385896807308207010952805 13384855651370288814553651)
    ·
      refine ⟨20077283477055433221830477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13384855651370288814553651 20077283477055433221830477)
      ·
        refine ⟨7528981303895787458186429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20077283477055433221830477 7528981303895787458186429)
        ·
          refine ⟨2823367988960920296819911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7528981303895787458186429 2823367988960920296819911)
          ·
            refine ⟨4235051983441380445229867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2823367988960920296819911 4235051983441380445229867)
            ·
              refine ⟨6352577975162070667844801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4235051983441380445229867 6352577975162070667844801)
              ·
                refine ⟨4764433481371553000883601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6352577975162070667844801 4764433481371553000883601)
                ·
                  refine ⟨3573325111028664750662701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4764433481371553000883601 3573325111028664750662701)
                  ·
                    refine ⟨1339996916635749281498513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3573325111028664750662701 1339996916635749281498513)
                    ·
                      rfl

theorem cell22_3914452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_3914452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914452 prefixEnd_3914452 := by exact prefixLift 3914452
  have htrace : WordTrace (prefixWord ++ tailWord_3914452) baseStart_3914452 baseEnd_3914452 := by
    simpa [prefixWord, tailWord_3914452, baseEnd_3914452] using wordTrace_append hprefix tailTrace_3914452
  have hstable : (prefixWord ++ tailWord_3914452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914452).length < 2 ^ (prefixWord ++ tailWord_3914452).sum := by decide
  have hdescent : baseEnd_3914452 < baseStart_3914452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914463 : List Nat := [1, 1, 2, 3, 2, 3, 2, 4, 1, 3]
def baseStart_3914463 : Nat := 118140960795 + 3914463 * 2 ^ 59
def prefixEnd_3914463 : Nat := 4983230072969 + 3 ^ 40 * 3914463 * 2
def baseEnd_3914463 : Nat := 1340000682160548919473479

theorem tailTrace_3914463 : CollatzResearch.WordTrace tailWord_3914463 prefixEnd_3914463 1340000682160548919473479 := by
  unfold tailWord_3914463
  simp only [CollatzResearch.WordTrace]
  refine ⟨142772194817576562900556043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95181463211717708600370695 142772194817576562900556043)
  ·
    refine ⟨214158292226364844350834065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142772194817576562900556043 214158292226364844350834065)
    ·
      refine ⟨160618719169773633263125549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214158292226364844350834065 160618719169773633263125549)
      ·
        refine ⟨60232019688665112473672081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160618719169773633263125549 60232019688665112473672081)
        ·
          refine ⟨45174014766498834355254061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60232019688665112473672081 45174014766498834355254061)
          ·
            refine ⟨16940255537437062883220273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45174014766498834355254061 16940255537437062883220273)
            ·
              refine ⟨12705191653077797162415205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16940255537437062883220273 12705191653077797162415205)
              ·
                refine ⟨2382223434952086967952851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12705191653077797162415205 2382223434952086967952851)
                ·
                  refine ⟨3573335152428130451929277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2382223434952086967952851 3573335152428130451929277)
                  ·
                    refine ⟨1340000682160548919473479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3573335152428130451929277 1340000682160548919473479)
                    ·
                      rfl

theorem cell22_3914463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 4, 1, 3].length) (baseStart_3914463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914463 prefixEnd_3914463 := by exact prefixLift 3914463
  have htrace : WordTrace (prefixWord ++ tailWord_3914463) baseStart_3914463 baseEnd_3914463 := by
    simpa [prefixWord, tailWord_3914463, baseEnd_3914463] using wordTrace_append hprefix tailTrace_3914463
  have hstable : (prefixWord ++ tailWord_3914463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914463).length < 2 ^ (prefixWord ++ tailWord_3914463).sum := by decide
  have hdescent : baseEnd_3914463 < baseStart_3914463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914489 : List Nat := [1, 2, 1, 3, 1, 1, 1, 5, 3, 4]
def baseStart_3914489 : Nat := 118140960795 + 3914489 * 2 ^ 59
def prefixEnd_3914489 : Nat := 4983230072969 + 3 ^ 40 * 3914489 * 2
def baseEnd_3914489 : Nat := 1340009582491893518323399

theorem tailTrace_3914489 : CollatzResearch.WordTrace tailWord_3914489 prefixEnd_3914489 1340009582491893518323399 := by
  unfold tailWord_3914489
  simp only [CollatzResearch.WordTrace]
  refine ⟨142773143115482369341002521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95182095410321579560668347 142773143115482369341002521)
  ·
    refine ⟨107079857336611777005751891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142773143115482369341002521 107079857336611777005751891)
    ·
      refine ⟨160619786004917665508627837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107079857336611777005751891 160619786004917665508627837)
      ·
        refine ⟨60232419751844124565735439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160619786004917665508627837 60232419751844124565735439)
        ·
          refine ⟨90348629627766186848603159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60232419751844124565735439 90348629627766186848603159)
          ·
            refine ⟨135522944441649280272904739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90348629627766186848603159 135522944441649280272904739)
            ·
              refine ⟨203284416662473920409357109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135522944441649280272904739 203284416662473920409357109)
              ·
                refine ⟨19057914062106930038377229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 203284416662473920409357109 19057914062106930038377229)
                ·
                  refine ⟨7146717773290098764391461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19057914062106930038377229 7146717773290098764391461)
                  ·
                    refine ⟨1340009582491893518323399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7146717773290098764391461 1340009582491893518323399)
                    ·
                      rfl

theorem cell22_3914489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 4].length) (baseStart_3914489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914489 prefixEnd_3914489 := by exact prefixLift 3914489
  have htrace : WordTrace (prefixWord ++ tailWord_3914489) baseStart_3914489 baseEnd_3914489 := by
    simpa [prefixWord, tailWord_3914489, baseEnd_3914489] using wordTrace_append hprefix tailTrace_3914489
  have hstable : (prefixWord ++ tailWord_3914489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914489).length < 2 ^ (prefixWord ++ tailWord_3914489).sum := by decide
  have hdescent : baseEnd_3914489 < baseStart_3914489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914506 : List Nat := [3, 1, 2, 2, 1, 2, 1, 5, 1, 4]
def baseStart_3914506 : Nat := 118140960795 + 3914506 * 2 ^ 59
def prefixEnd_3914506 : Nat := 4983230072969 + 3 ^ 40 * 3914506 * 2
def baseEnd_3914506 : Nat := 1340015401939311140648347

theorem tailTrace_3914506 : CollatzResearch.WordTrace tailWord_3914506 prefixEnd_3914506 1340015401939311140648347 := by
  unfold tailWord_3914506
  simp only [CollatzResearch.WordTrace]
  refine ⟨35693440789105195311092843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95182508770947187496247581 35693440789105195311092843)
  ·
    refine ⟨53540161183657792966639265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35693440789105195311092843 53540161183657792966639265)
    ·
      refine ⟨40155120887743344724979449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53540161183657792966639265 40155120887743344724979449)
      ·
        refine ⟨30116340665807508543734587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40155120887743344724979449 30116340665807508543734587)
        ·
          refine ⟨45174510998711262815601881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30116340665807508543734587 45174510998711262815601881)
          ·
            refine ⟨33880883249033447111701411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45174510998711262815601881 33880883249033447111701411)
            ·
              refine ⟨50821324873550170667552117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33880883249033447111701411 50821324873550170667552117)
              ·
                refine ⟨4764499206895328500083011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50821324873550170667552117 4764499206895328500083011)
                ·
                  refine ⟨7146748810342992750124517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4764499206895328500083011 7146748810342992750124517)
                  ·
                    refine ⟨1340015401939311140648347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7146748810342992750124517 1340015401939311140648347)
                    ·
                      rfl

theorem cell22_3914506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_3914506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914506 prefixEnd_3914506 := by exact prefixLift 3914506
  have htrace : WordTrace (prefixWord ++ tailWord_3914506) baseStart_3914506 baseEnd_3914506 := by
    simpa [prefixWord, tailWord_3914506, baseEnd_3914506] using wordTrace_append hprefix tailTrace_3914506
  have hstable : (prefixWord ++ tailWord_3914506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914506).length < 2 ^ (prefixWord ++ tailWord_3914506).sum := by decide
  have hdescent : baseEnd_3914506 < baseStart_3914506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914514 : List Nat := [3, 2, 4, 1, 2, 1, 3, 2, 1, 3]
def baseStart_3914514 : Nat := 118140960795 + 3914514 * 2 ^ 59
def prefixEnd_3914514 : Nat := 4983230072969 + 3 ^ 40 * 3914514 * 2
def baseEnd_3914514 : Nat := 1340018140502801786448323

theorem tailTrace_3914514 : CollatzResearch.WordTrace tailWord_3914514 prefixEnd_3914514 1340018140502801786448323 := by
  unfold tailWord_3914514
  simp only [CollatzResearch.WordTrace]
  refine ⟨35693513735097949652665649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95182703293594532407108397 35693513735097949652665649)
  ·
    refine ⟨26770135301323462239499237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35693513735097949652665649 26770135301323462239499237)
    ·
      refine ⟨5019400368998149169906107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26770135301323462239499237 5019400368998149169906107)
      ·
        refine ⟨7529100553497223754859161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5019400368998149169906107 7529100553497223754859161)
        ·
          refine ⟨5646825415122917816144371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7529100553497223754859161 5646825415122917816144371)
          ·
            refine ⟨8470238122684376724216557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5646825415122917816144371 8470238122684376724216557)
            ·
              refine ⟨3176339296006641271581209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8470238122684376724216557 3176339296006641271581209)
              ·
                refine ⟨2382254472004980953685907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3176339296006641271581209 2382254472004980953685907)
                ·
                  refine ⟨3573381708007471430528861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2382254472004980953685907 3573381708007471430528861)
                  ·
                    refine ⟨1340018140502801786448323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3573381708007471430528861 1340018140502801786448323)
                    ·
                      rfl

theorem cell22_3914514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_3914514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914514 prefixEnd_3914514 := by exact prefixLift 3914514
  have htrace : WordTrace (prefixWord ++ tailWord_3914514) baseStart_3914514 baseEnd_3914514 := by
    simpa [prefixWord, tailWord_3914514, baseEnd_3914514] using wordTrace_append hprefix tailTrace_3914514
  have hstable : (prefixWord ++ tailWord_3914514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914514).length < 2 ^ (prefixWord ++ tailWord_3914514).sum := by decide
  have hdescent : baseEnd_3914514 < baseStart_3914514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914536 : List Nat := [2, 1, 5, 1, 1, 1, 2, 3, 1, 5]
def baseStart_3914536 : Nat := 118140960795 + 3914536 * 2 ^ 59
def prefixEnd_3914536 : Nat := 4983230072969 + 3 ^ 40 * 3914536 * 2
def baseEnd_3914536 : Nat := 1340025671552401062398255

theorem tailTrace_3914536 : CollatzResearch.WordTrace tailWord_3914536 prefixEnd_3914536 1340025671552401062398255 := by
  unfold tailWord_3914536
  simp only [CollatzResearch.WordTrace]
  refine ⟨71387428673156048183981731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95183238230874730911975641 71387428673156048183981731)
  ·
    refine ⟨107081143009734072275972597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71387428673156048183981731 107081143009734072275972597)
    ·
      refine ⟨10038857157162569275872431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107081143009734072275972597 10038857157162569275872431)
      ·
        refine ⟨15058285735743853913808647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10038857157162569275872431 15058285735743853913808647)
        ·
          refine ⟨22587428603615780870712971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15058285735743853913808647 22587428603615780870712971)
          ·
            refine ⟨33881142905423671306069457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22587428603615780870712971 33881142905423671306069457)
            ·
              refine ⟨25410857179067753479552093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33881142905423671306069457 25410857179067753479552093)
              ·
                refine ⟨9529071442150407554832035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25410857179067753479552093 9529071442150407554832035)
                ·
                  refine ⟨14293607163225611332248053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9529071442150407554832035 14293607163225611332248053)
                  ·
                    refine ⟨1340025671552401062398255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14293607163225611332248053 1340025671552401062398255)
                    ·
                      rfl

theorem cell22_3914536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_3914536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914536 prefixEnd_3914536 := by exact prefixLift 3914536
  have htrace : WordTrace (prefixWord ++ tailWord_3914536) baseStart_3914536 baseEnd_3914536 := by
    simpa [prefixWord, tailWord_3914536, baseEnd_3914536] using wordTrace_append hprefix tailTrace_3914536
  have hstable : (prefixWord ++ tailWord_3914536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914536).length < 2 ^ (prefixWord ++ tailWord_3914536).sum := by decide
  have hdescent : baseEnd_3914536 < baseStart_3914536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914551 : List Nat := [1, 1, 3, 1, 2, 1, 6, 1, 2, 4]
def baseStart_3914551 : Nat := 118140960795 + 3914551 * 2 ^ 59
def prefixEnd_3914551 : Nat := 4983230072969 + 3 ^ 40 * 3914551 * 2
def baseEnd_3914551 : Nat := 1340030806358946023273209

theorem tailTrace_3914551 : CollatzResearch.WordTrace tailWord_3914551 prefixEnd_3914551 1340030806358946023273209 := by
  unfold tailWord_3914551
  simp only [CollatzResearch.WordTrace]
  refine ⟨142775404441257753929759507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95183602960838502619839671 142775404441257753929759507)
  ·
    refine ⟨214163106661886630894639261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142775404441257753929759507 214163106661886630894639261)
    ·
      refine ⟨80311164998207486585489723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214163106661886630894639261 80311164998207486585489723)
      ·
        refine ⟨120466747497311229878234585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80311164998207486585489723 120466747497311229878234585)
        ·
          refine ⟨90350060622983422408675939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120466747497311229878234585 90350060622983422408675939)
          ·
            refine ⟨135525090934475133613013909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90350060622983422408675939 135525090934475133613013909)
            ·
              refine ⟨6352738637553521888110027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 135525090934475133613013909 6352738637553521888110027)
              ·
                refine ⟨9529107956330282832165041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6352738637553521888110027 9529107956330282832165041)
                ·
                  refine ⟨7146830967247712124123781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9529107956330282832165041 7146830967247712124123781)
                  ·
                    refine ⟨1340030806358946023273209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7146830967247712124123781 1340030806358946023273209)
                    ·
                      rfl

theorem cell22_3914551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 4].length) (baseStart_3914551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914551 prefixEnd_3914551 := by exact prefixLift 3914551
  have htrace : WordTrace (prefixWord ++ tailWord_3914551) baseStart_3914551 baseEnd_3914551 := by
    simpa [prefixWord, tailWord_3914551, baseEnd_3914551] using wordTrace_append hprefix tailTrace_3914551
  have hstable : (prefixWord ++ tailWord_3914551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914551).length < 2 ^ (prefixWord ++ tailWord_3914551).sum := by decide
  have hdescent : baseEnd_3914551 < baseStart_3914551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914656 : List Nat := [2, 1, 1, 4, 1, 1, 4, 2, 6]
def baseStart_3914656 : Nat := 118140960795 + 3914656 * 2 ^ 59
def prefixEnd_3914656 : Nat := 4983230072969 + 3 ^ 40 * 3914656 * 2
def baseEnd_3914656 : Nat := 446688916668253583132629

theorem tailTrace_3914656 : CollatzResearch.WordTrace tailWord_3914656 prefixEnd_3914656 446688916668253583132629 := by
  unfold tailWord_3914656
  simp only [CollatzResearch.WordTrace]
  refine ⟨71389617052938678431165911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95186156070584904574887881 71389617052938678431165911)
  ·
    refine ⟨107084425579408017646748867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71389617052938678431165911 107084425579408017646748867)
    ·
      refine ⟨160626638369112026470123301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107084425579408017646748867 160626638369112026470123301)
      ·
        refine ⟨30117494694208504963148119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160626638369112026470123301 30117494694208504963148119)
        ·
          refine ⟨45176242041312757444722179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30117494694208504963148119 45176242041312757444722179)
          ·
            refine ⟨67764363061969136167083269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45176242041312757444722179 67764363061969136167083269)
            ·
              refine ⟨12705818074119213031328113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67764363061969136167083269 12705818074119213031328113)
              ·
                refine ⟨9529363555589409773496085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12705818074119213031328113 9529363555589409773496085)
                ·
                  refine ⟨446688916668253583132629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9529363555589409773496085 446688916668253583132629)
                  ·
                    rfl

theorem cell22_3914656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 6].length) (baseStart_3914656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914656 prefixEnd_3914656 := by exact prefixLift 3914656
  have htrace : WordTrace (prefixWord ++ tailWord_3914656) baseStart_3914656 baseEnd_3914656 := by
    simpa [prefixWord, tailWord_3914656, baseEnd_3914656] using wordTrace_append hprefix tailTrace_3914656
  have hstable : (prefixWord ++ tailWord_3914656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914656).length < 2 ^ (prefixWord ++ tailWord_3914656).sum := by decide
  have hdescent : baseEnd_3914656 < baseStart_3914656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914688 : List Nat := [2, 1, 1, 2, 3, 3, 2, 1, 4, 3]
def baseStart_3914688 : Nat := 118140960795 + 3914688 * 2 ^ 59
def prefixEnd_3914688 : Nat := 4983230072969 + 3 ^ 40 * 3914688 * 2
def baseEnd_3914688 : Nat := 1340077704258723332597789

theorem tailTrace_3914688 : CollatzResearch.WordTrace tailWord_3914688 prefixEnd_3914688 1340077704258723332597789 := by
  unfold tailWord_3914688
  simp only [CollatzResearch.WordTrace]
  refine ⟨71390200620880713163748359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95186934161174284218331145 71390200620880713163748359)
  ·
    refine ⟨107085300931321069745622539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71390200620880713163748359 107085300931321069745622539)
    ·
      refine ⟨160627951396981604618433809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107085300931321069745622539 160627951396981604618433809)
      ·
        refine ⟨120470963547736203463825357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160627951396981604618433809 120470963547736203463825357)
        ·
          refine ⟨45176611330401076298934509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120470963547736203463825357 45176611330401076298934509)
          ·
            refine ⟨16941229248900403612100441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45176611330401076298934509 16941229248900403612100441)
            ·
              refine ⟨12705921936675302709075331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16941229248900403612100441 12705921936675302709075331)
              ·
                refine ⟨19058882905012954063612997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12705921936675302709075331 19058882905012954063612997)
                ·
                  refine ⟨3573540544689928886927437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19058882905012954063612997 3573540544689928886927437)
                  ·
                    refine ⟨1340077704258723332597789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3573540544689928886927437 1340077704258723332597789)
                    ·
                      rfl

theorem cell22_3914688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 4, 3].length) (baseStart_3914688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914688 prefixEnd_3914688 := by exact prefixLift 3914688
  have htrace : WordTrace (prefixWord ++ tailWord_3914688) baseStart_3914688 baseEnd_3914688 := by
    simpa [prefixWord, tailWord_3914688, baseEnd_3914688] using wordTrace_append hprefix tailTrace_3914688
  have hstable : (prefixWord ++ tailWord_3914688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914688).length < 2 ^ (prefixWord ++ tailWord_3914688).sum := by decide
  have hdescent : baseEnd_3914688 < baseStart_3914688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914741 : List Nat := [1, 3, 5, 2, 1, 2, 2, 2, 4]
def baseStart_3914741 : Nat := 118140960795 + 3914741 * 2 ^ 59
def prefixEnd_3914741 : Nat := 4983230072969 + 3 ^ 40 * 3914741 * 2
def baseEnd_3914741 : Nat := 446698615747282953674209

theorem tailTrace_3914741 : CollatzResearch.WordTrace tailWord_3914741 prefixEnd_3914741 446698615747282953674209 := by
  unfold tailWord_3914741
  simp only [CollatzResearch.WordTrace]
  refine ⟨142782334310569416379176077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95188222873712944252784051 142782334310569416379176077)
  ·
    refine ⟨53543375366463531142191029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142782334310569416379176077 53543375366463531142191029)
    ·
      refine ⟨5019691440605956044580409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53543375366463531142191029 5019691440605956044580409)
      ·
        refine ⟨3764768580454467033435307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5019691440605956044580409 3764768580454467033435307)
        ·
          refine ⟨5647152870681700550152961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3764768580454467033435307 5647152870681700550152961)
          ·
            refine ⟨4235364653011275412614721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5647152870681700550152961 4235364653011275412614721)
            ·
              refine ⟨3176523489758456559461041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4235364653011275412614721 3176523489758456559461041)
              ·
                refine ⟨2382392617318842419595781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3176523489758456559461041 2382392617318842419595781)
                ·
                  refine ⟨446698615747282953674209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2382392617318842419595781 446698615747282953674209)
                  ·
                    rfl

theorem cell22_3914741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 2, 4].length) (baseStart_3914741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914741 prefixEnd_3914741 := by exact prefixLift 3914741
  have htrace : WordTrace (prefixWord ++ tailWord_3914741) baseStart_3914741 baseEnd_3914741 := by
    simpa [prefixWord, tailWord_3914741, baseEnd_3914741] using wordTrace_append hprefix tailTrace_3914741
  have hstable : (prefixWord ++ tailWord_3914741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914741).length < 2 ^ (prefixWord ++ tailWord_3914741).sum := by decide
  have hdescent : baseEnd_3914741 < baseStart_3914741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914746 : List Nat := [3, 1, 1, 1, 1, 2, 1, 5, 7]
def baseStart_3914746 : Nat := 118140960795 + 3914746 * 2 ^ 59
def prefixEnd_3914746 : Nat := 4983230072969 + 3 ^ 40 * 3914746 * 2
def baseEnd_3914746 : Nat := 446699186281343504882537

theorem tailTrace_3914746 : CollatzResearch.WordTrace tailWord_3914746 prefixEnd_3914746 446699186281343504882537 := by
  unfold tailWord_3914746
  simp only [CollatzResearch.WordTrace]
  refine ⟨35695629168887825558277023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95188344450367534822072061 35695629168887825558277023)
  ·
    refine ⟨53543443753331738337415535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35695629168887825558277023 53543443753331738337415535)
    ·
      refine ⟨80315165629997607506123303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53543443753331738337415535 80315165629997607506123303)
      ·
        refine ⟨120472748444996411259184955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80315165629997607506123303 120472748444996411259184955)
        ·
          refine ⟨180709122667494616888777433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120472748444996411259184955 180709122667494616888777433)
          ·
            refine ⟨135531842000620962666583075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180709122667494616888777433 135531842000620962666583075)
            ·
              refine ⟨203297763000931443999874613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135531842000620962666583075 203297763000931443999874613)
              ·
                refine ⟨19059165281337322874988245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 203297763000931443999874613 19059165281337322874988245)
                ·
                  refine ⟨446699186281343504882537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19059165281337322874988245 446699186281343504882537)
                  ·
                    rfl

theorem cell22_3914746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 7].length) (baseStart_3914746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914746 prefixEnd_3914746 := by exact prefixLift 3914746
  have htrace : WordTrace (prefixWord ++ tailWord_3914746) baseStart_3914746 baseEnd_3914746 := by
    simpa [prefixWord, tailWord_3914746, baseEnd_3914746] using wordTrace_append hprefix tailTrace_3914746
  have hstable : (prefixWord ++ tailWord_3914746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914746).length < 2 ^ (prefixWord ++ tailWord_3914746).sum := by decide
  have hdescent : baseEnd_3914746 < baseStart_3914746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914763 : List Nat := [1, 1, 1, 1, 6, 2, 2, 3, 5]
def baseStart_3914763 : Nat := 118140960795 + 3914763 * 2 ^ 59
def prefixEnd_3914763 : Nat := 4983230072969 + 3 ^ 40 * 3914763 * 2
def baseEnd_3914763 : Nat := 446701126097149378990853

theorem tailTrace_3914763 : CollatzResearch.WordTrace tailWord_3914763 prefixEnd_3914763 446701126097149378990853 := by
  unfold tailWord_3914763
  simp only [CollatzResearch.WordTrace]
  refine ⟨142783136716489714136476943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95188757810993142757651295 142783136716489714136476943)
  ·
    refine ⟨214174705074734571204715415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142783136716489714136476943 214174705074734571204715415)
    ·
      refine ⟨321262057612101856807073123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214174705074734571204715415 321262057612101856807073123)
      ·
        refine ⟨481893086418152785210609685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321262057612101856807073123 481893086418152785210609685)
        ·
          refine ⟨22588738425850911806747329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 481893086418152785210609685 22588738425850911806747329)
          ·
            refine ⟨16941553819388183855060497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22588738425850911806747329 16941553819388183855060497)
            ·
              refine ⟨12706165364541137891295373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16941553819388183855060497 12706165364541137891295373)
              ·
                refine ⟨4764812011702926709235765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12706165364541137891295373 4764812011702926709235765)
                ·
                  refine ⟨446701126097149378990853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4764812011702926709235765 446701126097149378990853)
                  ·
                    rfl

theorem cell22_3914763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 5].length) (baseStart_3914763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914763 prefixEnd_3914763 := by exact prefixLift 3914763
  have htrace : WordTrace (prefixWord ++ tailWord_3914763) baseStart_3914763 baseEnd_3914763 := by
    simpa [prefixWord, tailWord_3914763, baseEnd_3914763] using wordTrace_append hprefix tailTrace_3914763
  have hstable : (prefixWord ++ tailWord_3914763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914763).length < 2 ^ (prefixWord ++ tailWord_3914763).sum := by decide
  have hdescent : baseEnd_3914763 < baseStart_3914763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914808 : List Nat := [2, 1, 2, 1, 5, 1, 1, 3, 6]
def baseStart_3914808 : Nat := 118140960795 + 3914808 * 2 ^ 59
def prefixEnd_3914808 : Nat := 4983230072969 + 3 ^ 40 * 3914808 * 2
def baseEnd_3914808 : Nat := 446706260903694339865807

theorem tailTrace_3914808 : CollatzResearch.WordTrace tailWord_3914808 prefixEnd_3914808 446706260903694339865807 := by
  unfold tailWord_3914808
  simp only [CollatzResearch.WordTrace]
  refine ⟨71392389000663343410932539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95189852000884457881243385 71392389000663343410932539)
  ·
    refine ⟨107088583500995015116398809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71392389000663343410932539 107088583500995015116398809)
    ·
      refine ⟨80316437625746261337299107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107088583500995015116398809 80316437625746261337299107)
      ·
        refine ⟨120474656438619392005948661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80316437625746261337299107 120474656438619392005948661)
        ·
          refine ⟨11294499041120568000557687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120474656438619392005948661 11294499041120568000557687)
          ·
            refine ⟨16941748561680852000836531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11294499041120568000557687 16941748561680852000836531)
            ·
              refine ⟨25412622842521278001254797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16941748561680852000836531 25412622842521278001254797)
              ·
                refine ⟨9529733565945479250470549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25412622842521278001254797 9529733565945479250470549)
                ·
                  refine ⟨446706260903694339865807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9529733565945479250470549 446706260903694339865807)
                  ·
                    rfl

theorem cell22_3914808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 6].length) (baseStart_3914808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914808 prefixEnd_3914808 := by exact prefixLift 3914808
  have htrace : WordTrace (prefixWord ++ tailWord_3914808) baseStart_3914808 baseEnd_3914808 := by
    simpa [prefixWord, tailWord_3914808, baseEnd_3914808] using wordTrace_append hprefix tailTrace_3914808
  have hstable : (prefixWord ++ tailWord_3914808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914808).length < 2 ^ (prefixWord ++ tailWord_3914808).sum := by decide
  have hdescent : baseEnd_3914808 < baseStart_3914808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914855 : List Nat := [1, 1, 5, 1, 1, 4, 1, 2, 2, 4]
def baseStart_3914855 : Nat := 118140960795 + 3914855 * 2 ^ 59
def prefixEnd_3914855 : Nat := 4983230072969 + 3 ^ 40 * 3914855 * 2
def baseEnd_3914855 : Nat := 1340134871771590563672277

theorem tailTrace_3914855 : CollatzResearch.WordTrace tailWord_3914855 prefixEnd_3914855 1340134871771590563672277 := by
  unfold tailWord_3914855
  simp only [CollatzResearch.WordTrace]
  refine ⟨142786492232156413848826019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95190994821437609232550679 142786492232156413848826019)
  ·
    refine ⟨214179738348234620773239029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142786492232156413848826019 214179738348234620773239029)
    ·
      refine ⟨20079350470146995697491159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 214179738348234620773239029 20079350470146995697491159)
      ·
        refine ⟨30119025705220493546236739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20079350470146995697491159 30119025705220493546236739)
        ·
          refine ⟨45178538557830740319355109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30119025705220493546236739 45178538557830740319355109)
          ·
            refine ⟨8470975979593263809879083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45178538557830740319355109 8470975979593263809879083)
            ·
              refine ⟨12706463969389895714818625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8470975979593263809879083 12706463969389895714818625)
              ·
                refine ⟨9529847977042421786113969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12706463969389895714818625 9529847977042421786113969)
                ·
                  refine ⟨7147385982781816339585477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9529847977042421786113969 7147385982781816339585477)
                  ·
                    refine ⟨1340134871771590563672277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7147385982781816339585477 1340134871771590563672277)
                    ·
                      rfl

theorem cell22_3914855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_3914855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914855 prefixEnd_3914855 := by exact prefixLift 3914855
  have htrace : WordTrace (prefixWord ++ tailWord_3914855) baseStart_3914855 baseEnd_3914855 := by
    simpa [prefixWord, tailWord_3914855, baseEnd_3914855] using wordTrace_append hprefix tailTrace_3914855
  have hstable : (prefixWord ++ tailWord_3914855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914855).length < 2 ^ (prefixWord ++ tailWord_3914855).sum := by decide
  have hdescent : baseEnd_3914855 < baseStart_3914855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914870 : List Nat := [5, 1, 1, 2, 1, 1, 4, 7]
def baseStart_3914870 : Nat := 118140960795 + 3914870 * 2 ^ 59
def prefixEnd_3914870 : Nat := 4983230072969 + 3 ^ 40 * 3914870 * 2
def baseEnd_3914870 : Nat := 148904445175348391616359

theorem tailTrace_3914870 : CollatzResearch.WordTrace tailWord_3914870 prefixEnd_3914870 148904445175348391616359 := by
  unfold tailWord_3914870
  simp only [CollatzResearch.WordTrace]
  refine ⟨8924189957943879463163879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95191359551401380940414709 8924189957943879463163879)
  ·
    refine ⟨13386284936915819194745819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8924189957943879463163879 13386284936915819194745819)
    ·
      refine ⟨20079427405373728792118729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13386284936915819194745819 20079427405373728792118729)
      ·
        refine ⟨15059570554030296594089047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20079427405373728792118729 15059570554030296594089047)
        ·
          refine ⟨22589355831045444891133571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15059570554030296594089047 22589355831045444891133571)
          ·
            refine ⟨33884033746568167336700357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22589355831045444891133571 33884033746568167336700357)
            ·
              refine ⟨6353256327481531375631317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33884033746568167336700357 6353256327481531375631317)
              ·
                refine ⟨148904445175348391616359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6353256327481531375631317 148904445175348391616359)
                ·
                  rfl

theorem cell22_3914870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_3914870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914870 prefixEnd_3914870 := by exact prefixLift 3914870
  have htrace : WordTrace (prefixWord ++ tailWord_3914870) baseStart_3914870 baseEnd_3914870 := by
    simpa [prefixWord, tailWord_3914870, baseEnd_3914870] using wordTrace_append hprefix tailTrace_3914870
  have hstable : (prefixWord ++ tailWord_3914870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914870).length < 2 ^ (prefixWord ++ tailWord_3914870).sum := by decide
  have hdescent : baseEnd_3914870 < baseStart_3914870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914878 : List Nat := [4, 2, 4, 1, 1, 2, 1, 2, 1, 4]
def baseStart_3914878 : Nat := 118140960795 + 3914878 * 2 ^ 59
def prefixEnd_3914878 : Nat := 4983230072969 + 3 ^ 40 * 3914878 * 2
def baseEnd_3914878 : Nat := 1340142745141626170347207

theorem tailTrace_3914878 : CollatzResearch.WordTrace tailWord_3914878 prefixEnd_3914878 1340142745141626170347207 := by
  unfold tailWord_3914878
  simp only [CollatzResearch.WordTrace]
  refine ⟨17848416388884136097114161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95191554074048725851275525 17848416388884136097114161)
  ·
    refine ⟨13386312291663102072835621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17848416388884136097114161 13386312291663102072835621)
    ·
      refine ⟨2509933554686831638656679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13386312291663102072835621 2509933554686831638656679)
      ·
        refine ⟨3764900332030247457985019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2509933554686831638656679 3764900332030247457985019)
        ·
          refine ⟨5647350498045371186977529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3764900332030247457985019 5647350498045371186977529)
          ·
            refine ⟨4235512873534028390233147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5647350498045371186977529 4235512873534028390233147)
            ·
              refine ⟨6353269310301042585349721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4235512873534028390233147 6353269310301042585349721)
              ·
                refine ⟨4764951982725781939012291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6353269310301042585349721 4764951982725781939012291)
                ·
                  refine ⟨7147427974088672908518437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4764951982725781939012291 7147427974088672908518437)
                  ·
                    refine ⟨1340142745141626170347207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7147427974088672908518437 1340142745141626170347207)
                    ·
                      rfl

theorem cell22_3914878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_3914878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914878 prefixEnd_3914878 := by exact prefixLift 3914878
  have htrace : WordTrace (prefixWord ++ tailWord_3914878) baseStart_3914878 baseEnd_3914878 := by
    simpa [prefixWord, tailWord_3914878, baseEnd_3914878] using wordTrace_append hprefix tailTrace_3914878
  have hstable : (prefixWord ++ tailWord_3914878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914878).length < 2 ^ (prefixWord ++ tailWord_3914878).sum := by decide
  have hdescent : baseEnd_3914878 < baseStart_3914878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914930 : List Nat := [3, 2, 1, 1, 1, 5, 1, 1, 2, 5]
def baseStart_3914930 : Nat := 118140960795 + 3914930 * 2 ^ 59
def prefixEnd_3914930 : Nat := 4983230072969 + 3 ^ 40 * 3914930 * 2
def baseEnd_3914930 : Nat := 1340160545804315368047047

theorem tailTrace_3914930 : CollatzResearch.WordTrace tailWord_3914930 prefixEnd_3914930 1340160545804315368047047 := by
  unfold tailWord_3914930
  simp only [CollatzResearch.WordTrace]
  refine ⟨35697306926721175414451561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95192818471256467771870829 35697306926721175414451561)
  ·
    refine ⟨26772980195040881560838671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35697306926721175414451561 26772980195040881560838671)
    ·
      refine ⟨40159470292561322341258007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26772980195040881560838671 40159470292561322341258007)
      ·
        refine ⟨60239205438841983511887011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40159470292561322341258007 60239205438841983511887011)
        ·
          refine ⟨90358808158262975267830517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60239205438841983511887011 90358808158262975267830517)
          ·
            refine ⟨8471138264837153931359111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90358808158262975267830517 8471138264837153931359111)
            ·
              refine ⟨12706707397255730897038667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8471138264837153931359111 12706707397255730897038667)
              ·
                refine ⟨19060061095883596345558001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12706707397255730897038667 19060061095883596345558001)
                ·
                  refine ⟨14295045821912697259168501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19060061095883596345558001 14295045821912697259168501)
                  ·
                    refine ⟨1340160545804315368047047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14295045821912697259168501 1340160545804315368047047)
                    ·
                      rfl

theorem cell22_3914930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_3914930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914930 prefixEnd_3914930 := by exact prefixLift 3914930
  have htrace : WordTrace (prefixWord ++ tailWord_3914930) baseStart_3914930 baseEnd_3914930 := by
    simpa [prefixWord, tailWord_3914930, baseEnd_3914930] using wordTrace_append hprefix tailTrace_3914930
  have hstable : (prefixWord ++ tailWord_3914930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914930).length < 2 ^ (prefixWord ++ tailWord_3914930).sum := by decide
  have hdescent : baseEnd_3914930 < baseStart_3914930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914943 : List Nat := [1, 1, 2, 2, 2, 2, 3, 1, 8]
def baseStart_3914943 : Nat := 118140960795 + 3914943 * 2 ^ 59
def prefixEnd_3914943 : Nat := 4983230072969 + 3 ^ 40 * 3914943 * 2
def baseEnd_3914943 : Nat := 446721665323329222490669

theorem tailTrace_3914943 : CollatzResearch.WordTrace tailWord_3914943 prefixEnd_3914943 446721665323329222490669 := by
  unfold tailWord_3914943
  simp only [CollatzResearch.WordTrace]
  refine ⟨142789701855837604878029483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95193134570558403252019655 142789701855837604878029483)
  ·
    refine ⟨214184552783756407317044225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142789701855837604878029483 214184552783756407317044225)
    ·
      refine ⟨160638414587817305487783169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214184552783756407317044225 160638414587817305487783169)
      ·
        refine ⟨120478810940862979115837377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160638414587817305487783169 120478810940862979115837377)
        ·
          refine ⟨90359108205647234336878033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120478810940862979115837377 90359108205647234336878033)
          ·
            refine ⟨67769331154235425752658525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90359108205647234336878033 67769331154235425752658525)
            ·
              refine ⟨25413499182838284657246947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67769331154235425752658525 25413499182838284657246947)
              ·
                refine ⟨38120248774257426985870421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25413499182838284657246947 38120248774257426985870421)
                ·
                  refine ⟨446721665323329222490669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38120248774257426985870421 446721665323329222490669)
                  ·
                    rfl

theorem cell22_3914943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 8].length) (baseStart_3914943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914943 prefixEnd_3914943 := by exact prefixLift 3914943
  have htrace : WordTrace (prefixWord ++ tailWord_3914943) baseStart_3914943 baseEnd_3914943 := by
    simpa [prefixWord, tailWord_3914943, baseEnd_3914943] using wordTrace_append hprefix tailTrace_3914943
  have hstable : (prefixWord ++ tailWord_3914943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914943).length < 2 ^ (prefixWord ++ tailWord_3914943).sum := by decide
  have hdescent : baseEnd_3914943 < baseStart_3914943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914962 : List Nat := [3, 2, 2, 2, 1, 1, 3, 3, 1, 4]
def baseStart_3914962 : Nat := 118140960795 + 3914962 * 2 ^ 59
def prefixEnd_3914962 : Nat := 4983230072969 + 3 ^ 40 * 3914962 * 2
def baseEnd_3914962 : Nat := 1340171500058277951246949

theorem tailTrace_3914962 : CollatzResearch.WordTrace tailWord_3914962 prefixEnd_3914962 1340171500058277951246949 := by
  unfold tailWord_3914962
  simp only [CollatzResearch.WordTrace]
  refine ⟨35697598710692192780742785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95193596561845847415314093 35697598710692192780742785)
  ·
    refine ⟨26773199033019144585557089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35697598710692192780742785 26773199033019144585557089)
    ·
      refine ⟨20079899274764358439167817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26773199033019144585557089 20079899274764358439167817)
      ·
        refine ⟨15059924456073268829375863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20079899274764358439167817 15059924456073268829375863)
        ·
          refine ⟨22589886684109903244063795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15059924456073268829375863 22589886684109903244063795)
          ·
            refine ⟨33884830026164854866095693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22589886684109903244063795 33884830026164854866095693)
            ·
              refine ⟨12706811259811820574785885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33884830026164854866095693 12706811259811820574785885)
              ·
                refine ⟨4765054222429432715544707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12706811259811820574785885 4765054222429432715544707)
                ·
                  refine ⟨7147581333644149073317061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4765054222429432715544707 7147581333644149073317061)
                  ·
                    refine ⟨1340171500058277951246949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7147581333644149073317061 1340171500058277951246949)
                    ·
                      rfl

theorem cell22_3914962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_3914962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914962 prefixEnd_3914962 := by exact prefixLift 3914962
  have htrace : WordTrace (prefixWord ++ tailWord_3914962) baseStart_3914962 baseEnd_3914962 := by
    simpa [prefixWord, tailWord_3914962, baseEnd_3914962] using wordTrace_append hprefix tailTrace_3914962
  have hstable : (prefixWord ++ tailWord_3914962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914962).length < 2 ^ (prefixWord ++ tailWord_3914962).sum := by decide
  have hdescent : baseEnd_3914962 < baseStart_3914962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914966 : List Nat := [5, 2, 1, 2, 2, 2, 1, 2, 5]
def baseStart_3914966 : Nat := 118140960795 + 3914966 * 2 ^ 59
def prefixEnd_3914966 : Nat := 4983230072969 + 3 ^ 40 * 3914966 * 2
def baseEnd_3914966 : Nat := 446724289780007758048979

theorem tailTrace_3914966 : CollatzResearch.WordTrace tailWord_3914966 prefixEnd_3914966 446724289780007758048979 := by
  unfold tailWord_3914966
  simp only [CollatzResearch.WordTrace]
  refine ⟨8924408795922142487882297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95193693823169519870744501 8924408795922142487882297)
  ·
    refine ⟨6693306596941606865911723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8924408795922142487882297 6693306596941606865911723)
    ·
      refine ⟨10039959895412410298867585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6693306596941606865911723 10039959895412410298867585)
      ·
        refine ⟨7529969921559307724150689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10039959895412410298867585 7529969921559307724150689)
        ·
          refine ⟨5647477441169480793113017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7529969921559307724150689 5647477441169480793113017)
          ·
            refine ⟨4235608080877110594834763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5647477441169480793113017 4235608080877110594834763)
            ·
              refine ⟨6353412121315665892252145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4235608080877110594834763 6353412121315665892252145)
              ·
                refine ⟨4765059090986749419189109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6353412121315665892252145 4765059090986749419189109)
                ·
                  refine ⟨446724289780007758048979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4765059090986749419189109 446724289780007758048979)
                  ·
                    rfl

theorem cell22_3914966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_3914966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914966 prefixEnd_3914966 := by exact prefixLift 3914966
  have htrace : WordTrace (prefixWord ++ tailWord_3914966) baseStart_3914966 baseEnd_3914966 := by
    simpa [prefixWord, tailWord_3914966, baseEnd_3914966] using wordTrace_append hprefix tailTrace_3914966
  have hstable : (prefixWord ++ tailWord_3914966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914966).length < 2 ^ (prefixWord ++ tailWord_3914966).sum := by decide
  have hdescent : baseEnd_3914966 < baseStart_3914966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914977 : List Nat := [1, 2, 3, 1, 3, 2, 2, 4, 4]
def baseStart_3914977 : Nat := 118140960795 + 3914977 * 2 ^ 59
def prefixEnd_3914977 : Nat := 4983230072969 + 3 ^ 40 * 3914977 * 2
def baseEnd_3914977 : Nat := 446725544954940970707301

theorem tailTrace_3914977 : CollatzResearch.WordTrace tailWord_3914977 prefixEnd_3914977 446725544954940970707301 := by
  unfold tailWord_3914977
  simp only [CollatzResearch.WordTrace]
  refine ⟨142790941937714428684767185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95193961291809619123178123 142790941937714428684767185)
  ·
    refine ⟨107093206453285821513575389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142790941937714428684767185 107093206453285821513575389)
    ·
      refine ⟨40159952419982183067590771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107093206453285821513575389 40159952419982183067590771)
      ·
        refine ⟨60239928629973274601386157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40159952419982183067590771 60239928629973274601386157)
        ·
          refine ⟨22589973236239977975519809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60239928629973274601386157 22589973236239977975519809)
          ·
            refine ⟨16942479927179983481639857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22589973236239977975519809 16942479927179983481639857)
            ·
              refine ⟨12706859945384987611229893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16942479927179983481639857 12706859945384987611229893)
              ·
                refine ⟨2382536239759685177105605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12706859945384987611229893 2382536239759685177105605)
                ·
                  refine ⟨446725544954940970707301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2382536239759685177105605 446725544954940970707301)
                  ·
                    rfl

theorem cell22_3914977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 4, 4].length) (baseStart_3914977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914977 prefixEnd_3914977 := by exact prefixLift 3914977
  have htrace : WordTrace (prefixWord ++ tailWord_3914977) baseStart_3914977 baseEnd_3914977 := by
    simpa [prefixWord, tailWord_3914977, baseEnd_3914977] using wordTrace_append hprefix tailTrace_3914977
  have hstable : (prefixWord ++ tailWord_3914977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914977).length < 2 ^ (prefixWord ++ tailWord_3914977).sum := by decide
  have hdescent : baseEnd_3914977 < baseStart_3914977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914990 : List Nat := [4, 1, 2, 1, 1, 1, 3, 2, 1, 6]
def baseStart_3914990 : Nat := 118140960795 + 3914990 * 2 ^ 59
def prefixEnd_3914990 : Nat := 4983230072969 + 3 ^ 40 * 3914990 * 2
def baseEnd_3914990 : Nat := 1340181085030495211546863

theorem tailTrace_3914990 : CollatzResearch.WordTrace tailWord_3914990 prefixEnd_3914990 1340181085030495211546863 := by
  unfold tailWord_3914990
  simp only [CollatzResearch.WordTrace]
  refine ⟨17848927010833416488123803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95194277391111554603326949 17848927010833416488123803)
  ·
    refine ⟨26773390516250124732185705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17848927010833416488123803 26773390516250124732185705)
    ·
      refine ⟨20080042887187593549139279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26773390516250124732185705 20080042887187593549139279)
      ·
        refine ⟨30120064330781390323708919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20080042887187593549139279 30120064330781390323708919)
        ·
          refine ⟨45180096496172085485563379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30120064330781390323708919 45180096496172085485563379)
          ·
            refine ⟨67770144744258128228345069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45180096496172085485563379 67770144744258128228345069)
            ·
              refine ⟨25413804279096798085629401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67770144744258128228345069 25413804279096798085629401)
              ·
                refine ⟨19060353209322598564222051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25413804279096798085629401 19060353209322598564222051)
                ·
                  refine ⟨28590529813983897846333077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19060353209322598564222051 28590529813983897846333077)
                  ·
                    refine ⟨1340181085030495211546863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28590529813983897846333077 1340181085030495211546863)
                    ·
                      rfl

theorem cell22_3914990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_3914990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914990 prefixEnd_3914990 := by exact prefixLift 3914990
  have htrace : WordTrace (prefixWord ++ tailWord_3914990) baseStart_3914990 baseEnd_3914990 := by
    simpa [prefixWord, tailWord_3914990, baseEnd_3914990] using wordTrace_append hprefix tailTrace_3914990
  have hstable : (prefixWord ++ tailWord_3914990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914990).length < 2 ^ (prefixWord ++ tailWord_3914990).sum := by decide
  have hdescent : baseEnd_3914990 < baseStart_3914990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915127 : List Nat := [1, 1, 3, 1, 1, 2, 4, 2, 4, 3]
def baseStart_3915127 : Nat := 118140960795 + 3915127 * 2 ^ 59
def prefixEnd_3915127 : Nat := 4983230072969 + 3 ^ 40 * 3915127 * 2
def baseEnd_3915127 : Nat := 1340227982930272520871443

theorem tailTrace_3915127 : CollatzResearch.WordTrace tailWord_3915127 prefixEnd_3915127 1340227982930272520871443 := by
  unfold tailWord_3915127
  simp only [CollatzResearch.WordTrace]
  refine ⟨142796412887171004302727635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95197608591447336201818423 142796412887171004302727635)
  ·
    refine ⟨214194619330756506454091453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142796412887171004302727635 214194619330756506454091453)
    ·
      refine ⟨80322982249033689920284295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214194619330756506454091453 80322982249033689920284295)
      ·
        refine ⟨120484473373550534880426443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80322982249033689920284295 120484473373550534880426443)
        ·
          refine ⟨180726710060325802320639665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120484473373550534880426443 180726710060325802320639665)
          ·
            refine ⟨135545032545244351740479749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180726710060325802320639665 135545032545244351740479749)
            ·
              refine ⟨25414693602233315951339953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135545032545244351740479749 25414693602233315951339953)
              ·
                refine ⟨19061020201674986963504965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25414693602233315951339953 19061020201674986963504965)
                ·
                  refine ⟨3573941287814060055657181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19061020201674986963504965 3573941287814060055657181)
                  ·
                    refine ⟨1340227982930272520871443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3573941287814060055657181 1340227982930272520871443)
                    ·
                      rfl

theorem cell22_3915127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 4, 3].length) (baseStart_3915127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3915127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3915127 prefixEnd_3915127 := by exact prefixLift 3915127
  have htrace : WordTrace (prefixWord ++ tailWord_3915127) baseStart_3915127 baseEnd_3915127 := by
    simpa [prefixWord, tailWord_3915127, baseEnd_3915127] using wordTrace_append hprefix tailTrace_3915127
  have hstable : (prefixWord ++ tailWord_3915127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915127).length < 2 ^ (prefixWord ++ tailWord_3915127).sum := by decide
  have hdescent : baseEnd_3915127 < baseStart_3915127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915144 : List Nat := [2, 1, 3, 3, 1, 3, 1, 1, 4, 3]
def baseStart_3915144 : Nat := 118140960795 + 3915144 * 2 ^ 59
def prefixEnd_3915144 : Nat := 4983230072969 + 3 ^ 40 * 3915144 * 2
def baseEnd_3915144 : Nat := 1340233802377690143196391

theorem tailTrace_3915144 : CollatzResearch.WordTrace tailWord_3915144 prefixEnd_3915144 1340233802377690143196391 := by
  unfold tailWord_3915144
  simp only [CollatzResearch.WordTrace]
  refine ⟨71398516464054708103048243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95198021952072944137397657 71398516464054708103048243)
  ·
    refine ⟨107097774696082062154572365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71398516464054708103048243 107097774696082062154572365)
    ·
      refine ⟨40161665511030773307964637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107097774696082062154572365 40161665511030773307964637)
      ·
        refine ⟨15060624566636539990486739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40161665511030773307964637 15060624566636539990486739)
        ·
          refine ⟨22590936849954809985730109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15060624566636539990486739 22590936849954809985730109)
          ·
            refine ⟨8471601318733053744648791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22590936849954809985730109 8471601318733053744648791)
            ·
              refine ⟨12707401978099580616973187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8471601318733053744648791 12707401978099580616973187)
              ·
                refine ⟨19061102967149370925459781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12707401978099580616973187 19061102967149370925459781)
                ·
                  refine ⟨3573956806340507048523709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19061102967149370925459781 3573956806340507048523709)
                  ·
                    refine ⟨1340233802377690143196391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3573956806340507048523709 1340233802377690143196391)
                    ·
                      rfl

theorem cell22_3915144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_3915144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3915144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3915144 prefixEnd_3915144 := by exact prefixLift 3915144
  have htrace : WordTrace (prefixWord ++ tailWord_3915144) baseStart_3915144 baseEnd_3915144 := by
    simpa [prefixWord, tailWord_3915144, baseEnd_3915144] using wordTrace_append hprefix tailTrace_3915144
  have hstable : (prefixWord ++ tailWord_3915144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915144).length < 2 ^ (prefixWord ++ tailWord_3915144).sum := by decide
  have hdescent : baseEnd_3915144 < baseStart_3915144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915161 : List Nat := [1, 2, 1, 2, 1, 6, 3, 1, 2, 3]
def baseStart_3915161 : Nat := 118140960795 + 3915161 * 2 ^ 59
def prefixEnd_3915161 : Nat := 4983230072969 + 3 ^ 40 * 3915161 * 2
def baseEnd_3915161 : Nat := 1340239621825107765521339

theorem tailTrace_3915161 : CollatzResearch.WordTrace tailWord_3915161 prefixEnd_3915161 1340239621825107765521339 := by
  unfold tailWord_3915161
  simp only [CollatzResearch.WordTrace]
  refine ⟨142797652969047828109465337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95198435312698552072976891 142797652969047828109465337)
  ·
    refine ⟨107098239726785871082099003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142797652969047828109465337 107098239726785871082099003)
    ·
      refine ⟨160647359590178806623148505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107098239726785871082099003 160647359590178806623148505)
      ·
        refine ⟨120485519692634104967361379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160647359590178806623148505 120485519692634104967361379)
        ·
          refine ⟨180728279538951157451042069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120485519692634104967361379 180728279538951157451042069)
          ·
            refine ⟨8471638103388335505517597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 180728279538951157451042069 8471638103388335505517597)
            ·
              refine ⟨3176864288770625814569099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8471638103388335505517597 3176864288770625814569099)
              ·
                refine ⟨4765296433155938721853649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3176864288770625814569099 4765296433155938721853649)
                ·
                  refine ⟨3573972324866954041390237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4765296433155938721853649 3573972324866954041390237)
                  ·
                    refine ⟨1340239621825107765521339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3573972324866954041390237 1340239621825107765521339)
                    ·
                      rfl

theorem cell22_3915161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 2, 3].length) (baseStart_3915161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3915161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3915161 prefixEnd_3915161 := by exact prefixLift 3915161
  have htrace : WordTrace (prefixWord ++ tailWord_3915161) baseStart_3915161 baseEnd_3915161 := by
    simpa [prefixWord, tailWord_3915161, baseEnd_3915161] using wordTrace_append hprefix tailTrace_3915161
  have hstable : (prefixWord ++ tailWord_3915161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915161).length < 2 ^ (prefixWord ++ tailWord_3915161).sum := by decide
  have hdescent : baseEnd_3915161 < baseStart_3915161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915266 : List Nat := [3, 4, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_3915266 : Nat := 118140960795 + 3915266 * 2 ^ 59
def prefixEnd_3915266 : Nat := 4983230072969 + 3 ^ 40 * 3915266 * 2
def baseEnd_3915266 : Nat := 1340275565470922491646017

theorem tailTrace_3915266 : CollatzResearch.WordTrace tailWord_3915266 prefixEnd_3915266 1340275565470922491646017 := by
  unfold tailWord_3915266
  simp only [CollatzResearch.WordTrace]
  refine ⟨35700370658416857760509413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95200988422444954028025101 35700370658416857760509413)
  ·
    refine ⟨6693819498453160830095515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35700370658416857760509413 6693819498453160830095515)
    ·
      refine ⟨10040729247679741245143273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6693819498453160830095515 10040729247679741245143273)
      ·
        refine ⟨7530546935759805933857455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10040729247679741245143273 7530546935759805933857455)
        ·
          refine ⟨11295820403639708900786183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7530546935759805933857455 11295820403639708900786183)
          ·
            refine ⟨16943730605459563351179275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11295820403639708900786183 16943730605459563351179275)
            ·
              refine ⟨25415595908189345026768913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16943730605459563351179275 25415595908189345026768913)
              ·
                refine ⟨19061696931142008770076685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25415595908189345026768913 19061696931142008770076685)
                ·
                  refine ⟨7148136349178253288778757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19061696931142008770076685 7148136349178253288778757)
                  ·
                    refine ⟨1340275565470922491646017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7148136349178253288778757 1340275565470922491646017)
                    ·
                      rfl

theorem cell22_3915266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_3915266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3915266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3915266 prefixEnd_3915266 := by exact prefixLift 3915266
  have htrace : WordTrace (prefixWord ++ tailWord_3915266) baseStart_3915266 baseEnd_3915266 := by
    simpa [prefixWord, tailWord_3915266, baseEnd_3915266] using wordTrace_append hprefix tailTrace_3915266
  have hstable : (prefixWord ++ tailWord_3915266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915266).length < 2 ^ (prefixWord ++ tailWord_3915266).sum := by decide
  have hdescent : baseEnd_3915266 < baseStart_3915266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915401 : List Nat := [1, 2, 1, 1, 4, 1, 5, 2, 1, 4]
def baseStart_3915401 : Nat := 118140960795 + 3915401 * 2 ^ 59
def prefixEnd_3915401 : Nat := 4983230072969 + 3 ^ 40 * 3915401 * 2
def baseEnd_3915401 : Nat := 1340321778729827139520603

theorem tailTrace_3915401 : CollatzResearch.WordTrace tailWord_3915401 prefixEnd_3915401 1340321778729827139520603 := by
  unfold tailWord_3915401
  simp only [CollatzResearch.WordTrace]
  refine ⟨142806406488178349098202057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95204270992118899398801371 142806406488178349098202057)
  ·
    refine ⟨107104804866133761823651543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142806406488178349098202057 107104804866133761823651543)
    ·
      refine ⟨160657207299200642735477315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107104804866133761823651543 160657207299200642735477315)
      ·
        refine ⟨240985810948800964103215973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160657207299200642735477315 240985810948800964103215973)
        ·
          refine ⟨45184839552900180769352995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 240985810948800964103215973 45184839552900180769352995)
          ·
            refine ⟨67777259329350271154029493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45184839552900180769352995 67777259329350271154029493)
            ·
              refine ⟨6354118062126587920690265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67777259329350271154029493 6354118062126587920690265)
              ·
                refine ⟨4765588546594940940517699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6354118062126587920690265 4765588546594940940517699)
                ·
                  refine ⟨7148382819892411410776549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4765588546594940940517699 7148382819892411410776549)
                  ·
                    refine ⟨1340321778729827139520603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7148382819892411410776549 1340321778729827139520603)
                    ·
                      rfl

theorem cell22_3915401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 4].length) (baseStart_3915401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3915401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3915401 prefixEnd_3915401 := by exact prefixLift 3915401
  have htrace : WordTrace (prefixWord ++ tailWord_3915401) baseStart_3915401 baseEnd_3915401 := by
    simpa [prefixWord, tailWord_3915401, baseEnd_3915401] using wordTrace_append hprefix tailTrace_3915401
  have hstable : (prefixWord ++ tailWord_3915401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915401).length < 2 ^ (prefixWord ++ tailWord_3915401).sum := by decide
  have hdescent : baseEnd_3915401 < baseStart_3915401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915426 : List Nat := [3, 3, 1, 4, 2, 1, 2, 2, 1, 3]
def baseStart_3915426 : Nat := 118140960795 + 3915426 * 2 ^ 59
def prefixEnd_3915426 : Nat := 4983230072969 + 3 ^ 40 * 3915426 * 2
def baseEnd_3915426 : Nat := 1340330336740735407645527

theorem tailTrace_3915426 : CollatzResearch.WordTrace tailWord_3915426 prefixEnd_3915426 1340330336740735407645527 := by
  unfold tailWord_3915426
  simp only [CollatzResearch.WordTrace]
  refine ⟨35701829578271944591965533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95204878875391852245241421 35701829578271944591965533)
  ·
    refine ⟨13388186091851979221987075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35701829578271944591965533 13388186091851979221987075)
    ·
      refine ⟨20082279137777968832980613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13388186091851979221987075 20082279137777968832980613)
      ·
        refine ⟨3765427338333369156183865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20082279137777968832980613 3765427338333369156183865)
        ·
          refine ⟨2824070503750026867137899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3765427338333369156183865 2824070503750026867137899)
          ·
            refine ⟨4236105755625040300706849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2824070503750026867137899 4236105755625040300706849)
            ·
              refine ⟨3177079316718780225530137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4236105755625040300706849 3177079316718780225530137)
              ·
                refine ⟨2382809487539085169147603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3177079316718780225530137 2382809487539085169147603)
                ·
                  refine ⟨3574214231308627753721405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2382809487539085169147603 3574214231308627753721405)
                  ·
                    refine ⟨1340330336740735407645527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3574214231308627753721405 1340330336740735407645527)
                    ·
                      rfl

theorem cell22_3915426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_3915426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3915426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3915426 prefixEnd_3915426 := by exact prefixLift 3915426
  have htrace : WordTrace (prefixWord ++ tailWord_3915426) baseStart_3915426 baseEnd_3915426 := by
    simpa [prefixWord, tailWord_3915426, baseEnd_3915426] using wordTrace_append hprefix tailTrace_3915426
  have hstable : (prefixWord ++ tailWord_3915426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915426).length < 2 ^ (prefixWord ++ tailWord_3915426).sum := by decide
  have hdescent : baseEnd_3915426 < baseStart_3915426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915493 : List Nat := [1, 3, 1, 4, 1, 1, 4, 1, 3, 3]
def baseStart_3915493 : Nat := 118140960795 + 3915493 * 2 ^ 59
def prefixEnd_3915493 : Nat := 4983230072969 + 3 ^ 40 * 3915493 * 2
def baseEnd_3915493 : Nat := 1340353272209969566220321

theorem tailTrace_3915493 : CollatzResearch.WordTrace tailWord_3915493 prefixEnd_3915493 1340353272209969566220321 := by
  unfold tailWord_3915493
  simp only [CollatzResearch.WordTrace]
  refine ⟨142809762003845048810551133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95206508002563365873700755 142809762003845048810551133)
  ·
    refine ⟨53553660751441893303956675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142809762003845048810551133 53553660751441893303956675)
    ·
      refine ⟨80330491127162839955935013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53553660751441893303956675 80330491127162839955935013)
      ·
        refine ⟨15061967086343032491737815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80330491127162839955935013 15061967086343032491737815)
        ·
          refine ⟨22592950629514548737606723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15061967086343032491737815 22592950629514548737606723)
          ·
            refine ⟨33889425944271823106410085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22592950629514548737606723 33889425944271823106410085)
            ·
              refine ⟨6354267364550966832451891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33889425944271823106410085 6354267364550966832451891)
              ·
                refine ⟨9531401046826450248677837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6354267364550966832451891 9531401046826450248677837)
                ·
                  refine ⟨3574275392559918843254189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9531401046826450248677837 3574275392559918843254189)
                  ·
                    refine ⟨1340353272209969566220321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3574275392559918843254189 1340353272209969566220321)
                    ·
                      rfl

theorem cell22_3915493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 3, 3].length) (baseStart_3915493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3915493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3915493 prefixEnd_3915493 := by exact prefixLift 3915493
  have htrace : WordTrace (prefixWord ++ tailWord_3915493) baseStart_3915493 baseEnd_3915493 := by
    simpa [prefixWord, tailWord_3915493, baseEnd_3915493] using wordTrace_append hprefix tailTrace_3915493
  have hstable : (prefixWord ++ tailWord_3915493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915493).length < 2 ^ (prefixWord ++ tailWord_3915493).sum := by decide
  have hdescent : baseEnd_3915493 < baseStart_3915493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915504 : List Nat := [2, 1, 1, 1, 3, 1, 2, 3, 1, 7]
def baseStart_3915504 : Nat := 118140960795 + 3915504 * 2 ^ 59
def prefixEnd_3915504 : Nat := 4983230072969 + 3 ^ 40 * 3915504 * 2
def baseEnd_3915504 : Nat := 1340357037734769204195287

theorem tailTrace_3915504 : CollatzResearch.WordTrace tailWord_3915504 prefixEnd_3915504 1340357037734769204195287 := by
  unfold tailWord_3915504
  simp only [CollatzResearch.WordTrace]
  refine ⟨71405081603402598844600783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95206775471203465126134377 71405081603402598844600783)
  ·
    refine ⟨107107622405103898266901175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71405081603402598844600783 107107622405103898266901175)
    ·
      refine ⟨160661433607655847400351763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107107622405103898266901175 160661433607655847400351763)
      ·
        refine ⟨240992150411483771100527645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160661433607655847400351763 240992150411483771100527645)
        ·
          refine ⟨90372056404306414162697867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240992150411483771100527645 90372056404306414162697867)
          ·
            refine ⟨135558084606459621244046801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90372056404306414162697867 135558084606459621244046801)
            ·
              refine ⟨101668563454844715933035101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135558084606459621244046801 101668563454844715933035101)
              ·
                refine ⟨38125711295566768474888163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101668563454844715933035101 38125711295566768474888163)
                ·
                  refine ⟨57188566943350152712332245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38125711295566768474888163 57188566943350152712332245)
                  ·
                    refine ⟨1340357037734769204195287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57188566943350152712332245 1340357037734769204195287)
                    ·
                      rfl

theorem cell22_3915504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 1, 7].length) (baseStart_3915504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3915504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3915504 prefixEnd_3915504 := by exact prefixLift 3915504
  have htrace : WordTrace (prefixWord ++ tailWord_3915504) baseStart_3915504 baseEnd_3915504 := by
    simpa [prefixWord, tailWord_3915504, baseEnd_3915504] using wordTrace_append hprefix tailTrace_3915504
  have hstable : (prefixWord ++ tailWord_3915504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915504).length < 2 ^ (prefixWord ++ tailWord_3915504).sum := by decide
  have hdescent : baseEnd_3915504 < baseStart_3915504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915570 : List Nat := [3, 2, 1, 1, 3, 4, 1, 2, 1, 4]
def baseStart_3915570 : Nat := 118140960795 + 3915570 * 2 ^ 59
def prefixEnd_3915570 : Nat := 4983230072969 + 3 ^ 40 * 3915570 * 2
def baseEnd_3915570 : Nat := 1340379630883567032045085

theorem tailTrace_3915570 : CollatzResearch.WordTrace tailWord_3915570 prefixEnd_3915570 1340379630883567032045085 := by
  unfold tailWord_3915570
  simp only [CollatzResearch.WordTrace]
  refine ⟨35703142606141522740276041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95208380283044060640736109 35703142606141522740276041)
  ·
    refine ⟨26777356954606142055207031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35703142606141522740276041 26777356954606142055207031)
    ·
      refine ⟨40166035431909213082810547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26777356954606142055207031 40166035431909213082810547)
      ·
        refine ⟨60249053147863819624215821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40166035431909213082810547 60249053147863819624215821)
        ·
          refine ⟨22593394930448932359080933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60249053147863819624215821 22593394930448932359080933)
          ·
            refine ⟨4236261549459174817327675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22593394930448932359080933 4236261549459174817327675)
            ·
              refine ⟨6354392324188762225991513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4236261549459174817327675 6354392324188762225991513)
              ·
                refine ⟨4765794243141571669493635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6354392324188762225991513 4765794243141571669493635)
                ·
                  refine ⟨7148691364712357504240453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4765794243141571669493635 7148691364712357504240453)
                  ·
                    refine ⟨1340379630883567032045085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7148691364712357504240453 1340379630883567032045085)
                    ·
                      rfl

theorem cell22_3915570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_3915570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3915570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3915570 prefixEnd_3915570 := by exact prefixLift 3915570
  have htrace : WordTrace (prefixWord ++ tailWord_3915570) baseStart_3915570 baseEnd_3915570 := by
    simpa [prefixWord, tailWord_3915570, baseEnd_3915570] using wordTrace_append hprefix tailTrace_3915570
  have hstable : (prefixWord ++ tailWord_3915570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915570).length < 2 ^ (prefixWord ++ tailWord_3915570).sum := by decide
  have hdescent : baseEnd_3915570 < baseStart_3915570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915583 : List Nat := [1, 1, 2, 2, 6, 1, 1, 2, 1, 5]
def baseStart_3915583 : Nat := 118140960795 + 3915583 * 2 ^ 59
def prefixEnd_3915583 : Nat := 4983230072969 + 3 ^ 40 * 3915583 * 2
def baseEnd_3915583 : Nat := 1340384081049239331470045

theorem tailTrace_3915583 : CollatzResearch.WordTrace tailWord_3915583 prefixEnd_3915583 1340384081049239331470045 := by
  unfold tailWord_3915583
  simp only [CollatzResearch.WordTrace]
  refine ⟨142813044573518994181327403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95208696382345996120884935 142813044573518994181327403)
  ·
    refine ⟨214219566860278491271991105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142813044573518994181327403 214219566860278491271991105)
    ·
      refine ⟨160664675145208868453993329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214219566860278491271991105 160664675145208868453993329)
      ·
        refine ⟨120498506358906651340494997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160664675145208868453993329 120498506358906651340494997)
        ·
          refine ⟨5648367485573749281585703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 120498506358906651340494997 5648367485573749281585703)
          ·
            refine ⟨8472551228360623922378555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5648367485573749281585703 8472551228360623922378555)
            ·
              refine ⟨12708826842540935883567833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8472551228360623922378555 12708826842540935883567833)
              ·
                refine ⟨9531620131905701912675875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12708826842540935883567833 9531620131905701912675875)
                ·
                  refine ⟨14297430197858552869013813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9531620131905701912675875 14297430197858552869013813)
                  ·
                    refine ⟨1340384081049239331470045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14297430197858552869013813 1340384081049239331470045)
                    ·
                      rfl

theorem cell22_3915583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 5].length) (baseStart_3915583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3915583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3915583 prefixEnd_3915583 := by exact prefixLift 3915583
  have htrace : WordTrace (prefixWord ++ tailWord_3915583) baseStart_3915583 baseEnd_3915583 := by
    simpa [prefixWord, tailWord_3915583, baseEnd_3915583] using wordTrace_append hprefix tailTrace_3915583
  have hstable : (prefixWord ++ tailWord_3915583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915583).length < 2 ^ (prefixWord ++ tailWord_3915583).sum := by decide
  have hdescent : baseEnd_3915583 < baseStart_3915583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915596 : List Nat := [2, 2, 1, 3, 4, 10]
def baseStart_3915596 : Nat := 118140960795 + 3915596 * 2 ^ 59
def prefixEnd_3915596 : Nat := 4983230072969 + 3 ^ 40 * 3915596 * 2
def baseEnd_3915596 : Nat := 16548006558208785566605

theorem tailTrace_3915596 : CollatzResearch.WordTrace tailWord_3915596 prefixEnd_3915596 16548006558208785566605 := by
  unfold tailWord_3915596
  simp only [CollatzResearch.WordTrace]
  refine ⟨71406759361235948700775321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95209012481647931601033761 71406759361235948700775321)
  ·
    refine ⟨53555069520926961525581491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71406759361235948700775321 53555069520926961525581491)
    ·
      refine ⟨80332604281390442288372237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53555069520926961525581491 80332604281390442288372237)
      ·
        refine ⟨30124726605521415858139589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80332604281390442288372237 30124726605521415858139589)
        ·
          refine ⟨5648386238535265473401173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30124726605521415858139589 5648386238535265473401173)
          ·
            refine ⟨16548006558208785566605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5648386238535265473401173 16548006558208785566605)
            ·
              rfl

theorem cell22_3915596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 10].length) (baseStart_3915596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3915596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3915596 prefixEnd_3915596 := by exact prefixLift 3915596
  have htrace : WordTrace (prefixWord ++ tailWord_3915596) baseStart_3915596 baseEnd_3915596 := by
    simpa [prefixWord, tailWord_3915596, baseEnd_3915596] using wordTrace_append hprefix tailTrace_3915596
  have hstable : (prefixWord ++ tailWord_3915596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915596).length < 2 ^ (prefixWord ++ tailWord_3915596).sum := by decide
  have hdescent : baseEnd_3915596 < baseStart_3915596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915602 : List Nat := [3, 2, 2, 1, 1, 5, 2, 2, 4]
def baseStart_3915602 : Nat := 118140960795 + 3915602 * 2 ^ 59
def prefixEnd_3915602 : Nat := 4983230072969 + 3 ^ 40 * 3915602 * 2
def baseEnd_3915602 : Nat := 446796861712509871748329

theorem tailTrace_3915602 : CollatzResearch.WordTrace tailWord_3915602 prefixEnd_3915602 446796861712509871748329 := by
  unfold tailWord_3915602
  simp only [CollatzResearch.WordTrace]
  refine ⟨35703434390112540106567265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95209158373633440284179373 35703434390112540106567265)
  ·
    refine ⟨26777575792584405079925449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35703434390112540106567265 26777575792584405079925449)
    ·
      refine ⟨20083181844438303809944087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26777575792584405079925449 20083181844438303809944087)
      ·
        refine ⟨30124772766657455714916131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20083181844438303809944087 30124772766657455714916131)
        ·
          refine ⟨45187159149986183572374197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30124772766657455714916131 45187159149986183572374197)
          ·
            refine ⟨4236296170311204709910081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45187159149986183572374197 4236296170311204709910081)
            ·
              refine ⟨3177222127733403532432561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4236296170311204709910081 3177222127733403532432561)
              ·
                refine ⟨2382916595800052649324421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3177222127733403532432561 2382916595800052649324421)
                ·
                  refine ⟨446796861712509871748329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2382916595800052649324421 446796861712509871748329)
                  ·
                    rfl

theorem cell22_3915602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_3915602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3915602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3915602 prefixEnd_3915602 := by exact prefixLift 3915602
  have htrace : WordTrace (prefixWord ++ tailWord_3915602) baseStart_3915602 baseEnd_3915602 := by
    simpa [prefixWord, tailWord_3915602, baseEnd_3915602] using wordTrace_append hprefix tailTrace_3915602
  have hstable : (prefixWord ++ tailWord_3915602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915602).length < 2 ^ (prefixWord ++ tailWord_3915602).sum := by decide
  have hdescent : baseEnd_3915602 < baseStart_3915602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915628 : List Nat := [2, 2, 1, 1, 4, 2, 1, 1, 5, 3]
def baseStart_3915628 : Nat := 118140960795 + 3915628 * 2 ^ 59
def prefixEnd_3915628 : Nat := 4983230072969 + 3 ^ 40 * 3915628 * 2
def baseEnd_3915628 : Nat := 1340399485468874214094907

theorem tailTrace_3915628 : CollatzResearch.WordTrace tailWord_3915628 prefixEnd_3915628 1340399485468874214094907 := by
  unfold tailWord_3915628
  simp only [CollatzResearch.WordTrace]
  refine ⟨71407342929177983433357769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95209790572237311244477025 71407342929177983433357769)
  ·
    refine ⟨53555507196883487575018327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71407342929177983433357769 53555507196883487575018327)
    ·
      refine ⟨80333260795325231362527491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53555507196883487575018327 80333260795325231362527491)
      ·
        refine ⟨120499891192987847043791237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80333260795325231362527491 120499891192987847043791237)
        ·
          refine ⟨22593729598685221320710857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120499891192987847043791237 22593729598685221320710857)
          ·
            refine ⟨16945297199013915990533143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22593729598685221320710857 16945297199013915990533143)
            ·
              refine ⟨25417945798520873985799715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16945297199013915990533143 25417945798520873985799715)
              ·
                refine ⟨38126918697781310978699573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25417945798520873985799715 38126918697781310978699573)
                ·
                  refine ⟨3574398627916997904253085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38126918697781310978699573 3574398627916997904253085)
                  ·
                    refine ⟨1340399485468874214094907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3574398627916997904253085 1340399485468874214094907)
                    ·
                      rfl

theorem cell22_3915628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 3].length) (baseStart_3915628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3915628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3915628 prefixEnd_3915628 := by exact prefixLift 3915628
  have htrace : WordTrace (prefixWord ++ tailWord_3915628) baseStart_3915628 baseEnd_3915628 := by
    simpa [prefixWord, tailWord_3915628, baseEnd_3915628] using wordTrace_append hprefix tailTrace_3915628
  have hstable : (prefixWord ++ tailWord_3915628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915628).length < 2 ^ (prefixWord ++ tailWord_3915628).sum := by decide
  have hdescent : baseEnd_3915628 < baseStart_3915628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915630 : List Nat := [4, 1, 2, 3, 1, 2, 3, 6]
def baseStart_3915630 : Nat := 118140960795 + 3915630 * 2 ^ 59
def prefixEnd_3915630 : Nat := 4983230072969 + 3 ^ 40 * 3915630 * 2
def baseEnd_3915630 : Nat := 148933352234416319504989

theorem tailTrace_3915630 : CollatzResearch.WordTrace tailWord_3915630 prefixEnd_3915630 148933352234416319504989 := by
  unfold tailWord_3915630
  simp only [CollatzResearch.WordTrace]
  refine ⟨17851844850543590151036043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95209839202899147472192229 17851844850543590151036043)
  ·
    refine ⟨26777767275815385226554065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17851844850543590151036043 26777767275815385226554065)
    ·
      refine ⟨20083325456861538919915549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26777767275815385226554065 20083325456861538919915549)
      ·
        refine ⟨7531247046323077094968331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20083325456861538919915549 7531247046323077094968331)
        ·
          refine ⟨11296870569484615642452497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7531247046323077094968331 11296870569484615642452497)
          ·
            refine ⟨8472652927113461731839373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11296870569484615642452497 8472652927113461731839373)
            ·
              refine ⟨3177244847667548149439765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8472652927113461731839373 3177244847667548149439765)
              ·
                refine ⟨148933352234416319504989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3177244847667548149439765 148933352234416319504989)
                ·
                  rfl

theorem cell22_3915630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 6].length) (baseStart_3915630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3915630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3915630 prefixEnd_3915630 := by exact prefixLift 3915630
  have htrace : WordTrace (prefixWord ++ tailWord_3915630) baseStart_3915630 baseEnd_3915630 := by
    simpa [prefixWord, tailWord_3915630, baseEnd_3915630] using wordTrace_append hprefix tailTrace_3915630
  have hstable : (prefixWord ++ tailWord_3915630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915630).length < 2 ^ (prefixWord ++ tailWord_3915630).sum := by decide
  have hdescent : baseEnd_3915630 < baseStart_3915630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915641 : List Nat := [1, 2, 1, 3, 2, 2, 2, 2, 7]
def baseStart_3915641 : Nat := 118140960795 + 3915641 * 2 ^ 59
def prefixEnd_3915641 : Nat := 4983230072969 + 3 ^ 40 * 3915641 * 2
def baseEnd_3915641 : Nat := 446801311878182171173289

theorem tailTrace_3915641 : CollatzResearch.WordTrace tailWord_3915641 prefixEnd_3915641 446801311878182171173289 := by
  unfold tailWord_3915641
  simp only [CollatzResearch.WordTrace]
  refine ⟨142815160007308870086938777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95210106671539246724625851 142815160007308870086938777)
  ·
    refine ⟨107111370005481652565204083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142815160007308870086938777 107111370005481652565204083)
    ·
      refine ⟨160667055008222478847806125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107111370005481652565204083 160667055008222478847806125)
      ·
        refine ⟨60250145628083429567927297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160667055008222478847806125 60250145628083429567927297)
        ·
          refine ⟨45187609221062572175945473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60250145628083429567927297 45187609221062572175945473)
          ·
            refine ⟨33890706915796929131959105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45187609221062572175945473 33890706915796929131959105)
            ·
              refine ⟨25418030186847696848969329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33890706915796929131959105 25418030186847696848969329)
              ·
                refine ⟨19063522640135772636726997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25418030186847696848969329 19063522640135772636726997)
                ·
                  refine ⟨446801311878182171173289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19063522640135772636726997 446801311878182171173289)
                  ·
                    rfl

theorem cell22_3915641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 7].length) (baseStart_3915641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3915641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3915641 prefixEnd_3915641 := by exact prefixLift 3915641
  have htrace : WordTrace (prefixWord ++ tailWord_3915641) baseStart_3915641 baseEnd_3915641 := by
    simpa [prefixWord, tailWord_3915641, baseEnd_3915641] using wordTrace_append hprefix tailTrace_3915641
  have hstable : (prefixWord ++ tailWord_3915641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915641).length < 2 ^ (prefixWord ++ tailWord_3915641).sum := by decide
  have hdescent : baseEnd_3915641 < baseStart_3915641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915720 : List Nat := [2, 1, 3, 1, 4, 3, 1, 1, 6]
def baseStart_3915720 : Nat := 118140960795 + 3915720 * 2 ^ 59
def prefixEnd_3915720 : Nat := 4983230072969 + 3 ^ 40 * 3915720 * 2
def baseEnd_3915720 : Nat := 446810326316338880264875

theorem tailTrace_3915720 : CollatzResearch.WordTrace tailWord_3915720 prefixEnd_3915720 446810326316338880264875 := by
  unfold tailWord_3915720
  simp only [CollatzResearch.WordTrace]
  refine ⟨71409020687011333289532307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95212027582681777719376409 71409020687011333289532307)
  ·
    refine ⟨107113531030516999934298461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71409020687011333289532307 107113531030516999934298461)
    ·
      refine ⟨40167574136443874975361923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107113531030516999934298461 40167574136443874975361923)
      ·
        refine ⟨60251361204665812463042885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40167574136443874975361923 60251361204665812463042885)
        ·
          refine ⟨11297130225874839836820541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60251361204665812463042885 11297130225874839836820541)
          ·
            refine ⟨4236423834703064938807703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11297130225874839836820541 4236423834703064938807703)
            ·
              refine ⟨6354635752054597408211555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4236423834703064938807703 6354635752054597408211555)
              ·
                refine ⟨9531953628081896112317333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6354635752054597408211555 9531953628081896112317333)
                ·
                  refine ⟨446810326316338880264875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9531953628081896112317333 446810326316338880264875)
                  ·
                    rfl

theorem cell22_3915720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 6].length) (baseStart_3915720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3915720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3915720 prefixEnd_3915720 := by exact prefixLift 3915720
  have htrace : WordTrace (prefixWord ++ tailWord_3915720) baseStart_3915720 baseEnd_3915720 := by
    simpa [prefixWord, tailWord_3915720, baseEnd_3915720] using wordTrace_append hprefix tailTrace_3915720
  have hstable : (prefixWord ++ tailWord_3915720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915720).length < 2 ^ (prefixWord ++ tailWord_3915720).sum := by decide
  have hdescent : baseEnd_3915720 < baseStart_3915720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915735 : List Nat := [1, 1, 3, 2, 1, 1, 5, 3, 2, 3]
def baseStart_3915735 : Nat := 118140960795 + 3915735 * 2 ^ 59
def prefixEnd_3915735 : Nat := 4983230072969 + 3 ^ 40 * 3915735 * 2
def baseEnd_3915735 : Nat := 1340436113755561601669579

theorem tailTrace_3915735 : CollatzResearch.WordTrace tailWord_3915735 prefixEnd_3915735 1340436113755561601669579 := by
  unfold tailWord_3915735
  simp only [CollatzResearch.WordTrace]
  refine ⟨142818588468968324140860659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95212392312645549427240439 142818588468968324140860659)
  ·
    refine ⟨214227882703452486211290989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142818588468968324140860659 214227882703452486211290989)
    ·
      refine ⟨80335456013794682329234121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214227882703452486211290989 80335456013794682329234121)
      ·
        refine ⟨60251592010346011746925591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80335456013794682329234121 60251592010346011746925591)
        ·
          refine ⟨90377388015519017620388387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60251592010346011746925591 90377388015519017620388387)
          ·
            refine ⟨135566082023278526430582581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90377388015519017620388387 135566082023278526430582581)
            ·
              refine ⟨12709320189682361852867117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135566082023278526430582581 12709320189682361852867117)
              ·
                refine ⟨4765995071130885694825169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12709320189682361852867117 4765995071130885694825169)
                ·
                  refine ⟨3574496303348164271118877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4765995071130885694825169 3574496303348164271118877)
                  ·
                    refine ⟨1340436113755561601669579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3574496303348164271118877 1340436113755561601669579)
                    ·
                      rfl

theorem cell22_3915735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 2, 3].length) (baseStart_3915735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3915735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3915735 prefixEnd_3915735 := by exact prefixLift 3915735
  have htrace : WordTrace (prefixWord ++ tailWord_3915735) baseStart_3915735 baseEnd_3915735 := by
    simpa [prefixWord, tailWord_3915735, baseEnd_3915735] using wordTrace_append hprefix tailTrace_3915735
  have hstable : (prefixWord ++ tailWord_3915735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915735).length < 2 ^ (prefixWord ++ tailWord_3915735).sum := by decide
  have hdescent : baseEnd_3915735 < baseStart_3915735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915797 : List Nat := [1, 3, 2, 1, 5, 1, 1, 2, 3, 3]
def baseStart_3915797 : Nat := 118140960795 + 3915797 * 2 ^ 59
def prefixEnd_3915797 : Nat := 4983230072969 + 3 ^ 40 * 3915797 * 2
def baseEnd_3915797 : Nat := 1340457337622614106619389

theorem tailTrace_3915797 : CollatzResearch.WordTrace tailWord_3915797 prefixEnd_3915797 1340457337622614106619389 := by
  unfold tailWord_3915797
  simp only [CollatzResearch.WordTrace]
  refine ⟨142820849794743708729617645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95213899863162472486411763 142820849794743708729617645)
  ·
    refine ⟨53557818673028890773606617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142820849794743708729617645 53557818673028890773606617)
    ·
      refine ⟨40168364004771668080204963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53557818673028890773606617 40168364004771668080204963)
      ·
        refine ⟨60252546007157502120307445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40168364004771668080204963 60252546007157502120307445)
        ·
          refine ⟨5648676188171015823778823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60252546007157502120307445 5648676188171015823778823)
          ·
            refine ⟨8473014282256523735668235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5648676188171015823778823 8473014282256523735668235)
            ·
              refine ⟨12709521423384785603502353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8473014282256523735668235 12709521423384785603502353)
              ·
                refine ⟨9532141067538589202626765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12709521423384785603502353 9532141067538589202626765)
                ·
                  refine ⟨3574552900326970950985037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9532141067538589202626765 3574552900326970950985037)
                  ·
                    refine ⟨1340457337622614106619389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3574552900326970950985037 1340457337622614106619389)
                    ·
                      rfl

theorem cell22_3915797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_3915797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3915797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3915797 prefixEnd_3915797 := by exact prefixLift 3915797
  have htrace : WordTrace (prefixWord ++ tailWord_3915797) baseStart_3915797 baseEnd_3915797 := by
    simpa [prefixWord, tailWord_3915797, baseEnd_3915797] using wordTrace_append hprefix tailTrace_3915797
  have hstable : (prefixWord ++ tailWord_3915797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915797).length < 2 ^ (prefixWord ++ tailWord_3915797).sum := by decide
  have hdescent : baseEnd_3915797 < baseStart_3915797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915823 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 5, 4]
def baseStart_3915823 : Nat := 118140960795 + 3915823 * 2 ^ 59
def prefixEnd_3915823 : Nat := 4983230072969 + 3 ^ 40 * 3915823 * 2
def baseEnd_3915823 : Nat := 1340466237953958705469309

theorem tailTrace_3915823 : CollatzResearch.WordTrace tailWord_3915823 prefixEnd_3915823 1340466237953958705469309 := by
  unfold tailWord_3915823
  simp only [CollatzResearch.WordTrace]
  refine ⟨142821798092649515170064123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95214532061766343446709415 142821798092649515170064123)
  ·
    refine ⟨214232697138974272755096185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142821798092649515170064123 214232697138974272755096185)
    ·
      refine ⟨160674522854230704566322139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214232697138974272755096185 160674522854230704566322139)
      ·
        refine ⟨241011784281346056849483209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160674522854230704566322139 241011784281346056849483209)
        ·
          refine ⟨180758838211009542637112407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241011784281346056849483209 180758838211009542637112407)
          ·
            refine ⟨271138257316514313955668611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180758838211009542637112407 271138257316514313955668611)
            ·
              refine ⟨406707385974771470933502917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271138257316514313955668611 406707385974771470933502917)
              ·
                refine ⟨76257634870269650800031797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 406707385974771470933502917 76257634870269650800031797)
                ·
                  refine ⟨7149153269087779762502981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76257634870269650800031797 7149153269087779762502981)
                  ·
                    refine ⟨1340466237953958705469309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7149153269087779762502981 1340466237953958705469309)
                    ·
                      rfl

theorem cell22_3915823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 4].length) (baseStart_3915823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3915823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3915823 prefixEnd_3915823 := by exact prefixLift 3915823
  have htrace : WordTrace (prefixWord ++ tailWord_3915823) baseStart_3915823 baseEnd_3915823 := by
    simpa [prefixWord, tailWord_3915823, baseEnd_3915823] using wordTrace_append hprefix tailTrace_3915823
  have hstable : (prefixWord ++ tailWord_3915823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915823).length < 2 ^ (prefixWord ++ tailWord_3915823).sum := by decide
  have hdescent : baseEnd_3915823 < baseStart_3915823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915872 : List Nat := [2, 1, 1, 3, 2, 3, 3, 3, 4]
def baseStart_3915872 : Nat := 118140960795 + 3915872 * 2 ^ 59
def prefixEnd_3915872 : Nat := 4983230072969 + 3 ^ 40 * 3915872 * 2
def baseEnd_3915872 : Nat := 446827670551779636998053

theorem tailTrace_3915872 : CollatzResearch.WordTrace tailWord_3915872 prefixEnd_3915872 446827670551779636998053 := by
  unfold tailWord_3915872
  simp only [CollatzResearch.WordTrace]
  refine ⟨71411792634735998269298935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95215723512981331025731913 71411792634735998269298935)
  ·
    refine ⟨107117688952103997403948403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71411792634735998269298935 107117688952103997403948403)
    ·
      refine ⟨160676533428155996105922605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107117688952103997403948403 160676533428155996105922605)
      ·
        refine ⟨60253700035558498539720977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160676533428155996105922605 60253700035558498539720977)
        ·
          refine ⟨45190275026668873904790733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60253700035558498539720977 45190275026668873904790733)
          ·
            refine ⟨16946353135000827714296525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45190275026668873904790733 16946353135000827714296525)
            ·
              refine ⟨6354882425625310392861197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16946353135000827714296525 6354882425625310392861197)
              ·
                refine ⟨2383080909609491397322949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6354882425625310392861197 2383080909609491397322949)
                ·
                  refine ⟨446827670551779636998053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2383080909609491397322949 446827670551779636998053)
                  ·
                    rfl

theorem cell22_3915872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 3, 4].length) (baseStart_3915872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3915872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3915872 prefixEnd_3915872 := by exact prefixLift 3915872
  have htrace : WordTrace (prefixWord ++ tailWord_3915872) baseStart_3915872 baseEnd_3915872 := by
    simpa [prefixWord, tailWord_3915872, baseEnd_3915872] using wordTrace_append hprefix tailTrace_3915872
  have hstable : (prefixWord ++ tailWord_3915872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915872).length < 2 ^ (prefixWord ++ tailWord_3915872).sum := by decide
  have hdescent : baseEnd_3915872 < baseStart_3915872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915900 : List Nat := [2, 2, 2, 1, 1, 5, 2, 7]
def baseStart_3915900 : Nat := 118140960795 + 3915900 * 2 ^ 59
def prefixEnd_3915900 : Nat := 4983230072969 + 3 ^ 40 * 3915900 * 2
def baseEnd_3915900 : Nat := 148943621847506241254897

theorem tailTrace_3915900 : CollatzResearch.WordTrace tailWord_3915900 prefixEnd_3915900 148943621847506241254897 := by
  unfold tailWord_3915900
  simp only [CollatzResearch.WordTrace]
  refine ⟨71412303256685278660308577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95216404342247038213744769 71412303256685278660308577)
  ·
    refine ⟨53559227442513958995231433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71412303256685278660308577 53559227442513958995231433)
    ·
      refine ⟨40169420581885469246423575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53559227442513958995231433 40169420581885469246423575)
      ·
        refine ⟨60254130872828203869635363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40169420581885469246423575 60254130872828203869635363)
        ·
          refine ⟨90381196309242305804453045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60254130872828203869635363 90381196309242305804453045)
          ·
            refine ⟨8473237153991466169167473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90381196309242305804453045 8473237153991466169167473)
            ·
              refine ⟨6354927865493599626875605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8473237153991466169167473 6354927865493599626875605)
              ·
                refine ⟨148943621847506241254897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6354927865493599626875605 148943621847506241254897)
                ·
                  rfl

theorem cell22_3915900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 7].length) (baseStart_3915900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3915900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3915900 prefixEnd_3915900 := by exact prefixLift 3915900
  have htrace : WordTrace (prefixWord ++ tailWord_3915900) baseStart_3915900 baseEnd_3915900 := by
    simpa [prefixWord, tailWord_3915900, baseEnd_3915900] using wordTrace_append hprefix tailTrace_3915900
  have hstable : (prefixWord ++ tailWord_3915900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915900).length < 2 ^ (prefixWord ++ tailWord_3915900).sum := by decide
  have hdescent : baseEnd_3915900 < baseStart_3915900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3915960 : List Nat := [2, 1, 2, 1, 2, 1, 5, 1, 2, 5]
def baseStart_3915960 : Nat := 118140960795 + 3915960 * 2 ^ 59
def prefixEnd_3915960 : Nat := 4983230072969 + 3 ^ 40 * 3915960 * 2
def baseEnd_3915960 : Nat := 1340513135853736014793889

theorem tailTrace_3915960 : CollatzResearch.WordTrace tailWord_3915960 prefixEnd_3915960 1340513135853736014793889 := by
  unfold tailWord_3915960
  simp only [CollatzResearch.WordTrace]
  refine ⟨71413397446576593783900667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95217863262102125045200889 71413397446576593783900667)
  ·
    refine ⟨107120096169864890675851001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71413397446576593783900667 107120096169864890675851001)
    ·
      refine ⟨80340072127398668006888251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107120096169864890675851001 80340072127398668006888251)
      ·
        refine ⟨120510108191098002010332377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80340072127398668006888251 120510108191098002010332377)
        ·
          refine ⟨90382581143323501507749283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120510108191098002010332377 90382581143323501507749283)
          ·
            refine ⟨135573871714985252261623925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90382581143323501507749283 135573871714985252261623925)
            ·
              refine ⟨12710050473279867399527243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135573871714985252261623925 12710050473279867399527243)
              ·
                refine ⟨19065075709919801099290865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12710050473279867399527243 19065075709919801099290865)
                ·
                  refine ⟨14298806782439850824468149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19065075709919801099290865 14298806782439850824468149)
                  ·
                    refine ⟨1340513135853736014793889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14298806782439850824468149 1340513135853736014793889)
                    ·
                      rfl

theorem cell22_3915960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_3915960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3915960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3915960 prefixEnd_3915960 := by exact prefixLift 3915960
  have htrace : WordTrace (prefixWord ++ tailWord_3915960) baseStart_3915960 baseEnd_3915960 := by
    simpa [prefixWord, tailWord_3915960, baseEnd_3915960] using wordTrace_append hprefix tailTrace_3915960
  have hstable : (prefixWord ++ tailWord_3915960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3915960).length < 2 ^ (prefixWord ++ tailWord_3915960).sum := by decide
  have hdescent : baseEnd_3915960 < baseStart_3915960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3915960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916007 : List Nat := [1, 1, 5, 3, 1, 1, 1, 3, 6]
def baseStart_3916007 : Nat := 118140960795 + 3916007 * 2 ^ 59
def prefixEnd_3916007 : Nat := 4983230072969 + 3 ^ 40 * 3916007 * 2
def baseEnd_3916007 : Nat := 446843074971414519622915

theorem tailTrace_3916007 : CollatzResearch.WordTrace tailWord_3916007 prefixEnd_3916007 446843074971414519622915 := by
  unfold tailWord_3916007
  simp only [CollatzResearch.WordTrace]
  refine ⟨142828509123982914594762275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95219006082655276396508183 142828509123982914594762275)
  ·
    refine ⟨214242763685974371892143413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142828509123982914594762275 214242763685974371892143413)
    ·
      refine ⟨20085259095560097364888445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 214242763685974371892143413 20085259095560097364888445)
      ·
        refine ⟨7531972160835036511833167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20085259095560097364888445 7531972160835036511833167)
        ·
          refine ⟨11297958241252554767749751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7531972160835036511833167 11297958241252554767749751)
          ·
            refine ⟨16946937361878832151624627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11297958241252554767749751 16946937361878832151624627)
            ·
              refine ⟨25420406042818248227436941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16946937361878832151624627 25420406042818248227436941)
              ·
                refine ⟨9532652266056843085288853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25420406042818248227436941 9532652266056843085288853)
                ·
                  refine ⟨446843074971414519622915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9532652266056843085288853 446843074971414519622915)
                  ·
                    rfl

theorem cell22_3916007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 6].length) (baseStart_3916007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3916007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3916007 prefixEnd_3916007 := by exact prefixLift 3916007
  have htrace : WordTrace (prefixWord ++ tailWord_3916007) baseStart_3916007 baseEnd_3916007 := by
    simpa [prefixWord, tailWord_3916007, baseEnd_3916007] using wordTrace_append hprefix tailTrace_3916007
  have hstable : (prefixWord ++ tailWord_3916007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916007).length < 2 ^ (prefixWord ++ tailWord_3916007).sum := by decide
  have hdescent : baseEnd_3916007 < baseStart_3916007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916035 : List Nat := [1, 1, 1, 3, 2, 3, 3, 8]
def baseStart_3916035 : Nat := 118140960795 + 3916035 * 2 ^ 59
def prefixEnd_3916035 : Nat := 4983230072969 + 3 ^ 40 * 3916035 * 2
def baseEnd_3916035 : Nat := 148948756654051202129851

theorem tailTrace_3916035 : CollatzResearch.WordTrace tailWord_3916035 prefixEnd_3916035 148948756654051202129851 := by
  unfold tailWord_3916035
  simp only [CollatzResearch.WordTrace]
  refine ⟨142829530367881475376781559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95219686911920983584521039 142829530367881475376781559)
  ·
    refine ⟨214244295551822213065172339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142829530367881475376781559 214244295551822213065172339)
    ·
      refine ⟨321366443327733319597758509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214244295551822213065172339 321366443327733319597758509)
      ·
        refine ⟨120512416247899994849159441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321366443327733319597758509 120512416247899994849159441)
        ·
          refine ⟨90384312185924996136869581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120512416247899994849159441 90384312185924996136869581)
          ·
            refine ⟨33894117069721873551326093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90384312185924996136869581 33894117069721873551326093)
            ·
              refine ⟨12710293901145702581747285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33894117069721873551326093 12710293901145702581747285)
              ·
                refine ⟨148948756654051202129851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12710293901145702581747285 148948756654051202129851)
                ·
                  rfl

theorem cell22_3916035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 8].length) (baseStart_3916035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3916035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3916035 prefixEnd_3916035 := by exact prefixLift 3916035
  have htrace : WordTrace (prefixWord ++ tailWord_3916035) baseStart_3916035 baseEnd_3916035 := by
    simpa [prefixWord, tailWord_3916035, baseEnd_3916035] using wordTrace_append hprefix tailTrace_3916035
  have hstable : (prefixWord ++ tailWord_3916035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916035).length < 2 ^ (prefixWord ++ tailWord_3916035).sum := by decide
  have hdescent : baseEnd_3916035 < baseStart_3916035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916080 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 9]
def baseStart_3916080 : Nat := 118140960795 + 3916080 * 2 ^ 59
def prefixEnd_3916080 : Nat := 4983230072969 + 3 ^ 40 * 3916080 * 2
def baseEnd_3916080 : Nat := 446851404768698567264507

theorem tailTrace_3916080 : CollatzResearch.WordTrace tailWord_3916080 prefixEnd_3916080 446851404768698567264507 := by
  unfold tailWord_3916080
  simp only [CollatzResearch.WordTrace]
  refine ⟨71415585826359224031084847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95220781101812298708113129 71415585826359224031084847)
  ·
    refine ⟨107123378739538836046627271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71415585826359224031084847 107123378739538836046627271)
    ·
      refine ⟨160685068109308254069940907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107123378739538836046627271 160685068109308254069940907)
      ·
        refine ⟨241027602163962381104911361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160685068109308254069940907 241027602163962381104911361)
        ·
          refine ⟨180770701622971785828683521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241027602163962381104911361 180770701622971785828683521)
          ·
            refine ⟨135578026217228839371512641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180770701622971785828683521 135578026217228839371512641)
            ·
              refine ⟨101683519662921629528634481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135578026217228839371512641 101683519662921629528634481)
              ·
                refine ⟨76262639747191222146475861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101683519662921629528634481 76262639747191222146475861)
                ·
                  refine ⟨446851404768698567264507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 76262639747191222146475861 446851404768698567264507)
                  ·
                    rfl

theorem cell22_3916080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 9].length) (baseStart_3916080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3916080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3916080 prefixEnd_3916080 := by exact prefixLift 3916080
  have htrace : WordTrace (prefixWord ++ tailWord_3916080) baseStart_3916080 baseEnd_3916080 := by
    simpa [prefixWord, tailWord_3916080, baseEnd_3916080] using wordTrace_append hprefix tailTrace_3916080
  have hstable : (prefixWord ++ tailWord_3916080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916080).length < 2 ^ (prefixWord ++ tailWord_3916080).sum := by decide
  have hdescent : baseEnd_3916080 < baseStart_3916080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916127 : List Nat := [1, 1, 2, 3, 1, 2, 3, 2, 3, 4]
def baseStart_3916127 : Nat := 118140960795 + 3916127 * 2 ^ 59
def prefixEnd_3916127 : Nat := 4983230072969 + 3 ^ 40 * 3916127 * 2
def baseEnd_3916127 : Nat := 1340570303366603245868377

theorem tailTrace_3916127 : CollatzResearch.WordTrace tailWord_3916127 prefixEnd_3916127 1340570303366603245868377 := by
  unfold tailWord_3916127
  simp only [CollatzResearch.WordTrace]
  refine ⟨142832885883548175089130635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95221923922365450059420423 142832885883548175089130635)
  ·
    refine ⟨214249328825322262633695953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142832885883548175089130635 214249328825322262633695953)
    ·
      refine ⟨160686996618991696975271965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214249328825322262633695953 160686996618991696975271965)
      ·
        refine ⟨60257623732121886365726987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160686996618991696975271965 60257623732121886365726987)
        ·
          refine ⟨90386435598182829548590481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60257623732121886365726987 90386435598182829548590481)
          ·
            refine ⟨67789826698637122161442861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90386435598182829548590481 67789826698637122161442861)
            ·
              refine ⟨25421185011988920810541073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67789826698637122161442861 25421185011988920810541073)
              ·
                refine ⟨19065888758991690607905805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25421185011988920810541073 19065888758991690607905805)
                ·
                  refine ⟨7149708284621883977964677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19065888758991690607905805 7149708284621883977964677)
                  ·
                    refine ⟨1340570303366603245868377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7149708284621883977964677 1340570303366603245868377)
                    ·
                      rfl

theorem cell22_3916127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 4].length) (baseStart_3916127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3916127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3916127 prefixEnd_3916127 := by exact prefixLift 3916127
  have htrace : WordTrace (prefixWord ++ tailWord_3916127) baseStart_3916127 baseEnd_3916127 := by
    simpa [prefixWord, tailWord_3916127, baseEnd_3916127] using wordTrace_append hprefix tailTrace_3916127
  have hstable : (prefixWord ++ tailWord_3916127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916127).length < 2 ^ (prefixWord ++ tailWord_3916127).sum := by decide
  have hdescent : baseEnd_3916127 < baseStart_3916127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916161 : List Nat := [1, 2, 4, 3, 1, 2, 1, 3, 1, 4]
def baseStart_3916161 : Nat := 118140960795 + 3916161 * 2 ^ 59
def prefixEnd_3916161 : Nat := 4983230072969 + 3 ^ 40 * 3916161 * 2
def baseEnd_3916161 : Nat := 1340581942261438490518273

theorem tailTrace_3916161 : CollatzResearch.WordTrace tailWord_3916161 prefixEnd_3916161 1340581942261438490518273 := by
  unfold tailWord_3916161
  simp only [CollatzResearch.WordTrace]
  refine ⟨142834125965424998895868337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95222750643616665930578891 142834125965424998895868337)
  ·
    refine ⟨107125594474068749171901253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142834125965424998895868337 107125594474068749171901253)
    ·
      refine ⟨20086048963887890469731485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107125594474068749171901253 20086048963887890469731485)
      ·
        refine ⟨7532268361457958926149307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20086048963887890469731485 7532268361457958926149307)
        ·
          refine ⟨11298402542186938389223961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7532268361457958926149307 11298402542186938389223961)
          ·
            refine ⟨8473801906640203791917971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11298402542186938389223961 8473801906640203791917971)
            ·
              refine ⟨12710702859960305687876957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8473801906640203791917971 12710702859960305687876957)
              ·
                refine ⟨4766513572485114632953859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12710702859960305687876957 4766513572485114632953859)
                ·
                  refine ⟨7149770358727671949430789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4766513572485114632953859 7149770358727671949430789)
                  ·
                    refine ⟨1340581942261438490518273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7149770358727671949430789 1340581942261438490518273)
                    ·
                      rfl

theorem cell22_3916161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_3916161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3916161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3916161 prefixEnd_3916161 := by exact prefixLift 3916161
  have htrace : WordTrace (prefixWord ++ tailWord_3916161) baseStart_3916161 baseEnd_3916161 := by
    simpa [prefixWord, tailWord_3916161, baseEnd_3916161] using wordTrace_append hprefix tailTrace_3916161
  have hstable : (prefixWord ++ tailWord_3916161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916161).length < 2 ^ (prefixWord ++ tailWord_3916161).sum := by decide
  have hdescent : baseEnd_3916161 < baseStart_3916161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916182 : List Nat := [5, 3, 1, 2, 1, 1, 3, 1, 5]
def baseStart_3916182 : Nat := 118140960795 + 3916182 * 2 ^ 59
def prefixEnd_3916182 : Nat := 4983230072969 + 3 ^ 40 * 3916182 * 2
def baseEnd_3916182 : Nat := 446863043663533811914403

theorem tailTrace_3916182 : CollatzResearch.WordTrace tailWord_3916182 prefixEnd_3916182 446863043663533811914403 := by
  unfold tailWord_3916182
  simp only [CollatzResearch.WordTrace]
  refine ⟨8927180743646807467648925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95223261265565946321588533 8927180743646807467648925)
  ·
    refine ⟨3347692778867552800368347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8927180743646807467648925 3347692778867552800368347)
    ·
      refine ⟨5021539168301329200552521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3347692778867552800368347 5021539168301329200552521)
      ·
        refine ⟨3766154376225996900414391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5021539168301329200552521 3766154376225996900414391)
        ·
          refine ⟨5649231564338995350621587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3766154376225996900414391 5649231564338995350621587)
          ·
            refine ⟨8473847346508493025932381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5649231564338995350621587 8473847346508493025932381)
            ·
              refine ⟨3177692754940684884724643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8473847346508493025932381 3177692754940684884724643)
              ·
                refine ⟨4766539132411027327086965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3177692754940684884724643 4766539132411027327086965)
                ·
                  refine ⟨446863043663533811914403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4766539132411027327086965 446863043663533811914403)
                  ·
                    rfl

theorem cell22_3916182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_3916182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3916182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3916182 prefixEnd_3916182 := by exact prefixLift 3916182
  have htrace : WordTrace (prefixWord ++ tailWord_3916182) baseStart_3916182 baseEnd_3916182 := by
    simpa [prefixWord, tailWord_3916182, baseEnd_3916182] using wordTrace_append hprefix tailTrace_3916182
  have hstable : (prefixWord ++ tailWord_3916182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916182).length < 2 ^ (prefixWord ++ tailWord_3916182).sum := by decide
  have hdescent : baseEnd_3916182 < baseStart_3916182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916242 : List Nat := [3, 2, 2, 4, 1, 2, 2, 1, 2, 3]
def baseStart_3916242 : Nat := 118140960795 + 3916242 * 2 ^ 59
def prefixEnd_3916242 : Nat := 4983230072969 + 3 ^ 40 * 3916242 * 2
def baseEnd_3916242 : Nat := 1340609670216781279243025

theorem tailTrace_3916242 : CollatzResearch.WordTrace tailWord_3916242 prefixEnd_3916242 1340609670216781279243025 := by
  unfold tailWord_3916242
  simp only [CollatzResearch.WordTrace]
  refine ⟨35709270069532887432391745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95224720185421033153044653 35709270069532887432391745)
  ·
    refine ⟨26781952552149665574293809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35709270069532887432391745 26781952552149665574293809)
    ·
      refine ⟨20086464414112249180720357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26781952552149665574293809 20086464414112249180720357)
      ·
        refine ⟨3766212077646046721385067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20086464414112249180720357 3766212077646046721385067)
        ·
          refine ⟨5649318116469070082077601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3766212077646046721385067 5649318116469070082077601)
          ·
            refine ⟨4236988587351802561558201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5649318116469070082077601 4236988587351802561558201)
            ·
              refine ⟨3177741440513851921168651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4236988587351802561558201 3177741440513851921168651)
              ·
                refine ⟨4766612160770777881752977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3177741440513851921168651 4766612160770777881752977)
                ·
                  refine ⟨3574959120578083411314733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4766612160770777881752977 3574959120578083411314733)
                  ·
                    refine ⟨1340609670216781279243025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3574959120578083411314733 1340609670216781279243025)
                    ·
                      rfl

theorem cell22_3916242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_3916242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3916242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3916242 prefixEnd_3916242 := by exact prefixLift 3916242
  have htrace : WordTrace (prefixWord ++ tailWord_3916242) baseStart_3916242 baseEnd_3916242 := by
    simpa [prefixWord, tailWord_3916242, baseEnd_3916242] using wordTrace_append hprefix tailTrace_3916242
  have hstable : (prefixWord ++ tailWord_3916242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916242).length < 2 ^ (prefixWord ++ tailWord_3916242).sum := by decide
  have hdescent : baseEnd_3916242 < baseStart_3916242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916249 : List Nat := [1, 2, 1, 2, 4, 1, 3, 3, 5]
def baseStart_3916249 : Nat := 118140960795 + 3916249 * 2 ^ 59
def prefixEnd_3916249 : Nat := 4983230072969 + 3 ^ 40 * 3916249 * 2
def baseEnd_3916249 : Nat := 446870688819945198106001

theorem tailTrace_3916249 : CollatzResearch.WordTrace tailWord_3916249 prefixEnd_3916249 446870688819945198106001 := by
  unfold tailWord_3916249
  simp only [CollatzResearch.WordTrace]
  refine ⟨142837335589106189925071801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95224890392737459950047867 142837335589106189925071801)
  ·
    refine ⟨107128001691829642443803851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142837335589106189925071801 107128001691829642443803851)
    ·
      refine ⟨160692002537744463665705777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107128001691829642443803851 160692002537744463665705777)
      ·
        refine ⟨120519001903308347749279333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160692002537744463665705777 120519001903308347749279333)
        ·
          refine ⟨22597312856870315202989875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120519001903308347749279333 22597312856870315202989875)
          ·
            refine ⟨33895969285305472804484813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22597312856870315202989875 33895969285305472804484813)
            ·
              refine ⟨12710988481989552301681805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33895969285305472804484813 12710988481989552301681805)
              ·
                refine ⟨4766620680746082113130677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12710988481989552301681805 4766620680746082113130677)
                ·
                  refine ⟨446870688819945198106001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4766620680746082113130677 446870688819945198106001)
                  ·
                    rfl

theorem cell22_3916249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 5].length) (baseStart_3916249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3916249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3916249 prefixEnd_3916249 := by exact prefixLift 3916249
  have htrace : WordTrace (prefixWord ++ tailWord_3916249) baseStart_3916249 baseEnd_3916249 := by
    simpa [prefixWord, tailWord_3916249, baseEnd_3916249] using wordTrace_append hprefix tailTrace_3916249
  have hstable : (prefixWord ++ tailWord_3916249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916249).length < 2 ^ (prefixWord ++ tailWord_3916249).sum := by decide
  have hdescent : baseEnd_3916249 < baseStart_3916249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916328 : List Nat := [2, 1, 5, 2, 1, 1, 1, 5, 4]
def baseStart_3916328 : Nat := 118140960795 + 3916328 * 2 ^ 59
def prefixEnd_3916328 : Nat := 4983230072969 + 3 ^ 40 * 3916328 * 2
def baseEnd_3916328 : Nat := 446879703258101907197587

theorem tailTrace_3916328 : CollatzResearch.WordTrace tailWord_3916328 prefixEnd_3916328 446879703258101907197587 := by
  unfold tailWord_3916328
  simp only [CollatzResearch.WordTrace]
  refine ⟨71420108477909993208598819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95226811303879990944798425 71420108477909993208598819)
  ·
    refine ⟨107130162716864989812898229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71420108477909993208598819 107130162716864989812898229)
    ·
      refine ⟨10043452754706092794959209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107130162716864989812898229 10043452754706092794959209)
      ·
        refine ⟨7532589566029569596219407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10043452754706092794959209 7532589566029569596219407)
        ·
          refine ⟨11298884349044354394329111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7532589566029569596219407 11298884349044354394329111)
          ·
            refine ⟨16948326523566531591493667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11298884349044354394329111 16948326523566531591493667)
            ·
              refine ⟨25422489785349797387240501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16948326523566531591493667 25422489785349797387240501)
              ·
                refine ⟨2383358417376543505053797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25422489785349797387240501 2383358417376543505053797)
                ·
                  refine ⟨446879703258101907197587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2383358417376543505053797 446879703258101907197587)
                  ·
                    rfl

theorem cell22_3916328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 5, 4].length) (baseStart_3916328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3916328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3916328 prefixEnd_3916328 := by exact prefixLift 3916328
  have htrace : WordTrace (prefixWord ++ tailWord_3916328) baseStart_3916328 baseEnd_3916328 := by
    simpa [prefixWord, tailWord_3916328, baseEnd_3916328] using wordTrace_append hprefix tailTrace_3916328
  have hstable : (prefixWord ++ tailWord_3916328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916328).length < 2 ^ (prefixWord ++ tailWord_3916328).sum := by decide
  have hdescent : baseEnd_3916328 < baseStart_3916328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916330 : List Nat := [3, 1, 4, 1, 1, 4, 2, 1, 1, 4]
def baseStart_3916330 : Nat := 118140960795 + 3916330 * 2 ^ 59
def prefixEnd_3916330 : Nat := 4983230072969 + 3 ^ 40 * 3916330 * 2
def baseEnd_3916330 : Nat := 1340639794415178383042755

theorem tailTrace_3916330 : CollatzResearch.WordTrace tailWord_3916330 prefixEnd_3916330 1340639794415178383042755 := by
  unfold tailWord_3916330
  simp only [CollatzResearch.WordTrace]
  refine ⟨35710072475453185189692611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95226859934541827172513629 35710072475453185189692611)
  ·
    refine ⟨53565108713179777784538917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35710072475453185189692611 53565108713179777784538917)
    ·
      refine ⟨10043457883721208334601047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53565108713179777784538917 10043457883721208334601047)
      ·
        refine ⟨15065186825581812501901571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10043457883721208334601047 15065186825581812501901571)
        ·
          refine ⟨22597780238372718752852357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15065186825581812501901571 22597780238372718752852357)
          ·
            refine ⟨4237083794694884766159817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22597780238372718752852357 4237083794694884766159817)
            ·
              refine ⟨3177812846021163574619863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4237083794694884766159817 3177812846021163574619863)
              ·
                refine ⟨4766719269031745361929795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3177812846021163574619863 4766719269031745361929795)
                ·
                  refine ⟨7150078903547618042894693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4766719269031745361929795 7150078903547618042894693)
                  ·
                    refine ⟨1340639794415178383042755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7150078903547618042894693 1340639794415178383042755)
                    ·
                      rfl

theorem cell22_3916330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_3916330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3916330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3916330 prefixEnd_3916330 := by exact prefixLift 3916330
  have htrace : WordTrace (prefixWord ++ tailWord_3916330) baseStart_3916330 baseEnd_3916330 := by
    simpa [prefixWord, tailWord_3916330, baseEnd_3916330] using wordTrace_append hprefix tailTrace_3916330
  have hstable : (prefixWord ++ tailWord_3916330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916330).length < 2 ^ (prefixWord ++ tailWord_3916330).sum := by decide
  have hdescent : baseEnd_3916330 < baseStart_3916330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916358 : List Nat := [6, 1, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_3916358 : Nat := 118140960795 + 3916358 * 2 ^ 59
def prefixEnd_3916358 : Nat := 4983230072969 + 3 ^ 40 * 3916358 * 2
def baseEnd_3916358 : Nat := 1340649379387395643342669

theorem tailTrace_3916358 : CollatzResearch.WordTrace tailWord_3916358 prefixEnd_3916358 1340649379387395643342669 := by
  unfold tailWord_3916358
  simp only [CollatzResearch.WordTrace]
  refine ⟨4463790973303478173149679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 95227540763807534360526485 4463790973303478173149679)
  ·
    refine ⟨6695686459955217259724519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4463790973303478173149679 6695686459955217259724519)
    ·
      refine ⟨10043529689932825889586779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6695686459955217259724519 10043529689932825889586779)
      ·
        refine ⟨15065294534899238834380169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10043529689932825889586779 15065294534899238834380169)
        ·
          refine ⟨11298970901174429125785127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15065294534899238834380169 11298970901174429125785127)
          ·
            refine ⟨16948456351761643688677691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11298970901174429125785127 16948456351761643688677691)
            ·
              refine ⟨25422684527642465533016537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16948456351761643688677691 25422684527642465533016537)
              ·
                refine ⟨19067013395731849149762403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25422684527642465533016537 19067013395731849149762403)
                ·
                  refine ⟨28600520093597773724643605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19067013395731849149762403 28600520093597773724643605)
                  ·
                    refine ⟨1340649379387395643342669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28600520093597773724643605 1340649379387395643342669)
                    ·
                      rfl

theorem cell22_3916358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_3916358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3916358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3916358 prefixEnd_3916358 := by exact prefixLift 3916358
  have htrace : WordTrace (prefixWord ++ tailWord_3916358) baseStart_3916358 baseEnd_3916358 := by
    simpa [prefixWord, tailWord_3916358, baseEnd_3916358] using wordTrace_append hprefix tailTrace_3916358
  have hstable : (prefixWord ++ tailWord_3916358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916358).length < 2 ^ (prefixWord ++ tailWord_3916358).sum := by decide
  have hdescent : baseEnd_3916358 < baseStart_3916358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916384 : List Nat := [2, 1, 1, 3, 2, 1, 3, 2, 7]
def baseStart_3916384 : Nat := 118140960795 + 3916384 * 2 ^ 59
def prefixEnd_3916384 : Nat := 4983230072969 + 3 ^ 40 * 3916384 * 2
def baseEnd_3916384 : Nat := 446886093239580080730863

theorem tailTrace_3916384 : CollatzResearch.WordTrace tailWord_3916384 prefixEnd_3916384 446886093239580080730863 := by
  unfold tailWord_3916384
  simp only [CollatzResearch.WordTrace]
  refine ⟨71421129721808553990618103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95228172962411405320824137 71421129721808553990618103)
  ·
    refine ⟨107131694582712830985927155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71421129721808553990618103 107131694582712830985927155)
    ·
      refine ⟨160697541874069246478890733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107131694582712830985927155 160697541874069246478890733)
      ·
        refine ⟨60261578202775967429584025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160697541874069246478890733 60261578202775967429584025)
        ·
          refine ⟨45196183652081975572188019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60261578202775967429584025 45196183652081975572188019)
          ·
            refine ⟨67794275478122963358282029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45196183652081975572188019 67794275478122963358282029)
            ·
              refine ⟨25422853304296111259355761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67794275478122963358282029 25422853304296111259355761)
              ·
                refine ⟨19067139978222083444516821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25422853304296111259355761 19067139978222083444516821)
                ·
                  refine ⟨446886093239580080730863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19067139978222083444516821 446886093239580080730863)
                  ·
                    rfl

theorem cell22_3916384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 7].length) (baseStart_3916384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3916384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3916384 prefixEnd_3916384 := by exact prefixLift 3916384
  have htrace : WordTrace (prefixWord ++ tailWord_3916384) baseStart_3916384 baseEnd_3916384 := by
    simpa [prefixWord, tailWord_3916384, baseEnd_3916384] using wordTrace_append hprefix tailTrace_3916384
  have hstable : (prefixWord ++ tailWord_3916384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916384).length < 2 ^ (prefixWord ++ tailWord_3916384).sum := by decide
  have hdescent : baseEnd_3916384 < baseStart_3916384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916399 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 4, 5]
def baseStart_3916399 : Nat := 118140960795 + 3916399 * 2 ^ 59
def prefixEnd_3916399 : Nat := 4983230072969 + 3 ^ 40 * 3916399 * 2
def baseEnd_3916399 : Nat := 1340663414525285203067543

theorem tailTrace_3916399 : CollatzResearch.WordTrace tailWord_3916399 prefixEnd_3916399 1340663414525285203067543 := by
  unfold tailWord_3916399
  simp only [CollatzResearch.WordTrace]
  refine ⟨142842806538562765543032251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95228537692375177028688167 142842806538562765543032251)
  ·
    refine ⟨214264209807844148314548377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142842806538562765543032251 214264209807844148314548377)
    ·
      refine ⟨160698157355883111235911283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214264209807844148314548377 160698157355883111235911283)
      ·
        refine ⟨241047236033824666853866925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160698157355883111235911283 241047236033824666853866925)
        ·
          refine ⟨90392713512684250070200097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241047236033824666853866925 90392713512684250070200097)
          ·
            refine ⟨67794535134513187552650073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90392713512684250070200097 67794535134513187552650073)
            ·
              refine ⟨50845901350884890664487555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67794535134513187552650073 50845901350884890664487555)
              ·
                refine ⟨76268852026327335996731333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50845901350884890664487555 76268852026327335996731333)
                ·
                  refine ⟨14300409754936375499387125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76268852026327335996731333 14300409754936375499387125)
                  ·
                    refine ⟨1340663414525285203067543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14300409754936375499387125 1340663414525285203067543)
                    ·
                      rfl

theorem cell22_3916399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 5].length) (baseStart_3916399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3916399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3916399 prefixEnd_3916399 := by exact prefixLift 3916399
  have htrace : WordTrace (prefixWord ++ tailWord_3916399) baseStart_3916399 baseEnd_3916399 := by
    simpa [prefixWord, tailWord_3916399, baseEnd_3916399] using wordTrace_append hprefix tailTrace_3916399
  have hstable : (prefixWord ++ tailWord_3916399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916399).length < 2 ^ (prefixWord ++ tailWord_3916399).sum := by decide
  have hdescent : baseEnd_3916399 < baseStart_3916399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916463 : List Nat := [1, 1, 2, 1, 2, 6, 1, 4, 4]
def baseStart_3916463 : Nat := 118140960795 + 3916463 * 2 ^ 59
def prefixEnd_3916463 : Nat := 4983230072969 + 3 ^ 40 * 3916463 * 2
def baseEnd_3916463 : Nat := 446895107677736789822449

theorem tailTrace_3916463 : CollatzResearch.WordTrace tailWord_3916463 prefixEnd_3916463 446895107677736789822449 := by
  unfold tailWord_3916463
  simp only [CollatzResearch.WordTrace]
  refine ⟨142845140810330904473362043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95230093873553936315574695 142845140810330904473362043)
  ·
    refine ⟨214267711215496356710043065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142845140810330904473362043 214267711215496356710043065)
    ·
      refine ⟨160700783411622267532532299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214267711215496356710043065 160700783411622267532532299)
      ·
        refine ⟨241051175117433401298798449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160700783411622267532532299 241051175117433401298798449)
        ·
          refine ⟨180788381338075050974098837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241051175117433401298798449 180788381338075050974098837)
          ·
            refine ⟨8474455375222268014410883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 180788381338075050974098837 8474455375222268014410883)
            ·
              refine ⟨12711683062833402021616325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8474455375222268014410883 12711683062833402021616325)
              ·
                refine ⟨2383440574281262879053061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12711683062833402021616325 2383440574281262879053061)
                ·
                  refine ⟨446895107677736789822449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2383440574281262879053061 446895107677736789822449)
                  ·
                    rfl

theorem cell22_3916463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 4, 4].length) (baseStart_3916463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3916463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3916463 prefixEnd_3916463 := by exact prefixLift 3916463
  have htrace : WordTrace (prefixWord ++ tailWord_3916463) baseStart_3916463 baseEnd_3916463 := by
    simpa [prefixWord, tailWord_3916463, baseEnd_3916463] using wordTrace_append hprefix tailTrace_3916463
  have hstable : (prefixWord ++ tailWord_3916463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916463).length < 2 ^ (prefixWord ++ tailWord_3916463).sum := by decide
  have hdescent : baseEnd_3916463 < baseStart_3916463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916476 : List Nat := [2, 2, 2, 3, 1, 1, 2, 2, 1, 6]
def baseStart_3916476 : Nat := 118140960795 + 3916476 * 2 ^ 59
def prefixEnd_3916476 : Nat := 4983230072969 + 3 ^ 40 * 3916476 * 2
def baseEnd_3916476 : Nat := 1340689773198882668892307

theorem tailTrace_3916476 : CollatzResearch.WordTrace tailWord_3916476 prefixEnd_3916476 1340689773198882668892307 := by
  unfold tailWord_3916476
  simp only [CollatzResearch.WordTrace]
  refine ⟨71422807479641903846792641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95230409972855871795723521 71422807479641903846792641)
  ·
    refine ⟨53567105609731427885094481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71422807479641903846792641 53567105609731427885094481)
    ·
      refine ⟨40175329207298570913820861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53567105609731427885094481 40175329207298570913820861)
      ·
        refine ⟨15065748452736964092682823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40175329207298570913820861 15065748452736964092682823)
        ·
          refine ⟨22598622679105446139024235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15065748452736964092682823 22598622679105446139024235)
          ·
            refine ⟨33897934018658169208536353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22598622679105446139024235 33897934018658169208536353)
            ·
              refine ⟨25423450513993626906402265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33897934018658169208536353 25423450513993626906402265)
              ·
                refine ⟨19067587885495220179801699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25423450513993626906402265 19067587885495220179801699)
                ·
                  refine ⟨28601381828242830269702549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19067587885495220179801699 28601381828242830269702549)
                  ·
                    refine ⟨1340689773198882668892307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28601381828242830269702549 1340689773198882668892307)
                    ·
                      rfl

theorem cell22_3916476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_3916476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3916476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3916476 prefixEnd_3916476 := by exact prefixLift 3916476
  have htrace : WordTrace (prefixWord ++ tailWord_3916476) baseStart_3916476 baseEnd_3916476 := by
    simpa [prefixWord, tailWord_3916476, baseEnd_3916476] using wordTrace_append hprefix tailTrace_3916476
  have hstable : (prefixWord ++ tailWord_3916476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916476).length < 2 ^ (prefixWord ++ tailWord_3916476).sum := by decide
  have hdescent : baseEnd_3916476 < baseStart_3916476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916478 : List Nat := [4, 2, 1, 1, 2, 1, 4, 1, 1, 5]
def baseStart_3916478 : Nat := 118140960795 + 3916478 * 2 ^ 59
def prefixEnd_3916478 : Nat := 4983230072969 + 3 ^ 40 * 3916478 * 2
def baseEnd_3916478 : Nat := 1340690457839755330342301

theorem tailTrace_3916478 : CollatzResearch.WordTrace tailWord_3916478 prefixEnd_3916478 1340690457839755330342301 := by
  unfold tailWord_3916478
  simp only [CollatzResearch.WordTrace]
  refine ⟨17855710988159570254394761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95230458603517708023438725 17855710988159570254394761)
  ·
    refine ⟨13391783241119677690796071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17855710988159570254394761 13391783241119677690796071)
    ·
      refine ⟨20087674861679516536194107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13391783241119677690796071 20087674861679516536194107)
      ·
        refine ⟨30131512292519274804291161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20087674861679516536194107 30131512292519274804291161)
        ·
          refine ⟨22598634219389456103218371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30131512292519274804291161 22598634219389456103218371)
          ·
            refine ⟨33897951329084184154827557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22598634219389456103218371 33897951329084184154827557)
            ·
              refine ⟨6355865874203284529030167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33897951329084184154827557 6355865874203284529030167)
              ·
                refine ⟨9533798811304926793545251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6355865874203284529030167 9533798811304926793545251)
                ·
                  refine ⟨14300698216957390190317877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9533798811304926793545251 14300698216957390190317877)
                  ·
                    refine ⟨1340690457839755330342301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14300698216957390190317877 1340690457839755330342301)
                    ·
                      rfl

theorem cell22_3916478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_3916478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3916478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3916478 prefixEnd_3916478 := by exact prefixLift 3916478
  have htrace : WordTrace (prefixWord ++ tailWord_3916478) baseStart_3916478 baseEnd_3916478 := by
    simpa [prefixWord, tailWord_3916478, baseEnd_3916478] using wordTrace_append hprefix tailTrace_3916478
  have hstable : (prefixWord ++ tailWord_3916478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916478).length < 2 ^ (prefixWord ++ tailWord_3916478).sum := by decide
  have hdescent : baseEnd_3916478 < baseStart_3916478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916508 : List Nat := [2, 2, 5, 1, 1, 2, 9]
def baseStart_3916508 : Nat := 118140960795 + 3916508 * 2 ^ 59
def prefixEnd_3916508 : Nat := 4983230072969 + 3 ^ 40 * 3916508 * 2
def baseEnd_3916508 : Nat := 49655582498253527855267

theorem tailTrace_3916508 : CollatzResearch.WordTrace tailWord_3916508 prefixEnd_3916508 49655582498253527855267 := by
  unfold tailWord_3916508
  simp only [CollatzResearch.WordTrace]
  refine ⟨71423391047583938579375089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95231188063445251439166785 71423391047583938579375089)
  ·
    refine ⟨53567543285687953934531317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71423391047583938579375089 53567543285687953934531317)
    ·
      refine ⟨5021957183033245681362311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53567543285687953934531317 5021957183033245681362311)
      ·
        refine ⟨7532935774549868522043467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5021957183033245681362311 7532935774549868522043467)
        ·
          refine ⟨11299403661824802783065201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7532935774549868522043467 11299403661824802783065201)
          ·
            refine ⟨8474552746368602087298901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11299403661824802783065201 8474552746368602087298901)
            ·
              refine ⟨49655582498253527855267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8474552746368602087298901 49655582498253527855267)
              ·
                rfl

theorem cell22_3916508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 9].length) (baseStart_3916508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3916508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3916508 prefixEnd_3916508 := by exact prefixLift 3916508
  have htrace : WordTrace (prefixWord ++ tailWord_3916508) baseStart_3916508 baseEnd_3916508 := by
    simpa [prefixWord, tailWord_3916508, baseEnd_3916508] using wordTrace_append hprefix tailTrace_3916508
  have hstable : (prefixWord ++ tailWord_3916508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916508).length < 2 ^ (prefixWord ++ tailWord_3916508).sum := by decide
  have hdescent : baseEnd_3916508 < baseStart_3916508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916613 : List Nat := [1, 3, 1, 1, 1, 2, 2, 4, 4, 3]
def baseStart_3916613 : Nat := 118140960795 + 3916613 * 2 ^ 59
def prefixEnd_3916613 : Nat := 4983230072969 + 3 ^ 40 * 3916613 * 2
def baseEnd_3916613 : Nat := 1340736671098659978216887

theorem tailTrace_3916613 : CollatzResearch.WordTrace tailWord_3916613 prefixEnd_3916613 1340736671098659978216887 := by
  unfold tailWord_3916613
  simp only [CollatzResearch.WordTrace]
  refine ⟨142850611759787480091322493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95233741173191653394214995 142850611759787480091322493)
  ·
    refine ⟨53568979409920305034245935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142850611759787480091322493 53568979409920305034245935)
    ·
      refine ⟨80353469114880457551368903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53568979409920305034245935 80353469114880457551368903)
      ·
        refine ⟨120530203672320686327053355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80353469114880457551368903 120530203672320686327053355)
        ·
          refine ⟨180795305508481029490580033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120530203672320686327053355 180795305508481029490580033)
          ·
            refine ⟨135596479131360772117935025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180795305508481029490580033 135596479131360772117935025)
            ·
              refine ⟨101697359348520579088451269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135596479131360772117935025 101697359348520579088451269)
              ·
                refine ⟨19068254877847608579084613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101697359348520579088451269 19068254877847608579084613)
                ·
                  refine ⟨3575297789596426608578365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19068254877847608579084613 3575297789596426608578365)
                  ·
                    refine ⟨1340736671098659978216887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3575297789596426608578365 1340736671098659978216887)
                    ·
                      rfl

theorem cell22_3916613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 4, 3].length) (baseStart_3916613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3916613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3916613 prefixEnd_3916613 := by exact prefixLift 3916613
  have htrace : WordTrace (prefixWord ++ tailWord_3916613) baseStart_3916613 baseEnd_3916613 := by
    simpa [prefixWord, tailWord_3916613, baseEnd_3916613] using wordTrace_append hprefix tailTrace_3916613
  have hstable : (prefixWord ++ tailWord_3916613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916613).length < 2 ^ (prefixWord ++ tailWord_3916613).sum := by decide
  have hdescent : baseEnd_3916613 < baseStart_3916613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916643 : List Nat := [1, 1, 1, 5, 3, 1, 3, 7]
def baseStart_3916643 : Nat := 118140960795 + 3916643 * 2 ^ 59
def prefixEnd_3916643 : Nat := 4983230072969 + 3 ^ 40 * 3916643 * 2
def baseEnd_3916643 : Nat := 148971882301305544440755

theorem tailTrace_3916643 : CollatzResearch.WordTrace tailWord_3916643 prefixEnd_3916643 148971882301305544440755 := by
  unfold tailWord_3916643
  simp only [CollatzResearch.WordTrace]
  refine ⟨142851705949678795214914583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95234470633119196809943055 142851705949678795214914583)
  ·
    refine ⟨214277558924518192822371875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142851705949678795214914583 214277558924518192822371875)
    ·
      refine ⟨321416338386777289233557813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214277558924518192822371875 321416338386777289233557813)
      ·
        refine ⟨30132781723760370865646045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 321416338386777289233557813 30132781723760370865646045)
        ·
          refine ⟨11299793146410139074617267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30132781723760370865646045 11299793146410139074617267)
          ·
            refine ⟨16949689719615208611925901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11299793146410139074617267 16949689719615208611925901)
            ·
              refine ⟨6356133644855703229472213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16949689719615208611925901 6356133644855703229472213)
              ·
                refine ⟨148971882301305544440755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6356133644855703229472213 148971882301305544440755)
                ·
                  rfl

theorem cell22_3916643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 7].length) (baseStart_3916643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3916643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3916643 prefixEnd_3916643 := by exact prefixLift 3916643
  have htrace : WordTrace (prefixWord ++ tailWord_3916643) baseStart_3916643 baseEnd_3916643 := by
    simpa [prefixWord, tailWord_3916643, baseEnd_3916643] using wordTrace_append hprefix tailTrace_3916643
  have hstable : (prefixWord ++ tailWord_3916643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916643).length < 2 ^ (prefixWord ++ tailWord_3916643).sum := by decide
  have hdescent : baseEnd_3916643 < baseStart_3916643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916662 : List Nat := [5, 1, 1, 3, 1, 1, 3, 1, 2, 4]
def baseStart_3916662 : Nat := 118140960795 + 3916662 * 2 ^ 59
def prefixEnd_3916662 : Nat := 4983230072969 + 3 ^ 40 * 3916662 * 2
def baseEnd_3916662 : Nat := 1340753444800040183741737

theorem tailTrace_3916662 : CollatzResearch.WordTrace tailWord_3916662 prefixEnd_3916662 1340753444800040183741737 := by
  unfold tailWord_3916662
  simp only [CollatzResearch.WordTrace]
  refine ⟨8928274933538122591241015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95234932624406640973237493 8928274933538122591241015)
  ·
    refine ⟨13392412400307183886861523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8928274933538122591241015 13392412400307183886861523)
    ·
      refine ⟨20088618600460775830292285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13392412400307183886861523 20088618600460775830292285)
      ·
        refine ⟨7533231975172790936359607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20088618600460775830292285 7533231975172790936359607)
        ·
          refine ⟨11299847962759186404539411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7533231975172790936359607 11299847962759186404539411)
          ·
            refine ⟨16949771944138779606809117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11299847962759186404539411 16949771944138779606809117)
            ·
              refine ⟨6356164479052042352553419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16949771944138779606809117 6356164479052042352553419)
              ·
                refine ⟨9534246718578063528830129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6356164479052042352553419 9534246718578063528830129)
                ·
                  refine ⟨7150685038933547646622597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9534246718578063528830129 7150685038933547646622597)
                  ·
                    refine ⟨1340753444800040183741737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7150685038933547646622597 1340753444800040183741737)
                    ·
                      rfl

theorem cell22_3916662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_3916662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3916662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3916662 prefixEnd_3916662 := by exact prefixLift 3916662
  have htrace : WordTrace (prefixWord ++ tailWord_3916662) baseStart_3916662 baseEnd_3916662 := by
    simpa [prefixWord, tailWord_3916662, baseEnd_3916662] using wordTrace_append hprefix tailTrace_3916662
  have hstable : (prefixWord ++ tailWord_3916662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916662).length < 2 ^ (prefixWord ++ tailWord_3916662).sum := by decide
  have hdescent : baseEnd_3916662 < baseStart_3916662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916692 : List Nat := [2, 4, 2, 1, 1, 1, 4, 1, 3, 3]
def baseStart_3916692 : Nat := 118140960795 + 3916692 * 2 ^ 59
def prefixEnd_3916692 : Nat := 4983230072969 + 3 ^ 40 * 3916692 * 2
def baseEnd_3916692 : Nat := 1340763714413130105491645

theorem tailTrace_3916692 : CollatzResearch.WordTrace tailWord_3916692 prefixEnd_3916692 1340763714413130105491645 := by
  unfold tailWord_3916692
  simp only [CollatzResearch.WordTrace]
  refine ⟨71426746563250638291724165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95235662084334184388965553 71426746563250638291724165)
  ·
    refine ⟨13392514980609494679698281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71426746563250638291724165 13392514980609494679698281)
    ·
      refine ⟨10044386235457121009773711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13392514980609494679698281 10044386235457121009773711)
      ·
        refine ⟨15066579353185681514660567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10044386235457121009773711 15066579353185681514660567)
        ·
          refine ⟨22599869029778522271990851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15066579353185681514660567 22599869029778522271990851)
          ·
            refine ⟨33899803544667783407986277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22599869029778522271990851 33899803544667783407986277)
            ·
              refine ⟨6356213164625209388997427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33899803544667783407986277 6356213164625209388997427)
              ·
                refine ⟨9534319746937814083496141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6356213164625209388997427 9534319746937814083496141)
                ·
                  refine ⟨3575369905101680281311053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9534319746937814083496141 3575369905101680281311053)
                  ·
                    refine ⟨1340763714413130105491645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3575369905101680281311053 1340763714413130105491645)
                    ·
                      rfl

theorem cell22_3916692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_3916692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3916692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3916692 prefixEnd_3916692 := by exact prefixLift 3916692
  have htrace : WordTrace (prefixWord ++ tailWord_3916692) baseStart_3916692 baseEnd_3916692 := by
    simpa [prefixWord, tailWord_3916692, baseEnd_3916692] using wordTrace_append hprefix tailTrace_3916692
  have hstable : (prefixWord ++ tailWord_3916692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916692).length < 2 ^ (prefixWord ++ tailWord_3916692).sum := by decide
  have hdescent : baseEnd_3916692 < baseStart_3916692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916750 : List Nat := [4, 1, 1, 1, 2, 3, 3, 1, 6]
def baseStart_3916750 : Nat := 118140960795 + 3916750 * 2 ^ 59
def prefixEnd_3916750 : Nat := 4983230072969 + 3 ^ 40 * 3916750 * 2
def baseEnd_3916750 : Nat := 446927856332812429180489

theorem tailTrace_3916750 : CollatzResearch.WordTrace tailWord_3916750 prefixEnd_3916750 446927856332812429180489 := by
  unfold tailWord_3916750
  simp only [CollatzResearch.WordTrace]
  refine ⟨17856951070036394061132463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95237072373527434992706469 17856951070036394061132463)
  ·
    refine ⟨26785426605054591091698695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17856951070036394061132463 26785426605054591091698695)
    ·
      refine ⟨40178139907581886637548043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26785426605054591091698695 40178139907581886637548043)
      ·
        refine ⟨60267209861372829956322065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40178139907581886637548043 60267209861372829956322065)
        ·
          refine ⟨45200407396029622467241549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60267209861372829956322065 45200407396029622467241549)
          ·
            refine ⟨16950152773511108425215581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45200407396029622467241549 16950152773511108425215581)
            ·
              refine ⟨6356307290066665659455843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16950152773511108425215581 6356307290066665659455843)
              ·
                refine ⟨9534460935099998489183765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6356307290066665659455843 9534460935099998489183765)
                ·
                  refine ⟨446927856332812429180489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9534460935099998489183765 446927856332812429180489)
                  ·
                    rfl

theorem cell22_3916750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_3916750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3916750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3916750 prefixEnd_3916750 := by exact prefixLift 3916750
  have htrace : WordTrace (prefixWord ++ tailWord_3916750) baseStart_3916750 baseEnd_3916750 := by
    simpa [prefixWord, tailWord_3916750, baseEnd_3916750] using wordTrace_append hprefix tailTrace_3916750
  have hstable : (prefixWord ++ tailWord_3916750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916750).length < 2 ^ (prefixWord ++ tailWord_3916750).sum := by decide
  have hdescent : baseEnd_3916750 < baseStart_3916750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916782 : List Nat := [4, 1, 2, 1, 4, 1, 1, 2, 1, 5]
def baseStart_3916782 : Nat := 118140960795 + 3916782 * 2 ^ 59
def prefixEnd_3916782 : Nat := 4983230072969 + 3 ^ 40 * 3916782 * 2
def baseEnd_3916782 : Nat := 1340794523252399870741369

theorem tailTrace_3916782 : CollatzResearch.WordTrace tailWord_3916782 prefixEnd_3916782 1340794523252399870741369 := by
  unfold tailWord_3916782
  simp only [CollatzResearch.WordTrace]
  refine ⟨17857096962021902744278075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95237850464116814636149733 17857096962021902744278075)
  ·
    refine ⟨26785645443032854116417113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17857096962021902744278075 26785645443032854116417113)
    ·
      refine ⟨20089234082274640587312835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26785645443032854116417113 20089234082274640587312835)
      ·
        refine ⟨30133851123411960880969253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20089234082274640587312835 30133851123411960880969253)
        ·
          refine ⟨5650097085639742665181735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30133851123411960880969253 5650097085639742665181735)
          ·
            refine ⟨8475145628459613997772603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5650097085639742665181735 8475145628459613997772603)
            ·
              refine ⟨12712718442689420996658905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8475145628459613997772603 12712718442689420996658905)
              ·
                refine ⟨9534538832017065747494179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12712718442689420996658905 9534538832017065747494179)
                ·
                  refine ⟨14301808248025598621241269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9534538832017065747494179 14301808248025598621241269)
                  ·
                    refine ⟨1340794523252399870741369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14301808248025598621241269 1340794523252399870741369)
                    ·
                      rfl

theorem cell22_3916782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_3916782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3916782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3916782 prefixEnd_3916782 := by exact prefixLift 3916782
  have htrace : WordTrace (prefixWord ++ tailWord_3916782) baseStart_3916782 baseEnd_3916782 := by
    simpa [prefixWord, tailWord_3916782, baseEnd_3916782] using wordTrace_append hprefix tailTrace_3916782
  have hstable : (prefixWord ++ tailWord_3916782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916782).length < 2 ^ (prefixWord ++ tailWord_3916782).sum := by decide
  have hdescent : baseEnd_3916782 < baseStart_3916782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916786 : List Nat := [3, 2, 1, 5, 1, 1, 3, 1, 1, 4]
def baseStart_3916786 : Nat := 118140960795 + 3916786 * 2 ^ 59
def prefixEnd_3916786 : Nat := 4983230072969 + 3 ^ 40 * 3916786 * 2
def baseEnd_3916786 : Nat := 1340795892534145193641357

theorem tailTrace_3916786 : CollatzResearch.WordTrace tailWord_3916786 prefixEnd_3916786 1340795892534145193641357 := by
  unfold tailWord_3916786
  simp only [CollatzResearch.WordTrace]
  refine ⟨35714230397040182659342553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95237947725440487091580141 35714230397040182659342553)
  ·
    refine ⟨26785672797780136994506915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35714230397040182659342553 26785672797780136994506915)
    ·
      refine ⟨40178509196670205491760373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26785672797780136994506915 40178509196670205491760373)
      ·
        refine ⟨3766735237187831764852535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40178509196670205491760373 3766735237187831764852535)
        ·
          refine ⟨5650102855781747647278803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3766735237187831764852535 5650102855781747647278803)
          ·
            refine ⟨8475154283672621470918205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5650102855781747647278803 8475154283672621470918205)
            ·
              refine ⟨3178182856377233051594327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8475154283672621470918205 3178182856377233051594327)
              ·
                refine ⟨4767274284565849577391491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3178182856377233051594327 4767274284565849577391491)
                ·
                  refine ⟨7150911426848774366087237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4767274284565849577391491 7150911426848774366087237)
                  ·
                    refine ⟨1340795892534145193641357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7150911426848774366087237 1340795892534145193641357)
                    ·
                      rfl

theorem cell22_3916786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 1, 4].length) (baseStart_3916786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3916786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3916786 prefixEnd_3916786 := by exact prefixLift 3916786
  have htrace : WordTrace (prefixWord ++ tailWord_3916786) baseStart_3916786 baseEnd_3916786 := by
    simpa [prefixWord, tailWord_3916786, baseEnd_3916786] using wordTrace_append hprefix tailTrace_3916786
  have hstable : (prefixWord ++ tailWord_3916786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916786).length < 2 ^ (prefixWord ++ tailWord_3916786).sum := by decide
  have hdescent : baseEnd_3916786 < baseStart_3916786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916844 : List Nat := [2, 2, 1, 1, 1, 2, 6, 3, 1, 3]
def baseStart_3916844 : Nat := 118140960795 + 3916844 * 2 ^ 59
def prefixEnd_3916844 : Nat := 4983230072969 + 3 ^ 40 * 3916844 * 2
def baseEnd_3916844 : Nat := 1340815747119452375691179

theorem tailTrace_3916844 : CollatzResearch.WordTrace tailWord_3916844 prefixEnd_3916844 1340815747119452375691179 := by
  unfold tailWord_3916844
  simp only [CollatzResearch.WordTrace]
  refine ⟨71429518510975303271490793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95239358014633737695321057 71429518510975303271490793)
  ·
    refine ⟨53572138883231477453618095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71429518510975303271490793 53572138883231477453618095)
    ·
      refine ⟨80358208324847216180427143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53572138883231477453618095 80358208324847216180427143)
      ·
        refine ⟨120537312487270824270640715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80358208324847216180427143 120537312487270824270640715)
        ·
          refine ⟨180805968730906236405961073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120537312487270824270640715 180805968730906236405961073)
          ·
            refine ⟨135604476548179677304470805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180805968730906236405961073 135604476548179677304470805)
            ·
              refine ⟨6356459838195922373647069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 135604476548179677304470805 6356459838195922373647069)
              ·
                refine ⟨2383672439323470890117651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6356459838195922373647069 2383672439323470890117651)
                ·
                  refine ⟨3575508658985206335176477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2383672439323470890117651 3575508658985206335176477)
                  ·
                    refine ⟨1340815747119452375691179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3575508658985206335176477 1340815747119452375691179)
                    ·
                      rfl

theorem cell22_3916844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 3, 1, 3].length) (baseStart_3916844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3916844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3916844 prefixEnd_3916844 := by exact prefixLift 3916844
  have htrace : WordTrace (prefixWord ++ tailWord_3916844) baseStart_3916844 baseEnd_3916844 := by
    simpa [prefixWord, tailWord_3916844, baseEnd_3916844] using wordTrace_append hprefix tailTrace_3916844
  have hstable : (prefixWord ++ tailWord_3916844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916844).length < 2 ^ (prefixWord ++ tailWord_3916844).sum := by decide
  have hdescent : baseEnd_3916844 < baseStart_3916844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916857 : List Nat := [1, 2, 1, 5, 2, 1, 3, 2, 5]
def baseStart_3916857 : Nat := 118140960795 + 3916857 * 2 ^ 59
def prefixEnd_3916857 : Nat := 4983230072969 + 3 ^ 40 * 3916857 * 2
def baseEnd_3916857 : Nat := 446940065761708225038713

theorem tailTrace_3916857 : CollatzResearch.WordTrace tailWord_3916857 prefixEnd_3916857 446940065761708225038713 := by
  unfold tailWord_3916857
  simp only [CollatzResearch.WordTrace]
  refine ⟨142859511170903509763204825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95239674113935673175469883 142859511170903509763204825)
  ·
    refine ⟨107144633378177632322403619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142859511170903509763204825 107144633378177632322403619)
    ·
      refine ⟨160716950067266448483605429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107144633378177632322403619 160716950067266448483605429)
      ·
        refine ⟨15067214068806229545338009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160716950067266448483605429 15067214068806229545338009)
        ·
          refine ⟨11300410551604672159003507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15067214068806229545338009 11300410551604672159003507)
          ·
            refine ⟨16950615827407008238505261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11300410551604672159003507 16950615827407008238505261)
            ·
              refine ⟨6356480935277628089439473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16950615827407008238505261 6356480935277628089439473)
              ·
                refine ⟨4767360701458221067079605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6356480935277628089439473 4767360701458221067079605)
                ·
                  refine ⟨446940065761708225038713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4767360701458221067079605 446940065761708225038713)
                  ·
                    rfl

theorem cell22_3916857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 5].length) (baseStart_3916857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3916857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3916857 prefixEnd_3916857 := by exact prefixLift 3916857
  have htrace : WordTrace (prefixWord ++ tailWord_3916857) baseStart_3916857 baseEnd_3916857 := by
    simpa [prefixWord, tailWord_3916857, baseEnd_3916857] using wordTrace_append hprefix tailTrace_3916857
  have hstable : (prefixWord ++ tailWord_3916857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916857).length < 2 ^ (prefixWord ++ tailWord_3916857).sum := by decide
  have hdescent : baseEnd_3916857 < baseStart_3916857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916885 : List Nat := [1, 3, 2, 2, 1, 2, 1, 4, 6]
def baseStart_3916885 : Nat := 118140960795 + 3916885 * 2 ^ 59
def prefixEnd_3916885 : Nat := 4983230072969 + 3 ^ 40 * 3916885 * 2
def baseEnd_3916885 : Nat := 446943260752447311805351

theorem tailTrace_3916885 : CollatzResearch.WordTrace tailWord_3916885 prefixEnd_3916885 446943260752447311805351 := by
  unfold tailWord_3916885
  simp only [CollatzResearch.WordTrace]
  refine ⟨142860532414802070545224109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95240354943201380363482739 142860532414802070545224109)
  ·
    refine ⟨53572699655550776454459041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142860532414802070545224109 53572699655550776454459041)
    ·
      refine ⟨40179524741663082340844281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53572699655550776454459041 40179524741663082340844281)
      ·
        refine ⟨30134643556247311755633211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40179524741663082340844281 30134643556247311755633211)
        ·
          refine ⟨45201965334370967633449817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30134643556247311755633211 45201965334370967633449817)
          ·
            refine ⟨33901474000778225725087363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45201965334370967633449817 33901474000778225725087363)
            ·
              refine ⟨50852211001167338587631045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33901474000778225725087363 50852211001167338587631045)
              ·
                refine ⟨9534789562718875985180821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50852211001167338587631045 9534789562718875985180821)
                ·
                  refine ⟨446943260752447311805351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9534789562718875985180821 446943260752447311805351)
                  ·
                    rfl

theorem cell22_3916885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 6].length) (baseStart_3916885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3916885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3916885 prefixEnd_3916885 := by exact prefixLift 3916885
  have htrace : WordTrace (prefixWord ++ tailWord_3916885) baseStart_3916885 baseEnd_3916885 := by
    simpa [prefixWord, tailWord_3916885, baseEnd_3916885] using wordTrace_append hprefix tailTrace_3916885
  have hstable : (prefixWord ++ tailWord_3916885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916885).length < 2 ^ (prefixWord ++ tailWord_3916885).sum := by decide
  have hdescent : baseEnd_3916885 < baseStart_3916885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916900 : List Nat := [2, 3, 1, 1, 2, 1, 1, 3, 3, 5]
def baseStart_3916900 : Nat := 118140960795 + 3916900 * 2 ^ 59
def prefixEnd_3916900 : Nat := 4983230072969 + 3 ^ 40 * 3916900 * 2
def baseEnd_3916900 : Nat := 1340834917063886896291007

theorem tailTrace_3916900 : CollatzResearch.WordTrace tailWord_3916900 prefixEnd_3916900 1340834917063886896291007 := by
  unfold tailWord_3916900
  simp only [CollatzResearch.WordTrace]
  refine ⟨71430539754873864053510077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95240719673165152071346769 71430539754873864053510077)
  ·
    refine ⟨26786452408077699020066279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71430539754873864053510077 26786452408077699020066279)
    ·
      refine ⟨40179678612116548530099419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26786452408077699020066279 40179678612116548530099419)
      ·
        refine ⟨60269517918174822795149129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40179678612116548530099419 60269517918174822795149129)
        ·
          refine ⟨45202138438631117096361847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60269517918174822795149129 45202138438631117096361847)
          ·
            refine ⟨67803207657946675644542771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45202138438631117096361847 67803207657946675644542771)
            ·
              refine ⟨101704811486920013466814157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67803207657946675644542771 101704811486920013466814157)
              ·
                refine ⟨38139304307595005050055309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101704811486920013466814157 38139304307595005050055309)
                ·
                  refine ⟨14302239115348126893770741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38139304307595005050055309 14302239115348126893770741)
                  ·
                    refine ⟨1340834917063886896291007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14302239115348126893770741 1340834917063886896291007)
                    ·
                      rfl

theorem cell22_3916900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_3916900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3916900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3916900 prefixEnd_3916900 := by exact prefixLift 3916900
  have htrace : WordTrace (prefixWord ++ tailWord_3916900) baseStart_3916900 baseEnd_3916900 := by
    simpa [prefixWord, tailWord_3916900, baseEnd_3916900] using wordTrace_append hprefix tailTrace_3916900
  have hstable : (prefixWord ++ tailWord_3916900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916900).length < 2 ^ (prefixWord ++ tailWord_3916900).sum := by decide
  have hdescent : baseEnd_3916900 < baseStart_3916900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916919 : List Nat := [1, 1, 3, 1, 1, 4, 5, 2, 4]
def baseStart_3916919 : Nat := 118140960795 + 3916919 * 2 ^ 59
def prefixEnd_3916919 : Nat := 4983230072969 + 3 ^ 40 * 3916919 * 2
def baseEnd_3916919 : Nat := 446947140384059060021983

theorem tailTrace_3916919 : CollatzResearch.WordTrace tailWord_3916919 prefixEnd_3916919 446947140384059060021983 := by
  unfold tailWord_3916919
  simp only [CollatzResearch.WordTrace]
  refine ⟨142861772496678894351961811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95241181664452596234641207 142861772496678894351961811)
  ·
    refine ⟨214292658745018341527942717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142861772496678894351961811 214292658745018341527942717)
    ·
      refine ⟨80359747029381878072978519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214292658745018341527942717 80359747029381878072978519)
      ·
        refine ⟨120539620544072817109467779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80359747029381878072978519 120539620544072817109467779)
        ·
          refine ⟨180809430816109225664201669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120539620544072817109467779 180809430816109225664201669)
          ·
            refine ⟨33901768278020479812037813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180809430816109225664201669 33901768278020479812037813)
            ·
              refine ⟨3178290776064419982378545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33901768278020479812037813 3178290776064419982378545)
              ·
                refine ⟨2383718082048314986783909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3178290776064419982378545 2383718082048314986783909)
                ·
                  refine ⟨446947140384059060021983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2383718082048314986783909 446947140384059060021983)
                  ·
                    rfl

theorem cell22_3916919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 2, 4].length) (baseStart_3916919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3916919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3916919 prefixEnd_3916919 := by exact prefixLift 3916919
  have htrace : WordTrace (prefixWord ++ tailWord_3916919) baseStart_3916919 baseEnd_3916919 := by
    simpa [prefixWord, tailWord_3916919, baseEnd_3916919] using wordTrace_append hprefix tailTrace_3916919
  have hstable : (prefixWord ++ tailWord_3916919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916919).length < 2 ^ (prefixWord ++ tailWord_3916919).sum := by decide
  have hdescent : baseEnd_3916919 < baseStart_3916919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916975 : List Nat := [1, 1, 2, 1, 2, 3, 2, 3, 7]
def baseStart_3916975 : Nat := 118140960795 + 3916975 * 2 ^ 59
def prefixEnd_3916975 : Nat := 4983230072969 + 3 ^ 40 * 3916975 * 2
def baseEnd_3916975 : Nat := 446953530365537233555259

theorem tailTrace_3916975 : CollatzResearch.WordTrace tailWord_3916975 prefixEnd_3916975 446953530365537233555259 := by
  unfold tailWord_3916975
  simp only [CollatzResearch.WordTrace]
  refine ⟨142863814984476015916000379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95242543322984010610666919 142863814984476015916000379)
  ·
    refine ⟨214295722476714023874000569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142863814984476015916000379 214295722476714023874000569)
    ·
      refine ⟨160721791857535517905500427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214295722476714023874000569 160721791857535517905500427)
      ·
        refine ⟨241082687786303276858250641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160721791857535517905500427 241082687786303276858250641)
        ·
          refine ⟨180812015839727457643687981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241082687786303276858250641 180812015839727457643687981)
          ·
            refine ⟨67804505939897796616382993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180812015839727457643687981 67804505939897796616382993)
            ·
              refine ⟨50853379454923347462287245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67804505939897796616382993 50853379454923347462287245)
              ·
                refine ⟨19070017295596255298357717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50853379454923347462287245 19070017295596255298357717)
                ·
                  refine ⟨446953530365537233555259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19070017295596255298357717 446953530365537233555259)
                  ·
                    rfl

theorem cell22_3916975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 7].length) (baseStart_3916975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3916975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3916975 prefixEnd_3916975 := by exact prefixLift 3916975
  have htrace : WordTrace (prefixWord ++ tailWord_3916975) baseStart_3916975 baseEnd_3916975 := by
    simpa [prefixWord, tailWord_3916975, baseEnd_3916975] using wordTrace_append hprefix tailTrace_3916975
  have hstable : (prefixWord ++ tailWord_3916975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916975).length < 2 ^ (prefixWord ++ tailWord_3916975).sum := by decide
  have hdescent : baseEnd_3916975 < baseStart_3916975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916977 : List Nat := [1, 2, 2, 5, 1, 1, 1, 1, 2, 6]
def baseStart_3916977 : Nat := 118140960795 + 3916977 * 2 ^ 59
def prefixEnd_3916977 : Nat := 4983230072969 + 3 ^ 40 * 3916977 * 2
def baseEnd_3916977 : Nat := 1340861275737484362115771

theorem tailTrace_3916977 : CollatzResearch.WordTrace tailWord_3916977 prefixEnd_3916977 1340861275737484362115771 := by
  unfold tailWord_3916977
  simp only [CollatzResearch.WordTrace]
  refine ⟨142863887930468770257573185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95242591953645846838382123 142863887930468770257573185)
  ·
    refine ⟨107147915947851577693179889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142863887930468770257573185 107147915947851577693179889)
    ·
      refine ⟨80360936960888683269884917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107147915947851577693179889 80360936960888683269884917)
      ·
        refine ⟨7533837840083314056551711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80360936960888683269884917 7533837840083314056551711)
        ·
          refine ⟨11300756760124971084827567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7533837840083314056551711 11300756760124971084827567)
          ·
            refine ⟨16951135140187456627241351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11300756760124971084827567 16951135140187456627241351)
            ·
              refine ⟨25426702710281184940862027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16951135140187456627241351 25426702710281184940862027)
              ·
                refine ⟨38140054065421777411293041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25426702710281184940862027 38140054065421777411293041)
                ·
                  refine ⟨28605040549066333058469781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38140054065421777411293041 28605040549066333058469781)
                  ·
                    refine ⟨1340861275737484362115771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28605040549066333058469781 1340861275737484362115771)
                    ·
                      rfl

theorem cell22_3916977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_3916977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3916977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3916977 prefixEnd_3916977 := by exact prefixLift 3916977
  have htrace : WordTrace (prefixWord ++ tailWord_3916977) baseStart_3916977 baseEnd_3916977 := by
    simpa [prefixWord, tailWord_3916977, baseEnd_3916977] using wordTrace_append hprefix tailTrace_3916977
  have hstable : (prefixWord ++ tailWord_3916977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916977).length < 2 ^ (prefixWord ++ tailWord_3916977).sum := by decide
  have hdescent : baseEnd_3916977 < baseStart_3916977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3916996 : List Nat := [2, 3, 3, 1, 3, 1, 1, 2, 3, 3]
def baseStart_3916996 : Nat := 118140960795 + 3916996 * 2 ^ 59
def prefixEnd_3916996 : Nat := 4983230072969 + 3 ^ 40 * 3916996 * 2
def baseEnd_3916996 : Nat := 1340867779825774645890713

theorem tailTrace_3916996 : CollatzResearch.WordTrace tailWord_3916996 prefixEnd_3916996 1340867779825774645890713 := by
  unfold tailWord_3916996
  simp only [CollatzResearch.WordTrace]
  refine ⟨71432290458699968251257421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95243053944933291001676561 71432290458699968251257421)
  ·
    refine ⟨26787108922012488094221533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71432290458699968251257421 26787108922012488094221533)
    ·
      refine ⟨10045165845754683035333075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26787108922012488094221533 10045165845754683035333075)
      ·
        refine ⟨15067748768632024552999613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10045165845754683035333075 15067748768632024552999613)
        ·
          refine ⟨5650405788237009207374855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15067748768632024552999613 5650405788237009207374855)
          ·
            refine ⟨8475608682355513811062283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5650405788237009207374855 8475608682355513811062283)
            ·
              refine ⟨12713413023533270716593425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8475608682355513811062283 12713413023533270716593425)
              ·
                refine ⟨9535059767649953037445069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12713413023533270716593425 9535059767649953037445069)
                ·
                  refine ⟨3575647412868732389041901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9535059767649953037445069 3575647412868732389041901)
                  ·
                    refine ⟨1340867779825774645890713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3575647412868732389041901 1340867779825774645890713)
                    ·
                      rfl

theorem cell22_3916996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_3916996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3916996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3916996 prefixEnd_3916996 := by exact prefixLift 3916996
  have htrace : WordTrace (prefixWord ++ tailWord_3916996) baseStart_3916996 baseEnd_3916996 := by
    simpa [prefixWord, tailWord_3916996, baseEnd_3916996] using wordTrace_append hprefix tailTrace_3916996
  have hstable : (prefixWord ++ tailWord_3916996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3916996).length < 2 ^ (prefixWord ++ tailWord_3916996).sum := by decide
  have hdescent : baseEnd_3916996 < baseStart_3916996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3916996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917013 : List Nat := [1, 3, 2, 4, 1, 2, 2, 3, 1, 3]
def baseStart_3917013 : Nat := 118140960795 + 3917013 * 2 ^ 59
def prefixEnd_3917013 : Nat := 4983230072969 + 3 ^ 40 * 3917013 * 2
def baseEnd_3917013 : Nat := 1340873599273192268215661

theorem tailTrace_3917013 : CollatzResearch.WordTrace tailWord_3917013 prefixEnd_3917013 1340873599273192268215661 := by
  unfold tailWord_3917013
  simp only [CollatzResearch.WordTrace]
  refine ⟨142865200958338348405883693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95243467305558898937255795 142865200958338348405883693)
  ·
    refine ⟨53574450359376880652206385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142865200958338348405883693 53574450359376880652206385)
    ·
      refine ⟨40180837769532660489154789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53574450359376880652206385 40180837769532660489154789)
      ·
        refine ⟨7533907081787373841716523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40180837769532660489154789 7533907081787373841716523)
        ·
          refine ⟨11300860622681060762574785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7533907081787373841716523 11300860622681060762574785)
          ·
            refine ⟨8475645467010795571931089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11300860622681060762574785 8475645467010795571931089)
            ·
              refine ⟨6356734100258096678948317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8475645467010795571931089 6356734100258096678948317)
              ·
                refine ⟨2383775287596786254605619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6356734100258096678948317 2383775287596786254605619)
                ·
                  refine ⟨3575662931395179381908429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2383775287596786254605619 3575662931395179381908429)
                  ·
                    refine ⟨1340873599273192268215661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3575662931395179381908429 1340873599273192268215661)
                    ·
                      rfl

theorem cell22_3917013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 3, 1, 3].length) (baseStart_3917013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3917013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3917013 prefixEnd_3917013 := by exact prefixLift 3917013
  have htrace : WordTrace (prefixWord ++ tailWord_3917013) baseStart_3917013 baseEnd_3917013 := by
    simpa [prefixWord, tailWord_3917013, baseEnd_3917013] using wordTrace_append hprefix tailTrace_3917013
  have hstable : (prefixWord ++ tailWord_3917013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917013).length < 2 ^ (prefixWord ++ tailWord_3917013).sum := by decide
  have hdescent : baseEnd_3917013 < baseStart_3917013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917054 : List Nat := [4, 2, 2, 1, 1, 2, 2, 2, 6]
def baseStart_3917054 : Nat := 118140960795 + 3917054 * 2 ^ 59
def prefixEnd_3917054 : Nat := 4983230072969 + 3 ^ 40 * 3917054 * 2
def baseEnd_3917054 : Nat := 446962544803693942646845

theorem tailTrace_3917054 : CollatzResearch.WordTrace tailWord_3917054 prefixEnd_3917054 446962544803693942646845 := by
  unfold tailWord_3917054
  simp only [CollatzResearch.WordTrace]
  refine ⟨17858337043898726551015777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95244464234126541605417477 17858337043898726551015777)
  ·
    refine ⟨13393752782924044913261833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17858337043898726551015777 13393752782924044913261833)
    ·
      refine ⟨10045314587193033684946375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13393752782924044913261833 10045314587193033684946375)
      ·
        refine ⟨15067971880789550527419563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10045314587193033684946375 15067971880789550527419563)
        ·
          refine ⟨22601957821184325791129345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15067971880789550527419563 22601957821184325791129345)
          ·
            refine ⟨16951468365888244343347009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22601957821184325791129345 16951468365888244343347009)
            ·
              refine ⟨12713601274416183257510257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16951468365888244343347009 12713601274416183257510257)
              ·
                refine ⟨9535200955812137443132693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12713601274416183257510257 9535200955812137443132693)
                ·
                  refine ⟨446962544803693942646845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9535200955812137443132693 446962544803693942646845)
                  ·
                    rfl

theorem cell22_3917054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_3917054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3917054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3917054 prefixEnd_3917054 := by exact prefixLift 3917054
  have htrace : WordTrace (prefixWord ++ tailWord_3917054) baseStart_3917054 baseEnd_3917054 := by
    simpa [prefixWord, tailWord_3917054, baseEnd_3917054] using wordTrace_append hprefix tailTrace_3917054
  have hstable : (prefixWord ++ tailWord_3917054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917054).length < 2 ^ (prefixWord ++ tailWord_3917054).sum := by decide
  have hdescent : baseEnd_3917054 < baseStart_3917054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917067 : List Nat := [1, 1, 1, 1, 5, 3, 2, 1, 1, 6]
def baseStart_3917067 : Nat := 118140960795 + 3917067 * 2 ^ 59
def prefixEnd_3917067 : Nat := 4983230072969 + 3 ^ 40 * 3917067 * 2
def baseEnd_3917067 : Nat := 1340892084576754127365495

theorem tailTrace_3917067 : CollatzResearch.WordTrace tailWord_3917067 prefixEnd_3917067 1340892084576754127365495 := by
  unfold tailWord_3917067
  simp only [CollatzResearch.WordTrace]
  refine ⟨142867170500142715628349455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95244780333428477085566303 142867170500142715628349455)
  ·
    refine ⟨214300755750214073442524183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142867170500142715628349455 214300755750214073442524183)
    ·
      refine ⟨321451133625321110163786275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214300755750214073442524183 321451133625321110163786275)
      ·
        refine ⟨482176700437981665245679413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321451133625321110163786275 482176700437981665245679413)
        ·
          refine ⟨45204065666060781116782445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 482176700437981665245679413 45204065666060781116782445)
          ·
            refine ⟨16951524624772792918793417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45204065666060781116782445 16951524624772792918793417)
            ·
              refine ⟨12713643468579594689095063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16951524624772792918793417 12713643468579594689095063)
              ·
                refine ⟨19070465202869392033642595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12713643468579594689095063 19070465202869392033642595)
                ·
                  refine ⟨28605697804304088050463893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19070465202869392033642595 28605697804304088050463893)
                  ·
                    refine ⟨1340892084576754127365495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28605697804304088050463893 1340892084576754127365495)
                    ·
                      rfl

theorem cell22_3917067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 6].length) (baseStart_3917067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3917067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3917067 prefixEnd_3917067 := by exact prefixLift 3917067
  have htrace : WordTrace (prefixWord ++ tailWord_3917067) baseStart_3917067 baseEnd_3917067 := by
    simpa [prefixWord, tailWord_3917067, baseEnd_3917067] using wordTrace_append hprefix tailTrace_3917067
  have hstable : (prefixWord ++ tailWord_3917067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917067).length < 2 ^ (prefixWord ++ tailWord_3917067).sum := by decide
  have hdescent : baseEnd_3917067 < baseStart_3917067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917082 : List Nat := [3, 1, 1, 3, 3, 1, 10]
def baseStart_3917082 : Nat := 118140960795 + 3917082 * 2 ^ 59
def prefixEnd_3917082 : Nat := 4983230072969 + 3 ^ 40 * 3917082 * 2
def baseEnd_3917082 : Nat := 49662859977159225490387

theorem tailTrace_3917082 : CollatzResearch.WordTrace tailWord_3917082 prefixEnd_3917082 49662859977159225490387 := by
  unfold tailWord_3917082
  simp only [CollatzResearch.WordTrace]
  refine ⟨35716929398772093297536375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95245145063392248793430333 35716929398772093297536375)
  ·
    refine ⟨53575394098158139946304563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35716929398772093297536375 53575394098158139946304563)
    ·
      refine ⟨80363091147237209919456845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53575394098158139946304563 80363091147237209919456845)
      ·
        refine ⟨30136159180213953719796317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80363091147237209919456845 30136159180213953719796317)
        ·
          refine ⟨11301059692580232644923619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30136159180213953719796317 11301059692580232644923619)
          ·
            refine ⟨16951589538870348967385429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11301059692580232644923619 16951589538870348967385429)
            ·
              refine ⟨49662859977159225490387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16951589538870348967385429 49662859977159225490387)
              ·
                rfl

theorem cell22_3917082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 10].length) (baseStart_3917082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3917082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3917082 prefixEnd_3917082 := by exact prefixLift 3917082
  have htrace : WordTrace (prefixWord ++ tailWord_3917082) baseStart_3917082 baseEnd_3917082 := by
    simpa [prefixWord, tailWord_3917082, baseEnd_3917082] using wordTrace_append hprefix tailTrace_3917082
  have hstable : (prefixWord ++ tailWord_3917082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917082).length < 2 ^ (prefixWord ++ tailWord_3917082).sum := by decide
  have hdescent : baseEnd_3917082 < baseStart_3917082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917088 : List Nat := [2, 1, 1, 5, 3, 1, 3, 2, 4]
def baseStart_3917088 : Nat := 118140960795 + 3917088 * 2 ^ 59
def prefixEnd_3917088 : Nat := 4983230072969 + 3 ^ 40 * 3917088 * 2
def baseEnd_3917088 : Nat := 446966424435305690863477

theorem tailTrace_3917088 : CollatzResearch.WordTrace tailWord_3917088 prefixEnd_3917088 446966424435305690863477 := by
  unfold tailWord_3917088
  simp only [CollatzResearch.WordTrace]
  refine ⟨71433968216533318107431959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95245290955377757476575945 71433968216533318107431959)
  ·
    refine ⟨107150952324799977161147939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71433968216533318107431959 107150952324799977161147939)
    ·
      refine ⟨160726428487199965741721909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107150952324799977161147939 160726428487199965741721909)
      ·
        refine ⟨15068102670674996788286429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160726428487199965741721909 15068102670674996788286429)
        ·
          refine ⟨5650538501503123795607411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15068102670674996788286429 5650538501503123795607411)
          ·
            refine ⟨8475807752254685693411117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5650538501503123795607411 8475807752254685693411117)
            ·
              refine ⟨3178427907095507135029169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8475807752254685693411117 3178427907095507135029169)
              ·
                refine ⟨2383820930321630351271877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3178427907095507135029169 2383820930321630351271877)
                ·
                  refine ⟨446966424435305690863477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2383820930321630351271877 446966424435305690863477)
                  ·
                    rfl

theorem cell22_3917088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 2, 4].length) (baseStart_3917088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3917088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3917088 prefixEnd_3917088 := by exact prefixLift 3917088
  have htrace : WordTrace (prefixWord ++ tailWord_3917088) baseStart_3917088 baseEnd_3917088 := by
    simpa [prefixWord, tailWord_3917088, baseEnd_3917088] using wordTrace_append hprefix tailTrace_3917088
  have hstable : (prefixWord ++ tailWord_3917088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917088).length < 2 ^ (prefixWord ++ tailWord_3917088).sum := by decide
  have hdescent : baseEnd_3917088 < baseStart_3917088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917114 : List Nat := [3, 1, 1, 1, 4, 1, 2, 1, 5, 3]
def baseStart_3917114 : Nat := 118140960795 + 3917114 * 2 ^ 59
def prefixEnd_3917114 : Nat := 4983230072969 + 3 ^ 40 * 3917114 * 2
def baseEnd_3917114 : Nat := 1340908173637261671440351

theorem tailTrace_3917114 : CollatzResearch.WordTrace tailWord_3917114 prefixEnd_3917114 1340908173637261671440351 := by
  unfold tailWord_3917114
  simp only [CollatzResearch.WordTrace]
  refine ⟨35717221182743110663827599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95245923153981628436873597 35717221182743110663827599)
  ·
    refine ⟨53575831774114665995741399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35717221182743110663827599 53575831774114665995741399)
    ·
      refine ⟨80363747661171998993612099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53575831774114665995741399 80363747661171998993612099)
      ·
        refine ⟨120545621491757998490418149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80363747661171998993612099 120545621491757998490418149)
        ·
          refine ⟨22602304029704624716953403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120545621491757998490418149 22602304029704624716953403)
          ·
            refine ⟨33903456044556937075430105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22602304029704624716953403 33903456044556937075430105)
            ·
              refine ⟨25427592033417702806572579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33903456044556937075430105 25427592033417702806572579)
              ·
                refine ⟨38141388050126554209858869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25427592033417702806572579 38141388050126554209858869)
                ·
                  refine ⟨3575755129699364457174269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38141388050126554209858869 3575755129699364457174269)
                  ·
                    refine ⟨1340908173637261671440351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3575755129699364457174269 1340908173637261671440351)
                    ·
                      rfl

theorem cell22_3917114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 5, 3].length) (baseStart_3917114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3917114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3917114 prefixEnd_3917114 := by exact prefixLift 3917114
  have htrace : WordTrace (prefixWord ++ tailWord_3917114) baseStart_3917114 baseEnd_3917114 := by
    simpa [prefixWord, tailWord_3917114, baseEnd_3917114] using wordTrace_append hprefix tailTrace_3917114
  have hstable : (prefixWord ++ tailWord_3917114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917114).length < 2 ^ (prefixWord ++ tailWord_3917114).sum := by decide
  have hdescent : baseEnd_3917114 < baseStart_3917114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917144 : List Nat := [2, 1, 2, 2, 1, 1, 6, 2, 5]
def baseStart_3917144 : Nat := 118140960795 + 3917144 * 2 ^ 59
def prefixEnd_3917144 : Nat := 4983230072969 + 3 ^ 40 * 3917144 * 2
def baseEnd_3917144 : Nat := 446972814416783864396753

theorem tailTrace_3917144 : CollatzResearch.WordTrace tailWord_3917144 prefixEnd_3917144 446972814416783864396753 := by
  unfold tailWord_3917144
  simp only [CollatzResearch.WordTrace]
  refine ⟨71434989460431878889451243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95246652613909171852601657 71434989460431878889451243)
  ·
    refine ⟨107152484190647818334176865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71434989460431878889451243 107152484190647818334176865)
    ·
      refine ⟨80364363142985863750632649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107152484190647818334176865 80364363142985863750632649)
      ·
        refine ⟨60273272357239397812974487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80364363142985863750632649 60273272357239397812974487)
        ·
          refine ⟨90409908535859096719461731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60273272357239397812974487 90409908535859096719461731)
          ·
            refine ⟨135614862803788645079192597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90409908535859096719461731 135614862803788645079192597)
            ·
              refine ⟨6356946693927592738087153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 135614862803788645079192597 6356946693927592738087153)
              ·
                refine ⟨4767710020445694553565365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6356946693927592738087153 4767710020445694553565365)
                ·
                  refine ⟨446972814416783864396753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4767710020445694553565365 446972814416783864396753)
                  ·
                    rfl

theorem cell22_3917144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 5].length) (baseStart_3917144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3917144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3917144 prefixEnd_3917144 := by exact prefixLift 3917144
  have htrace : WordTrace (prefixWord ++ tailWord_3917144) baseStart_3917144 baseEnd_3917144 := by
    simpa [prefixWord, tailWord_3917144, baseEnd_3917144] using wordTrace_append hprefix tailTrace_3917144
  have hstable : (prefixWord ++ tailWord_3917144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917144).length < 2 ^ (prefixWord ++ tailWord_3917144).sum := by decide
  have hdescent : baseEnd_3917144 < baseStart_3917144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917191 : List Nat := [1, 1, 4, 2, 2, 3, 1, 3, 1, 4]
def baseStart_3917191 : Nat := 118140960795 + 3917191 * 2 ^ 59
def prefixEnd_3917191 : Nat := 4983230072969 + 3 ^ 40 * 3917191 * 2
def baseEnd_3917191 : Nat := 1340934532310859137265115

theorem tailTrace_3917191 : CollatzResearch.WordTrace tailWord_3917191 prefixEnd_3917191 1340934532310859137265115 := by
  unfold tailWord_3917191
  simp only [CollatzResearch.WordTrace]
  refine ⟨142871693151693484805863427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95247795434462323203908951 142871693151693484805863427)
  ·
    refine ⟨214307539727540227208795141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142871693151693484805863427 214307539727540227208795141)
    ·
      refine ⟨40182663698913792601649089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214307539727540227208795141 40182663698913792601649089)
      ·
        refine ⟨30136997774185344451236817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40182663698913792601649089 30136997774185344451236817)
        ·
          refine ⟨22602748330639008338427613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30136997774185344451236817 22602748330639008338427613)
          ·
            refine ⟨8476030623989628126910355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22602748330639008338427613 8476030623989628126910355)
            ·
              refine ⟨12714045935984442190365533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8476030623989628126910355 12714045935984442190365533)
              ·
                refine ⟨4767767225994165821387075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12714045935984442190365533 4767767225994165821387075)
                ·
                  refine ⟨7151650838991248732080613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4767767225994165821387075 7151650838991248732080613)
                  ·
                    refine ⟨1340934532310859137265115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7151650838991248732080613 1340934532310859137265115)
                    ·
                      rfl

theorem cell22_3917191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_3917191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3917191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3917191 prefixEnd_3917191 := by exact prefixLift 3917191
  have htrace : WordTrace (prefixWord ++ tailWord_3917191) baseStart_3917191 baseEnd_3917191 := by
    simpa [prefixWord, tailWord_3917191, baseEnd_3917191] using wordTrace_append hprefix tailTrace_3917191
  have hstable : (prefixWord ++ tailWord_3917191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917191).length < 2 ^ (prefixWord ++ tailWord_3917191).sum := by decide
  have hdescent : baseEnd_3917191 < baseStart_3917191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917313 : List Nat := [1, 2, 4, 1, 4, 1, 2, 2, 5]
def baseStart_3917313 : Nat := 118140960795 + 3917313 * 2 ^ 59
def prefixEnd_3917313 : Nat := 4983230072969 + 3 ^ 40 * 3917313 * 2
def baseEnd_3917313 : Nat := 446992098468030495238247

theorem tailTrace_3917313 : CollatzResearch.WordTrace tailWord_3917313 prefixEnd_3917313 446992098468030495238247 := by
  unfold tailWord_3917313
  simp only [CollatzResearch.WordTrace]
  refine ⟨142876142857251499641804593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95250761904834333094536395 142876142857251499641804593)
  ·
    refine ⟨107157107142938624731353445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142876142857251499641804593 107157107142938624731353445)
    ·
      refine ⟨20091957589300992137128771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107157107142938624731353445 20091957589300992137128771)
      ·
        refine ⟨30137936383951488205693157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20091957589300992137128771 30137936383951488205693157)
        ·
          refine ⟨5650863071990904038567467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30137936383951488205693157 5650863071990904038567467)
          ·
            refine ⟨8476294607986356057851201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5650863071990904038567467 8476294607986356057851201)
            ·
              refine ⟨6357220955989767043388401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8476294607986356057851201 6357220955989767043388401)
              ·
                refine ⟨4767915716992325282541301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6357220955989767043388401 4767915716992325282541301)
                ·
                  refine ⟨446992098468030495238247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4767915716992325282541301 446992098468030495238247)
                  ·
                    rfl

theorem cell22_3917313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 5].length) (baseStart_3917313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3917313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3917313 prefixEnd_3917313 := by exact prefixLift 3917313
  have htrace : WordTrace (prefixWord ++ tailWord_3917313) baseStart_3917313 baseEnd_3917313 := by
    simpa [prefixWord, tailWord_3917313, baseEnd_3917313] using wordTrace_append hprefix tailTrace_3917313
  have hstable : (prefixWord ++ tailWord_3917313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917313).length < 2 ^ (prefixWord ++ tailWord_3917313).sum := by decide
  have hdescent : baseEnd_3917313 < baseStart_3917313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917341 : List Nat := [1, 4, 2, 2, 1, 1, 3, 2, 6]
def baseStart_3917341 : Nat := 118140960795 + 3917341 * 2 ^ 59
def prefixEnd_3917341 : Nat := 4983230072969 + 3 ^ 40 * 3917341 * 2
def baseEnd_3917341 : Nat := 446995293458769582004885

theorem tailTrace_3917341 : CollatzResearch.WordTrace tailWord_3917341 prefixEnd_3917341 446995293458769582004885 := by
  unfold tailWord_3917341
  simp only [CollatzResearch.WordTrace]
  refine ⟨142877164101150060423823877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95251442734100040282549251 142877164101150060423823877)
  ·
    refine ⟨26789468268965636329466977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142877164101150060423823877 26789468268965636329466977)
    ·
      refine ⟨20092101201724227247100233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26789468268965636329466977 20092101201724227247100233)
      ·
        refine ⟨15069075901293170435325175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20092101201724227247100233 15069075901293170435325175)
        ·
          refine ⟨22603613851939755652987763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15069075901293170435325175 22603613851939755652987763)
          ·
            refine ⟨33905420777909633479481645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22603613851939755652987763 33905420777909633479481645)
            ·
              refine ⟨12714532791716112554805617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33905420777909633479481645 12714532791716112554805617)
              ·
                refine ⟨9535899593787084416104213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12714532791716112554805617 9535899593787084416104213)
                ·
                  refine ⟨446995293458769582004885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9535899593787084416104213 446995293458769582004885)
                  ·
                    rfl

theorem cell22_3917341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_3917341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3917341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3917341 prefixEnd_3917341 := by exact prefixLift 3917341
  have htrace : WordTrace (prefixWord ++ tailWord_3917341) baseStart_3917341 baseEnd_3917341 := by
    simpa [prefixWord, tailWord_3917341, baseEnd_3917341] using wordTrace_append hprefix tailTrace_3917341
  have hstable : (prefixWord ++ tailWord_3917341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917341).length < 2 ^ (prefixWord ++ tailWord_3917341).sum := by decide
  have hdescent : baseEnd_3917341 < baseStart_3917341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917431 : List Nat := [1, 1, 3, 1, 1, 3, 1, 6, 5]
def baseStart_3917431 : Nat := 118140960795 + 3917431 * 2 ^ 59
def prefixEnd_3917431 : Nat := 4983230072969 + 3 ^ 40 * 3917431 * 2
def baseEnd_3917431 : Nat := 447005563071859503754793

theorem tailTrace_3917431 : CollatzResearch.WordTrace tailWord_3917431 prefixEnd_3917431 447005563071859503754793 := by
  unfold tailWord_3917431
  simp only [CollatzResearch.WordTrace]
  refine ⟨142880446670824005794600147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95253631113882670529733431 142880446670824005794600147)
  ·
    refine ⟨214320670006236008691900221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142880446670824005794600147 214320670006236008691900221)
    ·
      refine ⟨80370251252338503259462583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214320670006236008691900221 80370251252338503259462583)
      ·
        refine ⟨120555376878507754889193875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80370251252338503259462583 120555376878507754889193875)
        ·
          refine ⟨180833065317761632333790813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120555376878507754889193875 180833065317761632333790813)
          ·
            refine ⟨67812399494160612125171555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180833065317761632333790813 67812399494160612125171555)
            ·
              refine ⟨101718599241240918187757333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67812399494160612125171555 101718599241240918187757333)
              ·
                refine ⟨4768059339433168040051125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101718599241240918187757333 4768059339433168040051125)
                ·
                  refine ⟨447005563071859503754793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4768059339433168040051125 447005563071859503754793)
                  ·
                    rfl

theorem cell22_3917431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 5].length) (baseStart_3917431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3917431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3917431 prefixEnd_3917431 := by exact prefixLift 3917431
  have htrace : WordTrace (prefixWord ++ tailWord_3917431) baseStart_3917431 baseEnd_3917431 := by
    simpa [prefixWord, tailWord_3917431, baseEnd_3917431] using wordTrace_append hprefix tailTrace_3917431
  have hstable : (prefixWord ++ tailWord_3917431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917431).length < 2 ^ (prefixWord ++ tailWord_3917431).sum := by decide
  have hdescent : baseEnd_3917431 < baseStart_3917431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917491 : List Nat := [1, 1, 1, 2, 3, 3, 1, 2, 3, 5]
def baseStart_3917491 : Nat := 118140960795 + 3917491 * 2 ^ 59
def prefixEnd_3917491 : Nat := 4983230072969 + 3 ^ 40 * 3917491 * 2
def baseEnd_3917491 : Nat := 1341037228441758354764195

theorem tailTrace_3917491 : CollatzResearch.WordTrace tailWord_3917491 prefixEnd_3917491 1341037228441758354764195 := by
  unfold tailWord_3917491
  simp only [CollatzResearch.WordTrace]
  refine ⟨142882635050606636041784327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95255090033737757361189551 142882635050606636041784327)
  ·
    refine ⟨214323952575909954062676491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142882635050606636041784327 214323952575909954062676491)
    ·
      refine ⟨321485928863864931094014737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214323952575909954062676491 321485928863864931094014737)
      ·
        refine ⟨241114446647898698320511053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321485928863864931094014737 241114446647898698320511053)
        ·
          refine ⟨90417917492962011870191645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241114446647898698320511053 90417917492962011870191645)
          ·
            refine ⟨33906719059860754451321867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90417917492962011870191645 33906719059860754451321867)
            ·
              refine ⟨50860078589791131676982801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33906719059860754451321867 50860078589791131676982801)
              ·
                refine ⟨38145058942343348757737101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50860078589791131676982801 38145058942343348757737101)
                ·
                  refine ⟨14304397103378755784151413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38145058942343348757737101 14304397103378755784151413)
                  ·
                    refine ⟨1341037228441758354764195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14304397103378755784151413 1341037228441758354764195)
                    ·
                      rfl

theorem cell22_3917491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 5].length) (baseStart_3917491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3917491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3917491 prefixEnd_3917491 := by exact prefixLift 3917491
  have htrace : WordTrace (prefixWord ++ tailWord_3917491) baseStart_3917491 baseEnd_3917491 := by
    simpa [prefixWord, tailWord_3917491, baseEnd_3917491] using wordTrace_append hprefix tailTrace_3917491
  have hstable : (prefixWord ++ tailWord_3917491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917491).length < 2 ^ (prefixWord ++ tailWord_3917491).sum := by decide
  have hdescent : baseEnd_3917491 < baseStart_3917491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917617 : List Nat := [1, 2, 2, 3, 2, 4, 2, 1, 5]
def baseStart_3917617 : Nat := 118140960795 + 3917617 * 2 ^ 59
def prefixEnd_3917617 : Nat := 4983230072969 + 3 ^ 40 * 3917617 * 2
def baseEnd_3917617 : Nat := 447026786938912008704603

theorem tailTrace_3917617 : CollatzResearch.WordTrace tailWord_3917617 prefixEnd_3917617 447026786938912008704603 := by
  unfold tailWord_3917617
  simp only [CollatzResearch.WordTrace]
  refine ⟨142887230648150159560871105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95258153765433439707247403 142887230648150159560871105)
  ·
    refine ⟨107165422986112619670653329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142887230648150159560871105 107165422986112619670653329)
    ·
      refine ⟨80374067239584464752989997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107165422986112619670653329 80374067239584464752989997)
      ·
        refine ⟨30140275214844174282371249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80374067239584464752989997 30140275214844174282371249)
        ·
          refine ⟨22605206411133130711778437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30140275214844174282371249 22605206411133130711778437)
          ·
            refine ⟨4238476202087462008458457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22605206411133130711778437 4238476202087462008458457)
            ·
              refine ⟨3178857151565596506343843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4238476202087462008458457 3178857151565596506343843)
              ·
                refine ⟨4768285727348394759515765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3178857151565596506343843 4768285727348394759515765)
                ·
                  refine ⟨447026786938912008704603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4768285727348394759515765 447026786938912008704603)
                  ·
                    rfl

theorem cell22_3917617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 5].length) (baseStart_3917617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3917617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3917617 prefixEnd_3917617 := by exact prefixLift 3917617
  have htrace : WordTrace (prefixWord ++ tailWord_3917617) baseStart_3917617 baseEnd_3917617 := by
    simpa [prefixWord, tailWord_3917617, baseEnd_3917617] using wordTrace_append hprefix tailTrace_3917617
  have hstable : (prefixWord ++ tailWord_3917617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917617).length < 2 ^ (prefixWord ++ tailWord_3917617).sum := by decide
  have hdescent : baseEnd_3917617 < baseStart_3917617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917628 : List Nat := [2, 2, 2, 2, 1, 1, 2, 4, 6]
def baseStart_3917628 : Nat := 118140960795 + 3917628 * 2 ^ 59
def prefixEnd_3917628 : Nat := 4983230072969 + 3 ^ 40 * 3917628 * 2
def baseEnd_3917628 : Nat := 447028042113845221362925

theorem tailTrace_3917628 : CollatzResearch.WordTrace tailWord_3917628 prefixEnd_3917628 447028042113845221362925 := by
  unfold tailWord_3917628
  simp only [CollatzResearch.WordTrace]
  refine ⟨71443815925555154219760769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95258421234073538959681025 71443815925555154219760769)
  ·
    refine ⟨53582861944166365664820577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71443815925555154219760769 53582861944166365664820577)
    ·
      refine ⟨40187146458124774248615433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53582861944166365664820577 40187146458124774248615433)
      ·
        refine ⟨30140359843593580686461575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40187146458124774248615433 30140359843593580686461575)
        ·
          refine ⟨45210539765390371029692363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30140359843593580686461575 45210539765390371029692363)
          ·
            refine ⟨67815809648085556544538545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45210539765390371029692363 67815809648085556544538545)
            ·
              refine ⟨50861857236064167408403909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67815809648085556544538545 50861857236064167408403909)
              ·
                refine ⟨9536598231762031389075733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50861857236064167408403909 9536598231762031389075733)
                ·
                  refine ⟨447028042113845221362925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9536598231762031389075733 447028042113845221362925)
                  ·
                    rfl

theorem cell22_3917628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 6].length) (baseStart_3917628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3917628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3917628 prefixEnd_3917628 := by exact prefixLift 3917628
  have htrace : WordTrace (prefixWord ++ tailWord_3917628) baseStart_3917628 baseEnd_3917628 := by
    simpa [prefixWord, tailWord_3917628, baseEnd_3917628] using wordTrace_append hprefix tailTrace_3917628
  have hstable : (prefixWord ++ tailWord_3917628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917628).length < 2 ^ (prefixWord ++ tailWord_3917628).sum := by decide
  have hdescent : baseEnd_3917628 < baseStart_3917628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917677 : List Nat := [1, 5, 1, 1, 1, 1, 4, 3, 2, 3]
def baseStart_3917677 : Nat := 118140960795 + 3917677 * 2 ^ 59
def prefixEnd_3917677 : Nat := 4983230072969 + 3 ^ 40 * 3917677 * 2
def baseEnd_3917677 : Nat := 1341100900042915869613625

theorem tailTrace_3917677 : CollatzResearch.WordTrace tailWord_3917677 prefixEnd_3917677 1341100900042915869613625 := by
  unfold tailWord_3917677
  simp only [CollatzResearch.WordTrace]
  refine ⟨142889419027932789808055285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95259612685288526538703523 142889419027932789808055285)
  ·
    refine ⟨13395883033868699044505183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142889419027932789808055285 13395883033868699044505183)
    ·
      refine ⟨20093824550803048566757775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13395883033868699044505183 20093824550803048566757775)
      ·
        refine ⟨30140736826204572850136663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20093824550803048566757775 30140736826204572850136663)
        ·
          refine ⟨45211105239306859275204995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30140736826204572850136663 45211105239306859275204995)
          ·
            refine ⟨67816657858960288912807493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45211105239306859275204995 67816657858960288912807493)
            ·
              refine ⟨12715623348555054171151405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67816657858960288912807493 12715623348555054171151405)
              ·
                refine ⟨4768358755708145314181777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12715623348555054171151405 4768358755708145314181777)
                ·
                  refine ⟨3576269066781108985636333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4768358755708145314181777 3576269066781108985636333)
                  ·
                    refine ⟨1341100900042915869613625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3576269066781108985636333 1341100900042915869613625)
                    ·
                      rfl

theorem cell22_3917677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_3917677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3917677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3917677 prefixEnd_3917677 := by exact prefixLift 3917677
  have htrace : WordTrace (prefixWord ++ tailWord_3917677) baseStart_3917677 baseEnd_3917677 := by
    simpa [prefixWord, tailWord_3917677, baseEnd_3917677] using wordTrace_append hprefix tailTrace_3917677
  have hstable : (prefixWord ++ tailWord_3917677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917677).length < 2 ^ (prefixWord ++ tailWord_3917677).sum := by decide
  have hdescent : baseEnd_3917677 < baseStart_3917677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917705 : List Nat := [1, 2, 1, 1, 5, 1, 1, 2, 5, 3]
def baseStart_3917705 : Nat := 118140960795 + 3917705 * 2 ^ 59
def prefixEnd_3917705 : Nat := 4983230072969 + 3 ^ 40 * 3917705 * 2
def baseEnd_3917705 : Nat := 1341110485015133129913539

theorem tailTrace_3917705 : CollatzResearch.WordTrace tailWord_3917705 prefixEnd_3917705 1341110485015133129913539 := by
  unfold tailWord_3917705
  simp only [CollatzResearch.WordTrace]
  refine ⟨142890440271831350590074569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95260293514554233726716379 142890440271831350590074569)
  ·
    refine ⟨107167830203873512942555927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142890440271831350590074569 107167830203873512942555927)
    ·
      refine ⟨160751745305810269413833891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107167830203873512942555927 160751745305810269413833891)
      ·
        refine ⟨241127617958715404120750837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160751745305810269413833891 241127617958715404120750837)
        ·
          refine ⟨22605714183629569136320391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 241127617958715404120750837 22605714183629569136320391)
          ·
            refine ⟨33908571275444353704480587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22605714183629569136320391 33908571275444353704480587)
            ·
              refine ⟨50862856913166530556720881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33908571275444353704480587 50862856913166530556720881)
              ·
                refine ⟨38147142684874897917540661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50862856913166530556720881 38147142684874897917540661)
                ·
                  refine ⟨3576294626707021679769437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38147142684874897917540661 3576294626707021679769437)
                  ·
                    refine ⟨1341110485015133129913539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3576294626707021679769437 1341110485015133129913539)
                    ·
                      rfl

theorem cell22_3917705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 5, 3].length) (baseStart_3917705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3917705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3917705 prefixEnd_3917705 := by exact prefixLift 3917705
  have htrace : WordTrace (prefixWord ++ tailWord_3917705) baseStart_3917705 baseEnd_3917705 := by
    simpa [prefixWord, tailWord_3917705, baseEnd_3917705] using wordTrace_append hprefix tailTrace_3917705
  have hstable : (prefixWord ++ tailWord_3917705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917705).length < 2 ^ (prefixWord ++ tailWord_3917705).sum := by decide
  have hdescent : baseEnd_3917705 < baseStart_3917705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917722 : List Nat := [3, 1, 1, 4, 2, 1, 1, 3, 3, 3]
def baseStart_3917722 : Nat := 118140960795 + 3917722 * 2 ^ 59
def prefixEnd_3917722 : Nat := 4983230072969 + 3 ^ 40 * 3917722 * 2
def baseEnd_3917722 : Nat := 1341116304462550752238487

theorem tailTrace_3917722 : CollatzResearch.WordTrace tailWord_3917722 prefixEnd_3917722 1341116304462550752238487 := by
  unfold tailWord_3917722
  simp only [CollatzResearch.WordTrace]
  refine ⟨35722765078192440623360855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95260706875179841662295613 35722765078192440623360855)
  ·
    refine ⟨53584147617288660935041283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35722765078192440623360855 53584147617288660935041283)
    ·
      refine ⟨80376221425932991402561925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53584147617288660935041283 80376221425932991402561925)
      ·
        refine ⟨15070541517362435887980361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80376221425932991402561925 15070541517362435887980361)
        ·
          refine ⟨11302906138021826915985271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15070541517362435887980361 11302906138021826915985271)
          ·
            refine ⟨16954359207032740373977907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11302906138021826915985271 16954359207032740373977907)
            ·
              refine ⟨25431538810549110560966861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16954359207032740373977907 25431538810549110560966861)
              ·
                refine ⟨9536827053955916460362573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25431538810549110560966861 9536827053955916460362573)
                ·
                  refine ⟨3576310145233468672635965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9536827053955916460362573 3576310145233468672635965)
                  ·
                    refine ⟨1341116304462550752238487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3576310145233468672635965 1341116304462550752238487)
                    ·
                      rfl

theorem cell22_3917722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 3, 3].length) (baseStart_3917722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3917722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3917722 prefixEnd_3917722 := by exact prefixLift 3917722
  have htrace : WordTrace (prefixWord ++ tailWord_3917722) baseStart_3917722 baseEnd_3917722 := by
    simpa [prefixWord, tailWord_3917722, baseEnd_3917722] using wordTrace_append hprefix tailTrace_3917722
  have hstable : (prefixWord ++ tailWord_3917722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917722).length < 2 ^ (prefixWord ++ tailWord_3917722).sum := by decide
  have hdescent : baseEnd_3917722 < baseStart_3917722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917786 : List Nat := [3, 1, 1, 2, 6, 1, 2, 1, 5]
def baseStart_3917786 : Nat := 118140960795 + 3917786 * 2 ^ 59
def prefixEnd_3917786 : Nat := 4983230072969 + 3 ^ 40 * 3917786 * 2
def baseEnd_3917786 : Nat := 447046070990158639546097

theorem tailTrace_3917786 : CollatzResearch.WordTrace tailWord_3917786 prefixEnd_3917786 447046070990158639546097 := by
  unfold tailWord_3917786
  simp only [CollatzResearch.WordTrace]
  refine ⟨35723348646134475355943303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95262263056358600949182141 35723348646134475355943303)
  ·
    refine ⟨53585022969201713033914955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35723348646134475355943303 53585022969201713033914955)
    ·
      refine ⟨80377534453802569550872433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53585022969201713033914955 80377534453802569550872433)
      ·
        refine ⟨60283150840351927163154325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80377534453802569550872433 60283150840351927163154325)
        ·
          refine ⟨2825772695641496585772859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 60283150840351927163154325 2825772695641496585772859)
          ·
            refine ⟨4238659043462244878659289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2825772695641496585772859 4238659043462244878659289)
            ·
              refine ⟨3178994282596683658994467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4238659043462244878659289 3178994282596683658994467)
              ·
                refine ⟨4768491423895025488491701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3178994282596683658994467 4768491423895025488491701)
                ·
                  refine ⟨447046070990158639546097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4768491423895025488491701 447046070990158639546097)
                  ·
                    rfl

theorem cell22_3917786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 5].length) (baseStart_3917786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3917786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3917786 prefixEnd_3917786 := by exact prefixLift 3917786
  have htrace : WordTrace (prefixWord ++ tailWord_3917786) baseStart_3917786 baseEnd_3917786 := by
    simpa [prefixWord, tailWord_3917786, baseEnd_3917786] using wordTrace_append hprefix tailTrace_3917786
  have hstable : (prefixWord ++ tailWord_3917786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917786).length < 2 ^ (prefixWord ++ tailWord_3917786).sum := by decide
  have hdescent : baseEnd_3917786 < baseStart_3917786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917829 : List Nat := [1, 3, 1, 1, 2, 5, 2, 2, 2, 3]
def baseStart_3917829 : Nat := 118140960795 + 3917829 * 2 ^ 59
def prefixEnd_3917829 : Nat := 4983230072969 + 3 ^ 40 * 3917829 * 2
def baseEnd_3917829 : Nat := 1341152932749238139813159

theorem tailTrace_3917829 : CollatzResearch.WordTrace tailWord_3917829 prefixEnd_3917829 1341152932749238139813159 := by
  unfold tailWord_3917829
  simp only [CollatzResearch.WordTrace]
  refine ⟨142894962923382119767588541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95263308615588079845059027 142894962923382119767588541)
  ·
    refine ⟨53585611096268294912845703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142894962923382119767588541 53585611096268294912845703)
    ·
      refine ⟨80378416644402442369268555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53585611096268294912845703 80378416644402442369268555)
      ·
        refine ⟨120567624966603663553902833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80378416644402442369268555 120567624966603663553902833)
        ·
          refine ⟨90425718724952747665427125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120567624966603663553902833 90425718724952747665427125)
          ·
            refine ⟨8477411130464320093633793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90425718724952747665427125 8477411130464320093633793)
            ·
              refine ⟨6358058347848240070225345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8477411130464320093633793 6358058347848240070225345)
              ·
                refine ⟨4768543760886180052669009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6358058347848240070225345 4768543760886180052669009)
                ·
                  refine ⟨3576407820664635039501757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4768543760886180052669009 3576407820664635039501757)
                  ·
                    refine ⟨1341152932749238139813159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3576407820664635039501757 1341152932749238139813159)
                    ·
                      rfl

theorem cell22_3917829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 2, 3].length) (baseStart_3917829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3917829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3917829 prefixEnd_3917829 := by exact prefixLift 3917829
  have htrace : WordTrace (prefixWord ++ tailWord_3917829) baseStart_3917829 baseEnd_3917829 := by
    simpa [prefixWord, tailWord_3917829, baseEnd_3917829] using wordTrace_append hprefix tailTrace_3917829
  have hstable : (prefixWord ++ tailWord_3917829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917829).length < 2 ^ (prefixWord ++ tailWord_3917829).sum := by decide
  have hdescent : baseEnd_3917829 < baseStart_3917829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917831 : List Nat := [1, 1, 4, 3, 1, 4, 2, 2, 4]
def baseStart_3917831 : Nat := 118140960795 + 3917831 * 2 ^ 59
def prefixEnd_3917831 : Nat := 4983230072969 + 3 ^ 40 * 3917831 * 2
def baseEnd_3917831 : Nat := 447051205796703600421051

theorem tailTrace_3917831 : CollatzResearch.WordTrace tailWord_3917831 prefixEnd_3917831 447051205796703600421051 := by
  unfold tailWord_3917831
  simp only [CollatzResearch.WordTrace]
  refine ⟨142895035869374874109161347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95263357246249916072774231 142895035869374874109161347)
  ·
    refine ⟨214342553804062311163742021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142895035869374874109161347 214342553804062311163742021)
    ·
      refine ⟨40189228838261683343201629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214342553804062311163742021 40189228838261683343201629)
      ·
        refine ⟨15070960814348131253700611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40189228838261683343201629 15070960814348131253700611)
        ·
          refine ⟨22606441221522196880550917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15070960814348131253700611 22606441221522196880550917)
          ·
            refine ⟨4238707729035411915103297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22606441221522196880550917 4238707729035411915103297)
            ·
              refine ⟨3179030796776558936327473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4238707729035411915103297 3179030796776558936327473)
              ·
                refine ⟨2384273097582419202245605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3179030796776558936327473 2384273097582419202245605)
                ·
                  refine ⟨447051205796703600421051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2384273097582419202245605 447051205796703600421051)
                  ·
                    rfl

theorem cell22_3917831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 2, 4].length) (baseStart_3917831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3917831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3917831 prefixEnd_3917831 := by exact prefixLift 3917831
  have htrace : WordTrace (prefixWord ++ tailWord_3917831) baseStart_3917831 baseEnd_3917831 := by
    simpa [prefixWord, tailWord_3917831, baseEnd_3917831] using wordTrace_append hprefix tailTrace_3917831
  have hstable : (prefixWord ++ tailWord_3917831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917831).length < 2 ^ (prefixWord ++ tailWord_3917831).sum := by decide
  have hdescent : baseEnd_3917831 < baseStart_3917831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917855 : List Nat := [1, 1, 2, 4, 1, 2, 1, 2, 2, 6]
def baseStart_3917855 : Nat := 118140960795 + 3917855 * 2 ^ 59
def prefixEnd_3917855 : Nat := 4983230072969 + 3 ^ 40 * 3917855 * 2
def baseEnd_3917855 : Nat := 1341161833080582738663079

theorem tailTrace_3917855 : CollatzResearch.WordTrace tailWord_3917855 prefixEnd_3917855 1341161833080582738663079 := by
  unfold tailWord_3917855
  simp only [CollatzResearch.WordTrace]
  refine ⟨142895911221287926208035019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95263940814191950805356679 142895911221287926208035019)
  ·
    refine ⟨214343866831931889312052529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142895911221287926208035019 214343866831931889312052529)
    ·
      refine ⟨160757900123948916984039397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214343866831931889312052529 160757900123948916984039397)
      ·
        refine ⟨30142106273240421934507387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160757900123948916984039397 30142106273240421934507387)
        ·
          refine ⟨45213159409860632901761081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30142106273240421934507387 45213159409860632901761081)
          ·
            refine ⟨33909869557395474676320811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45213159409860632901761081 33909869557395474676320811)
            ·
              refine ⟨50864804336093212014481217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33909869557395474676320811 50864804336093212014481217)
              ·
                refine ⟨38148603252069909010860913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50864804336093212014481217 38148603252069909010860913)
                ·
                  refine ⟨28611452439052431758145685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38148603252069909010860913 28611452439052431758145685)
                  ·
                    refine ⟨1341161833080582738663079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28611452439052431758145685 1341161833080582738663079)
                    ·
                      rfl

theorem cell22_3917855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 6].length) (baseStart_3917855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3917855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3917855 prefixEnd_3917855 := by exact prefixLift 3917855
  have htrace : WordTrace (prefixWord ++ tailWord_3917855) baseStart_3917855 baseEnd_3917855 := by
    simpa [prefixWord, tailWord_3917855, baseEnd_3917855] using wordTrace_append hprefix tailTrace_3917855
  have hstable : (prefixWord ++ tailWord_3917855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917855).length < 2 ^ (prefixWord ++ tailWord_3917855).sum := by decide
  have hdescent : baseEnd_3917855 < baseStart_3917855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917887 : List Nat := [1, 1, 2, 2, 3, 1, 5, 2, 5]
def baseStart_3917887 : Nat := 118140960795 + 3917887 * 2 ^ 59
def prefixEnd_3917887 : Nat := 4983230072969 + 3 ^ 40 * 3917887 * 2
def baseEnd_3917887 : Nat := 447057595778181773954327

theorem tailTrace_3917887 : CollatzResearch.WordTrace tailWord_3917887 prefixEnd_3917887 447057595778181773954327 := by
  unfold tailWord_3917887
  simp only [CollatzResearch.WordTrace]
  refine ⟨142897078357171995673199915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95264718904781330448799943 142897078357171995673199915)
  ·
    refine ⟨214345617535757993509799873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142897078357171995673199915 214345617535757993509799873)
    ·
      refine ⟨160759213151818495132349905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214345617535757993509799873 160759213151818495132349905)
      ·
        refine ⟨120569409863863871349262429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160759213151818495132349905 120569409863863871349262429)
        ·
          refine ⟨45213528698948951755973411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120569409863863871349262429 45213528698948951755973411)
          ·
            refine ⟨67820293048423427633960117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45213528698948951755973411 67820293048423427633960117)
            ·
              refine ⟨6358152473289696340683761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67820293048423427633960117 6358152473289696340683761)
              ·
                refine ⟨4768614354967272255512821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6358152473289696340683761 4768614354967272255512821)
                ·
                  refine ⟨447057595778181773954327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4768614354967272255512821 447057595778181773954327)
                  ·
                    rfl

theorem cell22_3917887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 5].length) (baseStart_3917887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3917887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3917887 prefixEnd_3917887 := by exact prefixLift 3917887
  have htrace : WordTrace (prefixWord ++ tailWord_3917887) baseStart_3917887 baseEnd_3917887 := by
    simpa [prefixWord, tailWord_3917887, baseEnd_3917887] using wordTrace_append hprefix tailTrace_3917887
  have hstable : (prefixWord ++ tailWord_3917887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917887).length < 2 ^ (prefixWord ++ tailWord_3917887).sum := by decide
  have hdescent : baseEnd_3917887 < baseStart_3917887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917902 : List Nat := [4, 1, 1, 1, 1, 4, 2, 1, 2, 5]
def baseStart_3917902 : Nat := 118140960795 + 3917902 * 2 ^ 59
def prefixEnd_3917902 : Nat := 4983230072969 + 3 ^ 40 * 3917902 * 2
def baseEnd_3917902 : Nat := 1341177922141090282737935

theorem tailTrace_3917902 : CollatzResearch.WordTrace tailWord_3917902 prefixEnd_3917902 1341177922141090282737935 := by
  unfold tailWord_3917902
  simp only [CollatzResearch.WordTrace]
  refine ⟨17862203181514706654374495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95265083634745102156663973 17862203181514706654374495)
  ·
    refine ⟨26793304772272059981561743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17862203181514706654374495 26793304772272059981561743)
    ·
      refine ⟨40189957158408089972342615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26793304772272059981561743 40189957158408089972342615)
      ·
        refine ⟨60284935737612134958513923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40189957158408089972342615 60284935737612134958513923)
        ·
          refine ⟨90427403606418202437770885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60284935737612134958513923 90427403606418202437770885)
          ·
            refine ⟨16955138176203412957082041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90427403606418202437770885 16955138176203412957082041)
            ·
              refine ⟨12716353632152559717811531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16955138176203412957082041 12716353632152559717811531)
              ·
                refine ⟨19074530448228839576717297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12716353632152559717811531 19074530448228839576717297)
                ·
                  refine ⟨14305897836171629682537973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19074530448228839576717297 14305897836171629682537973)
                  ·
                    refine ⟨1341177922141090282737935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14305897836171629682537973 1341177922141090282737935)
                    ·
                      rfl

theorem cell22_3917902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_3917902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3917902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3917902 prefixEnd_3917902 := by exact prefixLift 3917902
  have htrace : WordTrace (prefixWord ++ tailWord_3917902) baseStart_3917902 baseEnd_3917902 := by
    simpa [prefixWord, tailWord_3917902, baseEnd_3917902] using wordTrace_append hprefix tailTrace_3917902
  have hstable : (prefixWord ++ tailWord_3917902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917902).length < 2 ^ (prefixWord ++ tailWord_3917902).sum := by decide
  have hdescent : baseEnd_3917902 < baseStart_3917902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917934 : List Nat := [4, 1, 2, 2, 1, 1, 1, 5, 1, 4]
def baseStart_3917934 : Nat := 118140960795 + 3917934 * 2 ^ 59
def prefixEnd_3917934 : Nat := 4983230072969 + 3 ^ 40 * 3917934 * 2
def baseEnd_3917934 : Nat := 1341188876395052865937837

theorem tailTrace_3917934 : CollatzResearch.WordTrace tailWord_3917934 prefixEnd_3917934 1341188876395052865937837 := by
  unfold tailWord_3917934
  simp only [CollatzResearch.WordTrace]
  refine ⟨17862349073500215337520107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95265861725334481800107237 17862349073500215337520107)
  ·
    refine ⟨26793523610250323006280161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17862349073500215337520107 26793523610250323006280161)
    ·
      refine ⟨20095142707687742254710121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26793523610250323006280161 20095142707687742254710121)
      ·
        refine ⟨15071357030765806691032591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20095142707687742254710121 15071357030765806691032591)
        ·
          refine ⟨22607035546148710036548887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15071357030765806691032591 22607035546148710036548887)
          ·
            refine ⟨33910553319223065054823331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22607035546148710036548887 33910553319223065054823331)
            ·
              refine ⟨50865829978834597582234997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33910553319223065054823331 50865829978834597582234997)
              ·
                refine ⟨4768671560515743523334531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50865829978834597582234997 4768671560515743523334531)
                ·
                  refine ⟨7153007340773615285001797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4768671560515743523334531 7153007340773615285001797)
                  ·
                    refine ⟨1341188876395052865937837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7153007340773615285001797 1341188876395052865937837)
                    ·
                      rfl

theorem cell22_3917934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_3917934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3917934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3917934 prefixEnd_3917934 := by exact prefixLift 3917934
  have htrace : WordTrace (prefixWord ++ tailWord_3917934) baseStart_3917934 baseEnd_3917934 := by
    simpa [prefixWord, tailWord_3917934, baseEnd_3917934] using wordTrace_append hprefix tailTrace_3917934
  have hstable : (prefixWord ++ tailWord_3917934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917934).length < 2 ^ (prefixWord ++ tailWord_3917934).sum := by decide
  have hdescent : baseEnd_3917934 < baseStart_3917934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917949 : List Nat := [1, 4, 1, 1, 3, 4, 1, 1, 6]
def baseStart_3917949 : Nat := 118140960795 + 3917949 * 2 ^ 59
def prefixEnd_3917949 : Nat := 4983230072969 + 3 ^ 40 * 3917949 * 2
def baseEnd_3917949 : Nat := 447064670400532608937597

theorem tailTrace_3917949 : CollatzResearch.WordTrace tailWord_3917949 prefixEnd_3917949 447064670400532608937597 := by
  unfold tailWord_3917949
  simp only [CollatzResearch.WordTrace]
  refine ⟨142899339682947380261956901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95266226455298253507971267 142899339682947380261956901)
  ·
    refine ⟨26793626190552633799116919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142899339682947380261956901 26793626190552633799116919)
    ·
      refine ⟨40190439285828950698675379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26793626190552633799116919 40190439285828950698675379)
      ·
        refine ⟨60285658928743426048013069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40190439285828950698675379 60285658928743426048013069)
        ·
          refine ⟨22607122098278784768004901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60285658928743426048013069 22607122098278784768004901)
          ·
            refine ⟨4238835393427272144000919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22607122098278784768004901 4238835393427272144000919)
            ·
              refine ⟨6358253090140908216001379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4238835393427272144000919 6358253090140908216001379)
              ·
                refine ⟨9537379635211362324002069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6358253090140908216001379 9537379635211362324002069)
                ·
                  refine ⟨447064670400532608937597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9537379635211362324002069 447064670400532608937597)
                  ·
                    rfl

theorem cell22_3917949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_3917949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3917949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3917949 prefixEnd_3917949 := by exact prefixLift 3917949
  have htrace : WordTrace (prefixWord ++ tailWord_3917949) baseStart_3917949 baseEnd_3917949 := by
    simpa [prefixWord, tailWord_3917949, baseEnd_3917949] using wordTrace_append hprefix tailTrace_3917949
  have hstable : (prefixWord ++ tailWord_3917949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917949).length < 2 ^ (prefixWord ++ tailWord_3917949).sum := by decide
  have hdescent : baseEnd_3917949 < baseStart_3917949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3917994 : List Nat := [3, 1, 5, 1, 2, 10]
def baseStart_3917994 : Nat := 118140960795 + 3917994 * 2 ^ 59
def prefixEnd_3917994 : Nat := 4983230072969 + 3 ^ 40 * 3917994 * 2
def baseEnd_3917994 : Nat := 16558140933595465548613

theorem tailTrace_3917994 : CollatzResearch.WordTrace tailWord_3917994 prefixEnd_3917994 16558140933595465548613 := by
  unfold tailWord_3917994
  simp only [CollatzResearch.WordTrace]
  refine ⟨35725245241946088236836259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95267320645189568631563357 35725245241946088236836259)
  ·
    refine ⟨53587867862919132355254389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35725245241946088236836259 53587867862919132355254389)
    ·
      refine ⟨5023862612148668658305099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53587867862919132355254389 5023862612148668658305099)
      ·
        refine ⟨7535793918223002987457649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5023862612148668658305099 7535793918223002987457649)
        ·
          refine ⟨5651845438667252240593237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7535793918223002987457649 5651845438667252240593237)
          ·
            refine ⟨16558140933595465548613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5651845438667252240593237 16558140933595465548613)
            ·
              rfl

theorem cell22_3917994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 10].length) (baseStart_3917994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3917994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3917994 prefixEnd_3917994 := by exact prefixLift 3917994
  have htrace : WordTrace (prefixWord ++ tailWord_3917994) baseStart_3917994 baseEnd_3917994 := by
    simpa [prefixWord, tailWord_3917994, baseEnd_3917994] using wordTrace_append hprefix tailTrace_3917994
  have hstable : (prefixWord ++ tailWord_3917994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3917994).length < 2 ^ (prefixWord ++ tailWord_3917994).sum := by decide
  have hdescent : baseEnd_3917994 < baseStart_3917994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3917994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918007 : List Nat := [1, 1, 3, 1, 4, 2, 1, 1, 2, 6]
def baseStart_3918007 : Nat := 118140960795 + 3918007 * 2 ^ 59
def prefixEnd_3918007 : Nat := 4983230072969 + 3 ^ 40 * 3918007 * 2
def baseEnd_3918007 : Nat := 1341213865786905008862613

theorem tailTrace_3918007 : CollatzResearch.WordTrace tailWord_3918007 prefixEnd_3918007 1341213865786905008862613 := by
  unfold tailWord_3918007
  simp only [CollatzResearch.WordTrace]
  refine ⟨142901455116737256167568275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95267636744491504111712183 142901455116737256167568275)
  ·
    refine ⟨214352182675105884251352413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142901455116737256167568275 214352182675105884251352413)
    ·
      refine ⟨80382068503164706594257155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214352182675105884251352413 80382068503164706594257155)
      ·
        refine ⟨120573102754747059891385733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80382068503164706594257155 120573102754747059891385733)
        ·
          refine ⟨22607456766515073729634825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120573102754747059891385733 22607456766515073729634825)
          ·
            refine ⟨16955592574886305297226119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22607456766515073729634825 16955592574886305297226119)
            ·
              refine ⟨25433388862329457945839179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16955592574886305297226119 25433388862329457945839179)
              ·
                refine ⟨38150083293494186918758769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25433388862329457945839179 38150083293494186918758769)
                ·
                  refine ⟨28612562470120640189069077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38150083293494186918758769 28612562470120640189069077)
                  ·
                    refine ⟨1341213865786905008862613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28612562470120640189069077 1341213865786905008862613)
                    ·
                      rfl

theorem cell22_3918007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_3918007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3918007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3918007 prefixEnd_3918007 := by exact prefixLift 3918007
  have htrace : WordTrace (prefixWord ++ tailWord_3918007) baseStart_3918007 baseEnd_3918007 := by
    simpa [prefixWord, tailWord_3918007, baseEnd_3918007] using wordTrace_append hprefix tailTrace_3918007
  have hstable : (prefixWord ++ tailWord_3918007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918007).length < 2 ^ (prefixWord ++ tailWord_3918007).sum := by decide
  have hdescent : baseEnd_3918007 < baseStart_3918007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918009 : List Nat := [1, 2, 1, 4, 1, 2, 2, 3, 3, 3]
def baseStart_3918009 : Nat := 118140960795 + 3918009 * 2 ^ 59
def prefixEnd_3918009 : Nat := 4983230072969 + 3 ^ 40 * 3918009 * 2
def baseEnd_3918009 : Nat := 1341214550427777670312607

theorem tailTrace_3918009 : CollatzResearch.WordTrace tailWord_3918009 prefixEnd_3918009 1341214550427777670312607 := by
  unfold tailWord_3918009
  simp only [CollatzResearch.WordTrace]
  refine ⟨142901528062730010509141081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95267685375153340339427387 142901528062730010509141081)
  ·
    refine ⟨107176146047047507881855811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142901528062730010509141081 107176146047047507881855811)
    ·
      refine ⟨160764219070571261822783717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107176146047047507881855811 160764219070571261822783717)
      ·
        refine ⟨30143291075732111591771947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160764219070571261822783717 30143291075732111591771947)
        ·
          refine ⟨45214936613598167387657921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30143291075732111591771947 45214936613598167387657921)
          ·
            refine ⟨33911202460198625540743441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45214936613598167387657921 33911202460198625540743441)
            ·
              refine ⟨25433401845148969155557581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33911202460198625540743441 25433401845148969155557581)
              ·
                refine ⟨9537525691930863433334093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25433401845148969155557581 9537525691930863433334093)
                ·
                  refine ⟨3576572134474073787500285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9537525691930863433334093 3576572134474073787500285)
                  ·
                    refine ⟨1341214550427777670312607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3576572134474073787500285 1341214550427777670312607)
                    ·
                      rfl

theorem cell22_3918009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 3, 3].length) (baseStart_3918009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3918009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3918009 prefixEnd_3918009 := by exact prefixLift 3918009
  have htrace : WordTrace (prefixWord ++ tailWord_3918009) baseStart_3918009 baseEnd_3918009 := by
    simpa [prefixWord, tailWord_3918009, baseEnd_3918009] using wordTrace_append hprefix tailTrace_3918009
  have hstable : (prefixWord ++ tailWord_3918009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918009).length < 2 ^ (prefixWord ++ tailWord_3918009).sum := by decide
  have hdescent : baseEnd_3918009 < baseStart_3918009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918056 : List Nat := [2, 1, 4, 1, 2, 4, 1, 2, 5]
def baseStart_3918056 : Nat := 118140960795 + 3918056 * 2 ^ 59
def prefixEnd_3918056 : Nat := 4983230072969 + 3 ^ 40 * 3918056 * 2
def baseEnd_3918056 : Nat := 447076879829428404795821

theorem tailTrace_3918056 : CollatzResearch.WordTrace tailWord_3918056 prefixEnd_3918056 447076879829428404795821 := by
  unfold tailWord_3918056
  simp only [CollatzResearch.WordTrace]
  refine ⟨71451621146779868768051011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95268828195706491690734681 71451621146779868768051011)
  ·
    refine ⟨107177431720169803152076517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71451621146779868768051011 107177431720169803152076517)
    ·
      refine ⟨20095768447531838091014347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107177431720169803152076517 20095768447531838091014347)
      ·
        refine ⟨30143652671297757136521521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20095768447531838091014347 30143652671297757136521521)
        ·
          refine ⟨22607739503473317852391141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30143652671297757136521521 22607739503473317852391141)
          ·
            refine ⟨4238951156901247097323339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22607739503473317852391141 4238951156901247097323339)
            ·
              refine ⟨6358426735351870645985009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4238951156901247097323339 6358426735351870645985009)
              ·
                refine ⟨4768820051513902984488757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6358426735351870645985009 4768820051513902984488757)
                ·
                  refine ⟨447076879829428404795821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4768820051513902984488757 447076879829428404795821)
                  ·
                    rfl

theorem cell22_3918056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 5].length) (baseStart_3918056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3918056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3918056 prefixEnd_3918056 := by exact prefixLift 3918056
  have htrace : WordTrace (prefixWord ++ tailWord_3918056) baseStart_3918056 baseEnd_3918056 := by
    simpa [prefixWord, tailWord_3918056, baseEnd_3918056] using wordTrace_append hprefix tailTrace_3918056
  have hstable : (prefixWord ++ tailWord_3918056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918056).length < 2 ^ (prefixWord ++ tailWord_3918056).sum := by decide
  have hdescent : baseEnd_3918056 < baseStart_3918056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918101 : List Nat := [1, 3, 2, 1, 2, 1, 5, 3, 4]
def baseStart_3918101 : Nat := 118140960795 + 3918101 * 2 ^ 59
def prefixEnd_3918101 : Nat := 4983230072969 + 3 ^ 40 * 3918101 * 2
def baseEnd_3918101 : Nat := 447082014635973365670775

theorem tailTrace_3918101 : CollatzResearch.WordTrace tailWord_3918101 prefixEnd_3918101 447082014635973365670775 := by
  unfold tailWord_3918101
  simp only [CollatzResearch.WordTrace]
  refine ⟨142904883578396710221490157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95269922385597806814326771 142904883578396710221490157)
  ·
    refine ⟨53589331341898766333058809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142904883578396710221490157 53589331341898766333058809)
    ·
      refine ⟨40191998506424074749794107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53589331341898766333058809 40191998506424074749794107)
      ·
        refine ⟨60287997759636112124691161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40191998506424074749794107 60287997759636112124691161)
        ·
          refine ⟨45215998319727084093518371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60287997759636112124691161 45215998319727084093518371)
          ·
            refine ⟨67823997479590626140277557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45215998319727084093518371 67823997479590626140277557)
            ·
              refine ⟨6358499763711621200651021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67823997479590626140277557 6358499763711621200651021)
              ·
                refine ⟨2384437411391857950244133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6358499763711621200651021 2384437411391857950244133)
                ·
                  refine ⟨447082014635973365670775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2384437411391857950244133 447082014635973365670775)
                  ·
                    rfl

theorem cell22_3918101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 3, 4].length) (baseStart_3918101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3918101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3918101 prefixEnd_3918101 := by exact prefixLift 3918101
  have htrace : WordTrace (prefixWord ++ tailWord_3918101) baseStart_3918101 baseEnd_3918101 := by
    simpa [prefixWord, tailWord_3918101, baseEnd_3918101] using wordTrace_append hprefix tailTrace_3918101
  have hstable : (prefixWord ++ tailWord_3918101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918101).length < 2 ^ (prefixWord ++ tailWord_3918101).sum := by decide
  have hdescent : baseEnd_3918101 < baseStart_3918101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918116 : List Nat := [2, 3, 1, 3, 1, 2, 2, 1, 4, 3]
def baseStart_3918116 : Nat := 118140960795 + 3918116 * 2 ^ 59
def prefixEnd_3918116 : Nat := 4983230072969 + 3 ^ 40 * 3918116 * 2
def baseEnd_3918116 : Nat := 1341251178714465057887279

theorem tailTrace_3918116 : CollatzResearch.WordTrace tailWord_3918116 prefixEnd_3918116 1341251178714465057887279 := by
  unfold tailWord_3918116
  simp only [CollatzResearch.WordTrace]
  refine ⟨71452715336671183891643101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95270287115561578522190801 71452715336671183891643101)
  ·
    refine ⟨26794768251251693959366163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71452715336671183891643101 26794768251251693959366163)
    ·
      refine ⟨40192152376877540939049245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26794768251251693959366163 40192152376877540939049245)
      ·
        refine ⟨15072057141329077852143467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40192152376877540939049245 15072057141329077852143467)
        ·
          refine ⟨22608085711993616778215201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15072057141329077852143467 22608085711993616778215201)
          ·
            refine ⟨16956064283995212583661401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22608085711993616778215201 16956064283995212583661401)
            ·
              refine ⟨12717048212996409437746051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16956064283995212583661401 12717048212996409437746051)
              ·
                refine ⟨19075572319494614156619077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12717048212996409437746051 19075572319494614156619077)
                ·
                  refine ⟨3576669809905240154366077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19075572319494614156619077 3576669809905240154366077)
                  ·
                    refine ⟨1341251178714465057887279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3576669809905240154366077 1341251178714465057887279)
                    ·
                      rfl

theorem cell22_3918116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_3918116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3918116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3918116 prefixEnd_3918116 := by exact prefixLift 3918116
  have htrace : WordTrace (prefixWord ++ tailWord_3918116) baseStart_3918116 baseEnd_3918116 := by
    simpa [prefixWord, tailWord_3918116, baseEnd_3918116] using wordTrace_append hprefix tailTrace_3918116
  have hstable : (prefixWord ++ tailWord_3918116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918116).length < 2 ^ (prefixWord ++ tailWord_3918116).sum := by decide
  have hdescent : baseEnd_3918116 < baseStart_3918116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918268 : List Nat := [2, 2, 2, 4, 1, 1, 1, 2, 4, 3]
def baseStart_3918268 : Nat := 118140960795 + 3918268 * 2 ^ 59
def prefixEnd_3918268 : Nat := 4983230072969 + 3 ^ 40 * 3918268 * 2
def baseEnd_3918268 : Nat := 1341303211420787328086813

theorem tailTrace_3918268 : CollatzResearch.WordTrace tailWord_3918268 prefixEnd_3918268 1341303211420787328086813 := by
  unfold tailWord_3918268
  simp only [CollatzResearch.WordTrace]
  refine ⟨71455487284395848871409729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95273983045861131828546305 71455487284395848871409729)
  ·
    refine ⟨53591615463296886653557297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71455487284395848871409729 53591615463296886653557297)
    ·
      refine ⟨40193711597472664990167973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53591615463296886653557297 40193711597472664990167973)
      ·
        refine ⟨7536320924526124685656495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40193711597472664990167973 7536320924526124685656495)
        ·
          refine ⟨11304481386789187028484743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7536320924526124685656495 11304481386789187028484743)
          ·
            refine ⟨16956722080183780542727115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11304481386789187028484743 16956722080183780542727115)
            ·
              refine ⟨25435083120275670814090673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16956722080183780542727115 25435083120275670814090673)
              ·
                refine ⟨19076312340206753110568005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25435083120275670814090673 19076312340206753110568005)
                ·
                  refine ⟨3576808563788766208231501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19076312340206753110568005 3576808563788766208231501)
                  ·
                    refine ⟨1341303211420787328086813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3576808563788766208231501 1341303211420787328086813)
                    ·
                      rfl

theorem cell22_3918268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_3918268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3918268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3918268 prefixEnd_3918268 := by exact prefixLift 3918268
  have htrace : WordTrace (prefixWord ++ tailWord_3918268) baseStart_3918268 baseEnd_3918268 := by
    simpa [prefixWord, tailWord_3918268, baseEnd_3918268] using wordTrace_append hprefix tailTrace_3918268
  have hstable : (prefixWord ++ tailWord_3918268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918268).length < 2 ^ (prefixWord ++ tailWord_3918268).sum := by decide
  have hdescent : baseEnd_3918268 < baseStart_3918268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918347 : List Nat := [1, 1, 1, 1, 7, 1, 4, 2, 1, 3]
def baseStart_3918347 : Nat := 118140960795 + 3918347 * 2 ^ 59
def prefixEnd_3918347 : Nat := 4983230072969 + 3 ^ 40 * 3918347 * 2
def baseEnd_3918347 : Nat := 1341330254735257455361571

theorem tailTrace_3918347 : CollatzResearch.WordTrace tailWord_3918347 prefixEnd_3918347 1341330254735257455361571 := by
  unfold tailWord_3918347
  simp only [CollatzResearch.WordTrace]
  refine ⟨142913855935505494234945295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95275903957003662823296863 142913855935505494234945295)
  ·
    refine ⟨214370783903258241352417943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142913855935505494234945295 214370783903258241352417943)
    ·
      refine ⟨321556175854887362028626915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214370783903258241352417943 321556175854887362028626915)
      ·
        refine ⟨482334263782331043042940373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321556175854887362028626915 482334263782331043042940373)
        ·
          refine ⟨11304709307398383821318915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 482334263782331043042940373 11304709307398383821318915)
          ·
            refine ⟨16957063961097575731978373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11304709307398383821318915 16957063961097575731978373)
            ·
              refine ⟨3179449492705795449745945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16957063961097575731978373 3179449492705795449745945)
              ·
                refine ⟨2384587119529346587309459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3179449492705795449745945 2384587119529346587309459)
                ·
                  refine ⟨3576880679294019880964189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2384587119529346587309459 3576880679294019880964189)
                  ·
                    refine ⟨1341330254735257455361571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3576880679294019880964189 1341330254735257455361571)
                    ·
                      rfl

theorem cell22_3918347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 2, 1, 3].length) (baseStart_3918347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3918347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3918347 prefixEnd_3918347 := by exact prefixLift 3918347
  have htrace : WordTrace (prefixWord ++ tailWord_3918347) baseStart_3918347 baseEnd_3918347 := by
    simpa [prefixWord, tailWord_3918347, baseEnd_3918347] using wordTrace_append hprefix tailTrace_3918347
  have hstable : (prefixWord ++ tailWord_3918347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918347).length < 2 ^ (prefixWord ++ tailWord_3918347).sum := by decide
  have hdescent : baseEnd_3918347 < baseStart_3918347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918371 : List Nat := [1, 1, 1, 4, 4, 1, 1, 1, 8]
def baseStart_3918371 : Nat := 118140960795 + 3918371 * 2 ^ 59
def prefixEnd_3918371 : Nat := 4983230072969 + 3 ^ 40 * 3918371 * 2
def baseEnd_3918371 : Nat := 447112823475243130920499

theorem tailTrace_3918371 : CollatzResearch.WordTrace tailWord_3918371 prefixEnd_3918371 447112823475243130920499 := by
  unfold tailWord_3918371
  simp only [CollatzResearch.WordTrace]
  refine ⟨142914731287418546333818967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95276487524945697555879311 142914731287418546333818967)
  ·
    refine ⟨214372096931127819500728451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142914731287418546333818967 214372096931127819500728451)
    ·
      refine ⟨321558145396691729251092677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214372096931127819500728451 321558145396691729251092677)
      ·
        refine ⟨60292152261879699234579877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 321558145396691729251092677 60292152261879699234579877)
        ·
          refine ⟨11304778549102443606483727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60292152261879699234579877 11304778549102443606483727)
          ·
            refine ⟨16957167823653665409725591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11304778549102443606483727 16957167823653665409725591)
            ·
              refine ⟨25435751735480498114588387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16957167823653665409725591 25435751735480498114588387)
              ·
                refine ⟨38153627603220747171882581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25435751735480498114588387 38153627603220747171882581)
                ·
                  refine ⟨447112823475243130920499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38153627603220747171882581 447112823475243130920499)
                  ·
                    rfl

theorem cell22_3918371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 8].length) (baseStart_3918371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3918371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3918371 prefixEnd_3918371 := by exact prefixLift 3918371
  have htrace : WordTrace (prefixWord ++ tailWord_3918371) baseStart_3918371 baseEnd_3918371 := by
    simpa [prefixWord, tailWord_3918371, baseEnd_3918371] using wordTrace_append hprefix tailTrace_3918371
  have hstable : (prefixWord ++ tailWord_3918371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918371).length < 2 ^ (prefixWord ++ tailWord_3918371).sum := by decide
  have hdescent : baseEnd_3918371 < baseStart_3918371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918420 : List Nat := [2, 4, 1, 1, 1, 5, 1, 1, 1, 5]
def baseStart_3918420 : Nat := 118140960795 + 3918420 * 2 ^ 59
def prefixEnd_3918420 : Nat := 4983230072969 + 3 ^ 40 * 3918420 * 2
def baseEnd_3918420 : Nat := 1341355244127109598286347

theorem tailTrace_3918420 : CollatzResearch.WordTrace tailWord_3918420 prefixEnd_3918420 1341355244127109598286347 := by
  unfold tailWord_3918420
  simp only [CollatzResearch.WordTrace]
  refine ⟨71458259232120513851176357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95277678976160685134901809 71458259232120513851176357)
  ·
    refine ⟨13398423606022596347095567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71458259232120513851176357 13398423606022596347095567)
    ·
      refine ⟨20097635409033894520643351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13398423606022596347095567 20097635409033894520643351)
      ·
        refine ⟨30146453113550841780965027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20097635409033894520643351 30146453113550841780965027)
        ·
          refine ⟨45219679670326262671447541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30146453113550841780965027 45219679670326262671447541)
          ·
            refine ⟨4239344969093087125448207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45219679670326262671447541 4239344969093087125448207)
            ·
              refine ⟨6359017453639630688172311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4239344969093087125448207 6359017453639630688172311)
              ·
                refine ⟨9538526180459446032258467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6359017453639630688172311 9538526180459446032258467)
                ·
                  refine ⟨14307789270689169048387701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9538526180459446032258467 14307789270689169048387701)
                  ·
                    refine ⟨1341355244127109598286347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14307789270689169048387701 1341355244127109598286347)
                    ·
                      rfl

theorem cell22_3918420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_3918420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3918420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3918420 prefixEnd_3918420 := by exact prefixLift 3918420
  have htrace : WordTrace (prefixWord ++ tailWord_3918420) baseStart_3918420 baseEnd_3918420 := by
    simpa [prefixWord, tailWord_3918420, baseEnd_3918420] using wordTrace_append hprefix tailTrace_3918420
  have hstable : (prefixWord ++ tailWord_3918420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918420).length < 2 ^ (prefixWord ++ tailWord_3918420).sum := by decide
  have hdescent : baseEnd_3918420 < baseStart_3918420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918433 : List Nat := [1, 2, 3, 1, 1, 4, 4, 6]
def baseStart_3918433 : Nat := 118140960795 + 3918433 * 2 ^ 59
def prefixEnd_3918433 : Nat := 4983230072969 + 3 ^ 40 * 3918433 * 2
def baseEnd_3918433 : Nat := 149039966032531321967923

theorem tailTrace_3918433 : CollatzResearch.WordTrace tailWord_3918433 prefixEnd_3918433 149039966032531321967923 := by
  unfold tailWord_3918433
  simp only [CollatzResearch.WordTrace]
  refine ⟨142916992613193930922575953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95277995075462620615050635 142916992613193930922575953)
  ·
    refine ⟨107187744459895448191931965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142916992613193930922575953 107187744459895448191931965)
    ·
      refine ⟨40195404172460793071974487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107187744459895448191931965 40195404172460793071974487)
      ·
        refine ⟨60293106258691189607961731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40195404172460793071974487 60293106258691189607961731)
        ·
          refine ⟨90439659388036784411942597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60293106258691189607961731 90439659388036784411942597)
          ·
            refine ⟨16957436135256897077239237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90439659388036784411942597 16957436135256897077239237)
            ·
              refine ⟨3179519275360668201982357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16957436135256897077239237 3179519275360668201982357)
              ·
                refine ⟨149039966032531321967923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3179519275360668201982357 149039966032531321967923)
                ·
                  rfl

theorem cell22_3918433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 6].length) (baseStart_3918433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3918433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3918433 prefixEnd_3918433 := by exact prefixLift 3918433
  have htrace : WordTrace (prefixWord ++ tailWord_3918433) baseStart_3918433 baseEnd_3918433 := by
    simpa [prefixWord, tailWord_3918433, baseEnd_3918433] using wordTrace_append hprefix tailTrace_3918433
  have hstable : (prefixWord ++ tailWord_3918433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918433).length < 2 ^ (prefixWord ++ tailWord_3918433).sum := by decide
  have hdescent : baseEnd_3918433 < baseStart_3918433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918450 : List Nat := [3, 2, 1, 2, 5, 1, 8]
def baseStart_3918450 : Nat := 118140960795 + 3918450 * 2 ^ 59
def prefixEnd_3918450 : Nat := 4983230072969 + 3 ^ 40 * 3918450 * 2
def baseEnd_3918450 : Nat := 49680204212599982223565

theorem tailTrace_3918450 : CollatzResearch.WordTrace tailWord_3918450 prefixEnd_3918450 49680204212599982223565 := by
  unfold tailWord_3918450
  simp only [CollatzResearch.WordTrace]
  refine ⟨35729403163533085706486201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95278408436088228550629869 35729403163533085706486201)
  ·
    refine ⟨26797052372649814279864651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35729403163533085706486201 26797052372649814279864651)
    ·
      refine ⟨40195578558974721419796977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26797052372649814279864651 40195578558974721419796977)
      ·
        refine ⟨30146683919231041064847733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40195578558974721419796977 30146683919231041064847733)
        ·
          refine ⟨2826251617427910099829475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30146683919231041064847733 2826251617427910099829475)
          ·
            refine ⟨4239377426141865149744213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2826251617427910099829475 4239377426141865149744213)
            ·
              refine ⟨49680204212599982223565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4239377426141865149744213 49680204212599982223565)
              ·
                rfl

theorem cell22_3918450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 8].length) (baseStart_3918450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3918450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3918450 prefixEnd_3918450 := by exact prefixLift 3918450
  have htrace : WordTrace (prefixWord ++ tailWord_3918450) baseStart_3918450 baseEnd_3918450 := by
    simpa [prefixWord, tailWord_3918450, baseEnd_3918450] using wordTrace_append hprefix tailTrace_3918450
  have hstable : (prefixWord ++ tailWord_3918450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918450).length < 2 ^ (prefixWord ++ tailWord_3918450).sum := by decide
  have hdescent : baseEnd_3918450 < baseStart_3918450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918540 : List Nat := [2, 2, 1, 5, 1, 2, 1, 2, 6]
def baseStart_3918540 : Nat := 118140960795 + 3918540 * 2 ^ 59
def prefixEnd_3918540 : Nat := 4983230072969 + 3 ^ 40 * 3918540 * 2
def baseEnd_3918540 : Nat := 447132107526489761761993

theorem tailTrace_3918540 : CollatzResearch.WordTrace tailWord_3918540 prefixEnd_3918540 447132107526489761761993 := by
  unfold tailWord_3918540
  simp only [CollatzResearch.WordTrace]
  refine ⟨71460447611903144098360537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95280596815870858797814049 71460447611903144098360537)
  ·
    refine ⟨53595335708927358073770403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71460447611903144098360537 53595335708927358073770403)
    ·
      refine ⟨80393003563391037110655605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53595335708927358073770403 80393003563391037110655605)
      ·
        refine ⟨7536844084067909729123963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80393003563391037110655605 7536844084067909729123963)
        ·
          refine ⟨11305266126101864593685945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7536844084067909729123963 11305266126101864593685945)
          ·
            refine ⟨8478949594576398445264459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11305266126101864593685945 8478949594576398445264459)
            ·
              refine ⟨12718424391864597667896689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8478949594576398445264459 12718424391864597667896689)
              ·
                refine ⟨9538818293898448250922517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12718424391864597667896689 9538818293898448250922517)
                ·
                  refine ⟨447132107526489761761993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9538818293898448250922517 447132107526489761761993)
                  ·
                    rfl

theorem cell22_3918540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 6].length) (baseStart_3918540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3918540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3918540 prefixEnd_3918540 := by exact prefixLift 3918540
  have htrace : WordTrace (prefixWord ++ tailWord_3918540) baseStart_3918540 baseEnd_3918540 := by
    simpa [prefixWord, tailWord_3918540, baseEnd_3918540] using wordTrace_append hprefix tailTrace_3918540
  have hstable : (prefixWord ++ tailWord_3918540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918540).length < 2 ^ (prefixWord ++ tailWord_3918540).sum := by decide
  have hdescent : baseEnd_3918540 < baseStart_3918540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918553 : List Nat := [1, 2, 1, 2, 3, 2, 3, 1, 1, 6]
def baseStart_3918553 : Nat := 118140960795 + 3918553 * 2 ^ 59
def prefixEnd_3918553 : Nat := 4983230072969 + 3 ^ 40 * 3918553 * 2
def baseEnd_3918553 : Nat := 1341400772745141584710939

theorem tailTrace_3918553 : CollatzResearch.WordTrace tailWord_3918553 prefixEnd_3918553 1341400772745141584710939 := by
  unfold tailWord_3918553
  simp only [CollatzResearch.WordTrace]
  refine ⟨142921369372759191416944313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95280912915172794277962875 142921369372759191416944313)
  ·
    refine ⟨107191027029569393562708235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142921369372759191416944313 107191027029569393562708235)
    ·
      refine ⟨160786540544354090344062353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107191027029569393562708235 160786540544354090344062353)
      ·
        refine ⟨120589905408265567758046765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160786540544354090344062353 120589905408265567758046765)
        ·
          refine ⟨45221214528099587909267537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120589905408265567758046765 45221214528099587909267537)
          ·
            refine ⟨33915910896074690931950653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45221214528099587909267537 33915910896074690931950653)
            ·
              refine ⟨12718466586028009099481495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33915910896074690931950653 12718466586028009099481495)
              ·
                refine ⟨19077699879042013649222243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12718466586028009099481495 19077699879042013649222243)
                ·
                  refine ⟨28616549818563020473833365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19077699879042013649222243 28616549818563020473833365)
                  ·
                    refine ⟨1341400772745141584710939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28616549818563020473833365 1341400772745141584710939)
                    ·
                      rfl

theorem cell22_3918553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 6].length) (baseStart_3918553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3918553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3918553 prefixEnd_3918553 := by exact prefixLift 3918553
  have htrace : WordTrace (prefixWord ++ tailWord_3918553) baseStart_3918553 baseEnd_3918553 := by
    simpa [prefixWord, tailWord_3918553, baseEnd_3918553] using wordTrace_append hprefix tailTrace_3918553
  have hstable : (prefixWord ++ tailWord_3918553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918553).length < 2 ^ (prefixWord ++ tailWord_3918553).sum := by decide
  have hdescent : baseEnd_3918553 < baseStart_3918553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918613 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 9]
def baseStart_3918613 : Nat := 118140960795 + 3918613 * 2 ^ 59
def prefixEnd_3918613 : Nat := 4983230072969 + 3 ^ 40 * 3918613 * 2
def baseEnd_3918613 : Nat := 447140437323773809403585

theorem tailTrace_3918613 : CollatzResearch.WordTrace tailWord_3918613 prefixEnd_3918613 447140437323773809403585 := by
  unfold tailWord_3918613
  simp only [CollatzResearch.WordTrace]
  refine ⟨142923557752541821664128493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95282371835027881109418995 142923557752541821664128493)
  ·
    refine ⟨53596334157203183124048185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142923557752541821664128493 53596334157203183124048185)
    ·
      refine ⟨40197250617902387343036139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53596334157203183124048185 40197250617902387343036139)
      ·
        refine ⟨60295875926853581014554209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40197250617902387343036139 60295875926853581014554209)
        ·
          refine ⟨45221906945140185760915657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60295875926853581014554209 45221906945140185760915657)
          ·
            refine ⟨33916430208855139320686743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45221906945140185760915657 33916430208855139320686743)
            ·
              refine ⟨50874645313282708981030115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33916430208855139320686743 50874645313282708981030115)
              ·
                refine ⟨76311967969924063471545173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50874645313282708981030115 76311967969924063471545173)
                ·
                  refine ⟨447140437323773809403585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 76311967969924063471545173 447140437323773809403585)
                  ·
                    rfl

theorem cell22_3918613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 9].length) (baseStart_3918613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3918613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3918613 prefixEnd_3918613 := by exact prefixLift 3918613
  have htrace : WordTrace (prefixWord ++ tailWord_3918613) baseStart_3918613 baseEnd_3918613 := by
    simpa [prefixWord, tailWord_3918613, baseEnd_3918613] using wordTrace_append hprefix tailTrace_3918613
  have hstable : (prefixWord ++ tailWord_3918613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918613).length < 2 ^ (prefixWord ++ tailWord_3918613).sum := by decide
  have hdescent : baseEnd_3918613 < baseStart_3918613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918617 : List Nat := [1, 2, 1, 2, 1, 1, 1, 9, 1, 3]
def baseStart_3918617 : Nat := 118140960795 + 3918617 * 2 ^ 59
def prefixEnd_3918617 : Nat := 4983230072969 + 3 ^ 40 * 3918617 * 2
def baseEnd_3918617 : Nat := 1341422681253066751110743

theorem tailTrace_3918617 : CollatzResearch.WordTrace tailWord_3918617 prefixEnd_3918617 1341422681253066751110743 := by
  unfold tailWord_3918617
  simp only [CollatzResearch.WordTrace]
  refine ⟨142923703644527330347274105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95282469096351553564849403 142923703644527330347274105)
  ·
    refine ⟨107192777733395497760455579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142923703644527330347274105 107192777733395497760455579)
    ·
      refine ⟨160789166600093246640683369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107192777733395497760455579 160789166600093246640683369)
      ·
        refine ⟨120591874950069934980512527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160789166600093246640683369 120591874950069934980512527)
        ·
          refine ⟨180887812425104902470768791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120591874950069934980512527 180887812425104902470768791)
          ·
            refine ⟨271331718637657353706153187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180887812425104902470768791 271331718637657353706153187)
            ·
              refine ⟨406997577956486030559229781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271331718637657353706153187 406997577956486030559229781)
              ·
                refine ⟨2384751433338785335307987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 406997577956486030559229781 2384751433338785335307987)
                ·
                  refine ⟨3577127150008178002961981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2384751433338785335307987 3577127150008178002961981)
                  ·
                    refine ⟨1341422681253066751110743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3577127150008178002961981 1341422681253066751110743)
                    ·
                      rfl

theorem cell22_3918617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 9, 1, 3].length) (baseStart_3918617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3918617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3918617 prefixEnd_3918617 := by exact prefixLift 3918617
  have htrace : WordTrace (prefixWord ++ tailWord_3918617) baseStart_3918617 baseEnd_3918617 := by
    simpa [prefixWord, tailWord_3918617, baseEnd_3918617] using wordTrace_append hprefix tailTrace_3918617
  have hstable : (prefixWord ++ tailWord_3918617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918617).length < 2 ^ (prefixWord ++ tailWord_3918617).sum := by decide
  have hdescent : baseEnd_3918617 < baseStart_3918617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918707 : List Nat := [1, 1, 1, 2, 2, 1, 6, 3, 2, 3]
def baseStart_3918707 : Nat := 118140960795 + 3918707 * 2 ^ 59
def prefixEnd_3918707 : Nat := 4983230072969 + 3 ^ 40 * 3918707 * 2
def baseEnd_3918707 : Nat := 1341453490092336516360467

theorem tailTrace_3918707 : CollatzResearch.WordTrace tailWord_3918707 prefixEnd_3918707 1341453490092336516360467 := by
  unfold tailWord_3918707
  simp only [CollatzResearch.WordTrace]
  refine ⟨142926986214201275718050375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95284657476134183812033583 142926986214201275718050375)
  ·
    refine ⟨214390479321301913577075563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142926986214201275718050375 214390479321301913577075563)
    ·
      refine ⟨321585718981952870365613345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214390479321301913577075563 321585718981952870365613345)
      ·
        refine ⟨241189289236464652774210009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321585718981952870365613345 241189289236464652774210009)
        ·
          refine ⟨180891966927348489580657507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241189289236464652774210009 180891966927348489580657507)
          ·
            refine ⟨271337950391022734370986261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180891966927348489580657507 271337950391022734370986261)
            ·
              refine ⟨12718966424579190673639981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 271337950391022734370986261 12718966424579190673639981)
              ·
                refine ⟨4769612409217196502614993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12718966424579190673639981 4769612409217196502614993)
                ·
                  refine ⟨3577209306912897376961245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4769612409217196502614993 3577209306912897376961245)
                  ·
                    refine ⟨1341453490092336516360467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3577209306912897376961245 1341453490092336516360467)
                    ·
                      rfl

theorem cell22_3918707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 2, 3].length) (baseStart_3918707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3918707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3918707 prefixEnd_3918707 := by exact prefixLift 3918707
  have htrace : WordTrace (prefixWord ++ tailWord_3918707) baseStart_3918707 baseEnd_3918707 := by
    simpa [prefixWord, tailWord_3918707, baseEnd_3918707] using wordTrace_append hprefix tailTrace_3918707
  have hstable : (prefixWord ++ tailWord_3918707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918707).length < 2 ^ (prefixWord ++ tailWord_3918707).sum := by decide
  have hdescent : baseEnd_3918707 < baseStart_3918707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918752 : List Nat := [2, 1, 1, 4, 1, 1, 3, 3, 3, 3]
def baseStart_3918752 : Nat := 118140960795 + 3918752 * 2 ^ 59
def prefixEnd_3918752 : Nat := 4983230072969 + 3 ^ 40 * 3918752 * 2
def baseEnd_3918752 : Nat := 1341468894511971398985329

theorem tailTrace_3918752 : CollatzResearch.WordTrace tailWord_3918752 prefixEnd_3918752 1341468894511971398985329 := by
  unfold tailWord_3918752
  simp only [CollatzResearch.WordTrace]
  refine ⟨71464313749519124201719255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95285751666025498935625673 71464313749519124201719255)
  ·
    refine ⟨107196470624278686302578883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71464313749519124201719255 107196470624278686302578883)
    ·
      refine ⟨160794705936418029453868325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107196470624278686302578883 160794705936418029453868325)
      ·
        refine ⟨30149007363078380522600311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160794705936418029453868325 30149007363078380522600311)
        ·
          refine ⟨45223511044617570783900467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30149007363078380522600311 45223511044617570783900467)
          ·
            refine ⟨67835266566926356175850701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45223511044617570783900467 67835266566926356175850701)
            ·
              refine ⟨25438224962597383565944013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67835266566926356175850701 25438224962597383565944013)
              ·
                refine ⟨9539334360974018837229005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25438224962597383565944013 9539334360974018837229005)
                ·
                  refine ⟨3577250385365257063960877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9539334360974018837229005 3577250385365257063960877)
                  ·
                    refine ⟨1341468894511971398985329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3577250385365257063960877 1341468894511971398985329)
                    ·
                      rfl

theorem cell22_3918752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 3, 3].length) (baseStart_3918752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3918752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3918752 prefixEnd_3918752 := by exact prefixLift 3918752
  have htrace : WordTrace (prefixWord ++ tailWord_3918752) baseStart_3918752 baseEnd_3918752 := by
    simpa [prefixWord, tailWord_3918752, baseEnd_3918752] using wordTrace_append hprefix tailTrace_3918752
  have hstable : (prefixWord ++ tailWord_3918752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918752).length < 2 ^ (prefixWord ++ tailWord_3918752).sum := by decide
  have hdescent : baseEnd_3918752 < baseStart_3918752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918790 : List Nat := [6, 1, 3, 1, 1, 1, 1, 2, 2, 4]
def baseStart_3918790 : Nat := 118140960795 + 3918790 * 2 ^ 59
def prefixEnd_3918790 : Nat := 4983230072969 + 3 ^ 40 * 3918790 * 2
def baseEnd_3918790 : Nat := 1341481902688551966535213

theorem tailTrace_3918790 : CollatzResearch.WordTrace tailWord_3918790 prefixEnd_3918790 1341481902688551966535213 := by
  unfold tailWord_3918790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4466562921028143152916307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 95286675648600387262214549 4466562921028143152916307)
  ·
    refine ⟨6699844381542214729374461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4466562921028143152916307 6699844381542214729374461)
    ·
      refine ⟨2512441643078330523515423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6699844381542214729374461 2512441643078330523515423)
      ·
        refine ⟨3768662464617495785273135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2512441643078330523515423 3768662464617495785273135)
        ·
          refine ⟨5652993696926243677909703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3768662464617495785273135 5652993696926243677909703)
          ·
            refine ⟨8479490545389365516864555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5652993696926243677909703 8479490545389365516864555)
            ·
              refine ⟨12719235818084048275296833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8479490545389365516864555 12719235818084048275296833)
              ·
                refine ⟨9539426863563036206472625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12719235818084048275296833 9539426863563036206472625)
                ·
                  refine ⟨7154570147672277154854469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9539426863563036206472625 7154570147672277154854469)
                  ·
                    refine ⟨1341481902688551966535213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7154570147672277154854469 1341481902688551966535213)
                    ·
                      rfl

theorem cell22_3918790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_3918790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3918790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3918790 prefixEnd_3918790 := by exact prefixLift 3918790
  have htrace : WordTrace (prefixWord ++ tailWord_3918790) baseStart_3918790 baseEnd_3918790 := by
    simpa [prefixWord, tailWord_3918790, baseEnd_3918790] using wordTrace_append hprefix tailTrace_3918790
  have hstable : (prefixWord ++ tailWord_3918790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918790).length < 2 ^ (prefixWord ++ tailWord_3918790).sum := by decide
  have hdescent : baseEnd_3918790 < baseStart_3918790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918825 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 7, 5]
def baseStart_3918825 : Nat := 118140960795 + 3918825 * 2 ^ 59
def prefixEnd_3918825 : Nat := 4983230072969 + 3 ^ 40 * 3918825 * 2
def baseEnd_3918825 : Nat := 1341493883903823541910105

theorem tailTrace_3918825 : CollatzResearch.WordTrace tailWord_3918825 prefixEnd_3918825 1341493883903823541910105 := by
  unfold tailWord_3918825
  simp only [CollatzResearch.WordTrace]
  refine ⟨142931290027773781870845929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95287526685182521247230619 142931290027773781870845929)
  ·
    refine ⟨107198467520830336403134447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142931290027773781870845929 107198467520830336403134447)
    ·
      refine ⟨160797701281245504604701671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107198467520830336403134447 160797701281245504604701671)
      ·
        refine ⟨241196551921868256907052507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160797701281245504604701671 241196551921868256907052507)
        ·
          refine ⟨361794827882802385360578761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241196551921868256907052507 361794827882802385360578761)
          ·
            refine ⟨271346120912101789020434071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361794827882802385360578761 271346120912101789020434071)
            ·
              refine ⟨407019181368152683530651107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271346120912101789020434071 407019181368152683530651107)
              ·
                refine ⟨610528772052229025295976661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407019181368152683530651107 610528772052229025295976661)
                ·
                  refine ⟨14309268094974117780374453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 610528772052229025295976661 14309268094974117780374453)
                  ·
                    refine ⟨1341493883903823541910105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14309268094974117780374453 1341493883903823541910105)
                    ·
                      rfl

theorem cell22_3918825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 5].length) (baseStart_3918825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3918825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3918825 prefixEnd_3918825 := by exact prefixLift 3918825
  have htrace : WordTrace (prefixWord ++ tailWord_3918825) baseStart_3918825 baseEnd_3918825 := by
    simpa [prefixWord, tailWord_3918825, baseEnd_3918825] using wordTrace_append hprefix tailTrace_3918825
  have hstable : (prefixWord ++ tailWord_3918825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918825).length < 2 ^ (prefixWord ++ tailWord_3918825).sum := by decide
  have hdescent : baseEnd_3918825 < baseStart_3918825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918842 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 6, 3]
def baseStart_3918842 : Nat := 118140960795 + 3918842 * 2 ^ 59
def prefixEnd_3918842 : Nat := 4983230072969 + 3 ^ 40 * 3918842 * 2
def baseEnd_3918842 : Nat := 1341499703351241164235053

theorem tailTrace_3918842 : CollatzResearch.WordTrace tailWord_3918842 prefixEnd_3918842 1341499703351241164235053 := by
  unfold tailWord_3918842
  simp only [CollatzResearch.WordTrace]
  refine ⟨35732977517178048443553695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95287940045808129182809853 35732977517178048443553695)
  ·
    refine ⟨53599466275767072665330543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35732977517178048443553695 53599466275767072665330543)
    ·
      refine ⟨80399199413650608997995815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53599466275767072665330543 80399199413650608997995815)
      ·
        refine ⟨120598799120475913496993723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80399199413650608997995815 120598799120475913496993723)
        ·
          refine ⟨180898198680713870245490585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120598799120475913496993723 180898198680713870245490585)
          ·
            refine ⟨135673649010535402684117939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180898198680713870245490585 135673649010535402684117939)
            ·
              refine ⟨203510473515803104026176909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135673649010535402684117939 203510473515803104026176909)
              ·
                refine ⟨76316427568426164009816341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203510473515803104026176909 76316427568426164009816341)
                ·
                  refine ⟨3577332542269976437960141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 76316427568426164009816341 3577332542269976437960141)
                  ·
                    refine ⟨1341499703351241164235053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3577332542269976437960141 1341499703351241164235053)
                    ·
                      rfl

theorem cell22_3918842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 6, 3].length) (baseStart_3918842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3918842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3918842 prefixEnd_3918842 := by exact prefixLift 3918842
  have htrace : WordTrace (prefixWord ++ tailWord_3918842) baseStart_3918842 baseEnd_3918842 := by
    simpa [prefixWord, tailWord_3918842, baseEnd_3918842] using wordTrace_append hprefix tailTrace_3918842
  have hstable : (prefixWord ++ tailWord_3918842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918842).length < 2 ^ (prefixWord ++ tailWord_3918842).sum := by decide
  have hdescent : baseEnd_3918842 < baseStart_3918842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918859 : List Nat := [1, 1, 1, 1, 6, 2, 1, 4, 2, 3]
def baseStart_3918859 : Nat := 118140960795 + 3918859 * 2 ^ 59
def prefixEnd_3918859 : Nat := 4983230072969 + 3 ^ 40 * 3918859 * 2
def baseEnd_3918859 : Nat := 1341505522798658786560001

theorem tailTrace_3918859 : CollatzResearch.WordTrace tailWord_3918859 prefixEnd_3918859 1341505522798658786560001 := by
  unfold tailWord_3918859
  simp only [CollatzResearch.WordTrace]
  refine ⟨142932530109650605677583631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95288353406433737118389087 142932530109650605677583631)
  ·
    refine ⟨214398795164475908516375447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142932530109650605677583631 214398795164475908516375447)
    ·
      refine ⟨321598192746713862774563171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214398795164475908516375447 321598192746713862774563171)
      ·
        refine ⟨482397289120070794161844757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321598192746713862774563171 482397289120070794161844757)
        ·
          refine ⟨22612372927503318476336473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 482397289120070794161844757 22612372927503318476336473)
          ·
            refine ⟨16959279695627488857252355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22612372927503318476336473 16959279695627488857252355)
            ·
              refine ⟨25438919543441233285878533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16959279695627488857252355 25438919543441233285878533)
              ·
                refine ⟨4769797414395231241102225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25438919543441233285878533 4769797414395231241102225)
                ·
                  refine ⟨3577348060796423430826669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4769797414395231241102225 3577348060796423430826669)
                  ·
                    refine ⟨1341505522798658786560001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3577348060796423430826669 1341505522798658786560001)
                    ·
                      rfl

theorem cell22_3918859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 2, 3].length) (baseStart_3918859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3918859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3918859 prefixEnd_3918859 := by exact prefixLift 3918859
  have htrace : WordTrace (prefixWord ++ tailWord_3918859) baseStart_3918859 baseEnd_3918859 := by
    simpa [prefixWord, tailWord_3918859, baseEnd_3918859] using wordTrace_append hprefix tailTrace_3918859
  have hstable : (prefixWord ++ tailWord_3918859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918859).length < 2 ^ (prefixWord ++ tailWord_3918859).sum := by decide
  have hdescent : baseEnd_3918859 < baseStart_3918859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918872 : List Nat := [2, 1, 2, 3, 2, 2, 3, 7]
def baseStart_3918872 : Nat := 118140960795 + 3918872 * 2 ^ 59
def prefixEnd_3918872 : Nat := 4983230072969 + 3 ^ 40 * 3918872 * 2
def baseEnd_3918872 : Nat := 149056663662703453998329

theorem tailTrace_3918872 : CollatzResearch.WordTrace tailWord_3918872 prefixEnd_3918872 149056663662703453998329 := by
  unfold tailWord_3918872
  simp only [CollatzResearch.WordTrace]
  refine ⟨71466502129301754448903435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95288669505735672598537913 71466502129301754448903435)
  ·
    refine ⟨107199753193952631673355153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71466502129301754448903435 107199753193952631673355153)
    ·
      refine ⟨80399814895464473755016365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107199753193952631673355153 80399814895464473755016365)
      ·
        refine ⟨30149930585799177658131137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80399814895464473755016365 30149930585799177658131137)
        ·
          refine ⟨22612447939349383243598353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30149930585799177658131137 22612447939349383243598353)
          ·
            refine ⟨16959335954512037432698765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22612447939349383243598353 16959335954512037432698765)
            ·
              refine ⟨6359750982942014037262037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16959335954512037432698765 6359750982942014037262037)
              ·
                refine ⟨149056663662703453998329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6359750982942014037262037 149056663662703453998329)
                ·
                  rfl

theorem cell22_3918872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 7].length) (baseStart_3918872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3918872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3918872 prefixEnd_3918872 := by exact prefixLift 3918872
  have htrace : WordTrace (prefixWord ++ tailWord_3918872) baseStart_3918872 baseEnd_3918872 := by
    simpa [prefixWord, tailWord_3918872, baseEnd_3918872] using wordTrace_append hprefix tailTrace_3918872
  have hstable : (prefixWord ++ tailWord_3918872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918872).length < 2 ^ (prefixWord ++ tailWord_3918872).sum := by decide
  have hdescent : baseEnd_3918872 < baseStart_3918872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3918992 : List Nat := [2, 1, 1, 1, 1, 1, 4, 4, 1, 6]
def baseStart_3918992 : Nat := 118140960795 + 3918992 * 2 ^ 59
def prefixEnd_3918992 : Nat := 4983230072969 + 3 ^ 40 * 3918992 * 2
def baseEnd_3918992 : Nat := 1341551051416690772984593

theorem tailTrace_3918992 : CollatzResearch.WordTrace tailWord_3918992 prefixEnd_3918992 1341551051416690772984593 := by
  unfold tailWord_3918992
  simp only [CollatzResearch.WordTrace]
  refine ⟨71468690509084384696087615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95291587345445846261450153 71468690509084384696087615)
  ·
    refine ⟨107203035763626577044131423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71468690509084384696087615 107203035763626577044131423)
    ·
      refine ⟨160804553645439865566197135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107203035763626577044131423 160804553645439865566197135)
      ·
        refine ⟨241206830468159798349295703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160804553645439865566197135 241206830468159798349295703)
        ·
          refine ⟨361810245702239697523943555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241206830468159798349295703 361810245702239697523943555)
          ·
            refine ⟨542715368553359546285915333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361810245702239697523943555 542715368553359546285915333)
            ·
              refine ⟨101759131603754914928609125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 542715368553359546285915333 101759131603754914928609125)
              ·
                refine ⟨19079837175704046549114211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101759131603754914928609125 19079837175704046549114211)
                ·
                  refine ⟨28619755763556069823671317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19079837175704046549114211 28619755763556069823671317)
                  ·
                    refine ⟨1341551051416690772984593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28619755763556069823671317 1341551051416690772984593)
                    ·
                      rfl

theorem cell22_3918992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 1, 6].length) (baseStart_3918992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3918992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3918992 prefixEnd_3918992 := by exact prefixLift 3918992
  have htrace : WordTrace (prefixWord ++ tailWord_3918992) baseStart_3918992 baseEnd_3918992 := by
    simpa [prefixWord, tailWord_3918992, baseEnd_3918992] using wordTrace_append hprefix tailTrace_3918992
  have hstable : (prefixWord ++ tailWord_3918992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3918992).length < 2 ^ (prefixWord ++ tailWord_3918992).sum := by decide
  have hdescent : baseEnd_3918992 < baseStart_3918992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3918992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919041 : List Nat := [1, 2, 6, 1, 1, 1, 3, 7]
def baseStart_3919041 : Nat := 118140960795 + 3919041 * 2 ^ 59
def prefixEnd_3919041 : Nat := 4983230072969 + 3 ^ 40 * 3919041 * 2
def baseEnd_3919041 : Nat := 149063091679785664278827

theorem tailTrace_3919041 : CollatzResearch.WordTrace tailWord_3919041 prefixEnd_3919041 149063091679785664278827 := by
  unfold tailWord_3919041
  simp only [CollatzResearch.WordTrace]
  refine ⟨142939168194991250760708977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95292778796660833840472651 142939168194991250760708977)
  ·
    refine ⟨107204376146243438070531733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142939168194991250760708977 107204376146243438070531733)
    ·
      refine ⟨5025205131855161159556175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 107204376146243438070531733 5025205131855161159556175)
      ·
        refine ⟨7537807697782741739334263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5025205131855161159556175 7537807697782741739334263)
        ·
          refine ⟨11306711546674112609001395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7537807697782741739334263 11306711546674112609001395)
          ·
            refine ⟨16960067320011168913502093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11306711546674112609001395 16960067320011168913502093)
            ·
              refine ⟨6360025245004188342563285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16960067320011168913502093 6360025245004188342563285)
              ·
                refine ⟨149063091679785664278827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6360025245004188342563285 149063091679785664278827)
                ·
                  rfl

theorem cell22_3919041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 7].length) (baseStart_3919041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3919041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3919041 prefixEnd_3919041 := by exact prefixLift 3919041
  have htrace : WordTrace (prefixWord ++ tailWord_3919041) baseStart_3919041 baseEnd_3919041 := by
    simpa [prefixWord, tailWord_3919041, baseEnd_3919041] using wordTrace_append hprefix tailTrace_3919041
  have hstable : (prefixWord ++ tailWord_3919041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919041).length < 2 ^ (prefixWord ++ tailWord_3919041).sum := by decide
  have hdescent : baseEnd_3919041 < baseStart_3919041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919060 : List Nat := [2, 4, 1, 4, 1, 2, 1, 1, 2, 4]
def baseStart_3919060 : Nat := 118140960795 + 3919060 * 2 ^ 59
def prefixEnd_3919060 : Nat := 4983230072969 + 3 ^ 40 * 3919060 * 2
def baseEnd_3919060 : Nat := 1341574329206361262284385

theorem tailTrace_3919060 : CollatzResearch.WordTrace tailWord_3919060 prefixEnd_3919060 1341574329206361262284385 := by
  unfold tailWord_3919060
  simp only [CollatzResearch.WordTrace]
  refine ⟨71469930590961208502825317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95293240787948278003767089 71469930590961208502825317)
  ·
    refine ⟨13400611985805226594279747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71469930590961208502825317 13400611985805226594279747)
    ·
      refine ⟨20100917978707839891419621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13400611985805226594279747 20100917978707839891419621)
      ·
        refine ⟨3768922121007719979641179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20100917978707839891419621 3768922121007719979641179)
        ·
          refine ⟨5653383181511579969461769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3768922121007719979641179 5653383181511579969461769)
          ·
            refine ⟨4240037386133684977096327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5653383181511579969461769 4240037386133684977096327)
            ·
              refine ⟨6360056079200527465644491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4240037386133684977096327 6360056079200527465644491)
              ·
                refine ⟨9540084118800791198466737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6360056079200527465644491 9540084118800791198466737)
                ·
                  refine ⟨7155063089100593398850053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9540084118800791198466737 7155063089100593398850053)
                  ·
                    refine ⟨1341574329206361262284385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7155063089100593398850053 1341574329206361262284385)
                    ·
                      rfl

theorem cell22_3919060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_3919060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3919060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3919060 prefixEnd_3919060 := by exact prefixLift 3919060
  have htrace : WordTrace (prefixWord ++ tailWord_3919060) baseStart_3919060 baseEnd_3919060 := by
    simpa [prefixWord, tailWord_3919060, baseEnd_3919060] using wordTrace_append hprefix tailTrace_3919060
  have hstable : (prefixWord ++ tailWord_3919060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919060).length < 2 ^ (prefixWord ++ tailWord_3919060).sum := by decide
  have hdescent : baseEnd_3919060 < baseStart_3919060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919073 : List Nat := [1, 2, 3, 1, 3, 2, 1, 5, 1, 3]
def baseStart_3919073 : Nat := 118140960795 + 3919073 * 2 ^ 59
def prefixEnd_3919073 : Nat := 4983230072969 + 3 ^ 40 * 3919073 * 2
def baseEnd_3919073 : Nat := 1341578779372033561709345

theorem tailTrace_3919073 : CollatzResearch.WordTrace tailWord_3919073 prefixEnd_3919073 1341578779372033561709345 := by
  unfold tailWord_3919073
  simp only [CollatzResearch.WordTrace]
  refine ⟨142940335330875320225873873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95293556887250213483915915 142940335330875320225873873)
  ·
    refine ⟨107205251498156490169405405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142940335330875320225873873 107205251498156490169405405)
    ·
      refine ⟨40201969311808683813527027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107205251498156490169405405 40201969311808683813527027)
      ·
        refine ⟨60302953967713025720290541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40201969311808683813527027 60302953967713025720290541)
        ·
          refine ⟨22613607737892384645108953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60302953967713025720290541 22613607737892384645108953)
          ·
            refine ⟨16960205803419288483831715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22613607737892384645108953 16960205803419288483831715)
            ·
              refine ⟨25440308705128932725747573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16960205803419288483831715 25440308705128932725747573)
              ·
                refine ⟨2385028941105837443038835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25440308705128932725747573 2385028941105837443038835)
                ·
                  refine ⟨3577543411658756164558253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2385028941105837443038835 3577543411658756164558253)
                  ·
                    refine ⟨1341578779372033561709345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3577543411658756164558253 1341578779372033561709345)
                    ·
                      rfl

theorem cell22_3919073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 5, 1, 3].length) (baseStart_3919073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3919073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3919073 prefixEnd_3919073 := by exact prefixLift 3919073
  have htrace : WordTrace (prefixWord ++ tailWord_3919073) baseStart_3919073 baseEnd_3919073 := by
    simpa [prefixWord, tailWord_3919073, baseEnd_3919073] using wordTrace_append hprefix tailTrace_3919073
  have hstable : (prefixWord ++ tailWord_3919073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919073).length < 2 ^ (prefixWord ++ tailWord_3919073).sum := by decide
  have hdescent : baseEnd_3919073 < baseStart_3919073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919084 : List Nat := [2, 2, 1, 1, 2, 4, 1, 2, 2, 5]
def baseStart_3919084 : Nat := 118140960795 + 3919084 * 2 ^ 59
def prefixEnd_3919084 : Nat := 4983230072969 + 3 ^ 40 * 3919084 * 2
def baseEnd_3919084 : Nat := 1341582544896833199684311

theorem tailTrace_3919084 : CollatzResearch.WordTrace tailWord_3919084 prefixEnd_3919084 1341582544896833199684311 := by
  unfold tailWord_3919084
  simp only [CollatzResearch.WordTrace]
  refine ⟨71470368266917734552262153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95293824355890312736349537 71470368266917734552262153)
  ·
    refine ⟨53602776200188300914196615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71470368266917734552262153 53602776200188300914196615)
    ·
      refine ⟨80404164300282451371294923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53602776200188300914196615 80404164300282451371294923)
      ·
        refine ⟨120606246450423677056942385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80404164300282451371294923 120606246450423677056942385)
        ·
          refine ⟨90454684837817757792706789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120606246450423677056942385 90454684837817757792706789)
          ·
            refine ⟨16960253407090829586132523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90454684837817757792706789 16960253407090829586132523)
            ·
              refine ⟨25440380110636244379198785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16960253407090829586132523 25440380110636244379198785)
              ·
                refine ⟨19080285082977183284399089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25440380110636244379198785 19080285082977183284399089)
                ·
                  refine ⟨14310213812232887463299317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19080285082977183284399089 14310213812232887463299317)
                  ·
                    refine ⟨1341582544896833199684311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14310213812232887463299317 1341582544896833199684311)
                    ·
                      rfl

theorem cell22_3919084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_3919084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3919084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3919084 prefixEnd_3919084 := by exact prefixLift 3919084
  have htrace : WordTrace (prefixWord ++ tailWord_3919084) baseStart_3919084 baseEnd_3919084 := by
    simpa [prefixWord, tailWord_3919084, baseEnd_3919084] using wordTrace_append hprefix tailTrace_3919084
  have hstable : (prefixWord ++ tailWord_3919084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919084).length < 2 ^ (prefixWord ++ tailWord_3919084).sum := by decide
  have hdescent : baseEnd_3919084 < baseStart_3919084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919086 : List Nat := [4, 1, 2, 1, 1, 1, 5, 2, 5]
def baseStart_3919086 : Nat := 118140960795 + 3919086 * 2 ^ 59
def prefixEnd_3919086 : Nat := 4983230072969 + 3 ^ 40 * 3919086 * 2
def baseEnd_3919086 : Nat := 447194409845901953711435

theorem tailTrace_3919086 : CollatzResearch.WordTrace tailWord_3919086 prefixEnd_3919086 447194409845901953711435 := by
  unfold tailWord_3919086
  simp only [CollatzResearch.WordTrace]
  refine ⟨17867601184978527930762139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95293872986552148964064741 17867601184978527930762139)
  ·
    refine ⟨26801401777467791896143209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17867601184978527930762139 26801401777467791896143209)
    ·
      refine ⟨20101051333100843922107407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26801401777467791896143209 20101051333100843922107407)
      ·
        refine ⟨30151576999651265883161111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20101051333100843922107407 30151576999651265883161111)
        ·
          refine ⟨45227365499476898824741667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30151576999651265883161111 45227365499476898824741667)
          ·
            refine ⟨67841048249215348237112501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45227365499476898824741667 67841048249215348237112501)
            ·
              refine ⟨6360098273363938897229297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67841048249215348237112501 6360098273363938897229297)
              ·
                refine ⟨4770073705022954172921973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6360098273363938897229297 4770073705022954172921973)
                ·
                  refine ⟨447194409845901953711435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4770073705022954172921973 447194409845901953711435)
                  ·
                    rfl

theorem cell22_3919086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_3919086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3919086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3919086 prefixEnd_3919086 := by exact prefixLift 3919086
  have htrace : WordTrace (prefixWord ++ tailWord_3919086) baseStart_3919086 baseEnd_3919086 := by
    simpa [prefixWord, tailWord_3919086, baseEnd_3919086] using wordTrace_append hprefix tailTrace_3919086
  have hstable : (prefixWord ++ tailWord_3919086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919086).length < 2 ^ (prefixWord ++ tailWord_3919086).sum := by decide
  have hdescent : baseEnd_3919086 < baseStart_3919086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919116 : List Nat := [2, 2, 1, 2, 2, 3, 1, 4, 1, 4]
def baseStart_3919116 : Nat := 118140960795 + 3919116 * 2 ^ 59
def prefixEnd_3919116 : Nat := 4983230072969 + 3 ^ 40 * 3919116 * 2
def baseEnd_3919116 : Nat := 1341593499150795782884213

theorem tailTrace_3919116 : CollatzResearch.WordTrace tailWord_3919116 prefixEnd_3919116 1341593499150795782884213 := by
  unfold tailWord_3919116
  simp only [CollatzResearch.WordTrace]
  refine ⟨71470951834859769284844601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95294602446479692379792801 71470951834859769284844601)
  ·
    refine ⟨53603213876144826963633451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71470951834859769284844601 53603213876144826963633451)
    ·
      refine ⟨80404820814217240445450177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53603213876144826963633451 80404820814217240445450177)
      ·
        refine ⟨60303615610662930334087633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80404820814217240445450177 60303615610662930334087633)
        ·
          refine ⟨45227711707997197750565725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60303615610662930334087633 45227711707997197750565725)
          ·
            refine ⟨16960391890498949156462147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45227711707997197750565725 16960391890498949156462147)
            ·
              refine ⟨25440587835748423734693221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16960391890498949156462147 25440587835748423734693221)
              ·
                refine ⟨4770110219202829450254979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25440587835748423734693221 4770110219202829450254979)
                ·
                  refine ⟨7155165328804244175382469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4770110219202829450254979 7155165328804244175382469)
                  ·
                    refine ⟨1341593499150795782884213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7155165328804244175382469 1341593499150795782884213)
                    ·
                      rfl

theorem cell22_3919116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 1, 4].length) (baseStart_3919116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3919116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3919116 prefixEnd_3919116 := by exact prefixLift 3919116
  have htrace : WordTrace (prefixWord ++ tailWord_3919116) baseStart_3919116 baseEnd_3919116 := by
    simpa [prefixWord, tailWord_3919116, baseEnd_3919116] using wordTrace_append hprefix tailTrace_3919116
  have hstable : (prefixWord ++ tailWord_3919116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919116).length < 2 ^ (prefixWord ++ tailWord_3919116).sum := by decide
  have hdescent : baseEnd_3919116 < baseStart_3919116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919133 : List Nat := [1, 4, 2, 3, 1, 1, 2, 3, 1, 4]
def baseStart_3919133 : Nat := 118140960795 + 3919133 * 2 ^ 59
def prefixEnd_3919133 : Nat := 4983230072969 + 3 ^ 40 * 3919133 * 2
def baseEnd_3919133 : Nat := 1341599318598213405209161

theorem tailTrace_3919133 : CollatzResearch.WordTrace tailWord_3919133 prefixEnd_3919133 1341599318598213405209161 := by
  unfold tailWord_3919133
  simp only [CollatzResearch.WordTrace]
  refine ⟨142942523710657950473058053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95295015807105300315372035 142942523710657950473058053)
  ·
    refine ⟨26801723195748365713698385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142942523710657950473058053 26801723195748365713698385)
    ·
      refine ⟨20101292396811274285273789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26801723195748365713698385 20101292396811274285273789)
      ·
        refine ⟨7537984648804227856977671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20101292396811274285273789 7537984648804227856977671)
        ·
          refine ⟨11306976973206341785466507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7537984648804227856977671 11306976973206341785466507)
          ·
            refine ⟨16960465459809512678199761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11306976973206341785466507 16960465459809512678199761)
            ·
              refine ⟨12720349094857134508649821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16960465459809512678199761 12720349094857134508649821)
              ·
                refine ⟨4770130910571425440743683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12720349094857134508649821 4770130910571425440743683)
                ·
                  refine ⟨7155196365857138161115525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4770130910571425440743683 7155196365857138161115525)
                  ·
                    refine ⟨1341599318598213405209161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7155196365857138161115525 1341599318598213405209161)
                    ·
                      rfl

theorem cell22_3919133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_3919133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3919133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3919133 prefixEnd_3919133 := by exact prefixLift 3919133
  have htrace : WordTrace (prefixWord ++ tailWord_3919133) baseStart_3919133 baseEnd_3919133 := by
    simpa [prefixWord, tailWord_3919133, baseEnd_3919133] using wordTrace_append hprefix tailTrace_3919133
  have hstable : (prefixWord ++ tailWord_3919133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919133).length < 2 ^ (prefixWord ++ tailWord_3919133).sum := by decide
  have hdescent : baseEnd_3919133 < baseStart_3919133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919210 : List Nat := [3, 1, 3, 3, 3, 1, 1, 7]
def baseStart_3919210 : Nat := 118140960795 + 3919210 * 2 ^ 59
def prefixEnd_3919210 : Nat := 4983230072969 + 3 ^ 40 * 3919210 * 2
def baseEnd_3919210 : Nat := 149069519696867874559325

theorem tailTrace_3919210 : CollatzResearch.WordTrace tailWord_3919210 prefixEnd_3919210 149069519696867874559325 := by
  unfold tailWord_3919210
  simp only [CollatzResearch.WordTrace]
  refine ⟨35736333032844748155902771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95296888087585995082407389 35736333032844748155902771)
  ·
    refine ⟨53604499549267122233854157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35736333032844748155902771 53604499549267122233854157)
    ·
      refine ⟨20101687330975170837695309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53604499549267122233854157 20101687330975170837695309)
      ·
        refine ⟨7538132749115689064135741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20101687330975170837695309 7538132749115689064135741)
        ·
          refine ⟨2826799780918383399050903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7538132749115689064135741 2826799780918383399050903)
          ·
            refine ⟨4240199671377575098576355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2826799780918383399050903 4240199671377575098576355)
            ·
              refine ⟨6360299507066362647864533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4240199671377575098576355 6360299507066362647864533)
              ·
                refine ⟨149069519696867874559325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6360299507066362647864533 149069519696867874559325)
                ·
                  rfl

theorem cell22_3919210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 7].length) (baseStart_3919210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3919210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3919210 prefixEnd_3919210 := by exact prefixLift 3919210
  have htrace : WordTrace (prefixWord ++ tailWord_3919210) baseStart_3919210 baseEnd_3919210 := by
    simpa [prefixWord, tailWord_3919210, baseEnd_3919210] using wordTrace_append hprefix tailTrace_3919210
  have hstable : (prefixWord ++ tailWord_3919210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919210).length < 2 ^ (prefixWord ++ tailWord_3919210).sum := by decide
  have hdescent : baseEnd_3919210 < baseStart_3919210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919272 : List Nat := [2, 1, 6, 1, 2, 1, 3, 1, 5]
def baseStart_3919272 : Nat := 118140960795 + 3919272 * 2 ^ 59
def prefixEnd_3919272 : Nat := 4983230072969 + 3 ^ 40 * 3919272 * 2
def baseEnd_3919272 : Nat := 447215633712954458661245

theorem tailTrace_3919272 : CollatzResearch.WordTrace tailWord_3919272 prefixEnd_3919272 447215633712954458661245 := by
  unfold tailWord_3919272
  simp only [CollatzResearch.WordTrace]
  refine ⟨71473796728577188606184035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95298395638102918141578713 71473796728577188606184035)
  ·
    refine ⟨107210695092865782909276053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71473796728577188606184035 107210695092865782909276053)
    ·
      refine ⟨5025501332478083573872315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 107210695092865782909276053 5025501332478083573872315)
      ·
        refine ⟨7538251998717125360808473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5025501332478083573872315 7538251998717125360808473)
        ·
          refine ⟨5653688999037844020606355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7538251998717125360808473 5653688999037844020606355)
          ·
            refine ⟨8480533498556766030909533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5653688999037844020606355 8480533498556766030909533)
            ·
              refine ⟨3180200061958787261591075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8480533498556766030909533 3180200061958787261591075)
              ·
                refine ⟨4770300092938180892386613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3180200061958787261591075 4770300092938180892386613)
                ·
                  refine ⟨447215633712954458661245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4770300092938180892386613 447215633712954458661245)
                  ·
                    rfl

theorem cell22_3919272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 5].length) (baseStart_3919272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3919272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3919272 prefixEnd_3919272 := by exact prefixLift 3919272
  have htrace : WordTrace (prefixWord ++ tailWord_3919272) baseStart_3919272 baseEnd_3919272 := by
    simpa [prefixWord, tailWord_3919272, baseEnd_3919272] using wordTrace_append hprefix tailTrace_3919272
  have hstable : (prefixWord ++ tailWord_3919272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919272).length < 2 ^ (prefixWord ++ tailWord_3919272).sum := by decide
  have hdescent : baseEnd_3919272 < baseStart_3919272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919285 : List Nat := [1, 3, 3, 2, 2, 2, 2, 2, 1, 4]
def baseStart_3919285 : Nat := 118140960795 + 3919285 * 2 ^ 59
def prefixEnd_3919285 : Nat := 4983230072969 + 3 ^ 40 * 3919285 * 2
def baseEnd_3919285 : Nat := 1341651351304535675408695

theorem tailTrace_3919285 : CollatzResearch.WordTrace tailWord_3919285 prefixEnd_3919285 1341651351304535675408695 := by
  unfold tailWord_3919285
  simp only [CollatzResearch.WordTrace]
  refine ⟨142948067606107280432591309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95298711737404853621727539 142948067606107280432591309)
  ·
    refine ⟨53605525352290230162221741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142948067606107280432591309 53605525352290230162221741)
    ·
      refine ⟨20102072007108836310833153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53605525352290230162221741 20102072007108836310833153)
      ·
        refine ⟨15076554005331627233124865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20102072007108836310833153 15076554005331627233124865)
        ·
          refine ⟨11307415503998720424843649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15076554005331627233124865 11307415503998720424843649)
          ·
            refine ⟨8480561627999040318632737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11307415503998720424843649 8480561627999040318632737)
            ·
              refine ⟨6360421220999280238974553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8480561627999040318632737 6360421220999280238974553)
              ·
                refine ⟨4770315915749460179230915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6360421220999280238974553 4770315915749460179230915)
                ·
                  refine ⟨7155473873624190268846373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4770315915749460179230915 7155473873624190268846373)
                  ·
                    refine ⟨1341651351304535675408695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7155473873624190268846373 1341651351304535675408695)
                    ·
                      rfl

theorem cell22_3919285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_3919285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3919285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3919285 prefixEnd_3919285 := by exact prefixLift 3919285
  have htrace : WordTrace (prefixWord ++ tailWord_3919285) baseStart_3919285 baseEnd_3919285 := by
    simpa [prefixWord, tailWord_3919285, baseEnd_3919285] using wordTrace_append hprefix tailTrace_3919285
  have hstable : (prefixWord ++ tailWord_3919285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919285).length < 2 ^ (prefixWord ++ tailWord_3919285).sum := by decide
  have hdescent : baseEnd_3919285 < baseStart_3919285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919296 : List Nat := [2, 1, 1, 2, 3, 1, 4, 1, 1, 6]
def baseStart_3919296 : Nat := 118140960795 + 3919296 * 2 ^ 59
def prefixEnd_3919296 : Nat := 4983230072969 + 3 ^ 40 * 3919296 * 2
def baseEnd_3919296 : Nat := 1341655116829335313383661

theorem tailTrace_3919296 : CollatzResearch.WordTrace tailWord_3919296 prefixEnd_3919296 1341655116829335313383661 := by
  unfold tailWord_3919296
  simp only [CollatzResearch.WordTrace]
  refine ⟨71474234404533714655620871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95298979206044952874161161 71474234404533714655620871)
  ·
    refine ⟨107211351606800571983431307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71474234404533714655620871 107211351606800571983431307)
    ·
      refine ⟨160817027410200857975146961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107211351606800571983431307 160817027410200857975146961)
      ·
        refine ⟨120612770557650643481360221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160817027410200857975146961 120612770557650643481360221)
        ·
          refine ⟨45229788959118991305510083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120612770557650643481360221 45229788959118991305510083)
          ·
            refine ⟨67844683438678486958265125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45229788959118991305510083 67844683438678486958265125)
            ·
              refine ⟨12720878144752216304674711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67844683438678486958265125 12720878144752216304674711)
              ·
                refine ⟨19081317217128324457012067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12720878144752216304674711 19081317217128324457012067)
                ·
                  refine ⟨28621975825692486685518101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19081317217128324457012067 28621975825692486685518101)
                  ·
                    refine ⟨1341655116829335313383661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28621975825692486685518101 1341655116829335313383661)
                    ·
                      rfl

theorem cell22_3919296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 1, 6].length) (baseStart_3919296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3919296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3919296 prefixEnd_3919296 := by exact prefixLift 3919296
  have htrace : WordTrace (prefixWord ++ tailWord_3919296) baseStart_3919296 baseEnd_3919296 := by
    simpa [prefixWord, tailWord_3919296, baseEnd_3919296] using wordTrace_append hprefix tailTrace_3919296
  have hstable : (prefixWord ++ tailWord_3919296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919296).length < 2 ^ (prefixWord ++ tailWord_3919296).sum := by decide
  have hdescent : baseEnd_3919296 < baseStart_3919296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919343 : List Nat := [1, 1, 2, 1, 4, 1, 2, 4, 3, 3]
def baseStart_3919343 : Nat := 118140960795 + 3919343 * 2 ^ 59
def prefixEnd_3919343 : Nat := 4983230072969 + 3 ^ 40 * 3919343 * 2
def baseEnd_3919343 : Nat := 1341671205889842857458517

theorem tailTrace_3919343 : CollatzResearch.WordTrace tailWord_3919343 prefixEnd_3919343 1341671205889842857458517 := by
  unfold tailWord_3919343
  simp only [CollatzResearch.WordTrace]
  refine ⟨142950183039897156338202683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95300122026598104225468455 142950183039897156338202683)
  ·
    refine ⟨214425274559845734507304025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142950183039897156338202683 214425274559845734507304025)
    ·
      refine ⟨160818955919884300880478019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214425274559845734507304025 160818955919884300880478019)
      ·
        refine ⟨241228433879826451320717029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160818955919884300880478019 241228433879826451320717029)
        ·
          refine ⟨45230331352467459622634443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 241228433879826451320717029 45230331352467459622634443)
          ·
            refine ⟨67845497028701189433951665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45230331352467459622634443 67845497028701189433951665)
            ·
              refine ⟨50884122771525892075463749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67845497028701189433951665 50884122771525892075463749)
              ·
                refine ⟨9540773019661104764149453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50884122771525892075463749 9540773019661104764149453)
                ·
                  refine ⟨3577789882372914286556045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9540773019661104764149453 3577789882372914286556045)
                  ·
                    refine ⟨1341671205889842857458517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3577789882372914286556045 1341671205889842857458517)
                    ·
                      rfl

theorem cell22_3919343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 3, 3].length) (baseStart_3919343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3919343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3919343 prefixEnd_3919343 := by exact prefixLift 3919343
  have htrace : WordTrace (prefixWord ++ tailWord_3919343) baseStart_3919343 baseEnd_3919343 := by
    simpa [prefixWord, tailWord_3919343, baseEnd_3919343] using wordTrace_append hprefix tailTrace_3919343
  have hstable : (prefixWord ++ tailWord_3919343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919343).length < 2 ^ (prefixWord ++ tailWord_3919343).sum := by decide
  have hdescent : baseEnd_3919343 < baseStart_3919343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919356 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 9]
def baseStart_3919356 : Nat := 118140960795 + 3919356 * 2 ^ 59
def prefixEnd_3919356 : Nat := 4983230072969 + 3 ^ 40 * 3919356 * 2
def baseEnd_3919356 : Nat := 447225218685171718961159

theorem tailTrace_3919356 : CollatzResearch.WordTrace tailWord_3919356 prefixEnd_3919356 447225218685171718961159 := by
  unfold tailWord_3919356
  simp only [CollatzResearch.WordTrace]
  refine ⟨71475328594425029779212961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95300438125900039705617281 71475328594425029779212961)
  ·
    refine ⟨53606496445818772334409721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71475328594425029779212961 53606496445818772334409721)
    ·
      refine ⟨40204872334364079250807291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53606496445818772334409721 40204872334364079250807291)
      ·
        refine ⟨60307308501546118876210937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40204872334364079250807291 60307308501546118876210937)
        ·
          refine ⟨45230481376159589157158203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60307308501546118876210937 45230481376159589157158203)
          ·
            refine ⟨67845722064239383735737305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45230481376159589157158203 67845722064239383735737305)
            ·
              refine ⟨50884291548179537801802979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67845722064239383735737305 50884291548179537801802979)
              ·
                refine ⟨76326437322269306702704469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50884291548179537801802979 76326437322269306702704469)
                ·
                  refine ⟨447225218685171718961159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 76326437322269306702704469 447225218685171718961159)
                  ·
                    rfl

theorem cell22_3919356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 9].length) (baseStart_3919356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3919356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3919356 prefixEnd_3919356 := by exact prefixLift 3919356
  have htrace : WordTrace (prefixWord ++ tailWord_3919356) baseStart_3919356 baseEnd_3919356 := by
    simpa [prefixWord, tailWord_3919356, baseEnd_3919356] using wordTrace_append hprefix tailTrace_3919356
  have hstable : (prefixWord ++ tailWord_3919356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919356).length < 2 ^ (prefixWord ++ tailWord_3919356).sum := by decide
  have hdescent : baseEnd_3919356 < baseStart_3919356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919388 : List Nat := [2, 2, 3, 1, 2, 1, 3, 1, 2, 5]
def baseStart_3919388 : Nat := 118140960795 + 3919388 * 2 ^ 59
def prefixEnd_3919388 : Nat := 4983230072969 + 3 ^ 40 * 3919388 * 2
def baseEnd_3919388 : Nat := 1341686610309477740083379

theorem tailTrace_3919388 : CollatzResearch.WordTrace tailWord_3919388 prefixEnd_3919388 1341686610309477740083379 := by
  unfold tailWord_3919388
  simp only [CollatzResearch.WordTrace]
  refine ⟨71475912162367064511795409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95301216216489419349060545 71475912162367064511795409)
  ·
    refine ⟨53606934121775298383846557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71475912162367064511795409 53606934121775298383846557)
    ·
      refine ⟨20102600295665736893942459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53606934121775298383846557 20102600295665736893942459)
      ·
        refine ⟨30153900443498605340913689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20102600295665736893942459 30153900443498605340913689)
        ·
          refine ⟨22615425332623954005685267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30153900443498605340913689 22615425332623954005685267)
          ·
            refine ⟨33923137998935931008527901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22615425332623954005685267 33923137998935931008527901)
            ·
              refine ⟨12721176749600974128197963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33923137998935931008527901 12721176749600974128197963)
              ·
                refine ⟨19081765124401461192296945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12721176749600974128197963 19081765124401461192296945)
                ·
                  refine ⟨14311323843301095894222709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19081765124401461192296945 14311323843301095894222709)
                  ·
                    refine ⟨1341686610309477740083379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14311323843301095894222709 1341686610309477740083379)
                    ·
                      rfl

theorem cell22_3919388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_3919388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3919388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3919388 prefixEnd_3919388 := by exact prefixLift 3919388
  have htrace : WordTrace (prefixWord ++ tailWord_3919388) baseStart_3919388 baseEnd_3919388 := by
    simpa [prefixWord, tailWord_3919388, baseEnd_3919388] using wordTrace_append hprefix tailTrace_3919388
  have hstable : (prefixWord ++ tailWord_3919388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919388).length < 2 ^ (prefixWord ++ tailWord_3919388).sum := by decide
  have hdescent : baseEnd_3919388 < baseStart_3919388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919450 : List Nat := [3, 1, 1, 2, 1, 1, 1, 7, 2, 3]
def baseStart_3919450 : Nat := 118140960795 + 3919450 * 2 ^ 59
def prefixEnd_3919450 : Nat := 4983230072969 + 3 ^ 40 * 3919450 * 2
def baseEnd_3919450 : Nat := 1341707834176530245033189

theorem tailTrace_3919450 : CollatzResearch.WordTrace tailWord_3919450 prefixEnd_3919450 1341707834176530245033189 := by
  unfold tailWord_3919450
  simp only [CollatzResearch.WordTrace]
  refine ⟨35738521412627378403086951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95302723767006342408231869 35738521412627378403086951)
  ·
    refine ⟨53607782118941067604630427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35738521412627378403086951 53607782118941067604630427)
    ·
      refine ⟨80411673178411601406945641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53607782118941067604630427 80411673178411601406945641)
      ·
        refine ⟨60308754883808701055209231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80411673178411601406945641 60308754883808701055209231)
        ·
          refine ⟨90463132325713051582813847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60308754883808701055209231 90463132325713051582813847)
          ·
            refine ⟨135694698488569577374220771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90463132325713051582813847 135694698488569577374220771)
            ·
              refine ⟨203542047732854366061331157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135694698488569577374220771 203542047732854366061331157)
              ·
                refine ⟨4770516743738774204562449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 203542047732854366061331157 4770516743738774204562449)
                ·
                  refine ⟨3577887557804080653421837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4770516743738774204562449 3577887557804080653421837)
                  ·
                    refine ⟨1341707834176530245033189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3577887557804080653421837 1341707834176530245033189)
                    ·
                      rfl

theorem cell22_3919450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 2, 3].length) (baseStart_3919450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3919450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3919450 prefixEnd_3919450 := by exact prefixLift 3919450
  have htrace : WordTrace (prefixWord ++ tailWord_3919450) baseStart_3919450 baseEnd_3919450 := by
    simpa [prefixWord, tailWord_3919450, baseEnd_3919450] using wordTrace_append hprefix tailTrace_3919450
  have hstable : (prefixWord ++ tailWord_3919450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919450).length < 2 ^ (prefixWord ++ tailWord_3919450).sum := by decide
  have hdescent : baseEnd_3919450 < baseStart_3919450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919469 : List Nat := [1, 5, 1, 1, 4, 2, 1, 3, 4]
def baseStart_3919469 : Nat := 118140960795 + 3919469 * 2 ^ 59
def prefixEnd_3919469 : Nat := 4983230072969 + 3 ^ 40 * 3919469 * 2
def baseEnd_3919469 : Nat := 447238112754940176269377

theorem tailTrace_3919469 : CollatzResearch.WordTrace tailWord_3919469 prefixEnd_3919469 447238112754940176269377 := by
  unfold tailWord_3919469
  simp only [CollatzResearch.WordTrace]
  refine ⟨142954778637440679857289461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95303185758293786571526307 142954778637440679857289461)
  ·
    refine ⟨13402010497260063736620887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142954778637440679857289461 13402010497260063736620887)
    ·
      refine ⟨20103015745890095604931331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13402010497260063736620887 20103015745890095604931331)
      ·
        refine ⟨30154523618835143407396997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20103015745890095604931331 30154523618835143407396997)
        ·
          refine ⟨5653973178531589388886937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30154523618835143407396997 5653973178531589388886937)
          ·
            refine ⟨4240479883898692041665203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5653973178531589388886937 4240479883898692041665203)
            ·
              refine ⟨6360719825848038062497805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4240479883898692041665203 6360719825848038062497805)
              ·
                refine ⟨2385269934693014273436677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6360719825848038062497805 2385269934693014273436677)
                ·
                  refine ⟨447238112754940176269377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2385269934693014273436677 447238112754940176269377)
                  ·
                    rfl

theorem cell22_3919469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_3919469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3919469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3919469 prefixEnd_3919469 := by exact prefixLift 3919469
  have htrace : WordTrace (prefixWord ++ tailWord_3919469) baseStart_3919469 baseEnd_3919469 := by
    simpa [prefixWord, tailWord_3919469, baseEnd_3919469] using wordTrace_append hprefix tailTrace_3919469
  have hstable : (prefixWord ++ tailWord_3919469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919469).length < 2 ^ (prefixWord ++ tailWord_3919469).sum := by decide
  have hdescent : baseEnd_3919469 < baseStart_3919469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919493 : List Nat := [1, 3, 1, 1, 4, 1, 2, 1, 2, 6]
def baseStart_3919493 : Nat := 118140960795 + 3919493 * 2 ^ 59
def prefixEnd_3919493 : Nat := 4983230072969 + 3 ^ 40 * 3919493 * 2
def baseEnd_3919493 : Nat := 1341722553955292466208057

theorem tailTrace_3919493 : CollatzResearch.WordTrace tailWord_3919493 prefixEnd_3919493 1341722553955292466208057 := by
  unfold tailWord_3919493
  simp only [CollatzResearch.WordTrace]
  refine ⟨142955653989353731956163133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95303769326235821304108755 142955653989353731956163133)
  ·
    refine ⟨53608370246007649483561175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142955653989353731956163133 53608370246007649483561175)
    ·
      refine ⟨80412555369011474225341763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53608370246007649483561175 80412555369011474225341763)
      ·
        refine ⟨120618833053517211338012645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80412555369011474225341763 120618833053517211338012645)
        ·
          refine ⟨22616031197534477125877371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120618833053517211338012645 22616031197534477125877371)
          ·
            refine ⟨33924046796301715688816057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22616031197534477125877371 33924046796301715688816057)
            ·
              refine ⟨25443035097226286766612043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33924046796301715688816057 25443035097226286766612043)
              ·
                refine ⟨38164552645839430149918065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25443035097226286766612043 38164552645839430149918065)
                ·
                  refine ⟨28623414484379572612438549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38164552645839430149918065 28623414484379572612438549)
                  ·
                    refine ⟨1341722553955292466208057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28623414484379572612438549 1341722553955292466208057)
                    ·
                      rfl

theorem cell22_3919493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_3919493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3919493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3919493 prefixEnd_3919493 := by exact prefixLift 3919493
  have htrace : WordTrace (prefixWord ++ tailWord_3919493) baseStart_3919493 baseEnd_3919493 := by
    simpa [prefixWord, tailWord_3919493, baseEnd_3919493] using wordTrace_append hprefix tailTrace_3919493
  have hstable : (prefixWord ++ tailWord_3919493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919493).length < 2 ^ (prefixWord ++ tailWord_3919493).sum := by decide
  have hdescent : baseEnd_3919493 < baseStart_3919493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919546 : List Nat := [3, 1, 1, 1, 2, 6, 2, 2, 1, 3]
def baseStart_3919546 : Nat := 118140960795 + 3919546 * 2 ^ 59
def prefixEnd_3919546 : Nat := 4983230072969 + 3 ^ 40 * 3919546 * 2
def baseEnd_3919546 : Nat := 1341740696938417994632895

theorem tailTrace_3919546 : CollatzResearch.WordTrace tailWord_3919546 prefixEnd_3919546 1341740696938417994632895 := by
  unfold tailWord_3919546
  simp only [CollatzResearch.WordTrace]
  refine ⟨35739396764540430501960623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95305058038774481338561661 35739396764540430501960623)
  ·
    refine ⟨53609095146810645752940935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35739396764540430501960623 53609095146810645752940935)
    ·
      refine ⟨80413642720215968629411403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53609095146810645752940935 80413642720215968629411403)
      ·
        refine ⟨120620464080323952944117105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80413642720215968629411403 120620464080323952944117105)
        ·
          refine ⟨90465348060242964708087829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120620464080323952944117105 90465348060242964708087829)
          ·
            refine ⟨4240563190323888970691617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 90465348060242964708087829 4240563190323888970691617)
            ·
              refine ⟨3180422392742916728018713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4240563190323888970691617 3180422392742916728018713)
              ·
                refine ⟨2385316794557187546014035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3180422392742916728018713 2385316794557187546014035)
                ·
                  refine ⟨3577975191835781319021053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2385316794557187546014035 3577975191835781319021053)
                  ·
                    refine ⟨1341740696938417994632895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3577975191835781319021053 1341740696938417994632895)
                    ·
                      rfl

theorem cell22_3919546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 2, 1, 3].length) (baseStart_3919546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3919546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3919546 prefixEnd_3919546 := by exact prefixLift 3919546
  have htrace : WordTrace (prefixWord ++ tailWord_3919546) baseStart_3919546 baseEnd_3919546 := by
    simpa [prefixWord, tailWord_3919546, baseEnd_3919546] using wordTrace_append hprefix tailTrace_3919546
  have hstable : (prefixWord ++ tailWord_3919546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919546).length < 2 ^ (prefixWord ++ tailWord_3919546).sum := by decide
  have hdescent : baseEnd_3919546 < baseStart_3919546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919570 : List Nat := [3, 2, 2, 2, 2, 1, 1, 1, 8]
def baseStart_3919570 : Nat := 118140960795 + 3919570 * 2 ^ 59
def prefixEnd_3919570 : Nat := 4983230072969 + 3 ^ 40 * 3919570 * 2
def baseEnd_3919570 : Nat := 447249637542963310677607

theorem tailTrace_3919570 : CollatzResearch.WordTrace tailWord_3919570 prefixEnd_3919570 447249637542963310677607 := by
  unfold tailWord_3919570
  simp only [CollatzResearch.WordTrace]
  refine ⟨35739615602518693526679041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95305641606716516071144109 35739615602518693526679041)
  ·
    refine ⟨26804711701889020145009281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35739615602518693526679041 26804711701889020145009281)
    ·
      refine ⟨20103533776416765108756961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26804711701889020145009281 20103533776416765108756961)
      ·
        refine ⟨15077650332312573831567721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20103533776416765108756961 15077650332312573831567721)
        ·
          refine ⟨11308237749234430373675791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15077650332312573831567721 11308237749234430373675791)
          ·
            refine ⟨16962356623851645560513687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11308237749234430373675791 16962356623851645560513687)
            ·
              refine ⟨25443534935777468340770531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16962356623851645560513687 25443534935777468340770531)
              ·
                refine ⟨38165302403666202511155797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25443534935777468340770531 38165302403666202511155797)
                ·
                  refine ⟨447249637542963310677607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38165302403666202511155797 447249637542963310677607)
                  ·
                    rfl

theorem cell22_3919570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_3919570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3919570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3919570 prefixEnd_3919570 := by exact prefixLift 3919570
  have htrace : WordTrace (prefixWord ++ tailWord_3919570) baseStart_3919570 baseEnd_3919570 := by
    simpa [prefixWord, tailWord_3919570, baseEnd_3919570] using wordTrace_append hprefix tailTrace_3919570
  have hstable : (prefixWord ++ tailWord_3919570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919570).length < 2 ^ (prefixWord ++ tailWord_3919570).sum := by decide
  have hdescent : baseEnd_3919570 < baseStart_3919570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919572 : List Nat := [2, 4, 1, 3, 1, 1, 2, 1, 3, 4]
def baseStart_3919572 : Nat := 118140960795 + 3919572 * 2 ^ 59
def prefixEnd_3919572 : Nat := 4983230072969 + 3 ^ 40 * 3919572 * 2
def baseEnd_3919572 : Nat := 1341749597269762593482815

theorem tailTrace_3919572 : CollatzResearch.WordTrace tailWord_3919572 prefixEnd_3919572 1341749597269762593482815 := by
  unfold tailWord_3919572
  simp only [CollatzResearch.WordTrace]
  refine ⟨71479267678033764224144485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95305690237378352298859313 71479267678033764224144485)
  ·
    refine ⟨13402362689631330792027091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71479267678033764224144485 13402362689631330792027091)
    ·
      refine ⟨20103544034446996188040637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13402362689631330792027091 20103544034446996188040637)
      ·
        refine ⟨7538829012917623570515239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20103544034446996188040637 7538829012917623570515239)
        ·
          refine ⟨11308243519376435355772859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7538829012917623570515239 11308243519376435355772859)
          ·
            refine ⟨16962365279064653033659289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11308243519376435355772859 16962365279064653033659289)
            ·
              refine ⟨12721773959298489775244467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16962365279064653033659289 12721773959298489775244467)
              ·
                refine ⟨19082660938947734662866701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12721773959298489775244467 19082660938947734662866701)
                ·
                  refine ⟨7155997852105400498575013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19082660938947734662866701 7155997852105400498575013)
                  ·
                    refine ⟨1341749597269762593482815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7155997852105400498575013 1341749597269762593482815)
                    ·
                      rfl

theorem cell22_3919572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_3919572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3919572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3919572 prefixEnd_3919572 := by exact prefixLift 3919572
  have htrace : WordTrace (prefixWord ++ tailWord_3919572) baseStart_3919572 baseEnd_3919572 := by
    simpa [prefixWord, tailWord_3919572, baseEnd_3919572] using wordTrace_append hprefix tailTrace_3919572
  have hstable : (prefixWord ++ tailWord_3919572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919572).length < 2 ^ (prefixWord ++ tailWord_3919572).sum := by decide
  have hdescent : baseEnd_3919572 < baseStart_3919572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919602 : List Nat := [3, 2, 1, 3, 1, 1, 3, 1, 4, 3]
def baseStart_3919602 : Nat := 118140960795 + 3919602 * 2 ^ 59
def prefixEnd_3919602 : Nat := 4983230072969 + 3 ^ 40 * 3919602 * 2
def baseEnd_3919602 : Nat := 1341759866882852515232723

theorem tailTrace_3919602 : CollatzResearch.WordTrace tailWord_3919602 prefixEnd_3919602 1341759866882852515232723 := by
  unfold tailWord_3919602
  simp only [CollatzResearch.WordTrace]
  refine ⟨35739907386489710892970265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95306419697305895714587373 35739907386489710892970265)
  ·
    refine ⟨26804930539867283169727699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35739907386489710892970265 26804930539867283169727699)
    ·
      refine ⟨40207395809800924754591549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26804930539867283169727699 40207395809800924754591549)
      ·
        refine ⟨15077773428675346782971831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40207395809800924754591549 15077773428675346782971831)
        ·
          refine ⟨22616660143013020174457747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15077773428675346782971831 22616660143013020174457747)
          ·
            refine ⟨33924990214519530261686621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22616660143013020174457747 33924990214519530261686621)
            ·
              refine ⟨12721871330444823848132483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33924990214519530261686621 12721871330444823848132483)
              ·
                refine ⟨19082806995667235772198725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12721871330444823848132483 19082806995667235772198725)
                ·
                  refine ⟨3578026311687606707287261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19082806995667235772198725 3578026311687606707287261)
                  ·
                    refine ⟨1341759866882852515232723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3578026311687606707287261 1341759866882852515232723)
                    ·
                      rfl

theorem cell22_3919602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_3919602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3919602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3919602 prefixEnd_3919602 := by exact prefixLift 3919602
  have htrace : WordTrace (prefixWord ++ tailWord_3919602) baseStart_3919602 baseEnd_3919602 := by
    simpa [prefixWord, tailWord_3919602, baseEnd_3919602] using wordTrace_append hprefix tailTrace_3919602
  have hstable : (prefixWord ++ tailWord_3919602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919602).length < 2 ^ (prefixWord ++ tailWord_3919602).sum := by decide
  have hdescent : baseEnd_3919602 < baseStart_3919602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919604 : List Nat := [2, 6, 1, 1, 1, 1, 1, 3, 6]
def baseStart_3919604 : Nat := 118140960795 + 3919604 * 2 ^ 59
def prefixEnd_3919604 : Nat := 4983230072969 + 3 ^ 40 * 3919604 * 2
def baseEnd_3919604 : Nat := 447253517174575058894239

theorem tailTrace_3919604 : CollatzResearch.WordTrace tailWord_3919604 prefixEnd_3919604 447253517174575058894239 := by
  unfold tailWord_3919604
  simp only [CollatzResearch.WordTrace]
  refine ⟨71479851245975798956726933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95306468327967731942302577 71479851245975798956726933)
  ·
    refine ⟨3350618027155115576096575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 71479851245975798956726933 3350618027155115576096575)
    ·
      refine ⟨5025927040732673364144863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3350618027155115576096575 5025927040732673364144863)
      ·
        refine ⟨7538890561099010046217295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5025927040732673364144863 7538890561099010046217295)
        ·
          refine ⟨11308335841648515069325943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7538890561099010046217295 11308335841648515069325943)
          ·
            refine ⟨16962503762472772603988915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11308335841648515069325943 16962503762472772603988915)
            ·
              refine ⟨25443755643709158905983373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16962503762472772603988915 25443755643709158905983373)
              ·
                refine ⟨9541408366390934589743765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25443755643709158905983373 9541408366390934589743765)
                ·
                  refine ⟨447253517174575058894239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9541408366390934589743765 447253517174575058894239)
                  ·
                    rfl

theorem cell22_3919604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_3919604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3919604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3919604 prefixEnd_3919604 := by exact prefixLift 3919604
  have htrace : WordTrace (prefixWord ++ tailWord_3919604) baseStart_3919604 baseEnd_3919604 := by
    simpa [prefixWord, tailWord_3919604, baseEnd_3919604] using wordTrace_append hprefix tailTrace_3919604
  have hstable : (prefixWord ++ tailWord_3919604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919604).length < 2 ^ (prefixWord ++ tailWord_3919604).sum := by decide
  have hdescent : baseEnd_3919604 < baseStart_3919604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919660 : List Nat := [2, 2, 1, 1, 1, 5, 2, 1, 7]
def baseStart_3919660 : Nat := 118140960795 + 3919660 * 2 ^ 59
def prefixEnd_3919660 : Nat := 4983230072969 + 3 ^ 40 * 3919660 * 2
def baseEnd_3919660 : Nat := 447259907156053232427515

theorem tailTrace_3919660 : CollatzResearch.WordTrace tailWord_3919660 prefixEnd_3919660 447259907156053232427515 := by
  unfold tailWord_3919660
  simp only [CollatzResearch.WordTrace]
  refine ⟨71480872489874359738746217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95307829986499146318328289 71480872489874359738746217)
  ·
    refine ⟨53610654367405769804059663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71480872489874359738746217 53610654367405769804059663)
    ·
      refine ⟨80415981551108654706089495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53610654367405769804059663 80415981551108654706089495)
      ·
        refine ⟨120623972326662982059134243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80415981551108654706089495 120623972326662982059134243)
        ·
          refine ⟨180935958489994473088701365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120623972326662982059134243 180935958489994473088701365)
          ·
            refine ⟨16962746108436981852065753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 180935958489994473088701365 16962746108436981852065753)
            ·
              refine ⟨12722059581327736389049315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16962746108436981852065753 12722059581327736389049315)
              ·
                refine ⟨19083089371991604583573973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12722059581327736389049315 19083089371991604583573973)
                ·
                  refine ⟨447259907156053232427515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19083089371991604583573973 447259907156053232427515)
                  ·
                    rfl

theorem cell22_3919660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 7].length) (baseStart_3919660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3919660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3919660 prefixEnd_3919660 := by exact prefixLift 3919660
  have htrace : WordTrace (prefixWord ++ tailWord_3919660) baseStart_3919660 baseEnd_3919660 := by
    simpa [prefixWord, tailWord_3919660, baseEnd_3919660] using wordTrace_append hprefix tailTrace_3919660
  have hstable : (prefixWord ++ tailWord_3919660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919660).length < 2 ^ (prefixWord ++ tailWord_3919660).sum := by decide
  have hdescent : baseEnd_3919660 < baseStart_3919660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919715 : List Nat := [1, 1, 1, 5, 5, 1, 2, 2, 1, 3]
def baseStart_3919715 : Nat := 118140960795 + 3919715 * 2 ^ 59
def prefixEnd_3919715 : Nat := 4983230072969 + 3 ^ 40 * 3919715 * 2
def baseEnd_3919715 : Nat := 1341798549092157887157377

theorem tailTrace_3919715 : CollatzResearch.WordTrace tailWord_3919715 prefixEnd_3919715 1341798549092157887157377 := by
  unfold tailWord_3919715
  simp only [CollatzResearch.WordTrace]
  refine ⟨142963750994549463870744599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95309167329699642580496399 142963750994549463870744599)
  ·
    refine ⟨214445626491824195806116899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142963750994549463870744599 214445626491824195806116899)
    ·
      refine ⟨321668439737736293709175349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214445626491824195806116899 321668439737736293709175349)
      ·
        refine ⟨30156416225412777535235189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 321668439737736293709175349 30156416225412777535235189)
        ·
          refine ⟨2827164021132447893928299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30156416225412777535235189 2827164021132447893928299)
          ·
            refine ⟨4240746031698671840892449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2827164021132447893928299 4240746031698671840892449)
            ·
              refine ⟨3180559523774003880669337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4240746031698671840892449 3180559523774003880669337)
              ·
                refine ⟨2385419642830502910502003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3180559523774003880669337 2385419642830502910502003)
                ·
                  refine ⟨3578129464245754365753005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2385419642830502910502003 3578129464245754365753005)
                  ·
                    refine ⟨1341798549092157887157377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3578129464245754365753005 1341798549092157887157377)
                    ·
                      rfl

theorem cell22_3919715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 2, 1, 3].length) (baseStart_3919715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3919715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3919715 prefixEnd_3919715 := by exact prefixLift 3919715
  have htrace : WordTrace (prefixWord ++ tailWord_3919715) baseStart_3919715 baseEnd_3919715 := by
    simpa [prefixWord, tailWord_3919715, baseEnd_3919715] using wordTrace_append hprefix tailTrace_3919715
  have hstable : (prefixWord ++ tailWord_3919715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919715).length < 2 ^ (prefixWord ++ tailWord_3919715).sum := by decide
  have hdescent : baseEnd_3919715 < baseStart_3919715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919737 : List Nat := [1, 2, 1, 3, 2, 2, 4, 1, 1, 5]
def baseStart_3919737 : Nat := 118140960795 + 3919737 * 2 ^ 59
def prefixEnd_3919737 : Nat := 4983230072969 + 3 ^ 40 * 3919737 * 2
def baseEnd_3919737 : Nat := 1341806080141757163107309

theorem tailTrace_3919737 : CollatzResearch.WordTrace tailWord_3919737 prefixEnd_3919737 1341806080141757163107309 := by
  unfold tailWord_3919737
  simp only [CollatzResearch.WordTrace]
  refine ⟨142964553400469761628045465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95309702266979841085363643 142964553400469761628045465)
  ·
    refine ⟨107223415050352321221034099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142964553400469761628045465 107223415050352321221034099)
    ·
      refine ⟨160835122575528481831551149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107223415050352321221034099 160835122575528481831551149)
      ·
        refine ⟨60313170965823180686831681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160835122575528481831551149 60313170965823180686831681)
        ·
          refine ⟨45234878224367385515123761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60313170965823180686831681 45234878224367385515123761)
          ·
            refine ⟨33926158668275539136342821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45234878224367385515123761 33926158668275539136342821)
            ·
              refine ⟨6361154750301663588064279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33926158668275539136342821 6361154750301663588064279)
              ·
                refine ⟨9541732125452495382096419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6361154750301663588064279 9541732125452495382096419)
                ·
                  refine ⟨14312598188178743073144629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9541732125452495382096419 14312598188178743073144629)
                  ·
                    refine ⟨1341806080141757163107309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14312598188178743073144629 1341806080141757163107309)
                    ·
                      rfl

theorem cell22_3919737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 5].length) (baseStart_3919737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3919737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3919737 prefixEnd_3919737 := by exact prefixLift 3919737
  have htrace : WordTrace (prefixWord ++ tailWord_3919737) baseStart_3919737 baseEnd_3919737 := by
    simpa [prefixWord, tailWord_3919737, baseEnd_3919737] using wordTrace_append hprefix tailTrace_3919737
  have hstable : (prefixWord ++ tailWord_3919737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919737).length < 2 ^ (prefixWord ++ tailWord_3919737).sum := by decide
  have hdescent : baseEnd_3919737 < baseStart_3919737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919833 : List Nat := [1, 2, 1, 2, 7, 1, 1, 1, 3, 3]
def baseStart_3919833 : Nat := 118140960795 + 3919833 * 2 ^ 59
def prefixEnd_3919833 : Nat := 4983230072969 + 3 ^ 40 * 3919833 * 2
def baseEnd_3919833 : Nat := 1341838942903644912707015

theorem tailTrace_3919833 : CollatzResearch.WordTrace tailWord_3919833 prefixEnd_3919833 1341838942903644912707015 := by
  unfold tailWord_3919833
  simp only [CollatzResearch.WordTrace]
  refine ⟨142968054808121970023540153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95312036538747980015693435 142968054808121970023540153)
  ·
    refine ⟨107226041106091477517655115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142968054808121970023540153 107226041106091477517655115)
    ·
      refine ⟨160839061659137216276482673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107226041106091477517655115 160839061659137216276482673)
      ·
        refine ⟨120629296244352912207362005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160839061659137216276482673 120629296244352912207362005)
        ·
          refine ⟨2827249130727021379860047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 120629296244352912207362005 2827249130727021379860047)
          ·
            refine ⟨4240873696090532069790071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2827249130727021379860047 4240873696090532069790071)
            ·
              refine ⟨6361310544135798104685107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4240873696090532069790071 6361310544135798104685107)
              ·
                refine ⟨9541965816203697157027661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6361310544135798104685107 9541965816203697157027661)
                ·
                  refine ⟨3578237181076386433885373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9541965816203697157027661 3578237181076386433885373)
                  ·
                    refine ⟨1341838942903644912707015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3578237181076386433885373 1341838942903644912707015)
                    ·
                      rfl

theorem cell22_3919833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 3, 3].length) (baseStart_3919833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3919833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3919833 prefixEnd_3919833 := by exact prefixLift 3919833
  have htrace : WordTrace (prefixWord ++ tailWord_3919833) baseStart_3919833 baseEnd_3919833 := by
    simpa [prefixWord, tailWord_3919833, baseEnd_3919833] using wordTrace_append hprefix tailTrace_3919833
  have hstable : (prefixWord ++ tailWord_3919833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919833).length < 2 ^ (prefixWord ++ tailWord_3919833).sum := by decide
  have hdescent : baseEnd_3919833 < baseStart_3919833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919891 : List Nat := [1, 1, 1, 2, 1, 4, 6, 2, 4]
def baseStart_3919891 : Nat := 118140960795 + 3919891 * 2 ^ 59
def prefixEnd_3919891 : Nat := 4983230072969 + 3 ^ 40 * 3919891 * 2
def baseEnd_3919891 : Nat := 447286265829650698252279

theorem tailTrace_3919891 : CollatzResearch.WordTrace tailWord_3919891 prefixEnd_3919891 447286265829650698252279 := by
  unfold tailWord_3919891
  simp only [CollatzResearch.WordTrace]
  refine ⟨142970170241911845929151527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95313446827941230619434351 142970170241911845929151527)
  ·
    refine ⟨214455255362867768893727291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142970170241911845929151527 214455255362867768893727291)
    ·
      refine ⟨321682883044301653340590937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214455255362867768893727291 321682883044301653340590937)
      ·
        refine ⟨241262162283226240005443203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321682883044301653340590937 241262162283226240005443203)
        ·
          refine ⟨361893243424839360008164805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241262162283226240005443203 361893243424839360008164805)
          ·
            refine ⟨67854983142157380001530901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 361893243424839360008164805 67854983142157380001530901)
            ·
              refine ⟨3180702334788627187571761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67854983142157380001530901 3180702334788627187571761)
              ·
                refine ⟨2385526751091470390678821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3180702334788627187571761 2385526751091470390678821)
                ·
                  refine ⟨447286265829650698252279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2385526751091470390678821 447286265829650698252279)
                  ·
                    rfl

theorem cell22_3919891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 2, 4].length) (baseStart_3919891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3919891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3919891 prefixEnd_3919891 := by exact prefixLift 3919891
  have htrace : WordTrace (prefixWord ++ tailWord_3919891) baseStart_3919891 baseEnd_3919891 := by
    simpa [prefixWord, tailWord_3919891, baseEnd_3919891] using wordTrace_append hprefix tailTrace_3919891
  have hstable : (prefixWord ++ tailWord_3919891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919891).length < 2 ^ (prefixWord ++ tailWord_3919891).sum := by decide
  have hdescent : baseEnd_3919891 < baseStart_3919891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919906 : List Nat := [3, 3, 1, 1, 1, 2, 1, 5, 2, 3]
def baseStart_3919906 : Nat := 118140960795 + 3919906 * 2 ^ 59
def prefixEnd_3919906 : Nat := 4983230072969 + 3 ^ 40 * 3919906 * 2
def baseEnd_3919906 : Nat := 1341863932295497055631791

theorem tailTrace_3919906 : CollatzResearch.WordTrace tailWord_3919906 prefixEnd_3919906 1341863932295497055631791 := by
  unfold tailWord_3919906
  simp only [CollatzResearch.WordTrace]
  refine ⟨35742679334214375872736893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95313811557905002327298381 35742679334214375872736893)
  ·
    refine ⟨13403504750330390952276335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35742679334214375872736893 13403504750330390952276335)
    ·
      refine ⟨20105257125495586428414503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13403504750330390952276335 20105257125495586428414503)
      ·
        refine ⟨30157885688243379642621755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20105257125495586428414503 30157885688243379642621755)
        ·
          refine ⟨45236828532365069463932633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30157885688243379642621755 45236828532365069463932633)
          ·
            refine ⟨33927621399273802097949475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45236828532365069463932633 33927621399273802097949475)
            ·
              refine ⟨50891432098910703146924213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33927621399273802097949475 50891432098910703146924213)
              ·
                refine ⟨4771071759272878420024145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50891432098910703146924213 4771071759272878420024145)
                ·
                  refine ⟨3578303819454658815018109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4771071759272878420024145 3578303819454658815018109)
                  ·
                    refine ⟨1341863932295497055631791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3578303819454658815018109 1341863932295497055631791)
                    ·
                      rfl

theorem cell22_3919906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_3919906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3919906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3919906 prefixEnd_3919906 := by exact prefixLift 3919906
  have htrace : WordTrace (prefixWord ++ tailWord_3919906) baseStart_3919906 baseEnd_3919906 := by
    simpa [prefixWord, tailWord_3919906, baseEnd_3919906] using wordTrace_append hprefix tailTrace_3919906
  have hstable : (prefixWord ++ tailWord_3919906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919906).length < 2 ^ (prefixWord ++ tailWord_3919906).sum := by decide
  have hdescent : baseEnd_3919906 < baseStart_3919906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919921 : List Nat := [1, 2, 2, 3, 1, 5, 1, 1, 2, 4]
def baseStart_3919921 : Nat := 118140960795 + 3919921 * 2 ^ 59
def prefixEnd_3919921 : Nat := 4983230072969 + 3 ^ 40 * 3919921 * 2
def baseEnd_3919921 : Nat := 1341869067102042016506745

theorem tailTrace_3919921 : CollatzResearch.WordTrace tailWord_3919921 prefixEnd_3919921 1341869067102042016506745 := by
  unfold tailWord_3919921
  simp only [CollatzResearch.WordTrace]
  refine ⟨142971264431803161052743617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95314176287868774035162411 142971264431803161052743617)
  ·
    refine ⟨107228448323852370789557713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142971264431803161052743617 107228448323852370789557713)
    ·
      refine ⟨80421336242889278092168285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107228448323852370789557713 80421336242889278092168285)
      ·
        refine ⟨30158001091083479284563107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80421336242889278092168285 30158001091083479284563107)
        ·
          refine ⟨45237001636625218926844661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30158001091083479284563107 45237001636625218926844661)
          ·
            refine ⟨4240968903433614274391687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45237001636625218926844661 4240968903433614274391687)
            ·
              refine ⟨6361453355150421411587531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4240968903433614274391687 6361453355150421411587531)
              ·
                refine ⟨9542180032725632117381297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6361453355150421411587531 9542180032725632117381297)
                ·
                  refine ⟨7156635024544224088035973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9542180032725632117381297 7156635024544224088035973)
                  ·
                    refine ⟨1341869067102042016506745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7156635024544224088035973 1341869067102042016506745)
                    ·
                      rfl

theorem cell22_3919921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 4].length) (baseStart_3919921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3919921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3919921 prefixEnd_3919921 := by exact prefixLift 3919921
  have htrace : WordTrace (prefixWord ++ tailWord_3919921) baseStart_3919921 baseEnd_3919921 := by
    simpa [prefixWord, tailWord_3919921, baseEnd_3919921] using wordTrace_append hprefix tailTrace_3919921
  have hstable : (prefixWord ++ tailWord_3919921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919921).length < 2 ^ (prefixWord ++ tailWord_3919921).sum := by decide
  have hdescent : baseEnd_3919921 < baseStart_3919921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919947 : List Nat := [1, 1, 1, 1, 3, 1, 2, 5, 7]
def baseStart_3919947 : Nat := 118140960795 + 3919947 * 2 ^ 59
def prefixEnd_3919947 : Nat := 4983230072969 + 3 ^ 40 * 3919947 * 2
def baseEnd_3919947 : Nat := 447292655811128871785555

theorem tailTrace_3919947 : CollatzResearch.WordTrace tailWord_3919947 prefixEnd_3919947 447292655811128871785555 := by
  unfold tailWord_3919947
  simp only [CollatzResearch.WordTrace]
  refine ⟨142972212729708967493190095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95314808486472644995460063 142972212729708967493190095)
  ·
    refine ⟨214458319094563451239785143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142972212729708967493190095 214458319094563451239785143)
    ·
      refine ⟨321687478641845176859677715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214458319094563451239785143 321687478641845176859677715)
      ·
        refine ⟨482531217962767765289516573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321687478641845176859677715 482531217962767765289516573)
        ·
          refine ⟨180949206736037911983568715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 482531217962767765289516573 180949206736037911983568715)
          ·
            refine ⟨271423810104056867975353073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180949206736037911983568715 271423810104056867975353073)
            ·
              refine ⟨203567857578042650981514805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271423810104056867975353073 203567857578042650981514805)
              ·
                refine ⟨19084486647941498529517013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 203567857578042650981514805 19084486647941498529517013)
                ·
                  refine ⟨447292655811128871785555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19084486647941498529517013 447292655811128871785555)
                  ·
                    rfl

theorem cell22_3919947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 7].length) (baseStart_3919947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3919947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3919947 prefixEnd_3919947 := by exact prefixLift 3919947
  have htrace : WordTrace (prefixWord ++ tailWord_3919947) baseStart_3919947 baseEnd_3919947 := by
    simpa [prefixWord, tailWord_3919947, baseEnd_3919947] using wordTrace_append hprefix tailTrace_3919947
  have hstable : (prefixWord ++ tailWord_3919947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919947).length < 2 ^ (prefixWord ++ tailWord_3919947).sum := by decide
  have hdescent : baseEnd_3919947 < baseStart_3919947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919970 : List Nat := [3, 3, 2, 2, 3, 1, 2, 6]
def baseStart_3919970 : Nat := 118140960795 + 3919970 * 2 ^ 59
def prefixEnd_3919970 : Nat := 4983230072969 + 3 ^ 40 * 3919970 * 2
def baseEnd_3919970 : Nat := 149098426755935802447955

theorem tailTrace_3919970 : CollatzResearch.WordTrace tailWord_3919970 prefixEnd_3919970 149098426755935802447955 := by
  unfold tailWord_3919970
  simp only [CollatzResearch.WordTrace]
  refine ⟨35743262902156410605319341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95315367739083761614184909 35743262902156410605319341)
  ·
    refine ⟨13403723588308653976994753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35743262902156410605319341 13403723588308653976994753)
    ·
      refine ⟨10052792691231490482746065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13403723588308653976994753 10052792691231490482746065)
      ·
        refine ⟨7539594518423617862059549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10052792691231490482746065 7539594518423617862059549)
        ·
          refine ⟨2827347944408856698272331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7539594518423617862059549 2827347944408856698272331)
          ·
            refine ⟨4241021916613285047408497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2827347944408856698272331 4241021916613285047408497)
            ·
              refine ⟨3180766437459963785556373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4241021916613285047408497 3180766437459963785556373)
              ·
                refine ⟨149098426755935802447955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3180766437459963785556373 149098426755935802447955)
                ·
                  rfl

theorem cell22_3919970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 6].length) (baseStart_3919970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3919970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3919970 prefixEnd_3919970 := by exact prefixLift 3919970
  have htrace : WordTrace (prefixWord ++ tailWord_3919970) baseStart_3919970 baseEnd_3919970 := by
    simpa [prefixWord, tailWord_3919970, baseEnd_3919970] using wordTrace_append hprefix tailTrace_3919970
  have hstable : (prefixWord ++ tailWord_3919970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919970).length < 2 ^ (prefixWord ++ tailWord_3919970).sum := by decide
  have hdescent : baseEnd_3919970 < baseStart_3919970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920045 : List Nat := [1, 5, 2, 1, 2, 2, 3, 1, 1, 4]
def baseStart_3920045 : Nat := 118140960795 + 3920045 * 2 ^ 59
def prefixEnd_3920045 : Nat := 4983230072969 + 3 ^ 40 * 3920045 * 2
def baseEnd_3920045 : Nat := 1341911514836147026406365

theorem tailTrace_3920045 : CollatzResearch.WordTrace tailWord_3920045 prefixEnd_3920045 1341911514836147026406365 := by
  unfold tailWord_3920045
  simp only [CollatzResearch.WordTrace]
  refine ⟨142975787083353930230257589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95317191388902620153505059 142975787083353930230257589)
  ·
    refine ⟨13403980039064430959086649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142975787083353930230257589 13403980039064430959086649)
    ·
      refine ⟨10052985029298323219314987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13403980039064430959086649 10052985029298323219314987)
      ·
        refine ⟨15079477543947484828972481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10052985029298323219314987 15079477543947484828972481)
        ·
          refine ⟨11309608157960613621729361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15079477543947484828972481 11309608157960613621729361)
          ·
            refine ⟨8482206118470460216297021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11309608157960613621729361 8482206118470460216297021)
            ·
              refine ⟨3180827294426422581111383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8482206118470460216297021 3180827294426422581111383)
              ·
                refine ⟨4771240941639633871667075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3180827294426422581111383 4771240941639633871667075)
                ·
                  refine ⟨7156861412459450807500613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4771240941639633871667075 7156861412459450807500613)
                  ·
                    refine ⟨1341911514836147026406365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7156861412459450807500613 1341911514836147026406365)
                    ·
                      rfl

theorem cell22_3920045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_3920045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3920045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3920045 prefixEnd_3920045 := by exact prefixLift 3920045
  have htrace : WordTrace (prefixWord ++ tailWord_3920045) baseStart_3920045 baseEnd_3920045 := by
    simpa [prefixWord, tailWord_3920045, baseEnd_3920045] using wordTrace_append hprefix tailTrace_3920045
  have hstable : (prefixWord ++ tailWord_3920045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920045).length < 2 ^ (prefixWord ++ tailWord_3920045).sum := by decide
  have hdescent : baseEnd_3920045 < baseStart_3920045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920154 : List Nat := [3, 1, 1, 3, 5, 1, 1, 3, 1, 3]
def baseStart_3920154 : Nat := 118140960795 + 3920154 * 2 ^ 59
def prefixEnd_3920154 : Nat := 4983230072969 + 3 ^ 40 * 3920154 * 2
def baseEnd_3920154 : Nat := 1341948827763707075431031

theorem tailTrace_3920154 : CollatzResearch.WordTrace tailWord_3920154 prefixEnd_3920154 1341948827763707075431031 := by
  unfold tailWord_3920154
  simp only [CollatzResearch.WordTrace]
  refine ⟨35744940659989760461493879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95319841759972694563983677 35744940659989760461493879)
  ·
    refine ⟨53617410989984640692240819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35744940659989760461493879 53617410989984640692240819)
    ·
      refine ⟨80426116484976961038361229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53617410989984640692240819 80426116484976961038361229)
      ·
        refine ⟨30159793681866360389385461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80426116484976961038361229 30159793681866360389385461)
        ·
          refine ⟨2827480657674971286504887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30159793681866360389385461 2827480657674971286504887)
          ·
            refine ⟨4241220986512456929757331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2827480657674971286504887 4241220986512456929757331)
            ·
              refine ⟨6361831479768685394635997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4241220986512456929757331 6361831479768685394635997)
              ·
                refine ⟨2385686804913257022988499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6361831479768685394635997 2385686804913257022988499)
                ·
                  refine ⟨3578530207369885534482749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2385686804913257022988499 3578530207369885534482749)
                  ·
                    refine ⟨1341948827763707075431031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3578530207369885534482749 1341948827763707075431031)
                    ·
                      rfl

theorem cell22_3920154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 3, 1, 3].length) (baseStart_3920154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3920154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3920154 prefixEnd_3920154 := by exact prefixLift 3920154
  have htrace : WordTrace (prefixWord ++ tailWord_3920154) baseStart_3920154 baseEnd_3920154 := by
    simpa [prefixWord, tailWord_3920154, baseEnd_3920154] using wordTrace_append hprefix tailTrace_3920154
  have hstable : (prefixWord ++ tailWord_3920154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920154).length < 2 ^ (prefixWord ++ tailWord_3920154).sum := by decide
  have hdescent : baseEnd_3920154 < baseStart_3920154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920191 : List Nat := [1, 1, 2, 2, 4, 1, 1, 2, 4, 4]
def baseStart_3920191 : Nat := 118140960795 + 3920191 * 2 ^ 59
def prefixEnd_3920191 : Nat := 4983230072969 + 3 ^ 40 * 3920191 * 2
def baseEnd_3920191 : Nat := 1341961493619851312255917

theorem tailTrace_3920191 : CollatzResearch.WordTrace tailWord_3920191 prefixEnd_3920191 1341961493619851312255917 := by
  unfold tailWord_3920191
  simp only [CollatzResearch.WordTrace]
  refine ⟨142981112140824997165072427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95320741427216664776714951 142981112140824997165072427)
  ·
    refine ⟨214471668211237495747608641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142981112140824997165072427 214471668211237495747608641)
    ·
      refine ⟨160853751158428121810706481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214471668211237495747608641 160853751158428121810706481)
      ·
        refine ⟨120640313368821091358029861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160853751158428121810706481 120640313368821091358029861)
        ·
          refine ⟨22620058756653954629630599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120640313368821091358029861 22620058756653954629630599)
          ·
            refine ⟨33930088134980931944445899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22620058756653954629630599 33930088134980931944445899)
            ·
              refine ⟨50895132202471397916668849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33930088134980931944445899 50895132202471397916668849)
              ·
                refine ⟨38171349151853548437501637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50895132202471397916668849 38171349151853548437501637)
                ·
                  refine ⟨7157127965972540332031557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38171349151853548437501637 7157127965972540332031557)
                  ·
                    refine ⟨1341961493619851312255917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7157127965972540332031557 1341961493619851312255917)
                    ·
                      rfl

theorem cell22_3920191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 4].length) (baseStart_3920191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3920191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3920191 prefixEnd_3920191 := by exact prefixLift 3920191
  have htrace : WordTrace (prefixWord ++ tailWord_3920191) baseStart_3920191 baseEnd_3920191 := by
    simpa [prefixWord, tailWord_3920191, baseEnd_3920191] using wordTrace_append hprefix tailTrace_3920191
  have hstable : (prefixWord ++ tailWord_3920191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920191).length < 2 ^ (prefixWord ++ tailWord_3920191).sum := by decide
  have hdescent : baseEnd_3920191 < baseStart_3920191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920208 : List Nat := [2, 1, 1, 1, 1, 7, 2, 1, 2, 4]
def baseStart_3920208 : Nat := 118140960795 + 3920208 * 2 ^ 59
def prefixEnd_3920208 : Nat := 4983230072969 + 3 ^ 40 * 3920208 * 2
def baseEnd_3920208 : Nat := 1341967313067268934580865

theorem tailTrace_3920208 : CollatzResearch.WordTrace tailWord_3920208 prefixEnd_3920208 1341967313067268934580865 := by
  unfold tailWord_3920208
  simp only [CollatzResearch.WordTrace]
  refine ⟨71490866090881704534220639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95321154787842272712294185 71490866090881704534220639)
  ·
    refine ⟨107236299136322556801330959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71490866090881704534220639 107236299136322556801330959)
    ·
      refine ⟨160854448704483835201996439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107236299136322556801330959 160854448704483835201996439)
      ·
        refine ⟨241281673056725752802994659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160854448704483835201996439 241281673056725752802994659)
        ·
          refine ⟨361922509585088629204491989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241281673056725752802994659 361922509585088629204491989)
          ·
            refine ⟨8482558818400514746980281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 361922509585088629204491989 8482558818400514746980281)
            ·
              refine ⟨6361919113800386060235211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8482558818400514746980281 6361919113800386060235211)
              ·
                refine ⟨9542878670700579090352817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6361919113800386060235211 9542878670700579090352817)
                ·
                  refine ⟨7157159003025434317764613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9542878670700579090352817 7157159003025434317764613)
                  ·
                    refine ⟨1341967313067268934580865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7157159003025434317764613 1341967313067268934580865)
                    ·
                      rfl

theorem cell22_3920208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 2, 4].length) (baseStart_3920208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3920208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3920208 prefixEnd_3920208 := by exact prefixLift 3920208
  have htrace : WordTrace (prefixWord ++ tailWord_3920208) baseStart_3920208 baseEnd_3920208 := by
    simpa [prefixWord, tailWord_3920208, baseEnd_3920208] using wordTrace_append hprefix tailTrace_3920208
  have hstable : (prefixWord ++ tailWord_3920208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920208).length < 2 ^ (prefixWord ++ tailWord_3920208).sum := by decide
  have hdescent : baseEnd_3920208 < baseStart_3920208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920222 : List Nat := [4, 4, 2, 1, 2, 1, 2, 2, 1, 3]
def baseStart_3920222 : Nat := 118140960795 + 3920222 * 2 ^ 59
def prefixEnd_3920222 : Nat := 4983230072969 + 3 ^ 40 * 3920222 * 2
def baseEnd_3920222 : Nat := 1341972105553377564730823

theorem tailTrace_3920222 : CollatzResearch.WordTrace tailWord_3920222 prefixEnd_3920222 1341972105553377564730823 := by
  unfold tailWord_3920222
  simp only [CollatzResearch.WordTrace]
  refine ⟨17872780350464086182431365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95321495202475126306300613 17872780350464086182431365)
  ·
    refine ⟨3351146315712016159205881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17872780350464086182431365 3351146315712016159205881)
    ·
      refine ⟨2513359736784012119404411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3351146315712016159205881 2513359736784012119404411)
      ·
        refine ⟨3770039605176018179106617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2513359736784012119404411 3770039605176018179106617)
        ·
          refine ⟨2827529703882013634329963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3770039605176018179106617 2827529703882013634329963)
          ·
            refine ⟨4241294555823020451494945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2827529703882013634329963 4241294555823020451494945)
            ·
              refine ⟨3180970916867265338621209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4241294555823020451494945 3180970916867265338621209)
              ·
                refine ⟨2385728187650449003965907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3180970916867265338621209 2385728187650449003965907)
                ·
                  refine ⟨3578592281475673505948861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2385728187650449003965907 3578592281475673505948861)
                  ·
                    refine ⟨1341972105553377564730823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3578592281475673505948861 1341972105553377564730823)
                    ·
                      rfl

theorem cell22_3920222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_3920222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3920222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3920222 prefixEnd_3920222 := by exact prefixLift 3920222
  have htrace : WordTrace (prefixWord ++ tailWord_3920222) baseStart_3920222 baseEnd_3920222 := by
    simpa [prefixWord, tailWord_3920222, baseEnd_3920222] using wordTrace_append hprefix tailTrace_3920222
  have hstable : (prefixWord ++ tailWord_3920222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920222).length < 2 ^ (prefixWord ++ tailWord_3920222).sum := by decide
  have hdescent : baseEnd_3920222 < baseStart_3920222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920278 : List Nat := [5, 3, 1, 2, 1, 2, 1, 2, 2, 3]
def baseStart_3920278 : Nat := 118140960795 + 3920278 * 2 ^ 59
def prefixEnd_3920278 : Nat := 4983230072969 + 3 ^ 40 * 3920278 * 2
def baseEnd_3920278 : Nat := 1341991275497812085330651

theorem tailTrace_3920278 : CollatzResearch.WordTrace tailWord_3920278 prefixEnd_3920278 1341991275497812085330651 := by
  unfold tailWord_3920278
  simp only [CollatzResearch.WordTrace]
  refine ⟨8936517830719363188968093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95322856861006540682326325 8936517830719363188968093)
  ·
    refine ⟨3351194186519761195863035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8936517830719363188968093 3351194186519761195863035)
    ·
      refine ⟨5026791279779641793794553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3351194186519761195863035 5026791279779641793794553)
      ·
        refine ⟨3770093459834731345345915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5026791279779641793794553 3770093459834731345345915)
        ·
          refine ⟨5655140189752097018018873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3770093459834731345345915 5655140189752097018018873)
          ·
            refine ⟨4241355142314072763514155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5655140189752097018018873 4241355142314072763514155)
            ·
              refine ⟨6362032713471109145271233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4241355142314072763514155 6362032713471109145271233)
              ·
                refine ⟨4771524535103331858953425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6362032713471109145271233 4771524535103331858953425)
                ·
                  refine ⟨3578643401327498894215069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4771524535103331858953425 3578643401327498894215069)
                  ·
                    refine ⟨1341991275497812085330651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3578643401327498894215069 1341991275497812085330651)
                    ·
                      rfl

theorem cell22_3920278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_3920278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3920278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3920278 prefixEnd_3920278 := by exact prefixLift 3920278
  have htrace : WordTrace (prefixWord ++ tailWord_3920278) baseStart_3920278 baseEnd_3920278 := by
    simpa [prefixWord, tailWord_3920278, baseEnd_3920278] using wordTrace_append hprefix tailTrace_3920278
  have hstable : (prefixWord ++ tailWord_3920278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920278).length < 2 ^ (prefixWord ++ tailWord_3920278).sum := by decide
  have hdescent : baseEnd_3920278 < baseStart_3920278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920313 : List Nat := [1, 2, 1, 4, 3, 1, 2, 2, 6]
def baseStart_3920313 : Nat := 118140960795 + 3920313 * 2 ^ 59
def prefixEnd_3920313 : Nat := 4983230072969 + 3 ^ 40 * 3920313 * 2
def baseEnd_3920313 : Nat := 447334418904361220235181

theorem tailTrace_3920313 : CollatzResearch.WordTrace tailWord_3920313 prefixEnd_3920313 447334418904361220235181 := by
  unfold tailWord_3920313
  simp only [CollatzResearch.WordTrace]
  refine ⟨142985561846383012001013593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95323707897588674667342395 142985561846383012001013593)
  ·
    refine ⟨107239171384787259000760195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142985561846383012001013593 107239171384787259000760195)
    ·
      refine ⟨160858757077180888501140293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107239171384787259000760195 160858757077180888501140293)
      ·
        refine ⟨30161016951971416593963805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160858757077180888501140293 30161016951971416593963805)
        ·
          refine ⟨11310381356989281222736427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30161016951971416593963805 11310381356989281222736427)
          ·
            refine ⟨16965572035483921834104641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11310381356989281222736427 16965572035483921834104641)
            ·
              refine ⟨12724179026612941375578481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16965572035483921834104641 12724179026612941375578481)
              ·
                refine ⟨9543134269959706031683861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12724179026612941375578481 9543134269959706031683861)
                ·
                  refine ⟨447334418904361220235181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9543134269959706031683861 447334418904361220235181)
                  ·
                    rfl

theorem cell22_3920313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 6].length) (baseStart_3920313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3920313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3920313 prefixEnd_3920313 := by exact prefixLift 3920313
  have htrace : WordTrace (prefixWord ++ tailWord_3920313) baseStart_3920313 baseEnd_3920313 := by
    simpa [prefixWord, tailWord_3920313, baseEnd_3920313] using wordTrace_append hprefix tailTrace_3920313
  have hstable : (prefixWord ++ tailWord_3920313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920313).length < 2 ^ (prefixWord ++ tailWord_3920313).sum := by decide
  have hdescent : baseEnd_3920313 < baseStart_3920313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920345 : List Nat := [1, 2, 1, 2, 4, 1, 2, 4, 2, 3]
def baseStart_3920345 : Nat := 118140960795 + 3920345 * 2 ^ 59
def prefixEnd_3920345 : Nat := 4983230072969 + 3 ^ 40 * 3920345 * 2
def baseEnd_3920345 : Nat := 1342014210967046243905445

theorem tailTrace_3920345 : CollatzResearch.WordTrace tailWord_3920345 prefixEnd_3920345 1342014210967046243905445 := by
  unfold tailWord_3920345
  simp only [CollatzResearch.WordTrace]
  refine ⟨142986728982267081466178489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95324485988178054310785659 142986728982267081466178489)
  ·
    refine ⟨107240046736700311099633867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142986728982267081466178489 107240046736700311099633867)
    ·
      refine ⟨160860070105050466649450801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107240046736700311099633867 160860070105050466649450801)
      ·
        refine ⟨120645052578787849987088101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160860070105050466649450801 120645052578787849987088101)
        ·
          refine ⟨22620947358522721872579019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120645052578787849987088101 22620947358522721872579019)
          ·
            refine ⟨33931421037784082808868529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22620947358522721872579019 33931421037784082808868529)
            ·
              refine ⟨25448565778338062106651397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33931421037784082808868529 25448565778338062106651397)
              ·
                refine ⟨4771606083438386644997137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25448565778338062106651397 4771606083438386644997137)
                ·
                  refine ⟨3578704562578789983747853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4771606083438386644997137 3578704562578789983747853)
                  ·
                    refine ⟨1342014210967046243905445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3578704562578789983747853 1342014210967046243905445)
                    ·
                      rfl

theorem cell22_3920345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 2, 3].length) (baseStart_3920345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3920345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3920345 prefixEnd_3920345 := by exact prefixLift 3920345
  have htrace : WordTrace (prefixWord ++ tailWord_3920345) baseStart_3920345 baseEnd_3920345 := by
    simpa [prefixWord, tailWord_3920345, baseEnd_3920345] using wordTrace_append hprefix tailTrace_3920345
  have hstable : (prefixWord ++ tailWord_3920345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920345).length < 2 ^ (prefixWord ++ tailWord_3920345).sum := by decide
  have hdescent : baseEnd_3920345 < baseStart_3920345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920362 : List Nat := [3, 1, 3, 1, 3, 2, 1, 3, 2, 3]
def baseStart_3920362 : Nat := 118140960795 + 3920362 * 2 ^ 59
def prefixEnd_3920362 : Nat := 4983230072969 + 3 ^ 40 * 3920362 * 2
def baseEnd_3920362 : Nat := 1342020030414463866230393

theorem tailTrace_3920362 : CollatzResearch.WordTrace tailWord_3920362 prefixEnd_3920362 1342020030414463866230393 := by
  unfold tailWord_3920362
  simp only [CollatzResearch.WordTrace]
  refine ⟨35746837255801373342386835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95324899348803662246364893 35746837255801373342386835)
  ·
    refine ⟨53620255883702060013580253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35746837255801373342386835 53620255883702060013580253)
    ·
      refine ⟨20107595956388272505092595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53620255883702060013580253 20107595956388272505092595)
      ·
        refine ⟨30161393934582408757638893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20107595956388272505092595 30161393934582408757638893)
        ·
          refine ⟨11310522725468403284114585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30161393934582408757638893 11310522725468403284114585)
          ·
            refine ⟨8482892044101302463085939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11310522725468403284114585 8482892044101302463085939)
            ·
              refine ⟨12724338066151953694628909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8482892044101302463085939 12724338066151953694628909)
              ·
                refine ⟨4771626774806982635485841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12724338066151953694628909 4771626774806982635485841)
                ·
                  refine ⟨3578720081105236976614381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4771626774806982635485841 3578720081105236976614381)
                  ·
                    refine ⟨1342020030414463866230393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3578720081105236976614381 1342020030414463866230393)
                    ·
                      rfl

theorem cell22_3920362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_3920362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3920362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3920362 prefixEnd_3920362 := by exact prefixLift 3920362
  have htrace : WordTrace (prefixWord ++ tailWord_3920362) baseStart_3920362 baseEnd_3920362 := by
    simpa [prefixWord, tailWord_3920362, baseEnd_3920362] using wordTrace_append hprefix tailTrace_3920362
  have hstable : (prefixWord ++ tailWord_3920362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920362).length < 2 ^ (prefixWord ++ tailWord_3920362).sum := by decide
  have hdescent : baseEnd_3920362 < baseStart_3920362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920454 : List Nat := [6, 1, 1, 1, 2, 1, 3, 2, 5]
def baseStart_3920454 : Nat := 118140960795 + 3920454 * 2 ^ 59
def prefixEnd_3920454 : Nat := 4983230072969 + 3 ^ 40 * 3920454 * 2
def baseEnd_3920454 : Nat := 447350507964868764310037

theorem tailTrace_3920454 : CollatzResearch.WordTrace tailWord_3920454 prefixEnd_3920454 447350507964868764310037 := by
  unfold tailWord_3920454
  simp only [CollatzResearch.WordTrace]
  refine ⟨4468459516839756033809263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 95327136359248128721264277 4468459516839756033809263)
  ·
    refine ⟨6702689275259634050713895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4468459516839756033809263 6702689275259634050713895)
    ·
      refine ⟨10054033912889451076070843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6702689275259634050713895 10054033912889451076070843)
      ·
        refine ⟨15081050869334176614106265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10054033912889451076070843 15081050869334176614106265)
        ·
          refine ⟨11310788152000632460579699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15081050869334176614106265 11310788152000632460579699)
          ·
            refine ⟨16966182228000948690869549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11310788152000632460579699 16966182228000948690869549)
            ·
              refine ⟨6362318335500355759076081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16966182228000948690869549 6362318335500355759076081)
              ·
                refine ⟨4771738751625266819307061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6362318335500355759076081 4771738751625266819307061)
                ·
                  refine ⟨447350507964868764310037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4771738751625266819307061 447350507964868764310037)
                  ·
                    rfl

theorem cell22_3920454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_3920454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3920454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3920454 prefixEnd_3920454 := by exact prefixLift 3920454
  have htrace : WordTrace (prefixWord ++ tailWord_3920454) baseStart_3920454 baseEnd_3920454 := by
    simpa [prefixWord, tailWord_3920454, baseEnd_3920454] using wordTrace_append hprefix tailTrace_3920454
  have hstable : (prefixWord ++ tailWord_3920454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920454).length < 2 ^ (prefixWord ++ tailWord_3920454).sum := by decide
  have hdescent : baseEnd_3920454 < baseStart_3920454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920463 : List Nat := [1, 1, 2, 1, 1, 2, 4, 2, 3, 5]
def baseStart_3920463 : Nat := 118140960795 + 3920463 * 2 ^ 59
def prefixEnd_3920463 : Nat := 4983230072969 + 3 ^ 40 * 3920463 * 2
def baseEnd_3920463 : Nat := 1342054604778533269455083

theorem tailTrace_3920463 : CollatzResearch.WordTrace tailWord_3920463 prefixEnd_3920463 1342054604778533269455083 := by
  unfold tailWord_3920463
  simp only [CollatzResearch.WordTrace]
  refine ⟨142991032795839587618974043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95327355197226391745982695 142991032795839587618974043)
  ·
    refine ⟨214486549193759381428461065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142991032795839587618974043 214486549193759381428461065)
    ·
      refine ⟨160864911895319536071345799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214486549193759381428461065 160864911895319536071345799)
      ·
        refine ⟨241297367842979304107018699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160864911895319536071345799 241297367842979304107018699)
        ·
          refine ⟨361946051764468956160528049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241297367842979304107018699 361946051764468956160528049)
          ·
            refine ⟨271459538823351717120396037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361946051764468956160528049 271459538823351717120396037)
            ·
              refine ⟨50898663529378446960074257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 271459538823351717120396037 50898663529378446960074257)
              ·
                refine ⟨38173997647033835220055693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50898663529378446960074257 38173997647033835220055693)
                ·
                  refine ⟨14315249117637688207520885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38173997647033835220055693 14315249117637688207520885)
                  ·
                    refine ⟨1342054604778533269455083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14315249117637688207520885 1342054604778533269455083)
                    ·
                      rfl

theorem cell22_3920463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 5].length) (baseStart_3920463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3920463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3920463 prefixEnd_3920463 := by exact prefixLift 3920463
  have htrace : WordTrace (prefixWord ++ tailWord_3920463) baseStart_3920463 baseEnd_3920463 := by
    simpa [prefixWord, tailWord_3920463, baseEnd_3920463] using wordTrace_append hprefix tailTrace_3920463
  have hstable : (prefixWord ++ tailWord_3920463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920463).length < 2 ^ (prefixWord ++ tailWord_3920463).sum := by decide
  have hdescent : baseEnd_3920463 < baseStart_3920463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920465 : List Nat := [1, 2, 2, 1, 3, 4, 2, 1, 6]
def baseStart_3920465 : Nat := 118140960795 + 3920465 * 2 ^ 59
def prefixEnd_3920465 : Nat := 4983230072969 + 3 ^ 40 * 3920465 * 2
def baseEnd_3920465 : Nat := 447351763139801976968359

theorem tailTrace_3920465 : CollatzResearch.WordTrace tailWord_3920465 prefixEnd_3920465 447351763139801976968359 := by
  unfold tailWord_3920465
  simp only [CollatzResearch.WordTrace]
  refine ⟨142991105741832341960546849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95327403827888227973697899 142991105741832341960546849)
  ·
    refine ⟨107243329306374256470410137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142991105741832341960546849 107243329306374256470410137)
    ·
      refine ⟨80432496979780692352807603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107243329306374256470410137 80432496979780692352807603)
      ·
        refine ⟨120648745469671038529211405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80432496979780692352807603 120648745469671038529211405)
        ·
          refine ⟨45243279551126639448454277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120648745469671038529211405 45243279551126639448454277)
          ·
            refine ⟨8483114915836244896585177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45243279551126639448454277 8483114915836244896585177)
            ·
              refine ⟨6362336186877183672438883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8483114915836244896585177 6362336186877183672438883)
              ·
                refine ⟨9543504280315775508658325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6362336186877183672438883 9543504280315775508658325)
                ·
                  refine ⟨447351763139801976968359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9543504280315775508658325 447351763139801976968359)
                  ·
                    rfl

theorem cell22_3920465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 6].length) (baseStart_3920465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3920465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3920465 prefixEnd_3920465 := by exact prefixLift 3920465
  have htrace : WordTrace (prefixWord ++ tailWord_3920465) baseStart_3920465 baseEnd_3920465 := by
    simpa [prefixWord, tailWord_3920465, baseEnd_3920465] using wordTrace_append hprefix tailTrace_3920465
  have hstable : (prefixWord ++ tailWord_3920465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920465).length < 2 ^ (prefixWord ++ tailWord_3920465).sum := by decide
  have hdescent : baseEnd_3920465 < baseStart_3920465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920480 : List Nat := [2, 1, 1, 3, 2, 1, 5, 1, 1, 5]
def baseStart_3920480 : Nat := 118140960795 + 3920480 * 2 ^ 59
def prefixEnd_3920480 : Nat := 4983230072969 + 3 ^ 40 * 3920480 * 2
def baseEnd_3920480 : Nat := 1342060424225950891780031

theorem tailTrace_3920480 : CollatzResearch.WordTrace tailWord_3920480 prefixEnd_3920480 1342060424225950891780031 := by
  unfold tailWord_3920480
  simp only [CollatzResearch.WordTrace]
  refine ⟨71495826418388999761171447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95327768557851999681561929 71495826418388999761171447)
  ·
    refine ⟨107243739627583499641757171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71495826418388999761171447 107243739627583499641757171)
    ·
      refine ⟨160865609441375249462635757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107243739627583499641757171 160865609441375249462635757)
      ·
        refine ⟨60324603540515718548488409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160865609441375249462635757 60324603540515718548488409)
        ·
          refine ⟨45243452655386788911366307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60324603540515718548488409 45243452655386788911366307)
          ·
            refine ⟨67865178983080183367049461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45243452655386788911366307 67865178983080183367049461)
            ·
              refine ⟨6362360529663767190660887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67865178983080183367049461 6362360529663767190660887)
              ·
                refine ⟨9543540794495650785991331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6362360529663767190660887 9543540794495650785991331)
                ·
                  refine ⟨14315311191743476178986997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9543540794495650785991331 14315311191743476178986997)
                  ·
                    refine ⟨1342060424225950891780031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14315311191743476178986997 1342060424225950891780031)
                    ·
                      rfl

theorem cell22_3920480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 1, 5].length) (baseStart_3920480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3920480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3920480 prefixEnd_3920480 := by exact prefixLift 3920480
  have htrace : WordTrace (prefixWord ++ tailWord_3920480) baseStart_3920480 baseEnd_3920480 := by
    simpa [prefixWord, tailWord_3920480, baseEnd_3920480] using wordTrace_append hprefix tailTrace_3920480
  have hstable : (prefixWord ++ tailWord_3920480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920480).length < 2 ^ (prefixWord ++ tailWord_3920480).sum := by decide
  have hdescent : baseEnd_3920480 < baseStart_3920480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920570 : List Nat := [3, 1, 1, 1, 2, 3, 2, 2, 2, 5]
def baseStart_3920570 : Nat := 118140960795 + 3920570 * 2 ^ 59
def prefixEnd_3920570 : Nat := 4983230072969 + 3 ^ 40 * 3920570 * 2
def baseEnd_3920570 : Nat := 1342091233065220657029755

theorem tailTrace_3920570 : CollatzResearch.WordTrace tailWord_3920570 prefixEnd_3920570 1342091233065220657029755 := by
  unfold tailWord_3920570
  simp only [CollatzResearch.WordTrace]
  refine ⟨35748733851612986223279791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95329956937634629928746109 35748733851612986223279791)
  ·
    refine ⟨53623100777419479334919687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35748733851612986223279791 53623100777419479334919687)
    ·
      refine ⟨80434651166129219002379531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53623100777419479334919687 80434651166129219002379531)
      ·
        refine ⟨120651976749193828503569297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80434651166129219002379531 120651976749193828503569297)
        ·
          refine ⟨90488982561895371377676973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120651976749193828503569297 90488982561895371377676973)
          ·
            refine ⟨33933368460710764266628865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90488982561895371377676973 33933368460710764266628865)
            ·
              refine ⟨25450026345533073199971649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33933368460710764266628865 25450026345533073199971649)
              ·
                refine ⟨19087519759149804899978737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25450026345533073199971649 19087519759149804899978737)
                ·
                  refine ⟨14315639819362353674984053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19087519759149804899978737 14315639819362353674984053)
                  ·
                    refine ⟨1342091233065220657029755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14315639819362353674984053 1342091233065220657029755)
                    ·
                      rfl

theorem cell22_3920570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_3920570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3920570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3920570 prefixEnd_3920570 := by exact prefixLift 3920570
  have htrace : WordTrace (prefixWord ++ tailWord_3920570) baseStart_3920570 baseEnd_3920570 := by
    simpa [prefixWord, tailWord_3920570, baseEnd_3920570] using wordTrace_append hprefix tailTrace_3920570
  have hstable : (prefixWord ++ tailWord_3920570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920570).length < 2 ^ (prefixWord ++ tailWord_3920570).sum := by decide
  have hdescent : baseEnd_3920570 < baseStart_3920570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920572 : List Nat := [2, 2, 2, 3, 1, 1, 4, 2, 5]
def baseStart_3920572 : Nat := 118140960795 + 3920572 * 2 ^ 59
def prefixEnd_3920572 : Nat := 4983230072969 + 3 ^ 40 * 3920572 * 2
def baseEnd_3920572 : Nat := 447363972568697772826583

theorem tailTrace_3920572 : CollatzResearch.WordTrace tailWord_3920572 prefixEnd_3920572 447363972568697772826583 := by
  unfold tailWord_3920572
  simp only [CollatzResearch.WordTrace]
  refine ⟨71497504176222349617345985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95330005568296466156461313 71497504176222349617345985)
  ·
    refine ⟨53623128132166762213009489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71497504176222349617345985 53623128132166762213009489)
    ·
      refine ⟨40217346099125071659757117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53623128132166762213009489 40217346099125071659757117)
      ·
        refine ⟨15081504787171901872408919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40217346099125071659757117 15081504787171901872408919)
        ·
          refine ⟨22622257180757852808613379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15081504787171901872408919 22622257180757852808613379)
          ·
            refine ⟨33933385771136779212920069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22622257180757852808613379 33933385771136779212920069)
            ·
              refine ⟨6362509832088146102422513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33933385771136779212920069 6362509832088146102422513)
              ·
                refine ⟨4771882374066109576816885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6362509832088146102422513 4771882374066109576816885)
                ·
                  refine ⟨447363972568697772826583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4771882374066109576816885 447363972568697772826583)
                  ·
                    rfl

theorem cell22_3920572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 5].length) (baseStart_3920572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3920572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3920572 prefixEnd_3920572 := by exact prefixLift 3920572
  have htrace : WordTrace (prefixWord ++ tailWord_3920572) baseStart_3920572 baseEnd_3920572 := by
    simpa [prefixWord, tailWord_3920572, baseEnd_3920572] using wordTrace_append hprefix tailTrace_3920572
  have hstable : (prefixWord ++ tailWord_3920572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920572).length < 2 ^ (prefixWord ++ tailWord_3920572).sum := by decide
  have hdescent : baseEnd_3920572 < baseStart_3920572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920576 : List Nat := [2, 1, 1, 2, 4, 2, 4, 2, 1, 3]
def baseStart_3920576 : Nat := 118140960795 + 3920576 * 2 ^ 59
def prefixEnd_3920576 : Nat := 4983230072969 + 3 ^ 40 * 3920576 * 2
def baseEnd_3920576 : Nat := 1342093286987838641379737

theorem tailTrace_3920576 : CollatzResearch.WordTrace tailWord_3920576 prefixEnd_3920576 1342093286987838641379737 := by
  unfold tailWord_3920576
  simp only [CollatzResearch.WordTrace]
  refine ⟨71497577122215103958918791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95330102829620138611891721 71497577122215103958918791)
  ·
    refine ⟨107246365683322655938378187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71497577122215103958918791 107246365683322655938378187)
    ·
      refine ⟨160869548524983983907567281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107246365683322655938378187 160869548524983983907567281)
      ·
        refine ⟨120652161393737987930675461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160869548524983983907567281 120652161393737987930675461)
        ·
          refine ⟨22622280261325872737001649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120652161393737987930675461 22622280261325872737001649)
          ·
            refine ⟨16966710195994404552751237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22622280261325872737001649 16966710195994404552751237)
            ·
              refine ⟨3181258161748950853640857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16966710195994404552751237 3181258161748950853640857)
              ·
                refine ⟨2385943621311713140230643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3181258161748950853640857 2385943621311713140230643)
                ·
                  refine ⟨3578915431967569710345965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2385943621311713140230643 3578915431967569710345965)
                  ·
                    refine ⟨1342093286987838641379737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3578915431967569710345965 1342093286987838641379737)
                    ·
                      rfl

theorem cell22_3920576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 2, 1, 3].length) (baseStart_3920576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3920576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3920576 prefixEnd_3920576 := by exact prefixLift 3920576
  have htrace : WordTrace (prefixWord ++ tailWord_3920576) baseStart_3920576 baseEnd_3920576 := by
    simpa [prefixWord, tailWord_3920576, baseEnd_3920576] using wordTrace_append hprefix tailTrace_3920576
  have hstable : (prefixWord ++ tailWord_3920576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920576).length < 2 ^ (prefixWord ++ tailWord_3920576).sum := by decide
  have hdescent : baseEnd_3920576 < baseStart_3920576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920600 : List Nat := [2, 1, 2, 2, 3, 2, 1, 1, 8]
def baseStart_3920600 : Nat := 118140960795 + 3920600 * 2 ^ 59
def prefixEnd_3920600 : Nat := 4983230072969 + 3 ^ 40 * 3920600 * 2
def baseEnd_3920600 : Nat := 447367167559436859593221

theorem tailTrace_3920600 : CollatzResearch.WordTrace tailWord_3920600 prefixEnd_3920600 447367167559436859593221 := by
  unfold tailWord_3920600
  simp only [CollatzResearch.WordTrace]
  refine ⟨71498014798171630008355627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95330686397562173344474169 71498014798171630008355627)
  ·
    refine ⟨107247022197257445012533441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71498014798171630008355627 107247022197257445012533441)
    ·
      refine ⟨80435266647943083759400081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107247022197257445012533441 80435266647943083759400081)
      ·
        refine ⟨60326449985957312819550061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80435266647943083759400081 60326449985957312819550061)
        ·
          refine ⟨22622418744733992307331273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60326449985957312819550061 22622418744733992307331273)
          ·
            refine ⟨16966814058550494230498455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22622418744733992307331273 16966814058550494230498455)
            ·
              refine ⟨25450221087825741345747683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16966814058550494230498455 25450221087825741345747683)
              ·
                refine ⟨38175331631738612018621525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25450221087825741345747683 38175331631738612018621525)
                ·
                  refine ⟨447367167559436859593221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38175331631738612018621525 447367167559436859593221)
                  ·
                    rfl

theorem cell22_3920600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 8].length) (baseStart_3920600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3920600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3920600 prefixEnd_3920600 := by exact prefixLift 3920600
  have htrace : WordTrace (prefixWord ++ tailWord_3920600) baseStart_3920600 baseEnd_3920600 := by
    simpa [prefixWord, tailWord_3920600, baseEnd_3920600] using wordTrace_append hprefix tailTrace_3920600
  have hstable : (prefixWord ++ tailWord_3920600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920600).length < 2 ^ (prefixWord ++ tailWord_3920600).sum := by decide
  have hdescent : baseEnd_3920600 < baseStart_3920600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920602 : List Nat := [3, 1, 1, 2, 2, 2, 2, 4, 1, 4]
def baseStart_3920602 : Nat := 118140960795 + 3920602 * 2 ^ 59
def prefixEnd_3920602 : Nat := 4983230072969 + 3 ^ 40 * 3920602 * 2
def baseEnd_3920602 : Nat := 1342102187319183240229657

theorem tailTrace_3920602 : CollatzResearch.WordTrace tailWord_3920602 prefixEnd_3920602 1342102187319183240229657 := by
  unfold tailWord_3920602
  simp only [CollatzResearch.WordTrace]
  refine ⟨35749025635584003589571015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95330735028224009572189373 35749025635584003589571015)
  ·
    refine ⟨53623538453376005384356523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35749025635584003589571015 53623538453376005384356523)
    ·
      refine ⟨80435307680064008076534785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53623538453376005384356523 80435307680064008076534785)
      ·
        refine ⟨60326480760048006057401089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80435307680064008076534785 60326480760048006057401089)
        ·
          refine ⟨45244860570036004543050817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60326480760048006057401089 45244860570036004543050817)
          ·
            refine ⟨33933645427527003407288113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45244860570036004543050817 33933645427527003407288113)
            ·
              refine ⟨25450234070645252555466085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33933645427527003407288113 25450234070645252555466085)
              ·
                refine ⟨4771918888245984854149891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25450234070645252555466085 4771918888245984854149891)
                ·
                  refine ⟨7157878332368977281224837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4771918888245984854149891 7157878332368977281224837)
                  ·
                    refine ⟨1342102187319183240229657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7157878332368977281224837 1342102187319183240229657)
                    ·
                      rfl

theorem cell22_3920602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 1, 4].length) (baseStart_3920602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3920602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3920602 prefixEnd_3920602 := by exact prefixLift 3920602
  have htrace : WordTrace (prefixWord ++ tailWord_3920602) baseStart_3920602 baseEnd_3920602 := by
    simpa [prefixWord, tailWord_3920602, baseEnd_3920602] using wordTrace_append hprefix tailTrace_3920602
  have hstable : (prefixWord ++ tailWord_3920602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920602).length < 2 ^ (prefixWord ++ tailWord_3920602).sum := by decide
  have hdescent : baseEnd_3920602 < baseStart_3920602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920617 : List Nat := [1, 2, 1, 1, 1, 2, 5, 5, 4]
def baseStart_3920617 : Nat := 118140960795 + 3920617 * 2 ^ 59
def prefixEnd_3920617 : Nat := 4983230072969 + 3 ^ 40 * 3920617 * 2
def baseEnd_3920617 : Nat := 447369107375242733701537

theorem tailTrace_3920617 : CollatzResearch.WordTrace tailWord_3920617 prefixEnd_3920617 447369107375242733701537 := by
  unfold tailWord_3920617
  simp only [CollatzResearch.WordTrace]
  refine ⟨142996649637281671920080105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95331099758187781280053403 142996649637281671920080105)
  ·
    refine ⟨107247487227961253940060079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142996649637281671920080105 107247487227961253940060079)
    ·
      refine ⟨160871230841941880910090119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107247487227961253940060079 160871230841941880910090119)
      ·
        refine ⟨241306846262912821365135179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160871230841941880910090119 241306846262912821365135179)
        ·
          refine ⟨361960269394369232047702769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241306846262912821365135179 361960269394369232047702769)
          ·
            refine ⟨271470202045776924035777077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361960269394369232047702769 271470202045776924035777077)
            ·
              refine ⟨25450331441791586628354101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 271470202045776924035777077 25450331441791586628354101)
              ·
                refine ⟨2385968572667961246408197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25450331441791586628354101 2385968572667961246408197)
                ·
                  refine ⟨447369107375242733701537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2385968572667961246408197 447369107375242733701537)
                  ·
                    rfl

theorem cell22_3920617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 5, 4].length) (baseStart_3920617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3920617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3920617 prefixEnd_3920617 := by exact prefixLift 3920617
  have htrace : WordTrace (prefixWord ++ tailWord_3920617) baseStart_3920617 baseEnd_3920617 := by
    simpa [prefixWord, tailWord_3920617, baseEnd_3920617] using wordTrace_append hprefix tailTrace_3920617
  have hstable : (prefixWord ++ tailWord_3920617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920617).length < 2 ^ (prefixWord ++ tailWord_3920617).sum := by decide
  have hdescent : baseEnd_3920617 < baseStart_3920617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920632 : List Nat := [2, 1, 2, 1, 1, 2, 5, 1, 4, 3]
def baseStart_3920632 : Nat := 118140960795 + 3920632 * 2 ^ 59
def prefixEnd_3920632 : Nat := 4983230072969 + 3 ^ 40 * 3920632 * 2
def baseEnd_3920632 : Nat := 1342112456932273161979565

theorem tailTrace_3920632 : CollatzResearch.WordTrace tailWord_3920632 prefixEnd_3920632 1342112456932273161979565 := by
  unfold tailWord_3920632
  simp only [CollatzResearch.WordTrace]
  refine ⟨71498598366113664740938075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95331464488151552987917433 71498598366113664740938075)
  ·
    refine ⟨107247897549170497111407113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71498598366113664740938075 107247897549170497111407113)
    ·
      refine ⟨80435923161877872833555335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107247897549170497111407113 80435923161877872833555335)
      ·
        refine ⟨120653884742816809250333003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80435923161877872833555335 120653884742816809250333003)
        ·
          refine ⟨180980827114225213875499505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120653884742816809250333003 180980827114225213875499505)
          ·
            refine ⟨135735620335668910406624629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180980827114225213875499505 135735620335668910406624629)
            ·
              refine ⟨12725214406468960350621059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135735620335668910406624629 12725214406468960350621059)
              ·
                refine ⟨19087821609703440525931589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12725214406468960350621059 19087821609703440525931589)
                ·
                  refine ⟨3578966551819395098612173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19087821609703440525931589 3578966551819395098612173)
                  ·
                    refine ⟨1342112456932273161979565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3578966551819395098612173 1342112456932273161979565)
                    ·
                      rfl

theorem cell22_3920632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 4, 3].length) (baseStart_3920632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3920632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3920632 prefixEnd_3920632 := by exact prefixLift 3920632
  have htrace : WordTrace (prefixWord ++ tailWord_3920632) baseStart_3920632 baseEnd_3920632 := by
    simpa [prefixWord, tailWord_3920632, baseEnd_3920632] using wordTrace_append hprefix tailTrace_3920632
  have hstable : (prefixWord ++ tailWord_3920632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920632).length < 2 ^ (prefixWord ++ tailWord_3920632).sum := by decide
  have hdescent : baseEnd_3920632 < baseStart_3920632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920647 : List Nat := [1, 1, 4, 4, 1, 1, 1, 2, 1, 6]
def baseStart_3920647 : Nat := 118140960795 + 3920647 * 2 ^ 59
def prefixEnd_3920647 : Nat := 4983230072969 + 3 ^ 40 * 3920647 * 2
def baseEnd_3920647 : Nat := 1342117591738818122854519

theorem tailTrace_3920647 : CollatzResearch.WordTrace tailWord_3920647 prefixEnd_3920647 1342117591738818122854519 := by
  unfold tailWord_3920647
  simp only [CollatzResearch.WordTrace]
  refine ⟨142997743827172987043672195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95331829218115324695781463 142997743827172987043672195)
  ·
    refine ⟨214496615740759480565508293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142997743827172987043672195 214496615740759480565508293)
    ·
      refine ⟨40218115451392402606032805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214496615740759480565508293 40218115451392402606032805)
      ·
        refine ⟨7540896647136075488631151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40218115451392402606032805 7540896647136075488631151)
        ·
          refine ⟨11311344970704113232946727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7540896647136075488631151 11311344970704113232946727)
          ·
            refine ⟨16967017456056169849420091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11311344970704113232946727 16967017456056169849420091)
            ·
              refine ⟨25450526184084254774130137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16967017456056169849420091 25450526184084254774130137)
              ·
                refine ⟨19087894638063191080597603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25450526184084254774130137 19087894638063191080597603)
                ·
                  refine ⟨28631841957094786620896405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19087894638063191080597603 28631841957094786620896405)
                  ·
                    refine ⟨1342117591738818122854519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28631841957094786620896405 1342117591738818122854519)
                    ·
                      rfl

theorem cell22_3920647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_3920647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3920647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3920647 prefixEnd_3920647 := by exact prefixLift 3920647
  have htrace : WordTrace (prefixWord ++ tailWord_3920647) baseStart_3920647 baseEnd_3920647 := by
    simpa [prefixWord, tailWord_3920647, baseEnd_3920647] using wordTrace_append hprefix tailTrace_3920647
  have hstable : (prefixWord ++ tailWord_3920647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920647).length < 2 ^ (prefixWord ++ tailWord_3920647).sum := by decide
  have hdescent : baseEnd_3920647 < baseStart_3920647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920675 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 1, 8]
def baseStart_3920675 : Nat := 118140960795 + 3920675 * 2 ^ 59
def prefixEnd_3920675 : Nat := 4983230072969 + 3 ^ 40 * 3920675 * 2
def baseEnd_3920675 : Nat := 1342127176711035383154433

theorem tailTrace_3920675 : CollatzResearch.WordTrace tailWord_3920675 prefixEnd_3920675 1342127176711035383154433 := by
  unfold tailWord_3920675
  simp only [CollatzResearch.WordTrace]
  refine ⟨142998765071071547825691479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95332510047381031883794319 142998765071071547825691479)
  ·
    refine ⟨214498147606607321738537219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142998765071071547825691479 214498147606607321738537219)
    ·
      refine ⟨321747221409910982607805829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214498147606607321738537219 321747221409910982607805829)
      ·
        refine ⟨60327604014358309238963593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 321747221409910982607805829 60327604014358309238963593)
        ·
          refine ⟨45245703010768731929222695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60327604014358309238963593 45245703010768731929222695)
          ·
            refine ⟨67868554516153097893834043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45245703010768731929222695 67868554516153097893834043)
            ·
              refine ⟨101802831774229646840751065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67868554516153097893834043 101802831774229646840751065)
              ·
                refine ⟨76352123830672235130563299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101802831774229646840751065 76352123830672235130563299)
                ·
                  refine ⟨114528185746008352695844949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76352123830672235130563299 114528185746008352695844949)
                  ·
                    refine ⟨1342127176711035383154433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 114528185746008352695844949 1342127176711035383154433)
                    ·
                      rfl

theorem cell22_3920675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 8].length) (baseStart_3920675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3920675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3920675 prefixEnd_3920675 := by exact prefixLift 3920675
  have htrace : WordTrace (prefixWord ++ tailWord_3920675) baseStart_3920675 baseEnd_3920675 := by
    simpa [prefixWord, tailWord_3920675, baseEnd_3920675] using wordTrace_append hprefix tailTrace_3920675
  have hstable : (prefixWord ++ tailWord_3920675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920675).length < 2 ^ (prefixWord ++ tailWord_3920675).sum := by decide
  have hdescent : baseEnd_3920675 < baseStart_3920675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920685 : List Nat := [1, 5, 3, 2, 1, 1, 3, 2, 4]
def baseStart_3920685 : Nat := 118140960795 + 3920685 * 2 ^ 59
def prefixEnd_3920685 : Nat := 4983230072969 + 3 ^ 40 * 3920685 * 2
def baseEnd_3920685 : Nat := 447376866638466230134801

theorem tailTrace_3920685 : CollatzResearch.WordTrace tailWord_3920685 prefixEnd_3920685 447376866638466230134801 := by
  unfold tailWord_3920685
  simp only [CollatzResearch.WordTrace]
  refine ⟨142999129801035319533555509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95332753200690213022370339 142999129801035319533555509)
  ·
    refine ⟨13406168418847061206270829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142999129801035319533555509 13406168418847061206270829)
    ·
      refine ⟨5027313157067647952351561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13406168418847061206270829 5027313157067647952351561)
      ·
        refine ⟨3770484867800735964263671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5027313157067647952351561 3770484867800735964263671)
        ·
          refine ⟨5655727301701103946395507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3770484867800735964263671 5655727301701103946395507)
          ·
            refine ⟨8483590952551655919593261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5655727301701103946395507 8483590952551655919593261)
            ·
              refine ⟨3181346607206870969847473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8483590952551655919593261 3181346607206870969847473)
              ·
                refine ⟨2386009955405153227385605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3181346607206870969847473 2386009955405153227385605)
                ·
                  refine ⟨447376866638466230134801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2386009955405153227385605 447376866638466230134801)
                  ·
                    rfl

theorem cell22_3920685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_3920685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3920685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3920685 prefixEnd_3920685 := by exact prefixLift 3920685
  have htrace : WordTrace (prefixWord ++ tailWord_3920685) baseStart_3920685 baseEnd_3920685 := by
    simpa [prefixWord, tailWord_3920685, baseEnd_3920685] using wordTrace_append hprefix tailTrace_3920685
  have hstable : (prefixWord ++ tailWord_3920685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920685).length < 2 ^ (prefixWord ++ tailWord_3920685).sum := by decide
  have hdescent : baseEnd_3920685 < baseStart_3920685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920707 : List Nat := [1, 1, 1, 3, 1, 4, 3, 3, 5]
def baseStart_3920707 : Nat := 118140960795 + 3920707 * 2 ^ 59
def prefixEnd_3920707 : Nat := 4983230072969 + 3 ^ 40 * 3920707 * 2
def baseEnd_3920707 : Nat := 447379376988332655451445

theorem tailTrace_3920707 : CollatzResearch.WordTrace tailWord_3920707 prefixEnd_3920707 447379376988332655451445 := by
  unfold tailWord_3920707
  simp only [CollatzResearch.WordTrace]
  refine ⟨142999932206955617290856375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95333288137970411527237583 142999932206955617290856375)
  ·
    refine ⟨214499898310433425936284563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142999932206955617290856375 214499898310433425936284563)
    ·
      refine ⟨321749847465650138904426845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214499898310433425936284563 321749847465650138904426845)
      ·
        refine ⟨120656192799618802089160067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321749847465650138904426845 120656192799618802089160067)
        ·
          refine ⟨180984289199428203133740101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120656192799618802089160067 180984289199428203133740101)
          ·
            refine ⟨33934554224892788087576269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180984289199428203133740101 33934554224892788087576269)
            ·
              refine ⟨12725457834334795532841101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33934554224892788087576269 12725457834334795532841101)
              ·
                refine ⟨4772046687875548324815413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12725457834334795532841101 4772046687875548324815413)
                ·
                  refine ⟨447379376988332655451445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4772046687875548324815413 447379376988332655451445)
                  ·
                    rfl

theorem cell22_3920707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 5].length) (baseStart_3920707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3920707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3920707 prefixEnd_3920707 := by exact prefixLift 3920707
  have htrace : WordTrace (prefixWord ++ tailWord_3920707) baseStart_3920707 baseEnd_3920707 := by
    simpa [prefixWord, tailWord_3920707, baseEnd_3920707] using wordTrace_append hprefix tailTrace_3920707
  have hstable : (prefixWord ++ tailWord_3920707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920707).length < 2 ^ (prefixWord ++ tailWord_3920707).sum := by decide
  have hdescent : baseEnd_3920707 < baseStart_3920707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920767 : List Nat := [1, 1, 2, 2, 1, 1, 5, 3, 1, 5]
def baseStart_3920767 : Nat := 118140960795 + 3920767 * 2 ^ 59
def prefixEnd_3920767 : Nat := 4983230072969 + 3 ^ 40 * 3920767 * 2
def baseEnd_3920767 : Nat := 1342158670191177809854151

theorem tailTrace_3920767 : CollatzResearch.WordTrace tailWord_3920767 prefixEnd_3920767 1342158670191177809854151 := by
  unfold tailWord_3920767
  simp only [CollatzResearch.WordTrace]
  refine ⟨143002120586738247538040555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95334747057825498358693703 143002120586738247538040555)
  ·
    refine ⟨214503180880107371307060833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143002120586738247538040555 214503180880107371307060833)
    ·
      refine ⟨160877385660080528480295625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214503180880107371307060833 160877385660080528480295625)
      ·
        refine ⟨120658039245060396360221719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160877385660080528480295625 120658039245060396360221719)
        ·
          refine ⟨180987058867590594540332579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120658039245060396360221719 180987058867590594540332579)
          ·
            refine ⟨271480588301385891810498869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180987058867590594540332579 271480588301385891810498869)
            ·
              refine ⟨25451305153254927357234269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 271480588301385891810498869 25451305153254927357234269)
              ·
                refine ⟨9544239432470597758962851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25451305153254927357234269 9544239432470597758962851)
                ·
                  refine ⟨14316359148705896638444277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9544239432470597758962851 14316359148705896638444277)
                  ·
                    refine ⟨1342158670191177809854151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14316359148705896638444277 1342158670191177809854151)
                    ·
                      rfl

theorem cell22_3920767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 5].length) (baseStart_3920767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3920767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3920767 prefixEnd_3920767 := by exact prefixLift 3920767
  have htrace : WordTrace (prefixWord ++ tailWord_3920767) baseStart_3920767 baseEnd_3920767 := by
    simpa [prefixWord, tailWord_3920767, baseEnd_3920767] using wordTrace_append hprefix tailTrace_3920767
  have hstable : (prefixWord ++ tailWord_3920767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920767).length < 2 ^ (prefixWord ++ tailWord_3920767).sum := by decide
  have hdescent : baseEnd_3920767 < baseStart_3920767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920797 : List Nat := [1, 4, 2, 1, 2, 1, 11]
def baseStart_3920797 : Nat := 118140960795 + 3920797 * 2 ^ 59
def prefixEnd_3920797 : Nat := 4983230072969 + 3 ^ 40 * 3920797 * 2
def baseEnd_3920797 : Nat := 49709960733491397466817

theorem tailTrace_3920797 : CollatzResearch.WordTrace tailWord_3920797 prefixEnd_3920797 49709960733491397466817 := by
  unfold tailWord_3920797
  simp only [CollatzResearch.WordTrace]
  refine ⟨143003214776629562661632645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95335476517753041774421763 143003214776629562661632645)
  ·
    refine ⟨26813102770618042999056121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143003214776629562661632645 26813102770618042999056121)
    ·
      refine ⟨20109827077963532249292091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26813102770618042999056121 20109827077963532249292091)
      ·
        refine ⟨30164740616945298373938137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20109827077963532249292091 30164740616945298373938137)
        ·
          refine ⟨22623555462708973780453603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30164740616945298373938137 22623555462708973780453603)
          ·
            refine ⟨33935333194063460670680405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22623555462708973780453603 33935333194063460670680405)
            ·
              refine ⟨49709960733491397466817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 33935333194063460670680405 49709960733491397466817)
              ·
                rfl

theorem cell22_3920797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 11].length) (baseStart_3920797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3920797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3920797 prefixEnd_3920797 := by exact prefixLift 3920797
  have htrace : WordTrace (prefixWord ++ tailWord_3920797) baseStart_3920797 baseEnd_3920797 := by
    simpa [prefixWord, tailWord_3920797, baseEnd_3920797] using wordTrace_append hprefix tailTrace_3920797
  have hstable : (prefixWord ++ tailWord_3920797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920797).length < 2 ^ (prefixWord ++ tailWord_3920797).sum := by decide
  have hdescent : baseEnd_3920797 < baseStart_3920797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920801 : List Nat := [1, 2, 3, 4, 1, 2, 1, 1, 4, 3]
def baseStart_3920801 : Nat := 118140960795 + 3920801 * 2 ^ 59
def prefixEnd_3920801 : Nat := 4983230072969 + 3 ^ 40 * 3920801 * 2
def baseEnd_3920801 : Nat := 1342170309086013054504047

theorem tailTrace_3920801 : CollatzResearch.WordTrace tailWord_3920801 prefixEnd_3920801 1342170309086013054504047 := by
  unfold tailWord_3920801
  simp only [CollatzResearch.WordTrace]
  refine ⟨143003360668615071344778257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95335573779076714229852171 143003360668615071344778257)
  ·
    refine ⟨107252520501461303508583693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143003360668615071344778257 107252520501461303508583693)
    ·
      refine ⟨40219695188047988815718885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107252520501461303508583693 40219695188047988815718885)
      ·
        refine ⟨7541192847758997902947291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40219695188047988815718885 7541192847758997902947291)
        ·
          refine ⟨11311789271638496854420937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7541192847758997902947291 11311789271638496854420937)
          ·
            refine ⟨8483841953728872640815703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11311789271638496854420937 8483841953728872640815703)
            ·
              refine ⟨12725762930593308961223555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8483841953728872640815703 12725762930593308961223555)
              ·
                refine ⟨19088644395889963441835333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12725762930593308961223555 19088644395889963441835333)
                ·
                  refine ⟨3579120824229368145344125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19088644395889963441835333 3579120824229368145344125)
                  ·
                    refine ⟨1342170309086013054504047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3579120824229368145344125 1342170309086013054504047)
                    ·
                      rfl

theorem cell22_3920801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_3920801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3920801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3920801 prefixEnd_3920801 := by exact prefixLift 3920801
  have htrace : WordTrace (prefixWord ++ tailWord_3920801) baseStart_3920801 baseEnd_3920801 := by
    simpa [prefixWord, tailWord_3920801, baseEnd_3920801] using wordTrace_append hprefix tailTrace_3920801
  have hstable : (prefixWord ++ tailWord_3920801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920801).length < 2 ^ (prefixWord ++ tailWord_3920801).sum := by decide
  have hdescent : baseEnd_3920801 < baseStart_3920801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920822 : List Nat := [5, 1, 4, 1, 1, 1, 2, 2, 1, 4]
def baseStart_3920822 : Nat := 118140960795 + 3920822 * 2 ^ 59
def prefixEnd_3920822 : Nat := 4983230072969 + 3 ^ 40 * 3920822 * 2
def baseEnd_3920822 : Nat := 1342177497815175999728983

theorem tailTrace_3920822 : CollatzResearch.WordTrace tailWord_3920822 prefixEnd_3920822 1342177497815175999728983 := by
  unfold tailWord_3920822
  simp only [CollatzResearch.WordTrace]
  refine ⟨8937757912596186995705795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95336084401025994620861813 8937757912596186995705795)
  ·
    refine ⟨13406636868894280493558693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8937757912596186995705795 13406636868894280493558693)
    ·
      refine ⟨2513744412917677592542255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13406636868894280493558693 2513744412917677592542255)
      ·
        refine ⟨3770616619376516388813383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2513744412917677592542255 3770616619376516388813383)
        ·
          refine ⟨5655924929064774583220075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3770616619376516388813383 5655924929064774583220075)
          ·
            refine ⟨8483887393597161874830113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5655924929064774583220075 8483887393597161874830113)
            ·
              refine ⟨6362915545197871406122585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8483887393597161874830113 6362915545197871406122585)
              ·
                refine ⟨4772186658898403554591939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6362915545197871406122585 4772186658898403554591939)
                ·
                  refine ⟨7158279988347605331887909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4772186658898403554591939 7158279988347605331887909)
                  ·
                    refine ⟨1342177497815175999728983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7158279988347605331887909 1342177497815175999728983)
                    ·
                      rfl

theorem cell22_3920822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_3920822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3920822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3920822 prefixEnd_3920822 := by exact prefixLift 3920822
  have htrace : WordTrace (prefixWord ++ tailWord_3920822) baseStart_3920822 baseEnd_3920822 := by
    simpa [prefixWord, tailWord_3920822, baseEnd_3920822] using wordTrace_append hprefix tailTrace_3920822
  have hstable : (prefixWord ++ tailWord_3920822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920822).length < 2 ^ (prefixWord ++ tailWord_3920822).sum := by decide
  have hdescent : baseEnd_3920822 < baseStart_3920822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920863 : List Nat := [1, 1, 2, 3, 5, 2, 1, 1, 3, 3]
def baseStart_3920863 : Nat := 118140960795 + 3920863 * 2 ^ 59
def prefixEnd_3920863 : Nat := 4983230072969 + 3 ^ 40 * 3920863 * 2
def baseEnd_3920863 : Nat := 1342191532953065559453857

theorem tailTrace_3920863 : CollatzResearch.WordTrace tailWord_3920863 prefixEnd_3920863 1342191532953065559453857 := by
  unfold tailWord_3920863
  simp only [CollatzResearch.WordTrace]
  refine ⟨143005621994390455933535243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95337081329593637289023495 143005621994390455933535243)
  ·
    refine ⟨214508432991585683900302865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143005621994390455933535243 214508432991585683900302865)
    ·
      refine ⟨160881324743689262925227149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214508432991585683900302865 160881324743689262925227149)
      ·
        refine ⟨60330496778883473596960181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160881324743689262925227149 60330496778883473596960181)
        ·
          refine ⟨5655984073020325649715017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60330496778883473596960181 5655984073020325649715017)
          ·
            refine ⟨4241988054765244237286263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5655984073020325649715017 4241988054765244237286263)
            ·
              refine ⟨6362982082147866355929395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4241988054765244237286263 6362982082147866355929395)
              ·
                refine ⟨9544473123221799533894093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6362982082147866355929395 9544473123221799533894093)
                ·
                  refine ⟨3579177421208174825210285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9544473123221799533894093 3579177421208174825210285)
                  ·
                    refine ⟨1342191532953065559453857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3579177421208174825210285 1342191532953065559453857)
                    ·
                      rfl

theorem cell22_3920863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 3, 3].length) (baseStart_3920863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3920863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3920863 prefixEnd_3920863 := by exact prefixLift 3920863
  have htrace : WordTrace (prefixWord ++ tailWord_3920863) baseStart_3920863 baseEnd_3920863 := by
    simpa [prefixWord, tailWord_3920863, baseEnd_3920863] using wordTrace_append hprefix tailTrace_3920863
  have hstable : (prefixWord ++ tailWord_3920863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920863).length < 2 ^ (prefixWord ++ tailWord_3920863).sum := by decide
  have hdescent : baseEnd_3920863 < baseStart_3920863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920889 : List Nat := [1, 2, 1, 3, 1, 3, 3, 1, 3, 4]
def baseStart_3920889 : Nat := 118140960795 + 3920889 * 2 ^ 59
def prefixEnd_3920889 : Nat := 4983230072969 + 3 ^ 40 * 3920889 * 2
def baseEnd_3920889 : Nat := 1342200433284410158303777

theorem tailTrace_3920889 : CollatzResearch.WordTrace tailWord_3920889 prefixEnd_3920889 1342200433284410158303777 := by
  unfold tailWord_3920889
  simp only [CollatzResearch.WordTrace]
  refine ⟨143006570292296262373981721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95337713528197508249321147 143006570292296262373981721)
  ·
    refine ⟨107254927719222196780486291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143006570292296262373981721 107254927719222196780486291)
    ·
      refine ⟨160882391578833295170729437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107254927719222196780486291 160882391578833295170729437)
      ·
        refine ⟨60330896842062485689023539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160882391578833295170729437 60330896842062485689023539)
        ·
          refine ⟨90496345263093728533535309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60330896842062485689023539 90496345263093728533535309)
          ·
            refine ⟨33936129473660148200075741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90496345263093728533535309 33936129473660148200075741)
            ·
              refine ⟨12726048552622555575028403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33936129473660148200075741 12726048552622555575028403)
              ·
                refine ⟨19089072828933833362542605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12726048552622555575028403 19089072828933833362542605)
                ·
                  refine ⟨7158402310850187510953477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19089072828933833362542605 7158402310850187510953477)
                  ·
                    refine ⟨1342200433284410158303777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7158402310850187510953477 1342200433284410158303777)
                    ·
                      rfl

theorem cell22_3920889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 4].length) (baseStart_3920889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3920889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3920889 prefixEnd_3920889 := by exact prefixLift 3920889
  have htrace : WordTrace (prefixWord ++ tailWord_3920889) baseStart_3920889 baseEnd_3920889 := by
    simpa [prefixWord, tailWord_3920889, baseEnd_3920889] using wordTrace_append hprefix tailTrace_3920889
  have hstable : (prefixWord ++ tailWord_3920889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920889).length < 2 ^ (prefixWord ++ tailWord_3920889).sum := by decide
  have hdescent : baseEnd_3920889 < baseStart_3920889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920914 : List Nat := [3, 2, 5, 1, 1, 1, 1, 4, 1, 3]
def baseStart_3920914 : Nat := 118140960795 + 3920914 * 2 ^ 59
def prefixEnd_3920914 : Nat := 4983230072969 + 3 ^ 40 * 3920914 * 2
def baseEnd_3920914 : Nat := 1342208991295318426428701

theorem tailTrace_3920914 : CollatzResearch.WordTrace tailWord_3920914 prefixEnd_3920914 1342208991295318426428701 := by
  unfold tailWord_3920914
  simp only [CollatzResearch.WordTrace]
  refine ⟨35751870529301422910910449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95338321411470461095761197 35751870529301422910910449)
  ·
    refine ⟨26813902896976067183182837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35751870529301422910910449 26813902896976067183182837)
    ·
      refine ⟨2513803396591506298423391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26813902896976067183182837 2513803396591506298423391)
      ·
        refine ⟨3770705094887259447635087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2513803396591506298423391 3770705094887259447635087)
        ·
          refine ⟨5656057642330889171452631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3770705094887259447635087 5656057642330889171452631)
          ·
            refine ⟨8484086463496333757178947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5656057642330889171452631 8484086463496333757178947)
            ·
              refine ⟨12726129695244500635768421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8484086463496333757178947 12726129695244500635768421)
              ·
                refine ⟨2386149317858343869206579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12726129695244500635768421 2386149317858343869206579)
                ·
                  refine ⟨3579223976787515803809869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2386149317858343869206579 3579223976787515803809869)
                  ·
                    refine ⟨1342208991295318426428701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3579223976787515803809869 1342208991295318426428701)
                    ·
                      rfl

theorem cell22_3920914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_3920914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3920914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3920914 prefixEnd_3920914 := by exact prefixLift 3920914
  have htrace : WordTrace (prefixWord ++ tailWord_3920914) baseStart_3920914 baseEnd_3920914 := by
    simpa [prefixWord, tailWord_3920914, baseEnd_3920914] using wordTrace_append hprefix tailTrace_3920914
  have hstable : (prefixWord ++ tailWord_3920914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920914).length < 2 ^ (prefixWord ++ tailWord_3920914).sum := by decide
  have hdescent : baseEnd_3920914 < baseStart_3920914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921000 : List Nat := [2, 1, 4, 4, 1, 2, 2, 6]
def baseStart_3921000 : Nat := 118140960795 + 3921000 * 2 ^ 59
def prefixEnd_3921000 : Nat := 4983230072969 + 3 ^ 40 * 3921000 * 2
def baseEnd_3921000 : Nat := 149137603428093652086493

theorem tailTrace_3921000 : CollatzResearch.WordTrace tailWord_3921000 prefixEnd_3921000 149137603428093652086493 := by
  unfold tailWord_3921000
  simp only [CollatzResearch.WordTrace]
  refine ⟨71505309397447064165636227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95340412529929418887514969 71505309397447064165636227)
  ·
    refine ⟨107257964096170596248454341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71505309397447064165636227 107257964096170596248454341)
    ·
      refine ⟨20110868268031986796585189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107257964096170596248454341 20110868268031986796585189)
      ·
        refine ⟨3770787800255997524359723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20110868268031986796585189 3770787800255997524359723)
        ·
          refine ⟨5656181700383996286539585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3770787800255997524359723 5656181700383996286539585)
          ·
            refine ⟨4242136275287997214904689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5656181700383996286539585 4242136275287997214904689)
            ·
              refine ⟨3181602206465997911178517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4242136275287997214904689 3181602206465997911178517)
              ·
                refine ⟨149137603428093652086493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3181602206465997911178517 149137603428093652086493)
                ·
                  rfl

theorem cell22_3921000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 6].length) (baseStart_3921000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921000 prefixEnd_3921000 := by exact prefixLift 3921000
  have htrace : WordTrace (prefixWord ++ tailWord_3921000) baseStart_3921000 baseEnd_3921000 := by
    simpa [prefixWord, tailWord_3921000, baseEnd_3921000] using wordTrace_append hprefix tailTrace_3921000
  have hstable : (prefixWord ++ tailWord_3921000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921000).length < 2 ^ (prefixWord ++ tailWord_3921000).sum := by decide
  have hdescent : baseEnd_3921000 < baseStart_3921000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921009 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 4, 5]
def baseStart_3921009 : Nat := 118140960795 + 3921009 * 2 ^ 59
def prefixEnd_3921009 : Nat := 4983230072969 + 3 ^ 40 * 3921009 * 2
def baseEnd_3921009 : Nat := 1342241511736769845303409

theorem tailTrace_3921009 : CollatzResearch.WordTrace tailWord_3921009 prefixEnd_3921009 1342241511736769845303409 := by
  unfold tailWord_3921009
  simp only [CollatzResearch.WordTrace]
  refine ⟨143010947051861522868350081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95340631367907681912233387 143010947051861522868350081)
  ·
    refine ⟨107258210288896142151262561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143010947051861522868350081 107258210288896142151262561)
    ·
      refine ⟨80443657716672106613446921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107258210288896142151262561 80443657716672106613446921)
      ·
        refine ⟨60332743287504079960085191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80443657716672106613446921 60332743287504079960085191)
        ·
          refine ⟨90499114931256119940127787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60332743287504079960085191 90499114931256119940127787)
          ·
            refine ⟨135748672396884179910191681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90499114931256119940127787 135748672396884179910191681)
            ·
              refine ⟨101811504297663134932643761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135748672396884179910191681 101811504297663134932643761)
              ·
                refine ⟨76358628223247351199482821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101811504297663134932643761 76358628223247351199482821)
                ·
                  refine ⟨14317242791858878349903029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76358628223247351199482821 14317242791858878349903029)
                  ·
                    refine ⟨1342241511736769845303409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14317242791858878349903029 1342241511736769845303409)
                    ·
                      rfl

theorem cell22_3921009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_3921009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921009 prefixEnd_3921009 := by exact prefixLift 3921009
  have htrace : WordTrace (prefixWord ++ tailWord_3921009) baseStart_3921009 baseEnd_3921009 := by
    simpa [prefixWord, tailWord_3921009, baseEnd_3921009] using wordTrace_append hprefix tailTrace_3921009
  have hstable : (prefixWord ++ tailWord_3921009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921009).length < 2 ^ (prefixWord ++ tailWord_3921009).sum := by decide
  have hdescent : baseEnd_3921009 < baseStart_3921009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921032 : List Nat := [2, 1, 3, 4, 3, 1, 1, 1, 3, 3]
def baseStart_3921032 : Nat := 118140960795 + 3921032 * 2 ^ 59
def prefixEnd_3921032 : Nat := 4983230072969 + 3 ^ 40 * 3921032 * 2
def baseEnd_3921032 : Nat := 1342249385106805451978339

theorem tailTrace_3921032 : CollatzResearch.WordTrace tailWord_3921032 prefixEnd_3921032 1342249385106805451978339 := by
  unfold tailWord_3921032
  simp only [CollatzResearch.WordTrace]
  refine ⟨71505892965389098898218675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95341190620518798530958233 71505892965389098898218675)
  ·
    refine ⟨107258839448083648347328013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71505892965389098898218675 107258839448083648347328013)
    ·
      refine ⟨40222064793031368130248005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107258839448083648347328013 40222064793031368130248005)
      ·
        refine ⟨7541637148693381524421501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40222064793031368130248005 7541637148693381524421501)
        ·
          refine ⟨2828113930760018071658063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7541637148693381524421501 2828113930760018071658063)
          ·
            refine ⟨4242170896140027107487095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2828113930760018071658063 4242170896140027107487095)
            ·
              refine ⟨6363256344210040661230643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4242170896140027107487095 6363256344210040661230643)
              ·
                refine ⟨9544884516315060991845965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6363256344210040661230643 9544884516315060991845965)
                ·
                  refine ⟨3579331693618147871942237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9544884516315060991845965 3579331693618147871942237)
                  ·
                    refine ⟨1342249385106805451978339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3579331693618147871942237 1342249385106805451978339)
                    ·
                      rfl

theorem cell22_3921032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 3, 3].length) (baseStart_3921032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921032 prefixEnd_3921032 := by exact prefixLift 3921032
  have htrace : WordTrace (prefixWord ++ tailWord_3921032) baseStart_3921032 baseEnd_3921032 := by
    simpa [prefixWord, tailWord_3921032, baseEnd_3921032] using wordTrace_append hprefix tailTrace_3921032
  have hstable : (prefixWord ++ tailWord_3921032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921032).length < 2 ^ (prefixWord ++ tailWord_3921032).sum := by decide
  have hdescent : baseEnd_3921032 < baseStart_3921032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921071 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 6, 3]
def baseStart_3921071 : Nat := 118140960795 + 3921071 * 2 ^ 59
def prefixEnd_3921071 : Nat := 4983230072969 + 3 ^ 40 * 3921071 * 2
def baseEnd_3921071 : Nat := 1342262735603822350253219

theorem tailTrace_3921071 : CollatzResearch.WordTrace tailWord_3921071 prefixEnd_3921071 1342262735603822350253219 := by
  unfold tailWord_3921071
  simp only [CollatzResearch.WordTrace]
  refine ⟨143013208377636907457107067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95342138918424604971404711 143013208377636907457107067)
  ·
    refine ⟨214519812566455361185660601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143013208377636907457107067 214519812566455361185660601)
    ·
      refine ⟨160889859424841520889245451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214519812566455361185660601 160889859424841520889245451)
      ·
        refine ⟨241334789137262281333868177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160889859424841520889245451 241334789137262281333868177)
        ·
          refine ⟨181001091852946711000401133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241334789137262281333868177 181001091852946711000401133)
          ·
            refine ⟨67875409444855016625150425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181001091852946711000401133 67875409444855016625150425)
            ·
              refine ⟨50906557083641262468862819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67875409444855016625150425 50906557083641262468862819)
              ·
                refine ⟨76359835625461893703294229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50906557083641262468862819 76359835625461893703294229)
                ·
                  refine ⟨3579367294943526267341917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 76359835625461893703294229 3579367294943526267341917)
                  ·
                    refine ⟨1342262735603822350253219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3579367294943526267341917 1342262735603822350253219)
                    ·
                      rfl

theorem cell22_3921071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 6, 3].length) (baseStart_3921071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921071 prefixEnd_3921071 := by exact prefixLift 3921071
  have htrace : WordTrace (prefixWord ++ tailWord_3921071) baseStart_3921071 baseEnd_3921071 := by
    simpa [prefixWord, tailWord_3921071, baseEnd_3921071] using wordTrace_append hprefix tailTrace_3921071
  have hstable : (prefixWord ++ tailWord_3921071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921071).length < 2 ^ (prefixWord ++ tailWord_3921071).sum := by decide
  have hdescent : baseEnd_3921071 < baseStart_3921071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921146 : List Nat := [3, 1, 1, 1, 1, 4, 3, 1, 7]
def baseStart_3921146 : Nat := 118140960795 + 3921146 * 2 ^ 59
def prefixEnd_3921146 : Nat := 4983230072969 + 3 ^ 40 * 3921146 * 2
def baseEnd_3921146 : Nat := 447429469878849051542663

theorem tailTrace_3921146 : CollatzResearch.WordTrace tailWord_3921146 prefixEnd_3921146 447429469878849051542663 := by
  unfold tailWord_3921146
  simp only [CollatzResearch.WordTrace]
  refine ⟨35753985963091298816521823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95343962568243463510724861 35753985963091298816521823)
  ·
    refine ⟨53630978944636948224782735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35753985963091298816521823 53630978944636948224782735)
    ·
      refine ⟨80446468416955422337174103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53630978944636948224782735 80446468416955422337174103)
      ·
        refine ⟨120669702625433133505761155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80446468416955422337174103 120669702625433133505761155)
        ·
          refine ⟨181004553938149700258641733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120669702625433133505761155 181004553938149700258641733)
          ·
            refine ⟨33938353863403068798495325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181004553938149700258641733 33938353863403068798495325)
            ·
              refine ⟨12726882698776150799435747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33938353863403068798495325 12726882698776150799435747)
              ·
                refine ⟨19090324048164226199153621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12726882698776150799435747 19090324048164226199153621)
                ·
                  refine ⟨447429469878849051542663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19090324048164226199153621 447429469878849051542663)
                  ·
                    rfl

theorem cell22_3921146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 7].length) (baseStart_3921146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921146 prefixEnd_3921146 := by exact prefixLift 3921146
  have htrace : WordTrace (prefixWord ++ tailWord_3921146) baseStart_3921146 baseEnd_3921146 := by
    simpa [prefixWord, tailWord_3921146, baseEnd_3921146] using wordTrace_append hprefix tailTrace_3921146
  have hstable : (prefixWord ++ tailWord_3921146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921146).length < 2 ^ (prefixWord ++ tailWord_3921146).sum := by decide
  have hdescent : baseEnd_3921146 < baseStart_3921146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921150 : List Nat := [4, 2, 2, 1, 1, 2, 1, 3, 3, 3]
def baseStart_3921150 : Nat := 118140960795 + 3921150 * 2 ^ 59
def prefixEnd_3921150 : Nat := 4983230072969 + 3 ^ 40 * 3921150 * 2
def baseEnd_3921150 : Nat := 1342289778918292477527977

theorem tailTrace_3921150 : CollatzResearch.WordTrace tailWord_3921150 prefixEnd_3921150 1342289778918292477527977 := by
  unfold tailWord_3921150
  simp only [CollatzResearch.WordTrace]
  refine ⟨17877011218043837993654113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95344059829567135966155269 17877011218043837993654113)
  ·
    refine ⟨13407758413532878495240585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17877011218043837993654113 13407758413532878495240585)
    ·
      refine ⟨10055818810149658871430439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13407758413532878495240585 10055818810149658871430439)
      ·
        refine ⟨15083728215224488307145659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10055818810149658871430439 15083728215224488307145659)
        ·
          refine ⟨22625592322836732460718489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15083728215224488307145659 22625592322836732460718489)
          ·
            refine ⟨16969194242127549345538867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22625592322836732460718489 16969194242127549345538867)
            ·
              refine ⟨25453791363191324018308301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16969194242127549345538867 25453791363191324018308301)
              ·
                refine ⟨9545171761196746506865613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25453791363191324018308301 9545171761196746506865613)
                ·
                  refine ⟨3579439410448779940074605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9545171761196746506865613 3579439410448779940074605)
                  ·
                    refine ⟨1342289778918292477527977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3579439410448779940074605 1342289778918292477527977)
                    ·
                      rfl

theorem cell22_3921150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_3921150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921150 prefixEnd_3921150 := by exact prefixLift 3921150
  have htrace : WordTrace (prefixWord ++ tailWord_3921150) baseStart_3921150 baseEnd_3921150 := by
    simpa [prefixWord, tailWord_3921150, baseEnd_3921150] using wordTrace_append hprefix tailTrace_3921150
  have hstable : (prefixWord ++ tailWord_3921150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921150).length < 2 ^ (prefixWord ++ tailWord_3921150).sum := by decide
  have hdescent : baseEnd_3921150 < baseStart_3921150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921161 : List Nat := [1, 2, 1, 1, 3, 3, 1, 3, 2, 5]
def baseStart_3921161 : Nat := 118140960795 + 3921161 * 2 ^ 59
def prefixEnd_3921161 : Nat := 4983230072969 + 3 ^ 40 * 3921161 * 2
def baseEnd_3921161 : Nat := 1342293544443092115502943

theorem tailTrace_3921161 : CollatzResearch.WordTrace tailWord_3921161 prefixEnd_3921161 1342293544443092115502943 := by
  unfold tailWord_3921161
  simp only [CollatzResearch.WordTrace]
  refine ⟨143016490947310852827883337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95344327298207235218588891 143016490947310852827883337)
  ·
    refine ⟨107262368210483139620912503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143016490947310852827883337 107262368210483139620912503)
    ·
      refine ⟨160893552315724709431368755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107262368210483139620912503 160893552315724709431368755)
      ·
        refine ⟨241340328473587064147053133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160893552315724709431368755 241340328473587064147053133)
        ·
          refine ⟨90502623177595149055144925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241340328473587064147053133 90502623177595149055144925)
          ·
            refine ⟨33938483691598180895679347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90502623177595149055144925 33938483691598180895679347)
            ·
              refine ⟨50907725537397271343519021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33938483691598180895679347 50907725537397271343519021)
              ·
                refine ⟨19090397076523976753819633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50907725537397271343519021 19090397076523976753819633)
                ·
                  refine ⟨14317797807392982565364725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19090397076523976753819633 14317797807392982565364725)
                  ·
                    refine ⟨1342293544443092115502943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14317797807392982565364725 1342293544443092115502943)
                    ·
                      rfl

theorem cell22_3921161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 5].length) (baseStart_3921161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921161 prefixEnd_3921161 := by exact prefixLift 3921161
  have htrace : WordTrace (prefixWord ++ tailWord_3921161) baseStart_3921161 baseEnd_3921161 := by
    simpa [prefixWord, tailWord_3921161, baseEnd_3921161] using wordTrace_append hprefix tailTrace_3921161
  have hstable : (prefixWord ++ tailWord_3921161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921161).length < 2 ^ (prefixWord ++ tailWord_3921161).sum := by decide
  have hdescent : baseEnd_3921161 < baseStart_3921161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921184 : List Nat := [2, 1, 1, 5, 3, 2, 1, 3, 1, 3]
def baseStart_3921184 : Nat := 118140960795 + 3921184 * 2 ^ 59
def prefixEnd_3921184 : Nat := 4983230072969 + 3 ^ 40 * 3921184 * 2
def baseEnd_3921184 : Nat := 1342301417813127722177873

theorem tailTrace_3921184 : CollatzResearch.WordTrace tailWord_3921184 prefixEnd_3921184 1342301417813127722177873 := by
  unfold tailWord_3921184
  simp only [CollatzResearch.WordTrace]
  refine ⟨71508664913113763877985303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95344886550818351837313737 71508664913113763877985303)
  ·
    refine ⟨107262997369670645816977955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71508664913113763877985303 107262997369670645816977955)
    ·
      refine ⟨160894496054505968725466933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107262997369670645816977955 160894496054505968725466933)
      ·
        refine ⟨15083859005109934568012525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160894496054505968725466933 15083859005109934568012525)
        ·
          refine ⟨5656447126916225463004697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15083859005109934568012525 5656447126916225463004697)
          ·
            refine ⟨4242335345187169097253523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5656447126916225463004697 4242335345187169097253523)
            ·
              refine ⟨6363503017780753645880285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4242335345187169097253523 6363503017780753645880285)
              ·
                refine ⟨2386313631667782617205107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6363503017780753645880285 2386313631667782617205107)
                ·
                  refine ⟨3579470447501673925807661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2386313631667782617205107 3579470447501673925807661)
                  ·
                    refine ⟨1342301417813127722177873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3579470447501673925807661 1342301417813127722177873)
                    ·
                      rfl

theorem cell22_3921184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 3, 1, 3].length) (baseStart_3921184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921184 prefixEnd_3921184 := by exact prefixLift 3921184
  have htrace : WordTrace (prefixWord ++ tailWord_3921184) baseStart_3921184 baseEnd_3921184 := by
    simpa [prefixWord, tailWord_3921184, baseEnd_3921184] using wordTrace_append hprefix tailTrace_3921184
  have hstable : (prefixWord ++ tailWord_3921184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921184).length < 2 ^ (prefixWord ++ tailWord_3921184).sum := by decide
  have hdescent : baseEnd_3921184 < baseStart_3921184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921221 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 3, 6]
def baseStart_3921221 : Nat := 118140960795 + 3921221 * 2 ^ 59
def prefixEnd_3921221 : Nat := 4983230072969 + 3 ^ 40 * 3921221 * 2
def baseEnd_3921221 : Nat := 1342314083669271959002759

theorem tailTrace_3921221 : CollatzResearch.WordTrace tailWord_3921221 prefixEnd_3921221 1342314083669271959002759 := by
  unfold tailWord_3921221
  simp only [CollatzResearch.WordTrace]
  refine ⟨143018679327093483075067517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95345786218062322050045011 143018679327093483075067517)
  ·
    refine ⟨53632004747660056153150319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143018679327093483075067517 53632004747660056153150319)
    ·
      refine ⟨80448007121490084229725479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53632004747660056153150319 80448007121490084229725479)
      ·
        refine ⟨120672010682235126344588219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80448007121490084229725479 120672010682235126344588219)
        ·
          refine ⟨181008016023352689516882329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120672010682235126344588219 181008016023352689516882329)
          ·
            refine ⟨135756012017514517137661747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181008016023352689516882329 135756012017514517137661747)
            ·
              refine ⟨203634018026271775706492621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135756012017514517137661747 203634018026271775706492621)
              ·
                refine ⟨76362756759851915889934733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203634018026271775706492621 76362756759851915889934733)
                ·
                  refine ⟨28636033784944468458725525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76362756759851915889934733 28636033784944468458725525)
                  ·
                    refine ⟨1342314083669271959002759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28636033784944468458725525 1342314083669271959002759)
                    ·
                      rfl

theorem cell22_3921221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_3921221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921221 prefixEnd_3921221 := by exact prefixLift 3921221
  have htrace : WordTrace (prefixWord ++ tailWord_3921221) baseStart_3921221 baseEnd_3921221 := by
    simpa [prefixWord, tailWord_3921221, baseEnd_3921221] using wordTrace_append hprefix tailTrace_3921221
  have hstable : (prefixWord ++ tailWord_3921221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921221).length < 2 ^ (prefixWord ++ tailWord_3921221).sum := by decide
  have hdescent : baseEnd_3921221 < baseStart_3921221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921328 : List Nat := [2, 1, 1, 1, 2, 1, 1, 6, 3, 4]
def baseStart_3921328 : Nat := 118140960795 + 3921328 * 2 ^ 59
def prefixEnd_3921328 : Nat := 4983230072969 + 3 ^ 40 * 3921328 * 2
def baseEnd_3921328 : Nat := 1342350711955959346577431

theorem tailTrace_3921328 : CollatzResearch.WordTrace tailWord_3921328 prefixEnd_3921328 1342350711955959346577431 := by
  unfold tailWord_3921328
  simp only [CollatzResearch.WordTrace]
  refine ⟨71511290968852920174606319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95348387958470560232808425 71511290968852920174606319)
  ·
    refine ⟨107266936453279380261909479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71511290968852920174606319 107266936453279380261909479)
    ·
      refine ⟨160900404679919070392864219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107266936453279380261909479 160900404679919070392864219)
      ·
        refine ⟨241350607019878605589296329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160900404679919070392864219 241350607019878605589296329)
        ·
          refine ⟨181012955264908954191972247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241350607019878605589296329 181012955264908954191972247)
          ·
            refine ⟨271519432897363431287958371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181012955264908954191972247 271519432897363431287958371)
            ·
              refine ⟨407279149346045146931937557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271519432897363431287958371 407279149346045146931937557)
              ·
                refine ⟨19091210125595866262434573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 407279149346045146931937557 19091210125595866262434573)
                ·
                  refine ⟨7159203797098449848412965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19091210125595866262434573 7159203797098449848412965)
                  ·
                    refine ⟨1342350711955959346577431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7159203797098449848412965 1342350711955959346577431)
                    ·
                      rfl

theorem cell22_3921328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 3, 4].length) (baseStart_3921328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921328 prefixEnd_3921328 := by exact prefixLift 3921328
  have htrace : WordTrace (prefixWord ++ tailWord_3921328) baseStart_3921328 baseEnd_3921328 := by
    simpa [prefixWord, tailWord_3921328, baseEnd_3921328] using wordTrace_append hprefix tailTrace_3921328
  have hstable : (prefixWord ++ tailWord_3921328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921328).length < 2 ^ (prefixWord ++ tailWord_3921328).sum := by decide
  have hdescent : baseEnd_3921328 < baseStart_3921328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921375 : List Nat := [1, 1, 2, 3, 3, 1, 1, 3, 4, 3]
def baseStart_3921375 : Nat := 118140960795 + 3921375 * 2 ^ 59
def prefixEnd_3921375 : Nat := 4983230072969 + 3 ^ 40 * 3921375 * 2
def baseEnd_3921375 : Nat := 1342366801016466890652287

theorem tailTrace_3921375 : CollatzResearch.WordTrace tailWord_3921375 prefixEnd_3921375 1342366801016466890652287 := by
  unfold tailWord_3921375
  simp only [CollatzResearch.WordTrace]
  refine ⟨143024296168535567376173579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95349530779023711584115719 143024296168535567376173579)
  ·
    refine ⟨214536444252803351064260369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143024296168535567376173579 214536444252803351064260369)
    ·
      refine ⟨160902333189602513298195277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214536444252803351064260369 160902333189602513298195277)
      ·
        refine ⟨60338374946100942486823229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160902333189602513298195277 60338374946100942486823229)
        ·
          refine ⟨22626890604787853432558711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60338374946100942486823229 22626890604787853432558711)
          ·
            refine ⟨33940335907181780148838067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22626890604787853432558711 33940335907181780148838067)
            ·
              refine ⟨50910503860772670223257101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33940335907181780148838067 50910503860772670223257101)
              ·
                refine ⟨19091438947789751333721413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50910503860772670223257101 19091438947789751333721413)
                ·
                  refine ⟨3579644802710578375072765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19091438947789751333721413 3579644802710578375072765)
                  ·
                    refine ⟨1342366801016466890652287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3579644802710578375072765 1342366801016466890652287)
                    ·
                      rfl

theorem cell22_3921375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 4, 3].length) (baseStart_3921375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921375 prefixEnd_3921375 := by exact prefixLift 3921375
  have htrace : WordTrace (prefixWord ++ tailWord_3921375) baseStart_3921375 baseEnd_3921375 := by
    simpa [prefixWord, tailWord_3921375, baseEnd_3921375] using wordTrace_append hprefix tailTrace_3921375
  have hstable : (prefixWord ++ tailWord_3921375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921375).length < 2 ^ (prefixWord ++ tailWord_3921375).sum := by decide
  have hdescent : baseEnd_3921375 < baseStart_3921375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921390 : List Nat := [4, 1, 2, 1, 2, 1, 1, 2, 4, 4]
def baseStart_3921390 : Nat := 118140960795 + 3921390 * 2 ^ 59
def prefixEnd_3921390 : Nat := 4983230072969 + 3 ^ 40 * 3921390 * 2
def baseEnd_3921390 : Nat := 1342371935823011851527241

theorem tailTrace_3921390 : CollatzResearch.WordTrace tailWord_3921390 prefixEnd_3921390 1342371935823011851527241 := by
  unfold tailWord_3921390
  simp only [CollatzResearch.WordTrace]
  refine ⟨17878105407935153117246203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95349895508987483291979749 17878105407935153117246203)
  ·
    refine ⟨26817158111902729675869305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17878105407935153117246203 26817158111902729675869305)
    ·
      refine ⟨20112868583927047256901979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26817158111902729675869305 20112868583927047256901979)
      ·
        refine ⟨30169302875890570885352969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20112868583927047256901979 30169302875890570885352969)
        ·
          refine ⟨22626977156917928164014727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30169302875890570885352969 22626977156917928164014727)
          ·
            refine ⟨33940465735376892246022091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22626977156917928164014727 33940465735376892246022091)
            ·
              refine ⟨50910698603065338369033137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33940465735376892246022091 50910698603065338369033137)
              ·
                refine ⟨38183023952299003776774853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50910698603065338369033137 38183023952299003776774853)
                ·
                  refine ⟨7159316991056063208145285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38183023952299003776774853 7159316991056063208145285)
                  ·
                    refine ⟨1342371935823011851527241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7159316991056063208145285 1342371935823011851527241)
                    ·
                      rfl

theorem cell22_3921390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_3921390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921390 prefixEnd_3921390 := by exact prefixLift 3921390
  have htrace : WordTrace (prefixWord ++ tailWord_3921390) baseStart_3921390 baseEnd_3921390 := by
    simpa [prefixWord, tailWord_3921390, baseEnd_3921390] using wordTrace_append hprefix tailTrace_3921390
  have hstable : (prefixWord ++ tailWord_3921390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921390).length < 2 ^ (prefixWord ++ tailWord_3921390).sum := by decide
  have hdescent : baseEnd_3921390 < baseStart_3921390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921392 : List Nat := [2, 1, 1, 1, 3, 5, 1, 3, 2, 3]
def baseStart_3921392 : Nat := 118140960795 + 3921392 * 2 ^ 59
def prefixEnd_3921392 : Nat := 4983230072969 + 3 ^ 40 * 3921392 * 2
def baseEnd_3921392 : Nat := 1342372620463884512977235

theorem tailTrace_3921392 : CollatzResearch.WordTrace tailWord_3921392 prefixEnd_3921392 1342372620463884512977235 := by
  unfold tailWord_3921392
  simp only [CollatzResearch.WordTrace]
  refine ⟨71512458104736989639771215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95349944139649319519694953 71512458104736989639771215)
  ·
    refine ⟨107268687157105484459656823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71512458104736989639771215 107268687157105484459656823)
    ·
      refine ⟨160903030735658226689485235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107268687157105484459656823 160903030735658226689485235)
      ·
        refine ⟨241354546103487340034227853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160903030735658226689485235 241354546103487340034227853)
        ·
          refine ⟨90507954788807752512835445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241354546103487340034227853 90507954788807752512835445)
          ·
            refine ⟨8485120761450726798078323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90507954788807752512835445 8485120761450726798078323)
            ·
              refine ⟨12727681142176090197117485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8485120761450726798078323 12727681142176090197117485)
              ·
                refine ⟨4772880428316033823919057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12727681142176090197117485 4772880428316033823919057)
                ·
                  refine ⟨3579660321237025367939293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4772880428316033823919057 3579660321237025367939293)
                  ·
                    refine ⟨1342372620463884512977235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3579660321237025367939293 1342372620463884512977235)
                    ·
                      rfl

theorem cell22_3921392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 2, 3].length) (baseStart_3921392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921392 prefixEnd_3921392 := by exact prefixLift 3921392
  have htrace : WordTrace (prefixWord ++ tailWord_3921392) baseStart_3921392 baseEnd_3921392 := by
    simpa [prefixWord, tailWord_3921392, baseEnd_3921392] using wordTrace_append hprefix tailTrace_3921392
  have hstable : (prefixWord ++ tailWord_3921392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921392).length < 2 ^ (prefixWord ++ tailWord_3921392).sum := by decide
  have hdescent : baseEnd_3921392 < baseStart_3921392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921428 : List Nat := [2, 4, 3, 1, 2, 2, 2, 2, 4]
def baseStart_3921428 : Nat := 118140960795 + 3921428 * 2 ^ 59
def prefixEnd_3921428 : Nat := 4983230072969 + 3 ^ 40 * 3921428 * 2
def baseEnd_3921428 : Nat := 447461647999864139692375

theorem tailTrace_3921428 : CollatzResearch.WordTrace tailWord_3921428 prefixEnd_3921428 447461647999864139692375 := by
  unfold tailWord_3921428
  simp only [CollatzResearch.WordTrace]
  refine ⟨71513114618671778713926469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95350819491562371618568625 71513114618671778713926469)
  ·
    refine ⟨13408708991000958508861213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71513114618671778713926469 13408708991000958508861213)
    ·
      refine ⟨5028265871625359440822955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13408708991000958508861213 5028265871625359440822955)
      ·
        refine ⟨7542398807438039161234433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5028265871625359440822955 7542398807438039161234433)
        ·
          refine ⟨5656799105578529370925825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7542398807438039161234433 5656799105578529370925825)
          ·
            refine ⟨4242599329183897028194369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5656799105578529370925825 4242599329183897028194369)
            ·
              refine ⟨3181949496887922771145777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4242599329183897028194369 3181949496887922771145777)
              ·
                refine ⟨2386462122665942078359333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3181949496887922771145777 2386462122665942078359333)
                ·
                  refine ⟨447461647999864139692375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2386462122665942078359333 447461647999864139692375)
                  ·
                    rfl

theorem cell22_3921428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_3921428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921428 prefixEnd_3921428 := by exact prefixLift 3921428
  have htrace : WordTrace (prefixWord ++ tailWord_3921428) baseStart_3921428 baseEnd_3921428 := by
    simpa [prefixWord, tailWord_3921428, baseEnd_3921428] using wordTrace_append hprefix tailTrace_3921428
  have hstable : (prefixWord ++ tailWord_3921428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921428).length < 2 ^ (prefixWord ++ tailWord_3921428).sum := by decide
  have hdescent : baseEnd_3921428 < baseStart_3921428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921437 : List Nat := [1, 4, 2, 2, 1, 1, 2, 3, 3, 3]
def baseStart_3921437 : Nat := 118140960795 + 3921437 * 2 ^ 59
def prefixEnd_3921437 : Nat := 4983230072969 + 3 ^ 40 * 3921437 * 2
def baseEnd_3921437 : Nat := 1342388024883519395602097

theorem tailTrace_3921437 : CollatzResearch.WordTrace tailWord_3921437 prefixEnd_3921437 1342388024883519395602097 := by
  unfold tailWord_3921437
  simp only [CollatzResearch.WordTrace]
  refine ⟨143026557494310951964930565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95351038329540634643287043 143026557494310951964930565)
  ·
    refine ⟨26817479530183303493424481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143026557494310951964930565 26817479530183303493424481)
    ·
      refine ⟨20113109647637477620068361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26817479530183303493424481 20113109647637477620068361)
      ·
        refine ⟨15084832235728108215051271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20113109647637477620068361 15084832235728108215051271)
        ·
          refine ⟨22627248353592162322576907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15084832235728108215051271 22627248353592162322576907)
          ·
            refine ⟨33940872530388243483865361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22627248353592162322576907 33940872530388243483865361)
            ·
              refine ⟨25455654397791182612899021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33940872530388243483865361 25455654397791182612899021)
              ·
                refine ⟨9545870399171693479837133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25455654397791182612899021 9545870399171693479837133)
                ·
                  refine ⟨3579701399689385054938925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9545870399171693479837133 3579701399689385054938925)
                  ·
                    refine ⟨1342388024883519395602097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3579701399689385054938925 1342388024883519395602097)
                    ·
                      rfl

theorem cell22_3921437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_3921437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921437 prefixEnd_3921437 := by exact prefixLift 3921437
  have htrace : WordTrace (prefixWord ++ tailWord_3921437) baseStart_3921437 baseEnd_3921437 := by
    simpa [prefixWord, tailWord_3921437, baseEnd_3921437] using wordTrace_append hprefix tailTrace_3921437
  have hstable : (prefixWord ++ tailWord_3921437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921437).length < 2 ^ (prefixWord ++ tailWord_3921437).sum := by decide
  have hdescent : baseEnd_3921437 < baseStart_3921437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921454 : List Nat := [4, 1, 3, 1, 2, 2, 1, 2, 3, 3]
def baseStart_3921454 : Nat := 118140960795 + 3921454 * 2 ^ 59
def prefixEnd_3921454 : Nat := 4983230072969 + 3 ^ 40 * 3921454 * 2
def baseEnd_3921454 : Nat := 1342393844330937017927045

theorem tailTrace_3921454 : CollatzResearch.WordTrace tailWord_3921454 prefixEnd_3921454 1342393844330937017927045 := by
  unfold tailWord_3921454
  simp only [CollatzResearch.WordTrace]
  refine ⟨17878397191906170483537427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95351451690166242578866277 17878397191906170483537427)
  ·
    refine ⟨26817595787859255725306141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17878397191906170483537427 26817595787859255725306141)
    ·
      refine ⟨10056598420447220896989803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26817595787859255725306141 10056598420447220896989803)
      ·
        refine ⟨15084897630670831345484705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10056598420447220896989803 15084897630670831345484705)
        ·
          refine ⟨11313673223003123509113529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15084897630670831345484705 11313673223003123509113529)
          ·
            refine ⟨8485254917252342631835147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11313673223003123509113529 8485254917252342631835147)
            ·
              refine ⟨12727882375878513947752721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8485254917252342631835147 12727882375878513947752721)
              ·
                refine ⟨9545911781908885460814541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12727882375878513947752721 9545911781908885460814541)
                ·
                  refine ⟨3579716918215832047805453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9545911781908885460814541 3579716918215832047805453)
                  ·
                    refine ⟨1342393844330937017927045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3579716918215832047805453 1342393844330937017927045)
                    ·
                      rfl

theorem cell22_3921454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_3921454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921454 prefixEnd_3921454 := by exact prefixLift 3921454
  have htrace : WordTrace (prefixWord ++ tailWord_3921454) baseStart_3921454 baseEnd_3921454 := by
    simpa [prefixWord, tailWord_3921454, baseEnd_3921454] using wordTrace_append hprefix tailTrace_3921454
  have hstable : (prefixWord ++ tailWord_3921454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921454).length < 2 ^ (prefixWord ++ tailWord_3921454).sum := by decide
  have hdescent : baseEnd_3921454 < baseStart_3921454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921495 : List Nat := [1, 1, 3, 2, 2, 3, 1, 3, 6]
def baseStart_3921495 : Nat := 118140960795 + 3921495 * 2 ^ 59
def prefixEnd_3921495 : Nat := 4983230072969 + 3 ^ 40 * 3921495 * 2
def baseEnd_3921495 : Nat := 447469293156275525883973

theorem tailTrace_3921495 : CollatzResearch.WordTrace tailWord_3921495 prefixEnd_3921495 447469293156275525883973 := by
  unfold tailWord_3921495
  simp only [CollatzResearch.WordTrace]
  refine ⟨143028672928100827870541939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95352448618733885247027959 143028672928100827870541939)
  ·
    refine ⟨214543009392151241805812909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143028672928100827870541939 214543009392151241805812909)
    ·
      refine ⟨80453628522056715677179841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214543009392151241805812909 80453628522056715677179841)
      ·
        refine ⟨60340221391542536757884881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80453628522056715677179841 60340221391542536757884881)
        ·
          refine ⟨45255166043656902568413661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60340221391542536757884881 45255166043656902568413661)
          ·
            refine ⟨16970687266371338463155123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45255166043656902568413661 16970687266371338463155123)
            ·
              refine ⟨25456030899557007694732685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16970687266371338463155123 25456030899557007694732685)
              ·
                refine ⟨9546011587333877885524757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25456030899557007694732685 9546011587333877885524757)
                ·
                  refine ⟨447469293156275525883973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9546011587333877885524757 447469293156275525883973)
                  ·
                    rfl

theorem cell22_3921495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 6].length) (baseStart_3921495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921495 prefixEnd_3921495 := by exact prefixLift 3921495
  have htrace : WordTrace (prefixWord ++ tailWord_3921495) baseStart_3921495 baseEnd_3921495 := by
    simpa [prefixWord, tailWord_3921495, baseEnd_3921495] using wordTrace_append hprefix tailTrace_3921495
  have hstable : (prefixWord ++ tailWord_3921495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921495).length < 2 ^ (prefixWord ++ tailWord_3921495).sum := by decide
  have hdescent : baseEnd_3921495 < baseStart_3921495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921512 : List Nat := [2, 1, 4, 3, 1, 1, 2, 2, 6]
def baseStart_3921512 : Nat := 118140960795 + 3921512 * 2 ^ 59
def prefixEnd_3921512 : Nat := 4983230072969 + 3 ^ 40 * 3921512 * 2
def baseEnd_3921512 : Nat := 447471232972081399992289

theorem tailTrace_3921512 : CollatzResearch.WordTrace tailWord_3921512 prefixEnd_3921512 447471232972081399992289 := by
  unfold tailWord_3921512
  simp only [CollatzResearch.WordTrace]
  refine ⟨71514646484519619886955395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95352861979359493182607193 71514646484519619886955395)
  ·
    refine ⟨107271969726779429830433093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71514646484519619886955395 107271969726779429830433093)
    ·
      refine ⟨20113494323771143093206205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107271969726779429830433093 20113494323771143093206205)
      ·
        refine ⟨7542560371414178659952327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20113494323771143093206205 7542560371414178659952327)
        ·
          refine ⟨11313840557121267989928491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7542560371414178659952327 11313840557121267989928491)
          ·
            refine ⟨16970760835681901984892737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11313840557121267989928491 16970760835681901984892737)
            ·
              refine ⟨12728070626761426488669553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16970760835681901984892737 12728070626761426488669553)
              ·
                refine ⟨9546052970071069866502165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12728070626761426488669553 9546052970071069866502165)
                ·
                  refine ⟨447471232972081399992289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9546052970071069866502165 447471232972081399992289)
                  ·
                    rfl

theorem cell22_3921512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 6].length) (baseStart_3921512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921512 prefixEnd_3921512 := by exact prefixLift 3921512
  have htrace : WordTrace (prefixWord ++ tailWord_3921512) baseStart_3921512 baseEnd_3921512 := by
    simpa [prefixWord, tailWord_3921512, baseEnd_3921512] using wordTrace_append hprefix tailTrace_3921512
  have hstable : (prefixWord ++ tailWord_3921512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921512).length < 2 ^ (prefixWord ++ tailWord_3921512).sum := by decide
  have hdescent : baseEnd_3921512 < baseStart_3921512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921514 : List Nat := [3, 1, 3, 2, 1, 3, 2, 2, 1, 4]
def baseStart_3921514 : Nat := 118140960795 + 3921514 * 2 ^ 59
def prefixEnd_3921514 : Nat := 4983230072969 + 3 ^ 40 * 3921514 * 2
def baseEnd_3921514 : Nat := 1342414383557116861426861

theorem tailTrace_3921514 : CollatzResearch.WordTrace tailWord_3921514 prefixEnd_3921514 1342414383557116861426861 := by
  unfold tailWord_3921514
  simp only [CollatzResearch.WordTrace]
  refine ⟨35757341478757998528870899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95352910610021329410322397 35757341478757998528870899)
  ·
    refine ⟨53636012218136997793306349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35757341478757998528870899 53636012218136997793306349)
    ·
      refine ⟨20113504581801374172489881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53636012218136997793306349 20113504581801374172489881)
      ·
        refine ⟨15085128436351030629367411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20113504581801374172489881 15085128436351030629367411)
        ·
          refine ⟨22627692654526545944051117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15085128436351030629367411 22627692654526545944051117)
          ·
            refine ⟨8485384745447454729019169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22627692654526545944051117 8485384745447454729019169)
            ·
              refine ⟨6364038559085591046764377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8485384745447454729019169 6364038559085591046764377)
              ·
                refine ⟨4773028919314193285073283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6364038559085591046764377 4773028919314193285073283)
                ·
                  refine ⟨7159543378971289927609925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4773028919314193285073283 7159543378971289927609925)
                  ·
                    refine ⟨1342414383557116861426861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7159543378971289927609925 1342414383557116861426861)
                    ·
                      rfl

theorem cell22_3921514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_3921514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921514 prefixEnd_3921514 := by exact prefixLift 3921514
  have htrace : WordTrace (prefixWord ++ tailWord_3921514) baseStart_3921514 baseEnd_3921514 := by
    simpa [prefixWord, tailWord_3921514, baseEnd_3921514] using wordTrace_append hprefix tailTrace_3921514
  have hstable : (prefixWord ++ tailWord_3921514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921514).length < 2 ^ (prefixWord ++ tailWord_3921514).sum := by decide
  have hdescent : baseEnd_3921514 < baseStart_3921514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921546 : List Nat := [3, 1, 2, 3, 2, 2, 3, 2, 4]
def baseStart_3921546 : Nat := 118140960795 + 3921546 * 2 ^ 59
def prefixEnd_3921546 : Nat := 4983230072969 + 3 ^ 40 * 3921546 * 2
def baseEnd_3921546 : Nat := 447475112603693148208921

theorem tailTrace_3921546 : CollatzResearch.WordTrace tailWord_3921546 prefixEnd_3921546 447475112603693148208921 := by
  unfold tailWord_3921546
  simp only [CollatzResearch.WordTrace]
  refine ⟨35757633262729015895162123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95353688700610709053765661 35757633262729015895162123)
  ·
    refine ⟨53636449894093523842743185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35757633262729015895162123 53636449894093523842743185)
    ·
      refine ⟨40227337420570142882057389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53636449894093523842743185 40227337420570142882057389)
      ·
        refine ⟨15085251532713803580771521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40227337420570142882057389 15085251532713803580771521)
        ·
          refine ⟨11313938649535352685578641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15085251532713803580771521 11313938649535352685578641)
          ·
            refine ⟨8485453987151514514183981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11313938649535352685578641 8485453987151514514183981)
            ·
              refine ⟨3182045245181817942818993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8485453987151514514183981 3182045245181817942818993)
              ·
                refine ⟨2386533933886363457114245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3182045245181817942818993 2386533933886363457114245)
                ·
                  refine ⟨447475112603693148208921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2386533933886363457114245 447475112603693148208921)
                  ·
                    rfl

theorem cell22_3921546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 2, 4].length) (baseStart_3921546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921546 prefixEnd_3921546 := by exact prefixLift 3921546
  have htrace : WordTrace (prefixWord ++ tailWord_3921546) baseStart_3921546 baseEnd_3921546 := by
    simpa [prefixWord, tailWord_3921546, baseEnd_3921546] using wordTrace_append hprefix tailTrace_3921546
  have hstable : (prefixWord ++ tailWord_3921546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921546).length < 2 ^ (prefixWord ++ tailWord_3921546).sum := by decide
  have hdescent : baseEnd_3921546 < baseStart_3921546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921617 : List Nat := [1, 2, 2, 1, 2, 5, 1, 1, 2, 5]
def baseStart_3921617 : Nat := 118140960795 + 3921617 * 2 ^ 59
def prefixEnd_3921617 : Nat := 4983230072969 + 3 ^ 40 * 3921617 * 2
def baseEnd_3921617 : Nat := 1342449642562058926101545

theorem tailTrace_3921617 : CollatzResearch.WordTrace tailWord_3921617 prefixEnd_3921617 1342449642562058926101545 := by
  unfold tailWord_3921617
  simp only [CollatzResearch.WordTrace]
  refine ⟨143033122633658842706483105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95355415089105895137655403 143033122633658842706483105)
  ·
    refine ⟨107274841975244132029862329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143033122633658842706483105 107274841975244132029862329)
    ·
      refine ⟨80456131481433099022396747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107274841975244132029862329 80456131481433099022396747)
      ·
        refine ⟨120684197222149648533595121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80456131481433099022396747 120684197222149648533595121)
        ·
          refine ⟨90513147916612236400196341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120684197222149648533595121 90513147916612236400196341)
          ·
            refine ⟨8485607617182397162518407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90513147916612236400196341 8485607617182397162518407)
            ·
              refine ⟨12728411425773595743777611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8485607617182397162518407 12728411425773595743777611)
              ·
                refine ⟨19092617138660393615666417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12728411425773595743777611 19092617138660393615666417)
                ·
                  refine ⟨14319462853995295211749813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19092617138660393615666417 14319462853995295211749813)
                  ·
                    refine ⟨1342449642562058926101545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14319462853995295211749813 1342449642562058926101545)
                    ·
                      rfl

theorem cell22_3921617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_3921617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921617 prefixEnd_3921617 := by exact prefixLift 3921617
  have htrace : WordTrace (prefixWord ++ tailWord_3921617) baseStart_3921617 baseEnd_3921617 := by
    simpa [prefixWord, tailWord_3921617, baseEnd_3921617] using wordTrace_append hprefix tailTrace_3921617
  have hstable : (prefixWord ++ tailWord_3921617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921617).length < 2 ^ (prefixWord ++ tailWord_3921617).sum := by decide
  have hdescent : baseEnd_3921617 < baseStart_3921617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921632 : List Nat := [2, 1, 1, 3, 1, 2, 4, 1, 3, 4]
def baseStart_3921632 : Nat := 118140960795 + 3921632 * 2 ^ 59
def prefixEnd_3921632 : Nat := 4983230072969 + 3 ^ 40 * 3921632 * 2
def baseEnd_3921632 : Nat := 1342454777368603886976499

theorem tailTrace_3921632 : CollatzResearch.WordTrace tailWord_3921632 prefixEnd_3921632 1342454777368603886976499 := by
  unfold tailWord_3921632
  simp only [CollatzResearch.WordTrace]
  refine ⟨71516834864302250134139575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95355779819069666845519433 71516834864302250134139575)
  ·
    refine ⟨107275252296453375201209363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71516834864302250134139575 107275252296453375201209363)
    ·
      refine ⟨160912878444680062801814045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107275252296453375201209363 160912878444680062801814045)
      ·
        refine ⟨60342329416755023550680267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160912878444680062801814045 60342329416755023550680267)
        ·
          refine ⟨90513494125132535326020401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60342329416755023550680267 90513494125132535326020401)
          ·
            refine ⟨67885120593849401494515301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90513494125132535326020401 67885120593849401494515301)
            ·
              refine ⟨12728460111346762780221619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67885120593849401494515301 12728460111346762780221619)
              ·
                refine ⟨19092690167020144170332429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12728460111346762780221619 19092690167020144170332429)
                ·
                  refine ⟨7159758812632554063874661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19092690167020144170332429 7159758812632554063874661)
                  ·
                    refine ⟨1342454777368603886976499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7159758812632554063874661 1342454777368603886976499)
                    ·
                      rfl

theorem cell22_3921632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 3, 4].length) (baseStart_3921632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921632 prefixEnd_3921632 := by exact prefixLift 3921632
  have htrace : WordTrace (prefixWord ++ tailWord_3921632) baseStart_3921632 baseEnd_3921632 := by
    simpa [prefixWord, tailWord_3921632, baseEnd_3921632] using wordTrace_append hprefix tailTrace_3921632
  have hstable : (prefixWord ++ tailWord_3921632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921632).length < 2 ^ (prefixWord ++ tailWord_3921632).sum := by decide
  have hdescent : baseEnd_3921632 < baseStart_3921632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921649 : List Nat := [1, 2, 2, 2, 2, 4, 1, 3, 1, 4]
def baseStart_3921649 : Nat := 118140960795 + 3921649 * 2 ^ 59
def prefixEnd_3921649 : Nat := 4983230072969 + 3 ^ 40 * 3921649 * 2
def baseEnd_3921649 : Nat := 1342460596816021509301447

theorem tailTrace_3921649 : CollatzResearch.WordTrace tailWord_3921649 prefixEnd_3921649 1342460596816021509301447 := by
  unfold tailWord_3921649
  simp only [CollatzResearch.WordTrace]
  refine ⟨143034289769542912171648001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95356193179695274781098667 143034289769542912171648001)
  ·
    refine ⟨107275717327157184128736001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143034289769542912171648001 107275717327157184128736001)
    ·
      refine ⟨80456787995367888096552001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107275717327157184128736001 80456787995367888096552001)
      ·
        refine ⟨60342590996525916072414001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80456787995367888096552001 60342590996525916072414001)
        ·
          refine ⟨45256943247394437054310501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60342590996525916072414001 45256943247394437054310501)
          ·
            refine ⟨8485676858886456947683219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45256943247394437054310501 8485676858886456947683219)
            ·
              refine ⟨12728515288329685421524829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8485676858886456947683219 12728515288329685421524829)
              ·
                refine ⟨4773193233123632033071811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12728515288329685421524829 4773193233123632033071811)
                ·
                  refine ⟨7159789849685448049607717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4773193233123632033071811 7159789849685448049607717)
                  ·
                    refine ⟨1342460596816021509301447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7159789849685448049607717 1342460596816021509301447)
                    ·
                      rfl

theorem cell22_3921649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 4].length) (baseStart_3921649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921649 prefixEnd_3921649 := by exact prefixLift 3921649
  have htrace : WordTrace (prefixWord ++ tailWord_3921649) baseStart_3921649 baseEnd_3921649 := by
    simpa [prefixWord, tailWord_3921649, baseEnd_3921649] using wordTrace_append hprefix tailTrace_3921649
  have hstable : (prefixWord ++ tailWord_3921649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921649).length < 2 ^ (prefixWord ++ tailWord_3921649).sum := by decide
  have hdescent : baseEnd_3921649 < baseStart_3921649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921692 : List Nat := [2, 2, 3, 1, 1, 2, 3, 8]
def baseStart_3921692 : Nat := 118140960795 + 3921692 * 2 ^ 59
def prefixEnd_3921692 : Nat := 4983230072969 + 3 ^ 40 * 3921692 * 2
def baseEnd_3921692 : Nat := 149163924066087081164035

theorem tailTrace_3921692 : CollatzResearch.WordTrace tailWord_3921692 prefixEnd_3921692 149163924066087081164035 := by
  unfold tailWord_3921692
  simp only [CollatzResearch.WordTrace]
  refine ⟨71517929054193565257731665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95357238738924753676975553 71517929054193565257731665)
  ·
    refine ⟨53638446790645173943298749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71517929054193565257731665 53638446790645173943298749)
    ·
      refine ⟨20114417546491940228737031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53638446790645173943298749 20114417546491940228737031)
      ·
        refine ⟨30171626319737910343105547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20114417546491940228737031 30171626319737910343105547)
        ·
          refine ⟨45257439479606865514658321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30171626319737910343105547 45257439479606865514658321)
          ·
            refine ⟨33943079609705149135993741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45257439479606865514658321 33943079609705149135993741)
            ·
              refine ⟨12728654853639430925997653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33943079609705149135993741 12728654853639430925997653)
              ·
                refine ⟨149163924066087081164035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12728654853639430925997653 149163924066087081164035)
                ·
                  rfl

theorem cell22_3921692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 8].length) (baseStart_3921692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921692 prefixEnd_3921692 := by exact prefixLift 3921692
  have htrace : WordTrace (prefixWord ++ tailWord_3921692) baseStart_3921692 baseEnd_3921692 := by
    simpa [prefixWord, tailWord_3921692, baseEnd_3921692] using wordTrace_append hprefix tailTrace_3921692
  have hstable : (prefixWord ++ tailWord_3921692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921692).length < 2 ^ (prefixWord ++ tailWord_3921692).sum := by decide
  have hdescent : baseEnd_3921692 < baseStart_3921692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921752 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 6, 5]
def baseStart_3921752 : Nat := 118140960795 + 3921752 * 2 ^ 59
def prefixEnd_3921752 : Nat := 4983230072969 + 3 ^ 40 * 3921752 * 2
def baseEnd_3921752 : Nat := 1342495855820963573976131

theorem tailTrace_3921752 : CollatzResearch.WordTrace tailWord_3921752 prefixEnd_3921752 1342495855820963573976131 := by
  unfold tailWord_3921752
  simp only [CollatzResearch.WordTrace]
  refine ⟨71519023244084880381323755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95358697658779840508431673 71519023244084880381323755)
  ·
    refine ⟨107278534866127320571985633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71519023244084880381323755 107278534866127320571985633)
    ·
      refine ⟨80458901149595490428989225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107278534866127320571985633 80458901149595490428989225)
      ·
        refine ⟨60344175862196617821741919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80458901149595490428989225 60344175862196617821741919)
        ·
          refine ⟨90516263793294926732612879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60344175862196617821741919 90516263793294926732612879)
          ·
            refine ⟨135774395689942390098919319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90516263793294926732612879 135774395689942390098919319)
            ·
              refine ⟨203661593534913585148378979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135774395689942390098919319 203661593534913585148378979)
              ·
                refine ⟨305492390302370377722568469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203661593534913585148378979 305492390302370377722568469)
                ·
                  refine ⟨14319955795423611455745397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 305492390302370377722568469 14319955795423611455745397)
                  ·
                    refine ⟨1342495855820963573976131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14319955795423611455745397 1342495855820963573976131)
                    ·
                      rfl

theorem cell22_3921752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_3921752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921752 prefixEnd_3921752 := by exact prefixLift 3921752
  have htrace : WordTrace (prefixWord ++ tailWord_3921752) baseStart_3921752 baseEnd_3921752 := by
    simpa [prefixWord, tailWord_3921752, baseEnd_3921752] using wordTrace_append hprefix tailTrace_3921752
  have hstable : (prefixWord ++ tailWord_3921752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921752).length < 2 ^ (prefixWord ++ tailWord_3921752).sum := by decide
  have hdescent : baseEnd_3921752 < baseStart_3921752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921818 : List Nat := [3, 1, 1, 4, 2, 1, 4, 1, 1, 4]
def baseStart_3921818 : Nat := 118140960795 + 3921818 * 2 ^ 59
def prefixEnd_3921818 : Nat := 4983230072969 + 3 ^ 40 * 3921818 * 2
def baseEnd_3921818 : Nat := 1342518448969761401825929

theorem tailTrace_3921818 : CollatzResearch.WordTrace tailWord_3921818 prefixEnd_3921818 1342518448969761401825929 := by
  unfold tailWord_3921818
  simp only [CollatzResearch.WordTrace]
  refine ⟨35760113426482663508637527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95360302470620436023033405 35760113426482663508637527)
  ·
    refine ⟨53640170139723995262956291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35760113426482663508637527 53640170139723995262956291)
    ·
      refine ⟨80460255209585992894434437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53640170139723995262956291 80460255209585992894434437)
      ·
        refine ⟨15086297851797373667706457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80460255209585992894434437 15086297851797373667706457)
        ·
          refine ⟨11314723388848030250779843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15086297851797373667706457 11314723388848030250779843)
          ·
            refine ⟨16972085083272045376169765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11314723388848030250779843 16972085083272045376169765)
            ·
              refine ⟨3182265953113508508031831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16972085083272045376169765 3182265953113508508031831)
              ·
                refine ⟨4773398929670262762047747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3182265953113508508031831 4773398929670262762047747)
                ·
                  refine ⟨7160098394505394143071621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4773398929670262762047747 7160098394505394143071621)
                  ·
                    refine ⟨1342518448969761401825929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7160098394505394143071621 1342518448969761401825929)
                    ·
                      rfl

theorem cell22_3921818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 1, 4].length) (baseStart_3921818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921818 prefixEnd_3921818 := by exact prefixLift 3921818
  have htrace : WordTrace (prefixWord ++ tailWord_3921818) baseStart_3921818 baseEnd_3921818 := by
    simpa [prefixWord, tailWord_3921818, baseEnd_3921818] using wordTrace_append hprefix tailTrace_3921818
  have hstable : (prefixWord ++ tailWord_3921818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921818).length < 2 ^ (prefixWord ++ tailWord_3921818).sum := by decide
  have hdescent : baseEnd_3921818 < baseStart_3921818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921822 : List Nat := [4, 3, 1, 3, 2, 1, 1, 2, 5]
def baseStart_3921822 : Nat := 118140960795 + 3921822 * 2 ^ 59
def prefixEnd_3921822 : Nat := 4983230072969 + 3 ^ 40 * 3921822 * 2
def baseEnd_3921822 : Nat := 447506606083835574908639

theorem tailTrace_3921822 : CollatzResearch.WordTrace tailWord_3921822 prefixEnd_3921822 447506606083835574908639 := by
  unfold tailWord_3921822
  simp only [CollatzResearch.WordTrace]
  refine ⟨17880074949739520339711965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95360399731944108478463813 17880074949739520339711965)
  ·
    refine ⟨6705028106152320127391987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17880074949739520339711965 6705028106152320127391987)
    ·
      refine ⟨10057542159228480191087981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6705028106152320127391987 10057542159228480191087981)
      ·
        refine ⟨3771578309710680071657993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10057542159228480191087981 3771578309710680071657993)
        ·
          refine ⟨2828683732283010053743495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3771578309710680071657993 2828683732283010053743495)
          ·
            refine ⟨4243025598424515080615243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2828683732283010053743495 4243025598424515080615243)
            ·
              refine ⟨6364538397636772620922865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4243025598424515080615243 6364538397636772620922865)
              ·
                refine ⟨4773403798227579465692149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6364538397636772620922865 4773403798227579465692149)
                ·
                  refine ⟨447506606083835574908639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4773403798227579465692149 447506606083835574908639)
                  ·
                    rfl

theorem cell22_3921822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_3921822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921822 prefixEnd_3921822 := by exact prefixLift 3921822
  have htrace : WordTrace (prefixWord ++ tailWord_3921822) baseStart_3921822 baseEnd_3921822 := by
    simpa [prefixWord, tailWord_3921822, baseEnd_3921822] using wordTrace_append hprefix tailTrace_3921822
  have hstable : (prefixWord ++ tailWord_3921822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921822).length < 2 ^ (prefixWord ++ tailWord_3921822).sum := by decide
  have hdescent : baseEnd_3921822 < baseStart_3921822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921829 : List Nat := [1, 3, 1, 2, 1, 1, 1, 6, 2, 4]
def baseStart_3921829 : Nat := 118140960795 + 3921829 * 2 ^ 59
def prefixEnd_3921829 : Nat := 4983230072969 + 3 ^ 40 * 3921829 * 2
def baseEnd_3921829 : Nat := 1342522214494561039800895

theorem tailTrace_3921829 : CollatzResearch.WordTrace tailWord_3921829 prefixEnd_3921829 1342522214494561039800895 := by
  unfold tailWord_3921829
  simp only [CollatzResearch.WordTrace]
  refine ⟨143040854908890802913200541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95360569939260535275467027 143040854908890802913200541)
  ·
    refine ⟨53640320590834051092450203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143040854908890802913200541 53640320590834051092450203)
    ·
      refine ⟨80460480886251076638675305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53640320590834051092450203 80460480886251076638675305)
      ·
        refine ⟨60345360664688307479006479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80460480886251076638675305 60345360664688307479006479)
        ·
          refine ⟨90518040997032461218509719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60345360664688307479006479 90518040997032461218509719)
          ·
            refine ⟨135777061495548691827764579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90518040997032461218509719 135777061495548691827764579)
            ·
              refine ⟨203665592243323037741646869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135777061495548691827764579 203665592243323037741646869)
              ·
                refine ⟨9546824636405767394139697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 203665592243323037741646869 9546824636405767394139697)
                ·
                  refine ⟨7160118477304325545604773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9546824636405767394139697 7160118477304325545604773)
                  ·
                    refine ⟨1342522214494561039800895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7160118477304325545604773 1342522214494561039800895)
                    ·
                      rfl

theorem cell22_3921829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_3921829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921829 prefixEnd_3921829 := by exact prefixLift 3921829
  have htrace : WordTrace (prefixWord ++ tailWord_3921829) baseStart_3921829 baseEnd_3921829 := by
    simpa [prefixWord, tailWord_3921829, baseEnd_3921829] using wordTrace_append hprefix tailTrace_3921829
  have hstable : (prefixWord ++ tailWord_3921829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921829).length < 2 ^ (prefixWord ++ tailWord_3921829).sum := by decide
  have hdescent : baseEnd_3921829 < baseStart_3921829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921848 : List Nat := [2, 1, 2, 1, 2, 3, 5, 1, 2, 3]
def baseStart_3921848 : Nat := 118140960795 + 3921848 * 2 ^ 59
def prefixEnd_3921848 : Nat := 4983230072969 + 3 ^ 40 * 3921848 * 2
def baseEnd_3921848 : Nat := 1342528718582851323575837

theorem tailTrace_3921848 : CollatzResearch.WordTrace tailWord_3921848 prefixEnd_3921848 1342528718582851323575837 := by
  unfold tailWord_3921848
  simp only [CollatzResearch.WordTrace]
  refine ⟨71520773947910984579071099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95361031930547979438761465 71520773947910984579071099)
  ·
    refine ⟨107281160921866476868606649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71520773947910984579071099 107281160921866476868606649)
    ·
      refine ⟨80460870691399857651454987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107281160921866476868606649 80460870691399857651454987)
      ·
        refine ⟨120691306037099786477182481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80460870691399857651454987 120691306037099786477182481)
        ·
          refine ⟨90518479527824839857886861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120691306037099786477182481 90518479527824839857886861)
          ·
            refine ⟨33944429822934314946707573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90518479527824839857886861 33944429822934314946707573)
            ·
              refine ⟨3182290295900092026253835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33944429822934314946707573 3182290295900092026253835)
              ·
                refine ⟨4773435443850138039380753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3182290295900092026253835 4773435443850138039380753)
                ·
                  refine ⟨3580076582887603529535565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4773435443850138039380753 3580076582887603529535565)
                  ·
                    refine ⟨1342528718582851323575837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3580076582887603529535565 1342528718582851323575837)
                    ·
                      rfl

theorem cell22_3921848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 2, 3].length) (baseStart_3921848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921848 prefixEnd_3921848 := by exact prefixLift 3921848
  have htrace : WordTrace (prefixWord ++ tailWord_3921848) baseStart_3921848 baseEnd_3921848 := by
    simpa [prefixWord, tailWord_3921848, baseEnd_3921848] using wordTrace_append hprefix tailTrace_3921848
  have hstable : (prefixWord ++ tailWord_3921848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921848).length < 2 ^ (prefixWord ++ tailWord_3921848).sum := by decide
  have hdescent : baseEnd_3921848 < baseStart_3921848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921878 : List Nat := [5, 2, 1, 1, 3, 2, 8]
def baseStart_3921878 : Nat := 118140960795 + 3921878 * 2 ^ 59
def prefixEnd_3921878 : Nat := 4983230072969 + 3 ^ 40 * 3921878 * 2
def baseEnd_3921878 : Nat := 49723666229479305382435

theorem tailTrace_3921878 : CollatzResearch.WordTrace tailWord_3921878 prefixEnd_3921878 49723666229479305382435 := by
  unfold tailWord_3921878
  simp only [CollatzResearch.WordTrace]
  refine ⟨8940165130357080267608393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95361761390475522854489525 8940165130357080267608393)
  ·
    refine ⟨6705123847767810200706295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8940165130357080267608393 6705123847767810200706295)
    ·
      refine ⟨10057685771651715301059443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6705123847767810200706295 10057685771651715301059443)
      ·
        refine ⟨15086528657477572951589165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10057685771651715301059443 15086528657477572951589165)
        ·
          refine ⟨5657448246554089856845937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15086528657477572951589165 5657448246554089856845937)
          ·
            refine ⟨4243086184915567392634453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5657448246554089856845937 4243086184915567392634453)
            ·
              refine ⟨49723666229479305382435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4243086184915567392634453 49723666229479305382435)
              ·
                rfl

theorem cell22_3921878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 8].length) (baseStart_3921878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921878 prefixEnd_3921878 := by exact prefixLift 3921878
  have htrace : WordTrace (prefixWord ++ tailWord_3921878) baseStart_3921878 baseEnd_3921878 := by
    simpa [prefixWord, tailWord_3921878, baseEnd_3921878] using wordTrace_append hprefix tailTrace_3921878
  have hstable : (prefixWord ++ tailWord_3921878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921878).length < 2 ^ (prefixWord ++ tailWord_3921878).sum := by decide
  have hdescent : baseEnd_3921878 < baseStart_3921878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921884 : List Nat := [2, 2, 6, 1, 1, 1, 3, 2, 4]
def baseStart_3921884 : Nat := 118140960795 + 3921884 * 2 ^ 59
def prefixEnd_3921884 : Nat := 4983230072969 + 3 ^ 40 * 3921884 * 2
def baseEnd_3921884 : Nat := 447513680706186409891909

theorem tailTrace_3921884 : CollatzResearch.WordTrace tailWord_3921884 prefixEnd_3921884 447513680706186409891909 := by
  unfold tailWord_3921884
  simp only [CollatzResearch.WordTrace]
  refine ⟨71521430461845773653226353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95361907282461031537635137 71521430461845773653226353)
  ·
    refine ⟨53641072846384330239919765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71521430461845773653226353 53641072846384330239919765)
    ·
      refine ⟨2514425289674265479996239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53641072846384330239919765 2514425289674265479996239)
      ·
        refine ⟨3771637934511398219994359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2514425289674265479996239 3771637934511398219994359)
        ·
          refine ⟨5657456901767097329991539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3771637934511398219994359 5657456901767097329991539)
          ·
            refine ⟨8486185352650645994987309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5657456901767097329991539 8486185352650645994987309)
            ·
              refine ⟨3182319507243992248120241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8486185352650645994987309 3182319507243992248120241)
              ·
                refine ⟨2386739630432994186090181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3182319507243992248120241 2386739630432994186090181)
                ·
                  refine ⟨447513680706186409891909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2386739630432994186090181 447513680706186409891909)
                  ·
                    rfl

theorem cell22_3921884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 2, 4].length) (baseStart_3921884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921884 prefixEnd_3921884 := by exact prefixLift 3921884
  have htrace : WordTrace (prefixWord ++ tailWord_3921884) baseStart_3921884 baseEnd_3921884 := by
    simpa [prefixWord, tailWord_3921884, baseEnd_3921884] using wordTrace_append hprefix tailTrace_3921884
  have hstable : (prefixWord ++ tailWord_3921884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921884).length < 2 ^ (prefixWord ++ tailWord_3921884).sum := by decide
  have hdescent : baseEnd_3921884 < baseStart_3921884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921889 : List Nat := [1, 2, 3, 1, 2, 1, 4, 1, 7]
def baseStart_3921889 : Nat := 118140960795 + 3921889 * 2 ^ 59
def prefixEnd_3921889 : Nat := 4983230072969 + 3 ^ 40 * 3921889 * 2
def baseEnd_3921889 : Nat := 447514251240246961100237

theorem tailTrace_3921889 : CollatzResearch.WordTrace tailWord_3921889 prefixEnd_3921889 447514251240246961100237 := by
  unfold tailWord_3921889
  simp only [CollatzResearch.WordTrace]
  refine ⟨143043043288673433160384721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95362028859115622106923147 143043043288673433160384721)
  ·
    refine ⟨107282282466505074870288541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143043043288673433160384721 107282282466505074870288541)
    ·
      refine ⟨40230855924939403076358203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107282282466505074870288541 40230855924939403076358203)
      ·
        refine ⟨60346283887409104614537305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40230855924939403076358203 60346283887409104614537305)
        ·
          refine ⟨45259712915556828460902979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60346283887409104614537305 45259712915556828460902979)
          ·
            refine ⟨67889569373335242691354469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45259712915556828460902979 67889569373335242691354469)
            ·
              refine ⟨12729294257500358004628963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67889569373335242691354469 12729294257500358004628963)
              ·
                refine ⟨19093941386250537006943445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12729294257500358004628963 19093941386250537006943445)
                ·
                  refine ⟨447514251240246961100237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19093941386250537006943445 447514251240246961100237)
                  ·
                    rfl

theorem cell22_3921889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 7].length) (baseStart_3921889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921889 prefixEnd_3921889 := by exact prefixLift 3921889
  have htrace : WordTrace (prefixWord ++ tailWord_3921889) baseStart_3921889 baseEnd_3921889 := by
    simpa [prefixWord, tailWord_3921889, baseEnd_3921889] using wordTrace_append hprefix tailTrace_3921889
  have hstable : (prefixWord ++ tailWord_3921889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921889).length < 2 ^ (prefixWord ++ tailWord_3921889).sum := by decide
  have hdescent : baseEnd_3921889 < baseStart_3921889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921904 : List Nat := [2, 1, 1, 1, 3, 2, 2, 3, 2, 5]
def baseStart_3921904 : Nat := 118140960795 + 3921904 * 2 ^ 59
def prefixEnd_3921904 : Nat := 4983230072969 + 3 ^ 40 * 3921904 * 2
def baseEnd_3921904 : Nat := 1342547888527285844175665

theorem tailTrace_3921904 : CollatzResearch.WordTrace tailWord_3921904 prefixEnd_3921904 1342547888527285844175665 := by
  unfold tailWord_3921904
  simp only [CollatzResearch.WordTrace]
  refine ⟨71521795191809545361090383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95362393589079393814787177 71521795191809545361090383)
  ·
    refine ⟨107282692787714318041635575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71521795191809545361090383 107282692787714318041635575)
    ·
      refine ⟨160924039181571477062453363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107282692787714318041635575 160924039181571477062453363)
      ·
        refine ⟨241386058772357215593680045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160924039181571477062453363 241386058772357215593680045)
        ·
          refine ⟨90519772039633955847630017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241386058772357215593680045 90519772039633955847630017)
          ·
            refine ⟨67889829029725466885722513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90519772039633955847630017 67889829029725466885722513)
            ·
              refine ⟨50917371772294100164291885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67889829029725466885722513 50917371772294100164291885)
              ·
                refine ⟨19094014414610287561609457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50917371772294100164291885 19094014414610287561609457)
                ·
                  refine ⟨14320510810957715671207093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19094014414610287561609457 14320510810957715671207093)
                  ·
                    refine ⟨1342547888527285844175665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14320510810957715671207093 1342547888527285844175665)
                    ·
                      rfl

theorem cell22_3921904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 2, 5].length) (baseStart_3921904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921904 prefixEnd_3921904 := by exact prefixLift 3921904
  have htrace : WordTrace (prefixWord ++ tailWord_3921904) baseStart_3921904 baseEnd_3921904 := by
    simpa [prefixWord, tailWord_3921904, baseEnd_3921904] using wordTrace_append hprefix tailTrace_3921904
  have hstable : (prefixWord ++ tailWord_3921904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921904).length < 2 ^ (prefixWord ++ tailWord_3921904).sum := by decide
  have hdescent : baseEnd_3921904 < baseStart_3921904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921981 : List Nat := [1, 4, 1, 3, 1, 1, 3, 1, 1, 6]
def baseStart_3921981 : Nat := 118140960795 + 3921981 * 2 ^ 59
def prefixEnd_3921981 : Nat := 4983230072969 + 3 ^ 40 * 3921981 * 2
def baseEnd_3921981 : Nat := 1342574247200883310000429

theorem tailTrace_3921981 : CollatzResearch.WordTrace tailWord_3921981 prefixEnd_3921981 1342574247200883310000429 := by
  unfold tailWord_3921981
  simp only [CollatzResearch.WordTrace]
  refine ⟨143046398804340132872733797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95364265869560088581822531 143046398804340132872733797)
  ·
    refine ⟨26821199775813774913637587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143046398804340132872733797 26821199775813774913637587)
    ·
      refine ⟨40231799663720662370456381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26821199775813774913637587 40231799663720662370456381)
      ·
        refine ⟨15086924873895248388921143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40231799663720662370456381 15086924873895248388921143)
        ·
          refine ⟨22630387310842872583381715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15086924873895248388921143 22630387310842872583381715)
          ·
            refine ⟨33945580966264308875072573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22630387310842872583381715 33945580966264308875072573)
            ·
              refine ⟨12729592862349115828152215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33945580966264308875072573 12729592862349115828152215)
              ·
                refine ⟨19094389293523673742228323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12729592862349115828152215 19094389293523673742228323)
                ·
                  refine ⟨28641583940285510613342485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19094389293523673742228323 28641583940285510613342485)
                  ·
                    refine ⟨1342574247200883310000429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28641583940285510613342485 1342574247200883310000429)
                    ·
                      rfl

theorem cell22_3921981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_3921981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921981 prefixEnd_3921981 := by exact prefixLift 3921981
  have htrace : WordTrace (prefixWord ++ tailWord_3921981) baseStart_3921981 baseEnd_3921981 := by
    simpa [prefixWord, tailWord_3921981, baseEnd_3921981] using wordTrace_append hprefix tailTrace_3921981
  have hstable : (prefixWord ++ tailWord_3921981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921981).length < 2 ^ (prefixWord ++ tailWord_3921981).sum := by decide
  have hdescent : baseEnd_3921981 < baseStart_3921981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921985 : List Nat := [1, 2, 5, 1, 2, 2, 2, 3, 4]
def baseStart_3921985 : Nat := 118140960795 + 3921985 * 2 ^ 59
def prefixEnd_3921985 : Nat := 4983230072969 + 3 ^ 40 * 3921985 * 2
def baseEnd_3921985 : Nat := 447525205494209544300139

theorem tailTrace_3921985 : CollatzResearch.WordTrace tailWord_3921985 prefixEnd_3921985 447525205494209544300139 := by
  unfold tailWord_3921985
  simp only [CollatzResearch.WordTrace]
  refine ⟨143046544696325641555879409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95364363130883761037252939 143046544696325641555879409)
  ·
    refine ⟨107284908522244231166909557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143046544696325641555879409 107284908522244231166909557)
    ·
      refine ⟨10057960173960396671897771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107284908522244231166909557 10057960173960396671897771)
      ·
        refine ⟨15086940260940595007846657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10057960173960396671897771 15086940260940595007846657)
        ·
          refine ⟨11315205195705446255884993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15086940260940595007846657 11315205195705446255884993)
          ·
            refine ⟨8486403896779084691913745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11315205195705446255884993 8486403896779084691913745)
            ·
              refine ⟨6364802922584313518935309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8486403896779084691913745 6364802922584313518935309)
              ·
                refine ⟨2386801095969117569600741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6364802922584313518935309 2386801095969117569600741)
                ·
                  refine ⟨447525205494209544300139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2386801095969117569600741 447525205494209544300139)
                  ·
                    rfl

theorem cell22_3921985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 3, 4].length) (baseStart_3921985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3921985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3921985 prefixEnd_3921985 := by exact prefixLift 3921985
  have htrace : WordTrace (prefixWord ++ tailWord_3921985) baseStart_3921985 baseEnd_3921985 := by
    simpa [prefixWord, tailWord_3921985, baseEnd_3921985] using wordTrace_append hprefix tailTrace_3921985
  have hstable : (prefixWord ++ tailWord_3921985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921985).length < 2 ^ (prefixWord ++ tailWord_3921985).sum := by decide
  have hdescent : baseEnd_3921985 < baseStart_3921985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922028 : List Nat := [2, 2, 1, 1, 3, 3, 2, 2, 3, 3]
def baseStart_3922028 : Nat := 118140960795 + 3922028 * 2 ^ 59
def prefixEnd_3922028 : Nat := 4983230072969 + 3 ^ 40 * 3922028 * 2
def baseEnd_3922028 : Nat := 1342590336261390854075285

theorem tailTrace_3922028 : CollatzResearch.WordTrace tailWord_3922028 prefixEnd_3922028 1342590336261390854075285 := by
  unfold tailWord_3922028
  simp only [CollatzResearch.WordTrace]
  refine ⟨71524056517584929949847369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95365408690113239933129825 71524056517584929949847369)
  ·
    refine ⟨53643042388188697462385527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71524056517584929949847369 53643042388188697462385527)
    ·
      refine ⟨80464563582283046193578291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53643042388188697462385527 80464563582283046193578291)
      ·
        refine ⟨120696845373424569290367437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80464563582283046193578291 120696845373424569290367437)
        ·
          refine ⟨45261317015034213483887789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120696845373424569290367437 45261317015034213483887789)
          ·
            refine ⟨16972993880637830056457921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45261317015034213483887789 16972993880637830056457921)
            ·
              refine ⟨12729745410478372542343441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16972993880637830056457921 12729745410478372542343441)
              ·
                refine ⟨9547309057858779406757581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12729745410478372542343441 9547309057858779406757581)
                ·
                  refine ⟨3580240896697042277534093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9547309057858779406757581 3580240896697042277534093)
                  ·
                    refine ⟨1342590336261390854075285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3580240896697042277534093 1342590336261390854075285)
                    ·
                      rfl

theorem cell22_3922028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 3].length) (baseStart_3922028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3922028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3922028 prefixEnd_3922028 := by exact prefixLift 3922028
  have htrace : WordTrace (prefixWord ++ tailWord_3922028) baseStart_3922028 baseEnd_3922028 := by
    simpa [prefixWord, tailWord_3922028, baseEnd_3922028] using wordTrace_append hprefix tailTrace_3922028
  have hstable : (prefixWord ++ tailWord_3922028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922028).length < 2 ^ (prefixWord ++ tailWord_3922028).sum := by decide
  have hdescent : baseEnd_3922028 < baseStart_3922028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922041 : List Nat := [1, 2, 1, 3, 4, 1, 1, 2, 7]
def baseStart_3922041 : Nat := 118140960795 + 3922041 * 2 ^ 59
def prefixEnd_3922041 : Nat := 4983230072969 + 3 ^ 40 * 3922041 * 2
def baseEnd_3922041 : Nat := 447531595475687717833415

theorem tailTrace_3922041 : CollatzResearch.WordTrace tailWord_3922041 prefixEnd_3922041 447531595475687717833415 := by
  unfold tailWord_3922041
  simp only [CollatzResearch.WordTrace]
  refine ⟨143048587184122763119917977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95365724789415175413278651 143048587184122763119917977)
  ·
    refine ⟨107286440388092072339938483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143048587184122763119917977 107286440388092072339938483)
    ·
      refine ⟨160929660582138108509907725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107286440388092072339938483 160929660582138108509907725)
      ·
        refine ⟨60348622718301790691215397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160929660582138108509907725 60348622718301790691215397)
        ·
          refine ⟨11315366759681585754602887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60348622718301790691215397 11315366759681585754602887)
          ·
            refine ⟨16973050139522378631904331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11315366759681585754602887 16973050139522378631904331)
            ·
              refine ⟨25459575209283567947856497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16973050139522378631904331 25459575209283567947856497)
              ·
                refine ⟨19094681406962675960892373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25459575209283567947856497 19094681406962675960892373)
                ·
                  refine ⟨447531595475687717833415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19094681406962675960892373 447531595475687717833415)
                  ·
                    rfl

theorem cell22_3922041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 7].length) (baseStart_3922041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3922041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3922041 prefixEnd_3922041 := by exact prefixLift 3922041
  have htrace : WordTrace (prefixWord ++ tailWord_3922041) baseStart_3922041 baseEnd_3922041 := by
    simpa [prefixWord, tailWord_3922041, baseEnd_3922041] using wordTrace_append hprefix tailTrace_3922041
  have hstable : (prefixWord ++ tailWord_3922041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922041).length < 2 ^ (prefixWord ++ tailWord_3922041).sum := by decide
  have hdescent : baseEnd_3922041 < baseStart_3922041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922062 : List Nat := [4, 1, 1, 3, 3, 2, 1, 1, 3, 3]
def baseStart_3922062 : Nat := 118140960795 + 3922062 * 2 ^ 59
def prefixEnd_3922062 : Nat := 4983230072969 + 3 ^ 40 * 3922062 * 2
def baseEnd_3922062 : Nat := 1342601975156226098725181

theorem tailTrace_3922062 : CollatzResearch.WordTrace tailWord_3922062 prefixEnd_3922062 1342601975156226098725181 := by
  unfold tailWord_3922062
  simp only [CollatzResearch.WordTrace]
  refine ⟨17881169139630835463304055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95366235411364455804288293 17881169139630835463304055)
  ·
    refine ⟨26821753709446253194956083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17881169139630835463304055 26821753709446253194956083)
    ·
      refine ⟨40232630564169379792434125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26821753709446253194956083 40232630564169379792434125)
      ·
        refine ⟨15087236461563517422162797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40232630564169379792434125 15087236461563517422162797)
        ·
          refine ⟨5657713673086319033311049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15087236461563517422162797 5657713673086319033311049)
          ·
            refine ⟨4243285254814739274983287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5657713673086319033311049 4243285254814739274983287)
            ·
              refine ⟨6364927882222108912474931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4243285254814739274983287 6364927882222108912474931)
              ·
                refine ⟨9547391823333163368712397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6364927882222108912474931 9547391823333163368712397)
                ·
                  refine ⟨3580271933749936263267149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9547391823333163368712397 3580271933749936263267149)
                  ·
                    refine ⟨1342601975156226098725181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3580271933749936263267149 1342601975156226098725181)
                    ·
                      rfl

theorem cell22_3922062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_3922062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3922062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3922062 prefixEnd_3922062 := by exact prefixLift 3922062
  have htrace : WordTrace (prefixWord ++ tailWord_3922062) baseStart_3922062 baseEnd_3922062 := by
    simpa [prefixWord, tailWord_3922062, baseEnd_3922062] using wordTrace_append hprefix tailTrace_3922062
  have hstable : (prefixWord ++ tailWord_3922062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922062).length < 2 ^ (prefixWord ++ tailWord_3922062).sum := by decide
  have hdescent : baseEnd_3922062 < baseStart_3922062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922105 : List Nat := [1, 2, 1, 4, 1, 2, 5, 1, 1, 4]
def baseStart_3922105 : Nat := 118140960795 + 3922105 * 2 ^ 59
def prefixEnd_3922105 : Nat := 4983230072969 + 3 ^ 40 * 3922105 * 2
def baseEnd_3922105 : Nat := 1342616694934988319900049

theorem tailTrace_3922105 : CollatzResearch.WordTrace tailWord_3922105 prefixEnd_3922105 1342616694934988319900049 := by
  unfold tailWord_3922105
  simp only [CollatzResearch.WordTrace]
  refine ⟨143050921455890902050247769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95367280970593934700165179 143050921455890902050247769)
  ·
    refine ⟨107288191091918176537685827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143050921455890902050247769 107288191091918176537685827)
    ·
      refine ⟨160932286637877264806528741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107288191091918176537685827 160932286637877264806528741)
      ·
        refine ⟨30174803744601987151224139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160932286637877264806528741 30174803744601987151224139)
        ·
          refine ⟨45262205616902980726836209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30174803744601987151224139 45262205616902980726836209)
          ·
            refine ⟨33946654212677235545127157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45262205616902980726836209 33946654212677235545127157)
            ·
              refine ⟨3182498832438490832355671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33946654212677235545127157 3182498832438490832355671)
              ·
                refine ⟨4773748248657736248533507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3182498832438490832355671 4773748248657736248533507)
                ·
                  refine ⟨7160622372986604372800261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4773748248657736248533507 7160622372986604372800261)
                  ·
                    refine ⟨1342616694934988319900049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7160622372986604372800261 1342616694934988319900049)
                    ·
                      rfl

theorem cell22_3922105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 1, 4].length) (baseStart_3922105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3922105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3922105 prefixEnd_3922105 := by exact prefixLift 3922105
  have htrace : WordTrace (prefixWord ++ tailWord_3922105) baseStart_3922105 baseEnd_3922105 := by
    simpa [prefixWord, tailWord_3922105, baseEnd_3922105] using wordTrace_append hprefix tailTrace_3922105
  have hstable : (prefixWord ++ tailWord_3922105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922105).length < 2 ^ (prefixWord ++ tailWord_3922105).sum := by decide
  have hdescent : baseEnd_3922105 < baseStart_3922105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922113 : List Nat := [1, 2, 6, 1, 3, 1, 2, 2, 1, 3]
def baseStart_3922113 : Nat := 118140960795 + 3922113 * 2 ^ 59
def prefixEnd_3922113 : Nat := 4983230072969 + 3 ^ 40 * 3922113 * 2
def baseEnd_3922113 : Nat := 1342619433498478965700025

theorem tailTrace_3922113 : CollatzResearch.WordTrace tailWord_3922113 prefixEnd_3922113 1342619433498478965700025 := by
  unfold tailWord_3922113
  simp only [CollatzResearch.WordTrace]
  refine ⟨143051213239861919416538993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95367475493241279611025995 143051213239861919416538993)
  ·
    refine ⟨107288409929896439562404245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143051213239861919416538993 107288409929896439562404245)
    ·
      refine ⟨5029144215463895604487699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 107288409929896439562404245 5029144215463895604487699)
      ·
        refine ⟨7543716323195843406731549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5029144215463895604487699 7543716323195843406731549)
        ·
          refine ⟨2828893621198441277524331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7543716323195843406731549 2828893621198441277524331)
          ·
            refine ⟨4243340431797661916286497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2828893621198441277524331 4243340431797661916286497)
            ·
              refine ⟨3182505323848246437214873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4243340431797661916286497 3182505323848246437214873)
              ·
                refine ⟨2386878992886184827911155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3182505323848246437214873 2386878992886184827911155)
                ·
                  refine ⟨3580318489329277241866733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2386878992886184827911155 3580318489329277241866733)
                  ·
                    refine ⟨1342619433498478965700025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3580318489329277241866733 1342619433498478965700025)
                    ·
                      rfl

theorem cell22_3922113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_3922113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3922113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3922113 prefixEnd_3922113 := by exact prefixLift 3922113
  have htrace : WordTrace (prefixWord ++ tailWord_3922113) baseStart_3922113 baseEnd_3922113 := by
    simpa [prefixWord, tailWord_3922113, baseEnd_3922113] using wordTrace_append hprefix tailTrace_3922113
  have hstable : (prefixWord ++ tailWord_3922113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922113).length < 2 ^ (prefixWord ++ tailWord_3922113).sum := by decide
  have hdescent : baseEnd_3922113 < baseStart_3922113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922163 : List Nat := [1, 1, 1, 2, 2, 4, 1, 2, 5, 3]
def baseStart_3922163 : Nat := 118140960795 + 3922163 * 2 ^ 59
def prefixEnd_3922163 : Nat := 4983230072969 + 3 ^ 40 * 3922163 * 2
def baseEnd_3922163 : Nat := 1342636549520295501949871

theorem tailTrace_3922163 : CollatzResearch.WordTrace tailWord_3922163 prefixEnd_3922163 1342636549520295501949871 := by
  unfold tailWord_3922163
  simp only [CollatzResearch.WordTrace]
  refine ⟨143053036889680777955859143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95368691259787185303906095 143053036889680777955859143)
  ·
    refine ⟨214579555334521166933788715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143053036889680777955859143 214579555334521166933788715)
    ·
      refine ⟨321869333001781750400683073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214579555334521166933788715 321869333001781750400683073)
      ·
        refine ⟨241401999751336312800512305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321869333001781750400683073 241401999751336312800512305)
        ·
          refine ⟨181051499813502234600384229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241401999751336312800512305 181051499813502234600384229)
          ·
            refine ⟨33947156215031668987572043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181051499813502234600384229 33947156215031668987572043)
            ·
              refine ⟨50920734322547503481358065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33947156215031668987572043 50920734322547503481358065)
              ·
                refine ⟨38190550741910627611018549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50920734322547503481358065 38190550741910627611018549)
                ·
                  refine ⟨3580364132054121338532989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38190550741910627611018549 3580364132054121338532989)
                  ·
                    refine ⟨1342636549520295501949871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3580364132054121338532989 1342636549520295501949871)
                    ·
                      rfl

theorem cell22_3922163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 5, 3].length) (baseStart_3922163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3922163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3922163 prefixEnd_3922163 := by exact prefixLift 3922163
  have htrace : WordTrace (prefixWord ++ tailWord_3922163) baseStart_3922163 baseEnd_3922163 := by
    simpa [prefixWord, tailWord_3922163, baseEnd_3922163] using wordTrace_append hprefix tailTrace_3922163
  have hstable : (prefixWord ++ tailWord_3922163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922163).length < 2 ^ (prefixWord ++ tailWord_3922163).sum := by decide
  have hdescent : baseEnd_3922163 < baseStart_3922163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922257 : List Nat := [1, 2, 2, 1, 4, 4, 1, 2, 1, 4]
def baseStart_3922257 : Nat := 118140960795 + 3922257 * 2 ^ 59
def prefixEnd_3922257 : Nat := 4983230072969 + 3 ^ 40 * 3922257 * 2
def baseEnd_3922257 : Nat := 1342668727641310590099583

theorem tailTrace_3922257 : CollatzResearch.WordTrace tailWord_3922257 prefixEnd_3922257 1342668727641310590099583 := by
  unfold tailWord_3922257
  simp only [CollatzResearch.WordTrace]
  refine ⟨143056465351340232009781025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95370976900893488006520683 143056465351340232009781025)
  ·
    refine ⟨107292349013505174007335769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143056465351340232009781025 107292349013505174007335769)
    ·
      refine ⟨80469261760128880505501827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107292349013505174007335769 80469261760128880505501827)
      ·
        refine ⟨120703892640193320758252741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80469261760128880505501827 120703892640193320758252741)
        ·
          refine ⟨22631979870036247642172389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120703892640193320758252741 22631979870036247642172389)
          ·
            refine ⟨4243496225631796432907323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22631979870036247642172389 4243496225631796432907323)
            ·
              refine ⟨6365244338447694649360985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4243496225631796432907323 6365244338447694649360985)
              ·
                refine ⟨4773933253835770987020739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6365244338447694649360985 4773933253835770987020739)
                ·
                  refine ⟨7160899880753656480531109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4773933253835770987020739 7160899880753656480531109)
                  ·
                    refine ⟨1342668727641310590099583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7160899880753656480531109 1342668727641310590099583)
                    ·
                      rfl

theorem cell22_3922257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 4].length) (baseStart_3922257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3922257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3922257 prefixEnd_3922257 := by exact prefixLift 3922257
  have htrace : WordTrace (prefixWord ++ tailWord_3922257) baseStart_3922257 baseEnd_3922257 := by
    simpa [prefixWord, tailWord_3922257, baseEnd_3922257] using wordTrace_append hprefix tailTrace_3922257
  have hstable : (prefixWord ++ tailWord_3922257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922257).length < 2 ^ (prefixWord ++ tailWord_3922257).sum := by decide
  have hdescent : baseEnd_3922257 < baseStart_3922257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922274 : List Nat := [3, 3, 2, 1, 1, 3, 3, 1, 1, 4]
def baseStart_3922274 : Nat := 118140960795 + 3922274 * 2 ^ 59
def prefixEnd_3922274 : Nat := 4983230072969 + 3 ^ 40 * 3922274 * 2
def baseEnd_3922274 : Nat := 1342674547088728212424531

theorem tailTrace_3922274 : CollatzResearch.WordTrace tailWord_3922274 prefixEnd_3922274 1342674547088728212424531 := by
  unfold tailWord_3922274
  simp only [CollatzResearch.WordTrace]
  refine ⟨35764271348069660978287469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95371390261519095942099917 35764271348069660978287469)
  ·
    refine ⟨13411601755526122866857801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35764271348069660978287469 13411601755526122866857801)
    ·
      refine ⟨10058701316644592150143351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13411601755526122866857801 10058701316644592150143351)
      ·
        refine ⟨15088051974966888225215027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10058701316644592150143351 15088051974966888225215027)
        ·
          refine ⟨22632077962450332337822541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15088051974966888225215027 22632077962450332337822541)
          ·
            refine ⟨8487029235918874626683453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22632077962450332337822541 8487029235918874626683453)
            ·
              refine ⟨3182635963469577985006295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8487029235918874626683453 3182635963469577985006295)
              ·
                refine ⟨4773953945204366977509443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3182635963469577985006295 4773953945204366977509443)
                ·
                  refine ⟨7160930917806550466264165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4773953945204366977509443 7160930917806550466264165)
                  ·
                    refine ⟨1342674547088728212424531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7160930917806550466264165 1342674547088728212424531)
                    ·
                      rfl

theorem cell22_3922274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_3922274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3922274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3922274 prefixEnd_3922274 := by exact prefixLift 3922274
  have htrace : WordTrace (prefixWord ++ tailWord_3922274) baseStart_3922274 baseEnd_3922274 := by
    simpa [prefixWord, tailWord_3922274, baseEnd_3922274] using wordTrace_append hprefix tailTrace_3922274
  have hstable : (prefixWord ++ tailWord_3922274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922274).length < 2 ^ (prefixWord ++ tailWord_3922274).sum := by decide
  have hdescent : baseEnd_3922274 < baseStart_3922274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922285 : List Nat := [1, 5, 1, 1, 1, 2, 1, 4, 2, 4]
def baseStart_3922285 : Nat := 118140960795 + 3922285 * 2 ^ 59
def prefixEnd_3922285 : Nat := 4983230072969 + 3 ^ 40 * 3922285 * 2
def baseEnd_3922285 : Nat := 1342678312613527850399497

theorem tailTrace_3922285 : CollatzResearch.WordTrace tailWord_3922285 prefixEnd_3922285 1342678312613527850399497 := by
  unfold tailWord_3922285
  simp only [CollatzResearch.WordTrace]
  refine ⟨143057486595238792791800309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95371657730159195194533539 143057486595238792791800309)
  ·
    refine ⟨13411639368303636824231279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143057486595238792791800309 13411639368303636824231279)
    ·
      refine ⟨20117459052455455236346919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13411639368303636824231279 20117459052455455236346919)
      ·
        refine ⟨30176188578683182854520379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20117459052455455236346919 30176188578683182854520379)
        ·
          refine ⟨45264282868024774281780569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30176188578683182854520379 45264282868024774281780569)
          ·
            refine ⟨33948212151018580711335427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45264282868024774281780569 33948212151018580711335427)
            ·
              refine ⟨50922318226527871067003141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33948212151018580711335427 50922318226527871067003141)
              ·
                refine ⟨9547934667473975825063089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50922318226527871067003141 9547934667473975825063089)
                ·
                  refine ⟨7160951000605481868797317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9547934667473975825063089 7160951000605481868797317)
                  ·
                    refine ⟨1342678312613527850399497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7160951000605481868797317 1342678312613527850399497)
                    ·
                      rfl

theorem cell22_3922285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_3922285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3922285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3922285 prefixEnd_3922285 := by exact prefixLift 3922285
  have htrace : WordTrace (prefixWord ++ tailWord_3922285) baseStart_3922285 baseEnd_3922285 := by
    simpa [prefixWord, tailWord_3922285, baseEnd_3922285] using wordTrace_append hprefix tailTrace_3922285
  have hstable : (prefixWord ++ tailWord_3922285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922285).length < 2 ^ (prefixWord ++ tailWord_3922285).sum := by decide
  have hdescent : baseEnd_3922285 < baseStart_3922285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922315 : List Nat := [1, 1, 1, 1, 4, 4, 1, 1, 5, 3]
def baseStart_3922315 : Nat := 118140960795 + 3922315 * 2 ^ 59
def prefixEnd_3922315 : Nat := 4983230072969 + 3 ^ 40 * 3922315 * 2
def baseEnd_3922315 : Nat := 1342688582226617772149405

theorem tailTrace_3922315 : CollatzResearch.WordTrace tailWord_3922315 prefixEnd_3922315 1342688582226617772149405 := by
  unfold tailWord_3922315
  simp only [CollatzResearch.WordTrace]
  refine ⟨143058580785130107915392399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95372387190086738610261599 143058580785130107915392399)
  ·
    refine ⟨214587871177695161873088599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143058580785130107915392399 214587871177695161873088599)
    ·
      refine ⟨321881806766542742809632899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214587871177695161873088599 321881806766542742809632899)
      ·
        refine ⟨482822710149814114214449349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321881806766542742809632899 482822710149814114214449349)
        ·
          refine ⟨90529258153090146415209253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 482822710149814114214449349 90529258153090146415209253)
          ·
            refine ⟨16974235903704402452851735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90529258153090146415209253 16974235903704402452851735)
            ·
              refine ⟨25461353855556603679277603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16974235903704402452851735 25461353855556603679277603)
              ·
                refine ⟨38192030783334905518916405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25461353855556603679277603 38192030783334905518916405)
                ·
                  refine ⟨3580502885937647392398413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38192030783334905518916405 3580502885937647392398413)
                  ·
                    refine ⟨1342688582226617772149405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3580502885937647392398413 1342688582226617772149405)
                    ·
                      rfl

theorem cell22_3922315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 5, 3].length) (baseStart_3922315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3922315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3922315 prefixEnd_3922315 := by exact prefixLift 3922315
  have htrace : WordTrace (prefixWord ++ tailWord_3922315) baseStart_3922315 baseEnd_3922315 := by
    simpa [prefixWord, tailWord_3922315, baseEnd_3922315] using wordTrace_append hprefix tailTrace_3922315
  have hstable : (prefixWord ++ tailWord_3922315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922315).length < 2 ^ (prefixWord ++ tailWord_3922315).sum := by decide
  have hdescent : baseEnd_3922315 < baseStart_3922315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922422 : List Nat := [5, 1, 1, 1, 2, 1, 2, 3, 1, 5]
def baseStart_3922422 : Nat := 118140960795 + 3922422 * 2 ^ 59
def prefixEnd_3922422 : Nat := 4983230072969 + 3 ^ 40 * 3922422 * 2
def baseEnd_3922422 : Nat := 1342725210513305159724077

theorem tailTrace_3922422 : CollatzResearch.WordTrace tailWord_3922422 prefixEnd_3922422 1342725210513305159724077 := by
  unfold tailWord_3922422
  simp only [CollatzResearch.WordTrace]
  refine ⟨8941405212233904074346095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95374988930494976793025013 8941405212233904074346095)
  ·
    refine ⟨13412107818350856111519143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8941405212233904074346095 13412107818350856111519143)
    ·
      refine ⟨20118161727526284167278715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13412107818350856111519143 20118161727526284167278715)
      ·
        refine ⟨30177242591289426250918073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20118161727526284167278715 30177242591289426250918073)
        ·
          refine ⟨22632931943467069688188555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30177242591289426250918073 22632931943467069688188555)
          ·
            refine ⟨33949397915200604532282833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22632931943467069688188555 33949397915200604532282833)
            ·
              refine ⟨25462048436400453399212125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33949397915200604532282833 25462048436400453399212125)
              ·
                refine ⟨9548268163650170024704547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25462048436400453399212125 9548268163650170024704547)
                ·
                  refine ⟨14322402245475255037056821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9548268163650170024704547 14322402245475255037056821)
                  ·
                    refine ⟨1342725210513305159724077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14322402245475255037056821 1342725210513305159724077)
                    ·
                      rfl

theorem cell22_3922422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_3922422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3922422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3922422 prefixEnd_3922422 := by exact prefixLift 3922422
  have htrace : WordTrace (prefixWord ++ tailWord_3922422) baseStart_3922422 baseEnd_3922422 := by
    simpa [prefixWord, tailWord_3922422, baseEnd_3922422] using wordTrace_append hprefix tailTrace_3922422
  have hstable : (prefixWord ++ tailWord_3922422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922422).length < 2 ^ (prefixWord ++ tailWord_3922422).sum := by decide
  have hdescent : baseEnd_3922422 < baseStart_3922422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922452 : List Nat := [2, 4, 3, 1, 1, 11]
def baseStart_3922452 : Nat := 118140960795 + 3922452 * 2 ^ 59
def prefixEnd_3922452 : Nat := 4983230072969 + 3 ^ 40 * 3922452 * 2
def baseEnd_3922452 : Nat := 16576981236128334339185

theorem tailTrace_3922452 : CollatzResearch.WordTrace tailWord_3922452 prefixEnd_3922452 16576981236128334339185 := by
  unfold tailWord_3922452
  simp only [CollatzResearch.WordTrace]
  refine ⟨71531788792816890156564805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95375718390422520208753073 71531788792816890156564805)
  ·
    refine ⟨13412210398653166904355901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71531788792816890156564805 13412210398653166904355901)
    ·
      refine ⟨5029578899494937589133463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13412210398653166904355901 5029578899494937589133463)
      ·
        refine ⟨7544368349242406383700195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5029578899494937589133463 7544368349242406383700195)
        ·
          refine ⟨11316552523863609575550293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7544368349242406383700195 11316552523863609575550293)
          ·
            refine ⟨16576981236128334339185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11316552523863609575550293 16576981236128334339185)
            ·
              rfl

theorem cell22_3922452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 11].length) (baseStart_3922452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3922452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3922452 prefixEnd_3922452 := by exact prefixLift 3922452
  have htrace : WordTrace (prefixWord ++ tailWord_3922452) baseStart_3922452 baseEnd_3922452 := by
    simpa [prefixWord, tailWord_3922452, baseEnd_3922452] using wordTrace_append hprefix tailTrace_3922452
  have hstable : (prefixWord ++ tailWord_3922452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922452).length < 2 ^ (prefixWord ++ tailWord_3922452).sum := by decide
  have hdescent : baseEnd_3922452 < baseStart_3922452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922465 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 1, 8]
def baseStart_3922465 : Nat := 118140960795 + 3922465 * 2 ^ 59
def prefixEnd_3922465 : Nat := 4983230072969 + 3 ^ 40 * 3922465 * 2
def baseEnd_3922465 : Nat := 1342739930292067380898945

theorem tailTrace_3922465 : CollatzResearch.WordTrace tailWord_3922465 prefixEnd_3922465 1342739930292067380898945 := by
  unfold tailWord_3922465
  simp only [CollatzResearch.WordTrace]
  refine ⟨143064051734586683533352849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95376034489724455688901899 143064051734586683533352849)
  ·
    refine ⟨107298038800940012650014637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143064051734586683533352849 107298038800940012650014637)
    ·
      refine ⟨40236764550352504743755489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107298038800940012650014637 40236764550352504743755489)
      ·
        refine ⟨30177573412764378557816617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40236764550352504743755489 30177573412764378557816617)
        ·
          refine ⟨22633180059573283918362463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30177573412764378557816617 22633180059573283918362463)
          ·
            refine ⟨33949770089359925877543695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22633180059573283918362463 33949770089359925877543695)
            ·
              refine ⟨50924655134039888816315543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33949770089359925877543695 50924655134039888816315543)
              ·
                refine ⟨76386982701059833224473315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50924655134039888816315543 76386982701059833224473315)
                ·
                  refine ⟨114580474051589749836709973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76386982701059833224473315 114580474051589749836709973)
                  ·
                    refine ⟨1342739930292067380898945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 114580474051589749836709973 1342739930292067380898945)
                    ·
                      rfl

theorem cell22_3922465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_3922465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3922465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3922465 prefixEnd_3922465 := by exact prefixLift 3922465
  have htrace : WordTrace (prefixWord ++ tailWord_3922465) baseStart_3922465 baseEnd_3922465 := by
    simpa [prefixWord, tailWord_3922465, baseEnd_3922465] using wordTrace_append hprefix tailTrace_3922465
  have hstable : (prefixWord ++ tailWord_3922465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922465).length < 2 ^ (prefixWord ++ tailWord_3922465).sum := by decide
  have hdescent : baseEnd_3922465 < baseStart_3922465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922495 : List Nat := [1, 1, 2, 2, 3, 2, 1, 2, 1, 7]
def baseStart_3922495 : Nat := 118140960795 + 3922495 * 2 ^ 59
def prefixEnd_3922495 : Nat := 4983230072969 + 3 ^ 40 * 3922495 * 2
def baseEnd_3922495 : Nat := 1342750199905157302648853

theorem tailTrace_3922495 : CollatzResearch.WordTrace tailWord_3922495 prefixEnd_3922495 1342750199905157302648853 := by
  unfold tailWord_3922495
  simp only [CollatzResearch.WordTrace]
  refine ⟨143065145924477998656944939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95376763949651999104629959 143065145924477998656944939)
  ·
    refine ⟨214597718886716997985417409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143065145924477998656944939 214597718886716997985417409)
    ·
      refine ⟨160948289165037748489063057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214597718886716997985417409 160948289165037748489063057)
      ·
        refine ⟨120711216873778311366797293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160948289165037748489063057 120711216873778311366797293)
        ·
          refine ⟨45266706327666866762548985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120711216873778311366797293 45266706327666866762548985)
          ·
            refine ⟨33950029745750150071911739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45266706327666866762548985 33950029745750150071911739)
            ·
              refine ⟨50925044618625225107867609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33950029745750150071911739 50925044618625225107867609)
              ·
                refine ⟨38193783463968918830900707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50925044618625225107867609 38193783463968918830900707)
                ·
                  refine ⟨57290675195953378246351061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38193783463968918830900707 57290675195953378246351061)
                  ·
                    refine ⟨1342750199905157302648853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57290675195953378246351061 1342750199905157302648853)
                    ·
                      rfl

theorem cell22_3922495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 7].length) (baseStart_3922495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3922495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3922495 prefixEnd_3922495 := by exact prefixLift 3922495
  have htrace : WordTrace (prefixWord ++ tailWord_3922495) baseStart_3922495 baseEnd_3922495 := by
    simpa [prefixWord, tailWord_3922495, baseEnd_3922495] using wordTrace_append hprefix tailTrace_3922495
  have hstable : (prefixWord ++ tailWord_3922495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922495).length < 2 ^ (prefixWord ++ tailWord_3922495).sum := by decide
  have hdescent : baseEnd_3922495 < baseStart_3922495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922501 : List Nat := [1, 3, 1, 1, 1, 6, 2, 3, 1, 3]
def baseStart_3922501 : Nat := 118140960795 + 3922501 * 2 ^ 59
def prefixEnd_3922501 : Nat := 4983230072969 + 3 ^ 40 * 3922501 * 2
def baseEnd_3922501 : Nat := 1342752253827775286998835

theorem tailTrace_3922501 : CollatzResearch.WordTrace tailWord_3922501 prefixEnd_3922501 1342752253827775286998835 := by
  unfold tailWord_3922501
  simp only [CollatzResearch.WordTrace]
  refine ⟨143065364762456261681663357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95376909841637507787775571 143065364762456261681663357)
  ·
    refine ⟨53649511785921098130623759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143065364762456261681663357 53649511785921098130623759)
    ·
      refine ⟨80474267678881647195935639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53649511785921098130623759 80474267678881647195935639)
      ·
        refine ⟨120711401518322470793903459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80474267678881647195935639 120711401518322470793903459)
        ·
          refine ⟨181067102277483706190855189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120711401518322470793903459 181067102277483706190855189)
          ·
            refine ⟨8487520419257048727696337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 181067102277483706190855189 8487520419257048727696337)
            ·
              refine ⟨6365640314442786545772253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8487520419257048727696337 6365640314442786545772253)
              ·
                refine ⟨2387115117916044954664595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6365640314442786545772253 2387115117916044954664595)
                ·
                  refine ⟨3580672676874067431996893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2387115117916044954664595 3580672676874067431996893)
                  ·
                    refine ⟨1342752253827775286998835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3580672676874067431996893 1342752253827775286998835)
                    ·
                      rfl

theorem cell22_3922501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 3, 1, 3].length) (baseStart_3922501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3922501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3922501 prefixEnd_3922501 := by exact prefixLift 3922501
  have htrace : WordTrace (prefixWord ++ tailWord_3922501) baseStart_3922501 baseEnd_3922501 := by
    simpa [prefixWord, tailWord_3922501, baseEnd_3922501] using wordTrace_append hprefix tailTrace_3922501
  have hstable : (prefixWord ++ tailWord_3922501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922501).length < 2 ^ (prefixWord ++ tailWord_3922501).sum := by decide
  have hdescent : baseEnd_3922501 < baseStart_3922501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922574 : List Nat := [4, 1, 1, 3, 1, 1, 1, 3, 4, 3]
def baseStart_3922574 : Nat := 118140960795 + 3922574 * 2 ^ 59
def prefixEnd_3922574 : Nat := 4983230072969 + 3 ^ 40 * 3922574 * 2
def baseEnd_3922574 : Nat := 1342777243219627429923611

theorem tailTrace_3922574 : CollatzResearch.WordTrace tailWord_3922574 prefixEnd_3922574 1342777243219627429923611 := by
  unfold tailWord_3922574
  simp only [CollatzResearch.WordTrace]
  refine ⟨17883503411398974393633847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95378684860794530099380517 17883503411398974393633847)
  ·
    refine ⟨26825255117098461590450771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17883503411398974393633847 26825255117098461590450771)
    ·
      refine ⟨40237882675647692385676157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26825255117098461590450771 40237882675647692385676157)
      ·
        refine ⟨15089206003367884644628559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40237882675647692385676157 15089206003367884644628559)
        ·
          refine ⟨22633809005051826966942839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15089206003367884644628559 22633809005051826966942839)
          ·
            refine ⟨33950713507577740450414259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22633809005051826966942839 33950713507577740450414259)
            ·
              refine ⟨50926070261366610675621389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33950713507577740450414259 50926070261366610675621389)
              ·
                refine ⟨19097276348012479003358021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50926070261366610675621389 19097276348012479003358021)
                ·
                  refine ⟨3580739315252339813129629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19097276348012479003358021 3580739315252339813129629)
                  ·
                    refine ⟨1342777243219627429923611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3580739315252339813129629 1342777243219627429923611)
                    ·
                      rfl

theorem cell22_3922574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_3922574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3922574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3922574 prefixEnd_3922574 := by exact prefixLift 3922574
  have htrace : WordTrace (prefixWord ++ tailWord_3922574) baseStart_3922574 baseEnd_3922574 := by
    simpa [prefixWord, tailWord_3922574, baseEnd_3922574] using wordTrace_append hprefix tailTrace_3922574
  have hstable : (prefixWord ++ tailWord_3922574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922574).length < 2 ^ (prefixWord ++ tailWord_3922574).sum := by decide
  have hdescent : baseEnd_3922574 < baseStart_3922574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922606 : List Nat := [4, 1, 4, 1, 1, 1, 1, 3, 2, 4]
def baseStart_3922606 : Nat := 118140960795 + 3922606 * 2 ^ 59
def prefixEnd_3922606 : Nat := 4983230072969 + 3 ^ 40 * 3922606 * 2
def baseEnd_3922606 : Nat := 1342788197473590013123513

theorem tailTrace_3922606 : CollatzResearch.WordTrace tailWord_3922606 prefixEnd_3922606 1342788197473590013123513 := by
  unfold tailWord_3922606
  simp only [CollatzResearch.WordTrace]
  refine ⟨17883649303384483076779459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95379462951383909742823781 17883649303384483076779459)
  ·
    refine ⟨26825473955076724615169189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17883649303384483076779459 26825473955076724615169189)
    ·
      refine ⟨5029776366576885865344223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26825473955076724615169189 5029776366576885865344223)
      ·
        refine ⟨7544664549865328798016335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5029776366576885865344223 7544664549865328798016335)
        ·
          refine ⟨11316996824797993197024503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7544664549865328798016335 11316996824797993197024503)
          ·
            refine ⟨16975495237196989795536755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11316996824797993197024503 16975495237196989795536755)
            ·
              refine ⟨25463242855795484693305133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16975495237196989795536755 25463242855795484693305133)
              ·
                refine ⟨9548716070923306759989425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25463242855795484693305133 9548716070923306759989425)
                ·
                  refine ⟨7161537053192480069992069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9548716070923306759989425 7161537053192480069992069)
                  ·
                    refine ⟨1342788197473590013123513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7161537053192480069992069 1342788197473590013123513)
                    ·
                      rfl

theorem cell22_3922606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_3922606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3922606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3922606 prefixEnd_3922606 := by exact prefixLift 3922606
  have htrace : WordTrace (prefixWord ++ tailWord_3922606) baseStart_3922606 baseEnd_3922606 := by
    simpa [prefixWord, tailWord_3922606, baseEnd_3922606] using wordTrace_append hprefix tailTrace_3922606
  have hstable : (prefixWord ++ tailWord_3922606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922606).length < 2 ^ (prefixWord ++ tailWord_3922606).sum := by decide
  have hdescent : baseEnd_3922606 < baseStart_3922606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922625 : List Nat := [1, 2, 6, 2, 1, 1, 2, 2, 2, 3]
def baseStart_3922625 : Nat := 118140960795 + 3922625 * 2 ^ 59
def prefixEnd_3922625 : Nat := 4983230072969 + 3 ^ 40 * 3922625 * 2
def baseEnd_3922625 : Nat := 1342794701561880296898455

theorem tailTrace_3922625 : CollatzResearch.WordTrace tailWord_3922625 prefixEnd_3922625 1342794701561880296898455 := by
  unfold tailWord_3922625
  simp only [CollatzResearch.WordTrace]
  refine ⟨143069887414007030859177329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95379924942671353906118219 143069887414007030859177329)
  ·
    refine ⟨107302415560505273144382997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143069887414007030859177329 107302415560505273144382997)
    ·
      refine ⟨5029800729398684678642953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 107302415560505273144382997 5029800729398684678642953)
      ·
        refine ⟨3772350547049013508982215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5029800729398684678642953 3772350547049013508982215)
        ·
          refine ⟨5658525820573520263473323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3772350547049013508982215 5658525820573520263473323)
          ·
            refine ⟨8487788730860280395209985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5658525820573520263473323 8487788730860280395209985)
            ·
              refine ⟨6365841548145210296407489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8487788730860280395209985 6365841548145210296407489)
              ·
                refine ⟨4774381161108907722305617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6365841548145210296407489 4774381161108907722305617)
                ·
                  refine ⟨3580785870831680791729213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4774381161108907722305617 3580785870831680791729213)
                  ·
                    refine ⟨1342794701561880296898455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3580785870831680791729213 1342794701561880296898455)
                    ·
                      rfl

theorem cell22_3922625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_3922625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3922625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3922625 prefixEnd_3922625 := by exact prefixLift 3922625
  have htrace : WordTrace (prefixWord ++ tailWord_3922625) baseStart_3922625 baseEnd_3922625 := by
    simpa [prefixWord, tailWord_3922625, baseEnd_3922625] using wordTrace_append hprefix tailTrace_3922625
  have hstable : (prefixWord ++ tailWord_3922625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922625).length < 2 ^ (prefixWord ++ tailWord_3922625).sum := by decide
  have hdescent : baseEnd_3922625 < baseStart_3922625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922647 : List Nat := [1, 1, 3, 2, 1, 4, 1, 1, 1, 7]
def baseStart_3922647 : Nat := 118140960795 + 3922647 * 2 ^ 59
def prefixEnd_3922647 : Nat := 4983230072969 + 3 ^ 40 * 3922647 * 2
def baseEnd_3922647 : Nat := 1342802232611479572848387

theorem tailTrace_3922647 : CollatzResearch.WordTrace tailWord_3922647 prefixEnd_3922647 1342802232611479572848387 := by
  unfold tailWord_3922647
  simp only [CollatzResearch.WordTrace]
  refine ⟨143070689819927328616478195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95380459879951552410985463 143070689819927328616478195)
  ·
    refine ⟨214606034729890992924717293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143070689819927328616478195 214606034729890992924717293)
    ·
      refine ⟨80477263023709122346768985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214606034729890992924717293 80477263023709122346768985)
      ·
        refine ⟨60357947267781841760076739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80477263023709122346768985 60357947267781841760076739)
        ·
          refine ⟨90536920901672762640115109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60357947267781841760076739 90536920901672762640115109)
          ·
            refine ⟨16975672669063642995021583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90536920901672762640115109 16975672669063642995021583)
            ·
              refine ⟨25463509003595464492532375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16975672669063642995021583 25463509003595464492532375)
              ·
                refine ⟨38195263505393196738798563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25463509003595464492532375 38195263505393196738798563)
                ·
                  refine ⟨57292895258089795108197845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38195263505393196738798563 57292895258089795108197845)
                  ·
                    refine ⟨1342802232611479572848387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57292895258089795108197845 1342802232611479572848387)
                    ·
                      rfl

theorem cell22_3922647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_3922647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3922647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3922647 prefixEnd_3922647 := by exact prefixLift 3922647
  have htrace : WordTrace (prefixWord ++ tailWord_3922647) baseStart_3922647 baseEnd_3922647 := by
    simpa [prefixWord, tailWord_3922647, baseEnd_3922647] using wordTrace_append hprefix tailTrace_3922647
  have hstable : (prefixWord ++ tailWord_3922647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922647).length < 2 ^ (prefixWord ++ tailWord_3922647).sum := by decide
  have hdescent : baseEnd_3922647 < baseStart_3922647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922707 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 3, 6]
def baseStart_3922707 : Nat := 118140960795 + 3922707 * 2 ^ 59
def prefixEnd_3922707 : Nat := 4983230072969 + 3 ^ 40 * 3922707 * 2
def baseEnd_3922707 : Nat := 1342822771837659416348203

theorem tailTrace_3922707 : CollatzResearch.WordTrace tailWord_3922707 prefixEnd_3922707 1342822771837659416348203 := by
  unfold tailWord_3922707
  simp only [CollatzResearch.WordTrace]
  refine ⟨143072878199709958863662375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95381918799806639242441583 143072878199709958863662375)
  ·
    refine ⟨214609317299564938295493563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143072878199709958863662375 214609317299564938295493563)
    ·
      refine ⟨321913975949347407443240345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214609317299564938295493563 321913975949347407443240345)
      ·
        refine ⟨241435481962010555582430259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321913975949347407443240345 241435481962010555582430259)
        ·
          refine ⟨362153222943015833373645389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241435481962010555582430259 362153222943015833373645389)
          ·
            refine ⟨135807458603630937515117021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 362153222943015833373645389 135807458603630937515117021)
            ·
              refine ⟨50927796976361601568168883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135807458603630937515117021 50927796976361601568168883)
              ·
                refine ⟨76391695464542402352253325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50927796976361601568168883 76391695464542402352253325)
                ·
                  refine ⟨28646885799203400882094997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76391695464542402352253325 28646885799203400882094997)
                  ·
                    refine ⟨1342822771837659416348203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28646885799203400882094997 1342822771837659416348203)
                    ·
                      rfl

theorem cell22_3922707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 6].length) (baseStart_3922707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3922707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3922707 prefixEnd_3922707 := by exact prefixLift 3922707
  have htrace : WordTrace (prefixWord ++ tailWord_3922707) baseStart_3922707 baseEnd_3922707 := by
    simpa [prefixWord, tailWord_3922707, baseEnd_3922707] using wordTrace_append hprefix tailTrace_3922707
  have hstable : (prefixWord ++ tailWord_3922707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922707).length < 2 ^ (prefixWord ++ tailWord_3922707).sum := by decide
  have hdescent : baseEnd_3922707 < baseStart_3922707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922739 : List Nat := [1, 1, 1, 2, 6, 3, 8]
def baseStart_3922739 : Nat := 118140960795 + 3922739 * 2 ^ 59
def prefixEnd_3922739 : Nat := 4983230072969 + 3 ^ 40 * 3922739 * 2
def baseEnd_3922739 : Nat := 49734582447837851835115

theorem tailTrace_3922739 : CollatzResearch.WordTrace tailWord_3922739 prefixEnd_3922739 49734582447837851835115 := by
  unfold tailWord_3922739
  simp only [CollatzResearch.WordTrace]
  refine ⟨143074045335594028328827271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95382696890396018885884847 143074045335594028328827271)
  ·
    refine ⟨214611068003391042493240907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143074045335594028328827271 214611068003391042493240907)
    ·
      refine ⟨321916602005086563739861361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214611068003391042493240907 321916602005086563739861361)
      ·
        refine ⟨241437451503814922804896021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321916602005086563739861361 241437451503814922804896021)
        ·
          refine ⟨11317380539241324506479501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 241437451503814922804896021 11317380539241324506479501)
          ·
            refine ⟨4244017702215496689929813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11317380539241324506479501 4244017702215496689929813)
            ·
              refine ⟨49734582447837851835115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4244017702215496689929813 49734582447837851835115)
              ·
                rfl

theorem cell22_3922739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 8].length) (baseStart_3922739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3922739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3922739 prefixEnd_3922739 := by exact prefixLift 3922739
  have htrace : WordTrace (prefixWord ++ tailWord_3922739) baseStart_3922739 baseEnd_3922739 := by
    simpa [prefixWord, tailWord_3922739, baseEnd_3922739] using wordTrace_append hprefix tailTrace_3922739
  have hstable : (prefixWord ++ tailWord_3922739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922739).length < 2 ^ (prefixWord ++ tailWord_3922739).sum := by decide
  have hdescent : baseEnd_3922739 < baseStart_3922739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922741 : List Nat := [1, 3, 3, 1, 3, 2, 1, 2, 2, 4]
def baseStart_3922741 : Nat := 118140960795 + 3922741 * 2 ^ 59
def prefixEnd_3922741 : Nat := 4983230072969 + 3 ^ 40 * 3922741 * 2
def baseEnd_3922741 : Nat := 1342834410732494660998099

theorem tailTrace_3922741 : CollatzResearch.WordTrace tailWord_3922741 prefixEnd_3922741 1342834410732494660998099 := by
  unfold tailWord_3922741
  simp only [CollatzResearch.WordTrace]
  refine ⟨143074118281586782670400077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95382745521057855113600051 143074118281586782670400077)
  ·
    refine ⟨53652794355595043501400029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143074118281586782670400077 53652794355595043501400029)
    ·
      refine ⟨20119797883348141313025011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53652794355595043501400029 20119797883348141313025011)
      ·
        refine ⟨30179696825022211969537517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20119797883348141313025011 30179696825022211969537517)
        ·
          refine ⟨11317386309383329488576569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30179696825022211969537517 11317386309383329488576569)
          ·
            refine ⟨8488039732037497116432427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11317386309383329488576569 8488039732037497116432427)
            ·
              refine ⟨12732059598056245674648641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8488039732037497116432427 12732059598056245674648641)
              ·
                refine ⟨9549044698542184255986481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12732059598056245674648641 9549044698542184255986481)
                ·
                  refine ⟨7161783523906638191989861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9549044698542184255986481 7161783523906638191989861)
                  ·
                    refine ⟨1342834410732494660998099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7161783523906638191989861 1342834410732494660998099)
                    ·
                      rfl

theorem cell22_3922741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_3922741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3922741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3922741 prefixEnd_3922741 := by exact prefixLift 3922741
  have htrace : WordTrace (prefixWord ++ tailWord_3922741) baseStart_3922741 baseEnd_3922741 := by
    simpa [prefixWord, tailWord_3922741, baseEnd_3922741] using wordTrace_append hprefix tailTrace_3922741
  have hstable : (prefixWord ++ tailWord_3922741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922741).length < 2 ^ (prefixWord ++ tailWord_3922741).sum := by decide
  have hdescent : baseEnd_3922741 < baseStart_3922741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922801 : List Nat := [1, 2, 2, 2, 1, 5, 2, 2, 5]
def baseStart_3922801 : Nat := 118140960795 + 3922801 * 2 ^ 59
def prefixEnd_3922801 : Nat := 4983230072969 + 3 ^ 40 * 3922801 * 2
def baseEnd_3922801 : Nat := 447618316652891501499305

theorem tailTrace_3922801 : CollatzResearch.WordTrace tailWord_3922801 prefixEnd_3922801 447618316652891501499305 := by
  unfold tailWord_3922801
  simp only [CollatzResearch.WordTrace]
  refine ⟨143076306661369412917584257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95384204440912941945056171 143076306661369412917584257)
  ·
    refine ⟨107307229996027059688188193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143076306661369412917584257 107307229996027059688188193)
    ·
      refine ⟨80480422497020294766141145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107307229996027059688188193 80480422497020294766141145)
      ·
        refine ⟨60360316872765221074605859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80480422497020294766141145 60360316872765221074605859)
        ·
          refine ⟨90540475309147831611908789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60360316872765221074605859 90540475309147831611908789)
          ·
            refine ⟨8488169560232609213616449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90540475309147831611908789 8488169560232609213616449)
            ·
              refine ⟨6366127170174456910212337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8488169560232609213616449 6366127170174456910212337)
              ·
                refine ⟨4774595377630842682659253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6366127170174456910212337 4774595377630842682659253)
                ·
                  refine ⟨447618316652891501499305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4774595377630842682659253 447618316652891501499305)
                  ·
                    rfl

theorem cell22_3922801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 5].length) (baseStart_3922801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3922801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3922801 prefixEnd_3922801 := by exact prefixLift 3922801
  have htrace : WordTrace (prefixWord ++ tailWord_3922801) baseStart_3922801 baseEnd_3922801 := by
    simpa [prefixWord, tailWord_3922801, baseEnd_3922801] using wordTrace_append hprefix tailTrace_3922801
  have hstable : (prefixWord ++ tailWord_3922801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922801).length < 2 ^ (prefixWord ++ tailWord_3922801).sum := by decide
  have hdescent : baseEnd_3922801 < baseStart_3922801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922805 : List Nat := [1, 3, 4, 1, 1, 3, 1, 4, 1, 3]
def baseStart_3922805 : Nat := 118140960795 + 3922805 * 2 ^ 59
def prefixEnd_3922805 : Nat := 4983230072969 + 3 ^ 40 * 3922805 * 2
def baseEnd_3922805 : Nat := 1342856319240419827397903

theorem tailTrace_3922805 : CollatzResearch.WordTrace tailWord_3922805 prefixEnd_3922805 1342856319240419827397903 := by
  unfold tailWord_3922805
  simp only [CollatzResearch.WordTrace]
  refine ⟨143076452553354921600729869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95384301702236614400486579 143076452553354921600729869)
  ·
    refine ⟨53653669707508095600273701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143076452553354921600729869 53653669707508095600273701)
    ·
      refine ⟨10060063070157767925051319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53653669707508095600273701 10060063070157767925051319)
      ·
        refine ⟨15090094605236651887576979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10060063070157767925051319 15090094605236651887576979)
        ·
          refine ⟨22635141907854977831365469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15090094605236651887576979 22635141907854977831365469)
          ·
            refine ⟨8488178215445616686762051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22635141907854977831365469 8488178215445616686762051)
            ·
              refine ⟨12732267323168425030143077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8488178215445616686762051 12732267323168425030143077)
              ·
                refine ⟨2387300123094079693151827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12732267323168425030143077 2387300123094079693151827)
                ·
                  refine ⟨3580950184641119539727741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2387300123094079693151827 3580950184641119539727741)
                  ·
                    refine ⟨1342856319240419827397903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3580950184641119539727741 1342856319240419827397903)
                    ·
                      rfl

theorem cell22_3922805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_3922805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3922805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3922805 prefixEnd_3922805 := by exact prefixLift 3922805
  have htrace : WordTrace (prefixWord ++ tailWord_3922805) baseStart_3922805 baseEnd_3922805 := by
    simpa [prefixWord, tailWord_3922805, baseEnd_3922805] using wordTrace_append hprefix tailTrace_3922805
  have hstable : (prefixWord ++ tailWord_3922805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922805).length < 2 ^ (prefixWord ++ tailWord_3922805).sum := by decide
  have hdescent : baseEnd_3922805 < baseStart_3922805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922848 : List Nat := [2, 1, 1, 4, 1, 1, 6, 1, 1, 4]
def baseStart_3922848 : Nat := 118140960795 + 3922848 * 2 ^ 59
def prefixEnd_3922848 : Nat := 4983230072969 + 3 ^ 40 * 3922848 * 2
def baseEnd_3922848 : Nat := 1342871039019182048572771

theorem tailTrace_3922848 : CollatzResearch.WordTrace tailWord_3922848 prefixEnd_3922848 1342871039019182048572771 := by
  unfold tailWord_3922848
  simp only [CollatzResearch.WordTrace]
  refine ⟨71539010446099569972272599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95385347261466093296363465 71539010446099569972272599)
  ·
    refine ⟨107308515669149354958408899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71539010446099569972272599 107308515669149354958408899)
    ·
      refine ⟨160962773503724032437613349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107308515669149354958408899 160962773503724032437613349)
      ·
        refine ⟨30180520031948256082052503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160962773503724032437613349 30180520031948256082052503)
        ·
          refine ⟨45270780047922384123078755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30180520031948256082052503 45270780047922384123078755)
          ·
            refine ⟨67906170071883576184618133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45270780047922384123078755 67906170071883576184618133)
            ·
              refine ⟨3183101722119542633653975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67906170071883576184618133 3183101722119542633653975)
              ·
                refine ⟨4774652583179313950480963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3183101722119542633653975 4774652583179313950480963)
                ·
                  refine ⟨7161978874768970925721445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4774652583179313950480963 7161978874768970925721445)
                  ·
                    refine ⟨1342871039019182048572771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7161978874768970925721445 1342871039019182048572771)
                    ·
                      rfl

theorem cell22_3922848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 1, 4].length) (baseStart_3922848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3922848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3922848 prefixEnd_3922848 := by exact prefixLift 3922848
  have htrace : WordTrace (prefixWord ++ tailWord_3922848) baseStart_3922848 baseEnd_3922848 := by
    simpa [prefixWord, tailWord_3922848, baseEnd_3922848] using wordTrace_append hprefix tailTrace_3922848
  have hstable : (prefixWord ++ tailWord_3922848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922848).length < 2 ^ (prefixWord ++ tailWord_3922848).sum := by decide
  have hdescent : baseEnd_3922848 < baseStart_3922848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922874 : List Nat := [3, 1, 1, 1, 2, 1, 4, 9]
def baseStart_3922874 : Nat := 118140960795 + 3922874 * 2 ^ 59
def prefixEnd_3922874 : Nat := 4983230072969 + 3 ^ 40 * 3922874 * 2
def baseEnd_3922874 : Nat := 149208882150058516380299

theorem tailTrace_3922874 : CollatzResearch.WordTrace tailWord_3922874 prefixEnd_3922874 149208882150058516380299 := by
  unfold tailWord_3922874
  simp only [CollatzResearch.WordTrace]
  refine ⟨35769742297526236596247919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95385979460069964256661117 35769742297526236596247919)
  ·
    refine ⟨53654613446289354894371879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35769742297526236596247919 53654613446289354894371879)
    ·
      refine ⟨80481920169434032341557819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53654613446289354894371879 80481920169434032341557819)
      ·
        refine ⟨120722880254151048512336729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80481920169434032341557819 120722880254151048512336729)
        ·
          refine ⟨90542160190613286384252547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120722880254151048512336729 90542160190613286384252547)
          ·
            refine ⟨135813240285919929576378821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90542160190613286384252547 135813240285919929576378821)
            ·
              refine ⟨25464982553609986795571029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135813240285919929576378821 25464982553609986795571029)
              ·
                refine ⟨149208882150058516380299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25464982553609986795571029 149208882150058516380299)
                ·
                  rfl

theorem cell22_3922874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 9].length) (baseStart_3922874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3922874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3922874 prefixEnd_3922874 := by exact prefixLift 3922874
  have htrace : WordTrace (prefixWord ++ tailWord_3922874) baseStart_3922874 baseEnd_3922874 := by
    simpa [prefixWord, tailWord_3922874, baseEnd_3922874] using wordTrace_append hprefix tailTrace_3922874
  have hstable : (prefixWord ++ tailWord_3922874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922874).length < 2 ^ (prefixWord ++ tailWord_3922874).sum := by decide
  have hdescent : baseEnd_3922874 < baseStart_3922874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922891 : List Nat := [1, 1, 1, 1, 3, 5, 4, 6]
def baseStart_3922891 : Nat := 118140960795 + 3922891 * 2 ^ 59
def prefixEnd_3922891 : Nat := 4983230072969 + 3 ^ 40 * 3922891 * 2
def baseEnd_3922891 : Nat := 149209528755327141083071

theorem tailTrace_3922891 : CollatzResearch.WordTrace tailWord_3922891 prefixEnd_3922891 149209528755327141083071 := by
  unfold tailWord_3922891
  simp only [CollatzResearch.WordTrace]
  refine ⟨143079589231043358288360527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95386392820695572192240351 143079589231043358288360527)
  ·
    refine ⟨214619383846565037432540791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143079589231043358288360527 214619383846565037432540791)
    ·
      refine ⟨321929075769847556148811187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214619383846565037432540791 321929075769847556148811187)
      ·
        refine ⟨482893613654771334223216781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321929075769847556148811187 482893613654771334223216781)
        ·
          refine ⟨181085105120539250333706293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 482893613654771334223216781 181085105120539250333706293)
          ·
            refine ⟨16976728605050554718784965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 181085105120539250333706293 16976728605050554718784965)
            ·
              refine ⟨3183136613446979009772181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16976728605050554718784965 3183136613446979009772181)
              ·
                refine ⟨149209528755327141083071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3183136613446979009772181 149209528755327141083071)
                ·
                  rfl

theorem cell22_3922891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 6].length) (baseStart_3922891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3922891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3922891 prefixEnd_3922891 := by exact prefixLift 3922891
  have htrace : WordTrace (prefixWord ++ tailWord_3922891) baseStart_3922891 baseEnd_3922891 := by
    simpa [prefixWord, tailWord_3922891, baseEnd_3922891] using wordTrace_append hprefix tailTrace_3922891
  have hstable : (prefixWord ++ tailWord_3922891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922891).length < 2 ^ (prefixWord ++ tailWord_3922891).sum := by decide
  have hdescent : baseEnd_3922891 < baseStart_3922891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922981 : List Nat := [1, 3, 1, 2, 2, 2, 2, 3, 6]
def baseStart_3922981 : Nat := 118140960795 + 3922981 * 2 ^ 59
def prefixEnd_3922981 : Nat := 4983230072969 + 3 ^ 40 * 3922981 * 2
def baseEnd_3922981 : Nat := 447638855879071344999121

theorem tailTrace_3922981 : CollatzResearch.WordTrace tailWord_3922981 prefixEnd_3922981 447638855879071344999121 := by
  unfold tailWord_3922981
  simp only [CollatzResearch.WordTrace]
  refine ⟨143082871800717303659136797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95388581200478202439424531 143082871800717303659136797)
  ·
    refine ⟨53656076925268988872176299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143082871800717303659136797 53656076925268988872176299)
    ·
      refine ⟨80484115387903483308264449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53656076925268988872176299 80484115387903483308264449)
      ·
        refine ⟨60363086540927612481198337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80484115387903483308264449 60363086540927612481198337)
        ·
          refine ⟨45272314905695709360898753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60363086540927612481198337 45272314905695709360898753)
          ·
            refine ⟨33954236179271782020674065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45272314905695709360898753 33954236179271782020674065)
            ·
              refine ⟨25465677134453836515505549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33954236179271782020674065 25465677134453836515505549)
              ·
                refine ⟨9549628925420188693314581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25465677134453836515505549 9549628925420188693314581)
                ·
                  refine ⟨447638855879071344999121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9549628925420188693314581 447638855879071344999121)
                  ·
                    rfl

theorem cell22_3922981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 6].length) (baseStart_3922981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3922981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3922981 prefixEnd_3922981 := by exact prefixLift 3922981
  have htrace : WordTrace (prefixWord ++ tailWord_3922981) baseStart_3922981 baseEnd_3922981 := by
    simpa [prefixWord, tailWord_3922981, baseEnd_3922981] using wordTrace_append hprefix tailTrace_3922981
  have hstable : (prefixWord ++ tailWord_3922981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922981).length < 2 ^ (prefixWord ++ tailWord_3922981).sum := by decide
  have hdescent : baseEnd_3922981 < baseStart_3922981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922998 : List Nat := [5, 1, 2, 1, 1, 2, 1, 1, 8]
def baseStart_3922998 : Nat := 118140960795 + 3922998 * 2 ^ 59
def prefixEnd_3922998 : Nat := 4983230072969 + 3 ^ 40 * 3922998 * 2
def baseEnd_3922998 : Nat := 447640795694877219107437

theorem tailTrace_3922998 : CollatzResearch.WordTrace tailWord_3922998 prefixEnd_3922998 447640795694877219107437 := by
  unfold tailWord_3922998
  simp only [CollatzResearch.WordTrace]
  refine ⟨8942718240103482222656603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95388994561103810375003765 8942718240103482222656603)
  ·
    refine ⟨13414077360155223333984905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8942718240103482222656603 13414077360155223333984905)
    ·
      refine ⟨10060558020116417500488679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13414077360155223333984905 10060558020116417500488679)
      ·
        refine ⟨15090837030174626250733019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10060558020116417500488679 15090837030174626250733019)
        ·
          refine ⟨22636255545261939376099529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15090837030174626250733019 22636255545261939376099529)
          ·
            refine ⟨16977191658946454532074647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22636255545261939376099529 16977191658946454532074647)
            ·
              refine ⟨25465787488419681798111971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16977191658946454532074647 25465787488419681798111971)
              ·
                refine ⟨38198681232629522697167957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25465787488419681798111971 38198681232629522697167957)
                ·
                  refine ⟨447640795694877219107437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38198681232629522697167957 447640795694877219107437)
                  ·
                    rfl

theorem cell22_3922998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_3922998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3922998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3922998 prefixEnd_3922998 := by exact prefixLift 3922998
  have htrace : WordTrace (prefixWord ++ tailWord_3922998) baseStart_3922998 baseEnd_3922998 := by
    simpa [prefixWord, tailWord_3922998, baseEnd_3922998] using wordTrace_append hprefix tailTrace_3922998
  have hstable : (prefixWord ++ tailWord_3922998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922998).length < 2 ^ (prefixWord ++ tailWord_3922998).sum := by decide
  have hdescent : baseEnd_3922998 < baseStart_3922998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923011 : List Nat := [1, 1, 1, 3, 1, 2, 5, 1, 1, 6]
def baseStart_3923011 : Nat := 118140960795 + 3923011 * 2 ^ 59
def prefixEnd_3923011 : Nat := 4983230072969 + 3 ^ 40 * 3923011 * 2
def baseEnd_3923011 : Nat := 1342926837250303956747271

theorem tailTrace_3923011 : CollatzResearch.WordTrace tailWord_3923011 prefixEnd_3923011 1342926837250303956747271 := by
  unfold tailWord_3923011
  simp only [CollatzResearch.WordTrace]
  refine ⟨143083965990608618782728887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95389310660405745855152591 143083965990608618782728887)
  ·
    refine ⟨214625948985912928174093331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143083965990608618782728887 214625948985912928174093331)
    ·
      refine ⟨321938923478869392261139997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214625948985912928174093331 321938923478869392261139997)
      ·
        refine ⟨120727096304576022097927499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321938923478869392261139997 120727096304576022097927499)
        ·
          refine ⟨181090644456864033146891249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120727096304576022097927499 181090644456864033146891249)
          ·
            refine ⟨135817983342648024860168437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181090644456864033146891249 135817983342648024860168437)
            ·
              refine ⟨12732935938373252330640791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135817983342648024860168437 12732935938373252330640791)
              ·
                refine ⟨19099403907559878495961187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12732935938373252330640791 19099403907559878495961187)
                ·
                  refine ⟨28649105861339817743941781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19099403907559878495961187 28649105861339817743941781)
                  ·
                    refine ⟨1342926837250303956747271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28649105861339817743941781 1342926837250303956747271)
                    ·
                      rfl

theorem cell22_3923011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 6].length) (baseStart_3923011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3923011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3923011 prefixEnd_3923011 := by exact prefixLift 3923011
  have htrace : WordTrace (prefixWord ++ tailWord_3923011) baseStart_3923011 baseEnd_3923011 := by
    simpa [prefixWord, tailWord_3923011, baseEnd_3923011] using wordTrace_append hprefix tailTrace_3923011
  have hstable : (prefixWord ++ tailWord_3923011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923011).length < 2 ^ (prefixWord ++ tailWord_3923011).sum := by decide
  have hdescent : baseEnd_3923011 < baseStart_3923011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923015 : List Nat := [1, 1, 4, 1, 3, 3, 2, 3, 4]
def baseStart_3923015 : Nat := 118140960795 + 3923015 * 2 ^ 59
def prefixEnd_3923015 : Nat := 4983230072969 + 3 ^ 40 * 3923015 * 2
def baseEnd_3923015 : Nat := 447642735510683093215753

theorem tailTrace_3923015 : CollatzResearch.WordTrace tailWord_3923015 prefixEnd_3923015 447642735510683093215753 := by
  unfold tailWord_3923015
  simp only [CollatzResearch.WordTrace]
  refine ⟨143084111882594127465874499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95389407921729418310582999 143084111882594127465874499)
  ·
    refine ⟨214626167823891191198811749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143084111882594127465874499 214626167823891191198811749)
    ·
      refine ⟨40242406466979598349777203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214626167823891191198811749 40242406466979598349777203)
      ·
        refine ⟨60363609700469397524665805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40242406466979598349777203 60363609700469397524665805)
        ·
          refine ⟨22636353637676024071749677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60363609700469397524665805 22636353637676024071749677)
          ·
            refine ⟨8488632614128509026906129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22636353637676024071749677 8488632614128509026906129)
            ·
              refine ⟨6366474460596381770179597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8488632614128509026906129 6366474460596381770179597)
              ·
                refine ⟨2387427922723643163817349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6366474460596381770179597 2387427922723643163817349)
                ·
                  refine ⟨447642735510683093215753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2387427922723643163817349 447642735510683093215753)
                  ·
                    rfl

theorem cell22_3923015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 3, 4].length) (baseStart_3923015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3923015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3923015 prefixEnd_3923015 := by exact prefixLift 3923015
  have htrace : WordTrace (prefixWord ++ tailWord_3923015) baseStart_3923015 baseEnd_3923015 := by
    simpa [prefixWord, tailWord_3923015, baseEnd_3923015] using wordTrace_append hprefix tailTrace_3923015
  have hstable : (prefixWord ++ tailWord_3923015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923015).length < 2 ^ (prefixWord ++ tailWord_3923015).sum := by decide
  have hdescent : baseEnd_3923015 < baseStart_3923015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923028 : List Nat := [2, 4, 1, 1, 1, 1, 2, 4, 2, 4]
def baseStart_3923028 : Nat := 118140960795 + 3923028 * 2 ^ 59
def prefixEnd_3923028 : Nat := 4983230072969 + 3 ^ 40 * 3923028 * 2
def baseEnd_3923028 : Nat := 1342932656697721579072219

theorem tailTrace_3923028 : CollatzResearch.WordTrace tailWord_3923028 prefixEnd_3923028 1342932656697721579072219 := by
  unfold tailWord_3923028
  simp only [CollatzResearch.WordTrace]
  refine ⟨71542293015773515343048869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95389724021031353790731825 71542293015773515343048869)
  ·
    refine ⟨13414179940457534126821663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71542293015773515343048869 13414179940457534126821663)
    ·
      refine ⟨20121269910686301190232495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13414179940457534126821663 20121269910686301190232495)
      ·
        refine ⟨30181904866029451785348743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20121269910686301190232495 30181904866029451785348743)
        ·
          refine ⟨45272857299044177678023115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30181904866029451785348743 45272857299044177678023115)
          ·
            refine ⟨67909285948566266517034673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45272857299044177678023115 67909285948566266517034673)
            ·
              refine ⟨50931964461424699887776005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67909285948566266517034673 50931964461424699887776005)
              ·
                refine ⟨9549743336517131228958001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50931964461424699887776005 9549743336517131228958001)
                ·
                  refine ⟨7162307502387848421718501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9549743336517131228958001 7162307502387848421718501)
                  ·
                    refine ⟨1342932656697721579072219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7162307502387848421718501 1342932656697721579072219)
                    ·
                      rfl

theorem cell22_3923028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_3923028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3923028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3923028 prefixEnd_3923028 := by exact prefixLift 3923028
  have htrace : WordTrace (prefixWord ++ tailWord_3923028) baseStart_3923028 baseEnd_3923028 := by
    simpa [prefixWord, tailWord_3923028, baseEnd_3923028] using wordTrace_append hprefix tailTrace_3923028
  have hstable : (prefixWord ++ tailWord_3923028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923028).length < 2 ^ (prefixWord ++ tailWord_3923028).sum := by decide
  have hdescent : baseEnd_3923028 < baseStart_3923028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
