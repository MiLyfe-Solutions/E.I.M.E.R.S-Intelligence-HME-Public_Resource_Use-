import V185TrunkScan22Chunk358

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3202129 : List Nat := [1, 2, 2, 1, 3, 1, 4, 1, 1, 6]
def baseStart_3202129 : Nat := 118140960795 + 3202129 * 2 ^ 59
def prefixEnd_3202129 : Nat := 4983230072969 + 3 ^ 40 * 3202129 * 2
def baseEnd_3202129 : Nat := 1096154196467338259507455

theorem tailTrace_3202129 : CollatzResearch.WordTrace tailWord_3202129 prefixEnd_3202129 1096154196467338259507455 := by
  unfold tailWord_3202129
  simp only [CollatzResearch.WordTrace]
  refine ⟨116791239416240987938961441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77860826277493991959307627 116791239416240987938961441)
  ·
    refine ⟨87593429562180740954221081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116791239416240987938961441 87593429562180740954221081)
    ·
      refine ⟨65695072171635555715665811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87593429562180740954221081 65695072171635555715665811)
      ·
        refine ⟨98542608257453333573498717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65695072171635555715665811 98542608257453333573498717)
        ·
          refine ⟨36953478096545000090062019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98542608257453333573498717 36953478096545000090062019)
          ·
            refine ⟨55430217144817500135093029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36953478096545000090062019 55430217144817500135093029)
            ·
              refine ⟨10393165714653281275329943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55430217144817500135093029 10393165714653281275329943)
              ·
                refine ⟨15589748571979921912994915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10393165714653281275329943 15589748571979921912994915)
                ·
                  refine ⟨23384622857969882869492373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15589748571979921912994915 23384622857969882869492373)
                  ·
                    refine ⟨1096154196467338259507455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23384622857969882869492373 1096154196467338259507455)
                    ·
                      rfl

theorem cell22_3202129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_3202129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3202129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3202129 prefixEnd_3202129 := by exact prefixLift 3202129
  have htrace : WordTrace (prefixWord ++ tailWord_3202129) baseStart_3202129 baseEnd_3202129 := by
    simpa [prefixWord, tailWord_3202129, baseEnd_3202129] using wordTrace_append hprefix tailTrace_3202129
  have hstable : (prefixWord ++ tailWord_3202129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202129).length < 2 ^ (prefixWord ++ tailWord_3202129).sum := by decide
  have hdescent : baseEnd_3202129 < baseStart_3202129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202176 : List Nat := [2, 1, 1, 2, 1, 3, 2, 4, 3, 3]
def baseStart_3202176 : Nat := 118140960795 + 3202176 * 2 ^ 59
def prefixEnd_3202176 : Nat := 4983230072969 + 3 ^ 40 * 3202176 * 2
def baseEnd_3202176 : Nat := 1096170285527845803582311

theorem tailTrace_3202176 : CollatzResearch.WordTrace tailWord_3202176 prefixEnd_3202176 1096170285527845803582311 := by
  unfold tailWord_3202176
  simp only [CollatzResearch.WordTrace]
  refine ⟨58396476823535357482961191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77861969098047143310614921 58396476823535357482961191)
  ·
    refine ⟨87594715235303036224441787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58396476823535357482961191 87594715235303036224441787)
    ·
      refine ⟨131392072852954554336662681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87594715235303036224441787 131392072852954554336662681)
      ·
        refine ⟨98544054639715915752497011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131392072852954554336662681 98544054639715915752497011)
        ·
          refine ⟨147816081959573873628745517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98544054639715915752497011 147816081959573873628745517)
          ·
            refine ⟨55431030734840202610779569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147816081959573873628745517 55431030734840202610779569)
            ·
              refine ⟨41573273051130151958084677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55431030734840202610779569 41573273051130151958084677)
              ·
                refine ⟨7794988697086903492140877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41573273051130151958084677 7794988697086903492140877)
                ·
                  refine ⟨2923120761407588809552829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7794988697086903492140877 2923120761407588809552829)
                  ·
                    refine ⟨1096170285527845803582311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2923120761407588809552829 1096170285527845803582311)
                    ·
                      rfl

theorem cell22_3202176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 3, 3].length) (baseStart_3202176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3202176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3202176 prefixEnd_3202176 := by exact prefixLift 3202176
  have htrace : WordTrace (prefixWord ++ tailWord_3202176) baseStart_3202176 baseEnd_3202176 := by
    simpa [prefixWord, tailWord_3202176, baseEnd_3202176] using wordTrace_append hprefix tailTrace_3202176
  have hstable : (prefixWord ++ tailWord_3202176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202176).length < 2 ^ (prefixWord ++ tailWord_3202176).sum := by decide
  have hdescent : baseEnd_3202176 < baseStart_3202176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202249 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 2, 9]
def baseStart_3202249 : Nat := 118140960795 + 3202249 * 2 ^ 59
def prefixEnd_3202249 : Nat := 4983230072969 + 3 ^ 40 * 3202249 * 2
def baseEnd_3202249 : Nat := 1096195274919697946507087

theorem tailTrace_3202249 : CollatzResearch.WordTrace tailWord_3202249 prefixEnd_3202249 1096195274919697946507087 := by
  unfold tailWord_3202249
  simp only [CollatzResearch.WordTrace]
  refine ⟨116795616175806248433329801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77863744117204165622219867 116795616175806248433329801)
  ·
    refine ⟨87596712131854686324997351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116795616175806248433329801 87596712131854686324997351)
    ·
      refine ⟨131395068197782029487496027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87596712131854686324997351 131395068197782029487496027)
      ·
        refine ⟨197092602296673044231244041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131395068197782029487496027 197092602296673044231244041)
        ·
          refine ⟨147819451722504783173433031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197092602296673044231244041 147819451722504783173433031)
          ·
            refine ⟨221729177583757174760149547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147819451722504783173433031 221729177583757174760149547)
            ·
              refine ⟨332593766375635762140224321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221729177583757174760149547 332593766375635762140224321)
              ·
                refine ⟨249445324781726821605168241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 332593766375635762140224321 249445324781726821605168241)
                ·
                  refine ⟨187083993586295116203876181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249445324781726821605168241 187083993586295116203876181)
                  ·
                    refine ⟨1096195274919697946507087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 187083993586295116203876181 1096195274919697946507087)
                    ·
                      rfl

theorem cell22_3202249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 9].length) (baseStart_3202249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3202249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3202249 prefixEnd_3202249 := by exact prefixLift 3202249
  have htrace : WordTrace (prefixWord ++ tailWord_3202249) baseStart_3202249 baseEnd_3202249 := by
    simpa [prefixWord, tailWord_3202249, baseEnd_3202249] using wordTrace_append hprefix tailTrace_3202249
  have hstable : (prefixWord ++ tailWord_3202249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202249).length < 2 ^ (prefixWord ++ tailWord_3202249).sum := by decide
  have hdescent : baseEnd_3202249 < baseStart_3202249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202283 : List Nat := [1, 1, 1, 1, 2, 8, 1, 1, 1, 5]
def baseStart_3202283 : Nat := 118140960795 + 3202283 * 2 ^ 59
def prefixEnd_3202283 : Nat := 4983230072969 + 3 ^ 40 * 3202283 * 2
def baseEnd_3202283 : Nat := 1096206913814533191156983

theorem tailTrace_3202283 : CollatzResearch.WordTrace tailWord_3202283 prefixEnd_3202283 1096206913814533191156983 := by
  unfold tailWord_3202283
  simp only [CollatzResearch.WordTrace]
  refine ⟨116796856257683072240067503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77864570838455381493378335 116796856257683072240067503)
  ·
    refine ⟨175195284386524608360101255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116796856257683072240067503 175195284386524608360101255)
    ·
      refine ⟨262792926579786912540151883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175195284386524608360101255 262792926579786912540151883)
      ·
        refine ⟨394189389869680368810227825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262792926579786912540151883 394189389869680368810227825)
        ·
          refine ⟨295642042402260276607670869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394189389869680368810227825 295642042402260276607670869)
          ·
            refine ⟨3464555184401487616496143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 295642042402260276607670869 3464555184401487616496143)
            ·
              refine ⟨5196832776602231424744215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3464555184401487616496143 5196832776602231424744215)
              ·
                refine ⟨7795249164903347137116323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5196832776602231424744215 7795249164903347137116323)
                ·
                  refine ⟨11692873747355020705674485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7795249164903347137116323 11692873747355020705674485)
                  ·
                    refine ⟨1096206913814533191156983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11692873747355020705674485 1096206913814533191156983)
                    ·
                      rfl

theorem cell22_3202283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 5].length) (baseStart_3202283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3202283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3202283 prefixEnd_3202283 := by exact prefixLift 3202283
  have htrace : WordTrace (prefixWord ++ tailWord_3202283) baseStart_3202283 baseEnd_3202283 := by
    simpa [prefixWord, tailWord_3202283, baseEnd_3202283] using wordTrace_append hprefix tailTrace_3202283
  have hstable : (prefixWord ++ tailWord_3202283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202283).length < 2 ^ (prefixWord ++ tailWord_3202283).sum := by decide
  have hdescent : baseEnd_3202283 < baseStart_3202283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202302 : List Nat := [4, 2, 2, 1, 1, 4, 1, 3, 4]
def baseStart_3202302 : Nat := 118140960795 + 3202302 * 2 ^ 59
def prefixEnd_3202302 : Nat := 4983230072969 + 3 ^ 40 * 3202302 * 2
def baseEnd_3202302 : Nat := 365404472634274491643975

theorem tailTrace_3202302 : CollatzResearch.WordTrace tailWord_3202302 prefixEnd_3202302 365404472634274491643975 := by
  unfold tailWord_3202302
  simp only [CollatzResearch.WordTrace]
  refine ⟨14599693655576779810626145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77865032829742825656672773 14599693655576779810626145)
  ·
    refine ⟨10949770241682584857969609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14599693655576779810626145 10949770241682584857969609)
    ·
      refine ⟨8212327681261938643477207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10949770241682584857969609 8212327681261938643477207)
      ·
        refine ⟨12318491521892907965215811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8212327681261938643477207 12318491521892907965215811)
        ·
          refine ⟨18477737282839361947823717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12318491521892907965215811 18477737282839361947823717)
          ·
            refine ⟨3464575740532380365216947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18477737282839361947823717 3464575740532380365216947)
            ·
              refine ⟨5196863610798570547825421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3464575740532380365216947 5196863610798570547825421)
              ·
                refine ⟨1948823854049463955434533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5196863610798570547825421 1948823854049463955434533)
                ·
                  refine ⟨365404472634274491643975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1948823854049463955434533 365404472634274491643975)
                  ·
                    rfl

theorem cell22_3202302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_3202302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3202302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3202302 prefixEnd_3202302 := by exact prefixLift 3202302
  have htrace : WordTrace (prefixWord ++ tailWord_3202302) baseStart_3202302 baseEnd_3202302 := by
    simpa [prefixWord, tailWord_3202302, baseEnd_3202302] using wordTrace_append hprefix tailTrace_3202302
  have hstable : (prefixWord ++ tailWord_3202302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202302).length < 2 ^ (prefixWord ++ tailWord_3202302).sum := by decide
  have hdescent : baseEnd_3202302 < baseStart_3202302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202334 : List Nat := [4, 3, 2, 1, 2, 1, 1, 3, 2, 3]
def baseStart_3202334 : Nat := 118140960795 + 3202334 * 2 ^ 59
def prefixEnd_3202334 : Nat := 4983230072969 + 3 ^ 40 * 3202334 * 2
def baseEnd_3202334 : Nat := 1096224372156786058131827

theorem tailTrace_3202334 : CollatzResearch.WordTrace tailWord_3202334 prefixEnd_3202334 1096224372156786058131827 := by
  unfold tailWord_3202334
  simp only [CollatzResearch.WordTrace]
  refine ⟨14599839547562288493771757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77865810920332205300116037 14599839547562288493771757)
  ·
    refine ⟨5474939830335858185164409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14599839547562288493771757 5474939830335858185164409)
    ·
      refine ⟨4106204872751893638873307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5474939830335858185164409 4106204872751893638873307)
      ·
        refine ⟨6159307309127840458309961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4106204872751893638873307 6159307309127840458309961)
        ·
          refine ⟨4619480481845880343732471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6159307309127840458309961 4619480481845880343732471)
          ·
            refine ⟨6929220722768820515598707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4619480481845880343732471 6929220722768820515598707)
            ·
              refine ⟨10393831084153230773398061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6929220722768820515598707 10393831084153230773398061)
              ·
                refine ⟨3897686656557461540024273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10393831084153230773398061 3897686656557461540024273)
                ·
                  refine ⟨2923264992418096155018205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3897686656557461540024273 2923264992418096155018205)
                  ·
                    refine ⟨1096224372156786058131827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2923264992418096155018205 1096224372156786058131827)
                    ·
                      rfl

theorem cell22_3202334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_3202334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3202334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3202334 prefixEnd_3202334 := by exact prefixLift 3202334
  have htrace : WordTrace (prefixWord ++ tailWord_3202334) baseStart_3202334 baseEnd_3202334 := by
    simpa [prefixWord, tailWord_3202334, baseEnd_3202334] using wordTrace_append hprefix tailTrace_3202334
  have hstable : (prefixWord ++ tailWord_3202334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202334).length < 2 ^ (prefixWord ++ tailWord_3202334).sum := by decide
  have hdescent : baseEnd_3202334 < baseStart_3202334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202388 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 5, 4]
def baseStart_3202388 : Nat := 118140960795 + 3202388 * 2 ^ 59
def prefixEnd_3202388 : Nat := 4983230072969 + 3 ^ 40 * 3202388 * 2
def baseEnd_3202388 : Nat := 1096242857460347917281661

theorem tailTrace_3202388 : CollatzResearch.WordTrace tailWord_3202388 prefixEnd_3202388 1096242857460347917281661 := by
  unfold tailWord_3202388
  simp only [CollatzResearch.WordTrace]
  refine ⟨58400342961151337586319909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77867123948201783448426545 58400342961151337586319909)
  ·
    refine ⟨10950064305215875797434983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58400342961151337586319909 10950064305215875797434983)
    ·
      refine ⟨16425096457823813696152475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10950064305215875797434983 16425096457823813696152475)
      ·
        refine ⟨24637644686735720544228713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16425096457823813696152475 24637644686735720544228713)
        ·
          refine ⟨18478233515051790408171535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24637644686735720544228713 18478233515051790408171535)
          ·
            refine ⟨27717350272577685612257303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18478233515051790408171535 27717350272577685612257303)
            ·
              refine ⟨41576025408866528418385955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27717350272577685612257303 41576025408866528418385955)
              ·
                refine ⟨62364038113299792627578933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41576025408866528418385955 62364038113299792627578933)
                ·
                  refine ⟨5846628573121855558835525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62364038113299792627578933 5846628573121855558835525)
                  ·
                    refine ⟨1096242857460347917281661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5846628573121855558835525 1096242857460347917281661)
                    ·
                      rfl

theorem cell22_3202388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_3202388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3202388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3202388 prefixEnd_3202388 := by exact prefixLift 3202388
  have htrace : WordTrace (prefixWord ++ tailWord_3202388) baseStart_3202388 baseEnd_3202388 := by
    simpa [prefixWord, tailWord_3202388, baseEnd_3202388] using wordTrace_append hprefix tailTrace_3202388
  have hstable : (prefixWord ++ tailWord_3202388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202388).length < 2 ^ (prefixWord ++ tailWord_3202388).sum := by decide
  have hdescent : baseEnd_3202388 < baseStart_3202388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202403 : List Nat := [1, 1, 1, 5, 2, 3, 1, 2, 6]
def baseStart_3202403 : Nat := 118140960795 + 3202403 * 2 ^ 59
def prefixEnd_3202403 : Nat := 4983230072969 + 3 ^ 40 * 3202403 * 2
def baseEnd_3202403 : Nat := 365415997422297626052205

theorem tailTrace_3202403 : CollatzResearch.WordTrace tailWord_3202403 prefixEnd_3202403 365415997422297626052205 := by
  unfold tailWord_3202403
  simp only [CollatzResearch.WordTrace]
  refine ⟨116801233017248332734435863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77867488678165555156290575 116801233017248332734435863)
  ·
    refine ⟨175201849525872499101653795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116801233017248332734435863 175201849525872499101653795)
    ·
      refine ⟨262802774288808748652480693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175201849525872499101653795 262802774288808748652480693)
      ·
        refine ⟨24637760089575820186170065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 262802774288808748652480693 24637760089575820186170065)
        ·
          refine ⟨18478320067181865139627549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24637760089575820186170065 18478320067181865139627549)
          ·
            refine ⟨6929370025193199427360331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18478320067181865139627549 6929370025193199427360331)
            ·
              refine ⟨10394055037789799141040497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6929370025193199427360331 10394055037789799141040497)
              ·
                refine ⟨7795541278342349355780373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10394055037789799141040497 7795541278342349355780373)
                ·
                  refine ⟨365415997422297626052205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7795541278342349355780373 365415997422297626052205)
                  ·
                    rfl

theorem cell22_3202403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 6].length) (baseStart_3202403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3202403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3202403 prefixEnd_3202403 := by exact prefixLift 3202403
  have htrace : WordTrace (prefixWord ++ tailWord_3202403) baseStart_3202403 baseEnd_3202403 := by
    simpa [prefixWord, tailWord_3202403, baseEnd_3202403] using wordTrace_append hprefix tailTrace_3202403
  have hstable : (prefixWord ++ tailWord_3202403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202403).length < 2 ^ (prefixWord ++ tailWord_3202403).sum := by decide
  have hdescent : baseEnd_3202403 < baseStart_3202403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202418 : List Nat := [3, 2, 1, 2, 1, 2, 1, 4, 1, 5]
def baseStart_3202418 : Nat := 118140960795 + 3202418 * 2 ^ 59
def prefixEnd_3202418 : Nat := 4983230072969 + 3 ^ 40 * 3202418 * 2
def baseEnd_3202418 : Nat := 1096253127073437839031569

theorem tailTrace_3202418 : CollatzResearch.WordTrace tailWord_3202418 prefixEnd_3202418 1096253127073437839031569 := by
  unfold tailWord_3202418
  simp only [CollatzResearch.WordTrace]
  refine ⟨29200445028048497574057977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77867853408129326864154605 29200445028048497574057977)
  ·
    refine ⟨21900333771036373180543483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29200445028048497574057977 21900333771036373180543483)
    ·
      refine ⟨32850500656554559770815225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21900333771036373180543483 32850500656554559770815225)
      ·
        refine ⟨24637875492415919828111419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32850500656554559770815225 24637875492415919828111419)
        ·
          refine ⟨36956813238623879742167129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24637875492415919828111419 36956813238623879742167129)
          ·
            refine ⟨27717609928967909806625347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36956813238623879742167129 27717609928967909806625347)
            ·
              refine ⟨41576414893451864709938021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27717609928967909806625347 41576414893451864709938021)
              ·
                refine ⟨7795577792522224633113379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41576414893451864709938021 7795577792522224633113379)
                ·
                  refine ⟨11693366688783336949670069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7795577792522224633113379 11693366688783336949670069)
                  ·
                    refine ⟨1096253127073437839031569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11693366688783336949670069 1096253127073437839031569)
                    ·
                      rfl

theorem cell22_3202418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_3202418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3202418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3202418 prefixEnd_3202418 := by exact prefixLift 3202418
  have htrace : WordTrace (prefixWord ++ tailWord_3202418) baseStart_3202418 baseEnd_3202418 := by
    simpa [prefixWord, tailWord_3202418, baseEnd_3202418] using wordTrace_append hprefix tailTrace_3202418
  have hstable : (prefixWord ++ tailWord_3202418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202418).length < 2 ^ (prefixWord ++ tailWord_3202418).sum := by decide
  have hdescent : baseEnd_3202418 < baseStart_3202418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202435 : List Nat := [1, 1, 1, 3, 5, 2, 1, 1, 4, 3]
def baseStart_3202435 : Nat := 118140960795 + 3202435 * 2 ^ 59
def prefixEnd_3202435 : Nat := 4983230072969 + 3 ^ 40 * 3202435 * 2
def baseEnd_3202435 : Nat := 1096258946520855461356517

theorem tailTrace_3202435 : CollatzResearch.WordTrace tailWord_3202435 prefixEnd_3202435 1096258946520855461356517 := by
  unfold tailWord_3202435
  simp only [CollatzResearch.WordTrace]
  refine ⟨116802400153132402199600759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77868266768754934799733839 116802400153132402199600759)
  ·
    refine ⟨175203600229698603299401139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116802400153132402199600759 175203600229698603299401139)
    ·
      refine ⟨262805400344547904949101709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175203600229698603299401139 262805400344547904949101709)
      ·
        refine ⟨98552025129205464355913141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262805400344547904949101709 98552025129205464355913141)
        ·
          refine ⟨9239252355863012283366857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98552025129205464355913141 9239252355863012283366857)
          ·
            refine ⟨6929439266897259212525143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9239252355863012283366857 6929439266897259212525143)
            ·
              refine ⟨10394158900345888818787715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6929439266897259212525143 10394158900345888818787715)
              ·
                refine ⟨15591238350518833228181573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10394158900345888818787715 15591238350518833228181573)
                ·
                  refine ⟨2923357190722281230284045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15591238350518833228181573 2923357190722281230284045)
                  ·
                    refine ⟨1096258946520855461356517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2923357190722281230284045 1096258946520855461356517)
                    ·
                      rfl

theorem cell22_3202435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 4, 3].length) (baseStart_3202435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3202435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3202435 prefixEnd_3202435 := by exact prefixLift 3202435
  have htrace : WordTrace (prefixWord ++ tailWord_3202435) baseStart_3202435 baseEnd_3202435 := by
    simpa [prefixWord, tailWord_3202435, baseEnd_3202435] using wordTrace_append hprefix tailTrace_3202435
  have hstable : (prefixWord ++ tailWord_3202435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202435).length < 2 ^ (prefixWord ++ tailWord_3202435).sum := by decide
  have hdescent : baseEnd_3202435 < baseStart_3202435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202452 : List Nat := [2, 4, 2, 1, 2, 3, 1, 1, 1, 5]
def baseStart_3202452 : Nat := 118140960795 + 3202452 * 2 ^ 59
def prefixEnd_3202452 : Nat := 4983230072969 + 3 ^ 40 * 3202452 * 2
def baseEnd_3202452 : Nat := 1096264765968273083681465

theorem tailTrace_3202452 : CollatzResearch.WordTrace tailWord_3202452 prefixEnd_3202452 1096264765968273083681465 := by
  unfold tailWord_3202452
  simp only [CollatzResearch.WordTrace]
  refine ⟨58401510097035407051484805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77868680129380542735313073 58401510097035407051484805)
  ·
    refine ⟨10950283143194138822153401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58401510097035407051484805 10950283143194138822153401)
    ·
      refine ⟨8212712357395604116615051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10950283143194138822153401 8212712357395604116615051)
      ·
        refine ⟨12319068536093406174922577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8212712357395604116615051 12319068536093406174922577)
        ·
          refine ⟨9239301402070054631191933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12319068536093406174922577 9239301402070054631191933)
          ·
            refine ⟨3464738025776270486696975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9239301402070054631191933 3464738025776270486696975)
            ·
              refine ⟨5197107038664405730045463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3464738025776270486696975 5197107038664405730045463)
              ·
                refine ⟨7795660557996608595068195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5197107038664405730045463 7795660557996608595068195)
                ·
                  refine ⟨11693490836994912892602293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7795660557996608595068195 11693490836994912892602293)
                  ·
                    refine ⟨1096264765968273083681465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11693490836994912892602293 1096264765968273083681465)
                    ·
                      rfl

theorem cell22_3202452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_3202452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3202452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3202452 prefixEnd_3202452 := by exact prefixLift 3202452
  have htrace : WordTrace (prefixWord ++ tailWord_3202452) baseStart_3202452 baseEnd_3202452 := by
    simpa [prefixWord, tailWord_3202452, baseEnd_3202452] using wordTrace_append hprefix tailTrace_3202452
  have hstable : (prefixWord ++ tailWord_3202452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202452).length < 2 ^ (prefixWord ++ tailWord_3202452).sum := by decide
  have hdescent : baseEnd_3202452 < baseStart_3202452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202493 : List Nat := [1, 4, 1, 2, 2, 1, 1, 3, 7]
def baseStart_3202493 : Nat := 118140960795 + 3202493 * 2 ^ 59
def prefixEnd_3202493 : Nat := 4983230072969 + 3 ^ 40 * 3202493 * 2
def baseEnd_3202493 : Nat := 365426267035387547802113

theorem tailTrace_3202493 : CollatzResearch.WordTrace tailWord_3202493 prefixEnd_3202493 365426267035387547802113 := by
  unfold tailWord_3202493
  simp only [CollatzResearch.WordTrace]
  refine ⟨116804515586922278105212133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77869677057948185403474755 116804515586922278105212133)
  ·
    refine ⟨21900846672547927144727275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116804515586922278105212133 21900846672547927144727275)
    ·
      refine ⟨32851270008821890717090913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21900846672547927144727275 32851270008821890717090913)
      ·
        refine ⟨24638452506616418037818185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32851270008821890717090913 24638452506616418037818185)
        ·
          refine ⟨18478839379962313528363639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24638452506616418037818185 18478839379962313528363639)
          ·
            refine ⟨27718259069943470292545459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18478839379962313528363639 27718259069943470292545459)
            ·
              refine ⟨41577388604915205438818189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27718259069943470292545459 41577388604915205438818189)
              ·
                refine ⟨15591520726843202039556821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41577388604915205438818189 15591520726843202039556821)
                ·
                  refine ⟨365426267035387547802113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15591520726843202039556821 365426267035387547802113)
                  ·
                    rfl

theorem cell22_3202493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_3202493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3202493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3202493 prefixEnd_3202493 := by exact prefixLift 3202493
  have htrace : WordTrace (prefixWord ++ tailWord_3202493) baseStart_3202493 baseEnd_3202493 := by
    simpa [prefixWord, tailWord_3202493, baseEnd_3202493] using wordTrace_append hprefix tailTrace_3202493
  have hstable : (prefixWord ++ tailWord_3202493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202493).length < 2 ^ (prefixWord ++ tailWord_3202493).sum := by decide
  have hdescent : baseEnd_3202493 < baseStart_3202493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202553 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 5, 5]
def baseStart_3202553 : Nat := 118140960795 + 3202553 * 2 ^ 59
def prefixEnd_3202553 : Nat := 4983230072969 + 3 ^ 40 * 3202553 * 2
def baseEnd_3202553 : Nat := 1096299340332342486906155

theorem tailTrace_3202553 : CollatzResearch.WordTrace tailWord_3202553 prefixEnd_3202553 1096299340332342486906155 := by
  unfold tailWord_3202553
  simp only [CollatzResearch.WordTrace]
  refine ⟨116806703966704908352396313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77871135977803272234930875 116806703966704908352396313)
  ·
    refine ⟨87605027975028681264297235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116806703966704908352396313 87605027975028681264297235)
    ·
      refine ⟨131407541962543021896445853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87605027975028681264297235 131407541962543021896445853)
      ·
        refine ⟨49277828235953633211167195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131407541962543021896445853 49277828235953633211167195)
        ·
          refine ⟨73916742353930449816750793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49277828235953633211167195 73916742353930449816750793)
          ·
            refine ⟨55437556765447837362563095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73916742353930449816750793 55437556765447837362563095)
            ·
              refine ⟨83156335148171756043844643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55437556765447837362563095 83156335148171756043844643)
              ·
                refine ⟨124734502722257634065766965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83156335148171756043844643 124734502722257634065766965)
                ·
                  refine ⟨11693859630211653193665653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 124734502722257634065766965 11693859630211653193665653)
                  ·
                    refine ⟨1096299340332342486906155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11693859630211653193665653 1096299340332342486906155)
                    ·
                      rfl

theorem cell22_3202553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 5].length) (baseStart_3202553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3202553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3202553 prefixEnd_3202553 := by exact prefixLift 3202553
  have htrace : WordTrace (prefixWord ++ tailWord_3202553) baseStart_3202553 baseEnd_3202553 := by
    simpa [prefixWord, tailWord_3202553, baseEnd_3202553] using wordTrace_append hprefix tailTrace_3202553
  have hstable : (prefixWord ++ tailWord_3202553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202553).length < 2 ^ (prefixWord ++ tailWord_3202553).sum := by decide
  have hdescent : baseEnd_3202553 < baseStart_3202553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202555 : List Nat := [1, 1, 1, 1, 1, 3, 2, 8, 4]
def baseStart_3202555 : Nat := 118140960795 + 3202555 * 2 ^ 59
def prefixEnd_3202555 : Nat := 4983230072969 + 3 ^ 40 * 3202555 * 2
def baseEnd_3202555 : Nat := 365433341657738382785383

theorem tailTrace_3202555 : CollatzResearch.WordTrace tailWord_3202555 prefixEnd_3202555 365433341657738382785383 := by
  unfold tailWord_3202555
  simp only [CollatzResearch.WordTrace]
  refine ⟨116806776912697662693969119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77871184608465108462646079 116806776912697662693969119)
  ·
    refine ⟨175210165369046494040953679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116806776912697662693969119 175210165369046494040953679)
    ·
      refine ⟨262815248053569741061430519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175210165369046494040953679 262815248053569741061430519)
      ·
        refine ⟨394222872080354611592145779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262815248053569741061430519 394222872080354611592145779)
        ·
          refine ⟨591334308120531917388218669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394222872080354611592145779 591334308120531917388218669)
          ·
            refine ⟨221750365545199469020582001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 591334308120531917388218669 221750365545199469020582001)
            ·
              refine ⟨166312774158899601765436501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221750365545199469020582001 166312774158899601765436501)
              ·
                refine ⟨1948977822174604708188709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 166312774158899601765436501 1948977822174604708188709)
                ·
                  refine ⟨365433341657738382785383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1948977822174604708188709 365433341657738382785383)
                  ·
                    rfl

theorem cell22_3202555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 8, 4].length) (baseStart_3202555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3202555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3202555 prefixEnd_3202555 := by exact prefixLift 3202555
  have htrace : WordTrace (prefixWord ++ tailWord_3202555) baseStart_3202555 baseEnd_3202555 := by
    simpa [prefixWord, tailWord_3202555, baseEnd_3202555] using wordTrace_append hprefix tailTrace_3202555
  have hstable : (prefixWord ++ tailWord_3202555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202555).length < 2 ^ (prefixWord ++ tailWord_3202555).sum := by decide
  have hdescent : baseEnd_3202555 < baseStart_3202555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202570 : List Nat := [3, 1, 2, 2, 2, 2, 1, 3, 1, 5]
def baseStart_3202570 : Nat := 118140960795 + 3202570 * 2 ^ 59
def prefixEnd_3202570 : Nat := 4983230072969 + 3 ^ 40 * 3202570 * 2
def baseEnd_3202570 : Nat := 1096305159779760109231103

theorem tailTrace_3202570 : CollatzResearch.WordTrace tailWord_3202570 prefixEnd_3202570 1096305159779760109231103 := by
  unfold tailWord_3202570
  simp only [CollatzResearch.WordTrace]
  refine ⟨29201831001910830063941291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77871549338428880170510109 29201831001910830063941291)
  ·
    refine ⟨43802746502866245095911937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29201831001910830063941291 43802746502866245095911937)
    ·
      refine ⟨32852059877149683821933953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43802746502866245095911937 32852059877149683821933953)
      ·
        refine ⟨24639044907862262866450465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32852059877149683821933953 24639044907862262866450465)
        ·
          refine ⟨18479283680896697149837849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24639044907862262866450465 18479283680896697149837849)
          ·
            refine ⟨13859462760672522862378387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18479283680896697149837849 13859462760672522862378387)
            ·
              refine ⟨20789194141008784293567581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13859462760672522862378387 20789194141008784293567581)
              ·
                refine ⟨7795947802878294110087843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20789194141008784293567581 7795947802878294110087843)
                ·
                  refine ⟨11693921704317441165131765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7795947802878294110087843 11693921704317441165131765)
                  ·
                    refine ⟨1096305159779760109231103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11693921704317441165131765 1096305159779760109231103)
                    ·
                      rfl

theorem cell22_3202570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_3202570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3202570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3202570 prefixEnd_3202570 := by exact prefixLift 3202570
  have htrace : WordTrace (prefixWord ++ tailWord_3202570) baseStart_3202570 baseEnd_3202570 := by
    simpa [prefixWord, tailWord_3202570, baseEnd_3202570] using wordTrace_append hprefix tailTrace_3202570
  have hstable : (prefixWord ++ tailWord_3202570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202570).length < 2 ^ (prefixWord ++ tailWord_3202570).sum := by decide
  have hdescent : baseEnd_3202570 < baseStart_3202570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202621 : List Nat := [1, 4, 1, 3, 3, 1, 3, 1, 2, 3]
def baseStart_3202621 : Nat := 118140960795 + 3202621 * 2 ^ 59
def prefixEnd_3202621 : Nat := 4983230072969 + 3 ^ 40 * 3202621 * 2
def baseEnd_3202621 : Nat := 1096322618122012976205947

theorem tailTrace_3202621 : CollatzResearch.WordTrace tailWord_3202621 prefixEnd_3202621 1096322618122012976205947 := by
  unfold tailWord_3202621
  simp only [CollatzResearch.WordTrace]
  refine ⟨116809184130458555965871717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77872789420305703977247811 116809184130458555965871717)
  ·
    refine ⟨21901722024460979243600947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116809184130458555965871717 21901722024460979243600947)
    ·
      refine ⟨32852583036691468865401421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21901722024460979243600947 32852583036691468865401421)
      ·
        refine ⟨12319718638759300824525533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32852583036691468865401421 12319718638759300824525533)
        ·
          refine ⟨4619894489534737809197075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12319718638759300824525533 4619894489534737809197075)
          ·
            refine ⟨6929841734302106713795613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4619894489534737809197075 6929841734302106713795613)
            ·
              refine ⟨2598690650363290017673355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6929841734302106713795613 2598690650363290017673355)
              ·
                refine ⟨3898035975544935026510033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2598690650363290017673355 3898035975544935026510033)
                ·
                  refine ⟨2923526981658701269882525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3898035975544935026510033 2923526981658701269882525)
                  ·
                    refine ⟨1096322618122012976205947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2923526981658701269882525 1096322618122012976205947)
                    ·
                      rfl

theorem cell22_3202621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 2, 3].length) (baseStart_3202621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3202621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3202621 prefixEnd_3202621 := by exact prefixLift 3202621
  have htrace : WordTrace (prefixWord ++ tailWord_3202621) baseStart_3202621 baseEnd_3202621 := by
    simpa [prefixWord, tailWord_3202621, baseEnd_3202621] using wordTrace_append hprefix tailTrace_3202621
  have hstable : (prefixWord ++ tailWord_3202621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202621).length < 2 ^ (prefixWord ++ tailWord_3202621).sum := by decide
  have hdescent : baseEnd_3202621 < baseStart_3202621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202724 : List Nat := [2, 3, 1, 2, 2, 3, 1, 4, 4]
def baseStart_3202724 : Nat := 118140960795 + 3202724 * 2 ^ 59
def prefixEnd_3202724 : Nat := 4983230072969 + 3 ^ 40 * 3202724 * 2
def baseEnd_3202724 : Nat := 365452625708985013626877

theorem tailTrace_3202724 : CollatzResearch.WordTrace tailWord_3202724 prefixEnd_3202724 365452625708985013626877 := by
  unfold tailWord_3202724
  simp only [CollatzResearch.WordTrace]
  refine ⟨58406470424542702278435613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77875293899390269704580817 58406470424542702278435613)
  ·
    refine ⟨21902426409203513354413355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58406470424542702278435613 21902426409203513354413355)
    ·
      refine ⟨32853639613805270031620033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21902426409203513354413355 32853639613805270031620033)
      ·
        refine ⟨24640229710353952523715025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32853639613805270031620033 24640229710353952523715025)
        ·
          refine ⟨18480172282765464392786269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24640229710353952523715025 18480172282765464392786269)
          ·
            refine ⟨6930064606037049147294851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18480172282765464392786269 6930064606037049147294851)
            ·
              refine ⟨10395096909055573720942277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6930064606037049147294851 10395096909055573720942277)
              ·
                refine ⟨1949080670447920072676677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10395096909055573720942277 1949080670447920072676677)
                ·
                  refine ⟨365452625708985013626877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1949080670447920072676677 365452625708985013626877)
                  ·
                    rfl

theorem cell22_3202724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_3202724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3202724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3202724 prefixEnd_3202724 := by exact prefixLift 3202724
  have htrace : WordTrace (prefixWord ++ tailWord_3202724) baseStart_3202724 baseEnd_3202724 := by
    simpa [prefixWord, tailWord_3202724, baseEnd_3202724] using wordTrace_append hprefix tailTrace_3202724
  have hstable : (prefixWord ++ tailWord_3202724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202724).length < 2 ^ (prefixWord ++ tailWord_3202724).sum := by decide
  have hdescent : baseEnd_3202724 < baseStart_3202724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202752 : List Nat := [2, 1, 1, 2, 4, 1, 5, 6]
def baseStart_3202752 : Nat := 118140960795 + 3202752 * 2 ^ 59
def prefixEnd_3202752 : Nat := 4983230072969 + 3 ^ 40 * 3202752 * 2
def baseEnd_3202752 : Nat := 121818606899908033464505

theorem tailTrace_3202752 : CollatzResearch.WordTrace tailWord_3202752 prefixEnd_3202752 121818606899908033464505 := by
  unfold tailWord_3202752
  simp only [CollatzResearch.WordTrace]
  refine ⟨58406981046491982669445255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77875974728655976892593673 58406981046491982669445255)
  ·
    refine ⟨87610471569737974004167883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58406981046491982669445255 87610471569737974004167883)
    ·
      refine ⟨131415707354606961006251825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87610471569737974004167883 131415707354606961006251825)
      ·
        refine ⟨98561780515955220754688869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131415707354606961006251825 98561780515955220754688869)
        ·
          refine ⟨18480333846741603891504163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98561780515955220754688869 18480333846741603891504163)
          ·
            refine ⟨27720500770112405837256245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18480333846741603891504163 27720500770112405837256245)
            ·
              refine ⟨2598796947198038047242773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27720500770112405837256245 2598796947198038047242773)
              ·
                refine ⟨121818606899908033464505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2598796947198038047242773 121818606899908033464505)
                ·
                  rfl

theorem cell22_3202752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 6].length) (baseStart_3202752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3202752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3202752 prefixEnd_3202752 := by exact prefixLift 3202752
  have htrace : WordTrace (prefixWord ++ tailWord_3202752) baseStart_3202752 baseEnd_3202752 := by
    simpa [prefixWord, tailWord_3202752, baseEnd_3202752] using wordTrace_append hprefix tailTrace_3202752
  have hstable : (prefixWord ++ tailWord_3202752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202752).length < 2 ^ (prefixWord ++ tailWord_3202752).sum := by decide
  have hdescent : baseEnd_3202752 < baseStart_3202752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202758 : List Nat := [6, 1, 2, 1, 1, 1, 1, 5, 4]
def baseStart_3202758 : Nat := 118140960795 + 3202758 * 2 ^ 59
def prefixEnd_3202758 : Nat := 4983230072969 + 3 ^ 40 * 3202758 * 2
def baseEnd_3202758 : Nat := 365456505340596761843509

theorem tailTrace_3202758 : CollatzResearch.WordTrace tailWord_3202758 prefixEnd_3202758 365456505340596761843509 := by
  unfold tailWord_3202758
  simp only [CollatzResearch.WordTrace]
  refine ⟨3650443154092569636362779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 77876120620641485575739285 3650443154092569636362779)
  ·
    refine ⟨5475664731138854454544169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3650443154092569636362779 5475664731138854454544169)
    ·
      refine ⟨4106748548354140840908127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5475664731138854454544169 4106748548354140840908127)
      ·
        refine ⟨6160122822531211261362191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4106748548354140840908127 6160122822531211261362191)
        ·
          refine ⟨9240184233796816892043287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6160122822531211261362191 9240184233796816892043287)
          ·
            refine ⟨13860276350695225338064931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9240184233796816892043287 13860276350695225338064931)
            ·
              refine ⟨20790414526042838007097397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13860276350695225338064931 20790414526042838007097397)
              ·
                refine ⟨1949101361816516063165381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20790414526042838007097397 1949101361816516063165381)
                ·
                  refine ⟨365456505340596761843509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1949101361816516063165381 365456505340596761843509)
                  ·
                    rfl

theorem cell22_3202758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_3202758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3202758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3202758 prefixEnd_3202758 := by exact prefixLift 3202758
  have htrace : WordTrace (prefixWord ++ tailWord_3202758) baseStart_3202758 baseEnd_3202758 := by
    simpa [prefixWord, tailWord_3202758, baseEnd_3202758] using wordTrace_append hprefix tailTrace_3202758
  have hstable : (prefixWord ++ tailWord_3202758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202758).length < 2 ^ (prefixWord ++ tailWord_3202758).sum := by decide
  have hdescent : baseEnd_3202758 < baseStart_3202758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202822 : List Nat := [6, 2, 2, 1, 1, 1, 1, 2, 2, 4]
def baseStart_3202822 : Nat := 118140960795 + 3202822 * 2 ^ 59
def prefixEnd_3202822 : Nat := 4983230072969 + 3 ^ 40 * 3202822 * 2
def baseEnd_3202822 : Nat := 1096391424529715451930331

theorem tailTrace_3202822 : CollatzResearch.WordTrace tailWord_3202822 prefixEnd_3202822 1096391424529715451930331 := by
  unfold tailWord_3202822
  simp only [CollatzResearch.WordTrace]
  refine ⟨3650516100085323977935585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 77877676801820244862625813 3650516100085323977935585)
  ·
    refine ⟨2737887075063992983451689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3650516100085323977935585 2737887075063992983451689)
    ·
      refine ⟨2053415306297994737588767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2737887075063992983451689 2053415306297994737588767)
      ·
        refine ⟨3080122959446992106383151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2053415306297994737588767 3080122959446992106383151)
        ·
          refine ⟨4620184439170488159574727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3080122959446992106383151 4620184439170488159574727)
          ·
            refine ⟨6930276658755732239362091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4620184439170488159574727 6930276658755732239362091)
            ·
              refine ⟨10395414988133598359043137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6930276658755732239362091 10395414988133598359043137)
              ·
                refine ⟨7796561241100198769282353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10395414988133598359043137 7796561241100198769282353)
                ·
                  refine ⟨5847420930825149076961765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7796561241100198769282353 5847420930825149076961765)
                  ·
                    refine ⟨1096391424529715451930331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5847420930825149076961765 1096391424529715451930331)
                    ·
                      rfl

theorem cell22_3202822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_3202822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3202822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3202822 prefixEnd_3202822 := by exact prefixLift 3202822
  have htrace : WordTrace (prefixWord ++ tailWord_3202822) baseStart_3202822 baseEnd_3202822 := by
    simpa [prefixWord, tailWord_3202822, baseEnd_3202822] using wordTrace_append hprefix tailTrace_3202822
  have hstable : (prefixWord ++ tailWord_3202822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202822).length < 2 ^ (prefixWord ++ tailWord_3202822).sum := by decide
  have hdescent : baseEnd_3202822 < baseStart_3202822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202874 : List Nat := [3, 1, 1, 1, 5, 2, 1, 2, 1, 5]
def baseStart_3202874 : Nat := 118140960795 + 3202874 * 2 ^ 59
def prefixEnd_3202874 : Nat := 4983230072969 + 3 ^ 40 * 3202874 * 2
def baseEnd_3202874 : Nat := 1096409225192404649630171

theorem tailTrace_3202874 : CollatzResearch.WordTrace tailWord_3202874 prefixEnd_3202874 1096409225192404649630171 := by
  unfold tailWord_3202874
  simp only [CollatzResearch.WordTrace]
  refine ⟨29204602949635495043707919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77878941199027986783221117 29204602949635495043707919)
  ·
    refine ⟨43806904424453242565561879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29204602949635495043707919 43806904424453242565561879)
    ·
      refine ⟨65710356636679863848342819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43806904424453242565561879 65710356636679863848342819)
      ·
        refine ⟨98565534955019795772514229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65710356636679863848342819 98565534955019795772514229)
        ·
          refine ⟨9240518902033105853673209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98565534955019795772514229 9240518902033105853673209)
          ·
            refine ⟨6930389176524829390254907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9240518902033105853673209 6930389176524829390254907)
            ·
              refine ⟨10395583764787244085382361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6930389176524829390254907 10395583764787244085382361)
              ·
                refine ⟨7796687823590433064036771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10395583764787244085382361 7796687823590433064036771)
                ·
                  refine ⟨11695031735385649596055157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7796687823590433064036771 11695031735385649596055157)
                  ·
                    refine ⟨1096409225192404649630171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11695031735385649596055157 1096409225192404649630171)
                    ·
                      rfl

theorem cell22_3202874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_3202874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3202874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3202874 prefixEnd_3202874 := by exact prefixLift 3202874
  have htrace : WordTrace (prefixWord ++ tailWord_3202874) baseStart_3202874 baseEnd_3202874 := by
    simpa [prefixWord, tailWord_3202874, baseEnd_3202874] using wordTrace_append hprefix tailTrace_3202874
  have hstable : (prefixWord ++ tailWord_3202874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202874).length < 2 ^ (prefixWord ++ tailWord_3202874).sum := by decide
  have hdescent : baseEnd_3202874 < baseStart_3202874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202878 : List Nat := [4, 2, 1, 2, 2, 2, 3, 1, 1, 4]
def baseStart_3202878 : Nat := 118140960795 + 3202878 * 2 ^ 59
def prefixEnd_3202878 : Nat := 4983230072969 + 3 ^ 40 * 3202878 * 2
def baseEnd_3202878 : Nat := 1096410594474149972530159

theorem tailTrace_3202878 : CollatzResearch.WordTrace tailWord_3202878 prefixEnd_3202878 1096410594474149972530159 := by
  unfold tailWord_3202878
  simp only [CollatzResearch.WordTrace]
  refine ⟨14602319711315936107247161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77879038460351659238651525 14602319711315936107247161)
  ·
    refine ⟨10951739783486952080435371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14602319711315936107247161 10951739783486952080435371)
    ·
      refine ⟨16427609675230428120653057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10951739783486952080435371 16427609675230428120653057)
      ·
        refine ⟨12320707256422821090489793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16427609675230428120653057 12320707256422821090489793)
        ·
          refine ⟨9240530442317115817867345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12320707256422821090489793 9240530442317115817867345)
          ·
            refine ⟨6930397831737836863400509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9240530442317115817867345 6930397831737836863400509)
            ·
              refine ⟨2598899186901688823775191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6930397831737836863400509 2598899186901688823775191)
              ·
                refine ⟨3898348780352533235662787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2598899186901688823775191 3898348780352533235662787)
                ·
                  refine ⟨5847523170528799853494181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3898348780352533235662787 5847523170528799853494181)
                  ·
                    refine ⟨1096410594474149972530159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5847523170528799853494181 1096410594474149972530159)
                    ·
                      rfl

theorem cell22_3202878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_3202878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3202878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3202878 prefixEnd_3202878 := by exact prefixLift 3202878
  have htrace : WordTrace (prefixWord ++ tailWord_3202878) baseStart_3202878 baseEnd_3202878 := by
    simpa [prefixWord, tailWord_3202878, baseEnd_3202878] using wordTrace_append hprefix tailTrace_3202878
  have hstable : (prefixWord ++ tailWord_3202878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202878).length < 2 ^ (prefixWord ++ tailWord_3202878).sum := by decide
  have hdescent : baseEnd_3202878 < baseStart_3202878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202893 : List Nat := [1, 6, 1, 2, 1, 2, 1, 4, 4]
def baseStart_3202893 : Nat := 118140960795 + 3202893 * 2 ^ 59
def prefixEnd_3202893 : Nat := 4983230072969 + 3 ^ 40 * 3202893 * 2
def baseEnd_3202893 : Nat := 365471909760231644468371

theorem tailTrace_3202893 : CollatzResearch.WordTrace tailWord_3202893 prefixEnd_3202893 365471909760231644468371 := by
  unfold tailWord_3202893
  simp only [CollatzResearch.WordTrace]
  refine ⟨116819104785473146419773333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77879403190315430946515555 116819104785473146419773333)
  ·
    refine ⟨5475895536819053738426875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 116819104785473146419773333 5475895536819053738426875)
    ·
      refine ⟨8213843305228580607640313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5475895536819053738426875 8213843305228580607640313)
      ·
        refine ⟨6160382478921435455730235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8213843305228580607640313 6160382478921435455730235)
        ·
          refine ⟨9240573718382153183595353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6160382478921435455730235 9240573718382153183595353)
          ·
            refine ⟨6930430288786614887696515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9240573718382153183595353 6930430288786614887696515)
            ·
              refine ⟨10395645433179922331544773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6930430288786614887696515 10395645433179922331544773)
              ·
                refine ⟨1949183518721235437164645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10395645433179922331544773 1949183518721235437164645)
                ·
                  refine ⟨365471909760231644468371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1949183518721235437164645 365471909760231644468371)
                  ·
                    rfl

theorem cell22_3202893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_3202893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3202893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3202893 prefixEnd_3202893 := by exact prefixLift 3202893
  have htrace : WordTrace (prefixWord ++ tailWord_3202893) baseStart_3202893 baseEnd_3202893 := by
    simpa [prefixWord, tailWord_3202893, baseEnd_3202893] using wordTrace_append hprefix tailTrace_3202893
  have hstable : (prefixWord ++ tailWord_3202893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202893).length < 2 ^ (prefixWord ++ tailWord_3202893).sum := by decide
  have hdescent : baseEnd_3202893 < baseStart_3202893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3202917 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 4, 6]
def baseStart_3202917 : Nat := 118140960795 + 3202917 * 2 ^ 59
def prefixEnd_3202917 : Nat := 4983230072969 + 3 ^ 40 * 3202917 * 2
def baseEnd_3202917 : Nat := 1096423944971166870805039

theorem tailTrace_3202917 : CollatzResearch.WordTrace tailWord_3202917 prefixEnd_3202917 1096423944971166870805039 := by
  unfold tailWord_3202917
  simp only [CollatzResearch.WordTrace]
  refine ⟨116819980137386198518647005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77879986758257465679098003 116819980137386198518647005)
  ·
    refine ⟨43807492551519824444492627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116819980137386198518647005 43807492551519824444492627)
    ·
      refine ⟨65711238827279736666738941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43807492551519824444492627 65711238827279736666738941)
      ·
        refine ⟨24641714560229901250027103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65711238827279736666738941 24641714560229901250027103)
        ·
          refine ⟨36962571840344851875040655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24641714560229901250027103 36962571840344851875040655)
          ·
            refine ⟨55443857760517277812560983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36962571840344851875040655 55443857760517277812560983)
            ·
              refine ⟨83165786640775916718841475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55443857760517277812560983 83165786640775916718841475)
              ·
                refine ⟨124748679961163875078262213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83165786640775916718841475 124748679961163875078262213)
                ·
                  refine ⟨23390377492718226577174165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124748679961163875078262213 23390377492718226577174165)
                  ·
                    refine ⟨1096423944971166870805039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23390377492718226577174165 1096423944971166870805039)
                    ·
                      rfl

theorem cell22_3202917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_3202917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3202917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3202917 prefixEnd_3202917 := by exact prefixLift 3202917
  have htrace : WordTrace (prefixWord ++ tailWord_3202917) baseStart_3202917 baseEnd_3202917 := by
    simpa [prefixWord, tailWord_3202917, baseEnd_3202917] using wordTrace_append hprefix tailTrace_3202917
  have hstable : (prefixWord ++ tailWord_3202917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3202917).length < 2 ^ (prefixWord ++ tailWord_3202917).sum := by decide
  have hdescent : baseEnd_3202917 < baseStart_3202917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3202917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203039 : List Nat := [1, 1, 2, 3, 4, 1, 2, 8]
def baseStart_3203039 : Nat := 118140960795 + 3203039 * 2 ^ 59
def prefixEnd_3203039 : Nat := 4983230072969 + 3 ^ 40 * 3203039 * 2
def baseEnd_3203039 : Nat := 121829523118266579917185

theorem tailTrace_3203039 : CollatzResearch.WordTrace tailWord_3203039 prefixEnd_3203039 121829523118266579917185 := by
  unfold tailWord_3203039
  simp only [CollatzResearch.WordTrace]
  refine ⟨116824429842944213354588171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77882953228629475569725447 116824429842944213354588171)
  ·
    refine ⟨175236644764416320031882257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116824429842944213354588171 175236644764416320031882257)
    ·
      refine ⟨131427483573312240023911693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175236644764416320031882257 131427483573312240023911693)
      ·
        refine ⟨49285306339992090008966885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131427483573312240023911693 49285306339992090008966885)
        ·
          refine ⟨9240994938748516876681291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49285306339992090008966885 9240994938748516876681291)
          ·
            refine ⟨13861492408122775315021937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9240994938748516876681291 13861492408122775315021937)
            ·
              refine ⟨10396119306092081486266453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13861492408122775315021937 10396119306092081486266453)
              ·
                refine ⟨121829523118266579917185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10396119306092081486266453 121829523118266579917185)
                ·
                  rfl

theorem cell22_3203039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 8].length) (baseStart_3203039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3203039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3203039 prefixEnd_3203039 := by exact prefixLift 3203039
  have htrace : WordTrace (prefixWord ++ tailWord_3203039) baseStart_3203039 baseEnd_3203039 := by
    simpa [prefixWord, tailWord_3203039, baseEnd_3203039] using wordTrace_append hprefix tailTrace_3203039
  have hstable : (prefixWord ++ tailWord_3203039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203039).length < 2 ^ (prefixWord ++ tailWord_3203039).sum := by decide
  have hdescent : baseEnd_3203039 < baseStart_3203039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203062 : List Nat := [5, 1, 1, 1, 4, 2, 2, 2, 4]
def baseStart_3203062 : Nat := 118140960795 + 3203062 * 2 ^ 59
def prefixEnd_3203062 : Nat := 4983230072969 + 3 ^ 40 * 3203062 * 2
def baseEnd_3203062 : Nat := 365491193811478275309865

theorem tailTrace_3203062 : CollatzResearch.WordTrace tailWord_3203062 prefixEnd_3203062 365491193811478275309865 := by
  unfold tailWord_3203062
  simp only [CollatzResearch.WordTrace]
  refine ⟨7301579295116305517667215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77883512481240592188450293 7301579295116305517667215)
  ·
    refine ⟨10952368942674458276500823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7301579295116305517667215 10952368942674458276500823)
    ·
      refine ⟨16428553414011687414751235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10952368942674458276500823 16428553414011687414751235)
      ·
        refine ⟨24642830121017531122126853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16428553414011687414751235 24642830121017531122126853)
        ·
          refine ⟨4620530647690787085398785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24642830121017531122126853 4620530647690787085398785)
          ·
            refine ⟨3465397985768090314049089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4620530647690787085398785 3465397985768090314049089)
            ·
              refine ⟨2599048489326067735536817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3465397985768090314049089 2599048489326067735536817)
              ·
                refine ⟨1949286366994550801652613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2599048489326067735536817 1949286366994550801652613)
                ·
                  refine ⟨365491193811478275309865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1949286366994550801652613 365491193811478275309865)
                  ·
                    rfl

theorem cell22_3203062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_3203062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3203062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3203062 prefixEnd_3203062 := by exact prefixLift 3203062
  have htrace : WordTrace (prefixWord ++ tailWord_3203062) baseStart_3203062 baseEnd_3203062 := by
    simpa [prefixWord, tailWord_3203062, baseEnd_3203062] using wordTrace_append hprefix tailTrace_3203062
  have hstable : (prefixWord ++ tailWord_3203062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203062).length < 2 ^ (prefixWord ++ tailWord_3203062).sum := by decide
  have hdescent : baseEnd_3203062 < baseStart_3203062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203069 : List Nat := [1, 4, 1, 1, 1, 2, 3, 1, 2, 6]
def baseStart_3203069 : Nat := 118140960795 + 3203069 * 2 ^ 59
def prefixEnd_3203069 : Nat := 4983230072969 + 3 ^ 40 * 3203069 * 2
def baseEnd_3203069 : Nat := 1096475977677489141004573

theorem tailTrace_3203069 : CollatzResearch.WordTrace tailWord_3203069 prefixEnd_3203069 1096475977677489141004573 := by
  unfold tailWord_3203069
  simp only [CollatzResearch.WordTrace]
  refine ⟨116825524032835528478180261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77883682688557018985453507 116825524032835528478180261)
  ·
    refine ⟨21904785756156661589658799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116825524032835528478180261 21904785756156661589658799)
    ·
      refine ⟨32857178634234992384488199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21904785756156661589658799 32857178634234992384488199)
      ·
        refine ⟨49285767951352488576732299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32857178634234992384488199 49285767951352488576732299)
        ·
          refine ⟨73928651927028732865098449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49285767951352488576732299 73928651927028732865098449)
          ·
            refine ⟨55446488945271549648823837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73928651927028732865098449 55446488945271549648823837)
            ·
              refine ⟨20792433354476831118308939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55446488945271549648823837 20792433354476831118308939)
              ·
                refine ⟨31188650031715246677463409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20792433354476831118308939 31188650031715246677463409)
                ·
                  refine ⟨23391487523786435008097557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31188650031715246677463409 23391487523786435008097557)
                  ·
                    refine ⟨1096475977677489141004573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23391487523786435008097557 1096475977677489141004573)
                    ·
                      rfl

theorem cell22_3203069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_3203069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3203069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3203069 prefixEnd_3203069 := by exact prefixLift 3203069
  have htrace : WordTrace (prefixWord ++ tailWord_3203069) baseStart_3203069 baseEnd_3203069 := by
    simpa [prefixWord, tailWord_3203069, baseEnd_3203069] using wordTrace_append hprefix tailTrace_3203069
  have hstable : (prefixWord ++ tailWord_3203069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203069).length < 2 ^ (prefixWord ++ tailWord_3203069).sum := by decide
  have hdescent : baseEnd_3203069 < baseStart_3203069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203092 : List Nat := [2, 4, 3, 2, 1, 2, 1, 1, 2, 4]
def baseStart_3203092 : Nat := 118140960795 + 3203092 * 2 ^ 59
def prefixEnd_3203092 : Nat := 4983230072969 + 3 ^ 40 * 3203092 * 2
def baseEnd_3203092 : Nat := 1096483851047524747679503

theorem tailTrace_3203092 : CollatzResearch.WordTrace tailWord_3203092 prefixEnd_3203092 1096483851047524747679503 := by
  unfold tailWord_3203092
  simp only [CollatzResearch.WordTrace]
  refine ⟨58413181455876101703133765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77884241941168135604178353 58413181455876101703133765)
  ·
    refine ⟨10952471522976769069337581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58413181455876101703133765 10952471522976769069337581)
    ·
      refine ⟨4107176821116288401001593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10952471522976769069337581 4107176821116288401001593)
      ·
        refine ⟨3080382615837216300751195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4107176821116288401001593 3080382615837216300751195)
        ·
          refine ⟨4620573923755824451126793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3080382615837216300751195 4620573923755824451126793)
          ·
            refine ⟨3465430442816868338345095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4620573923755824451126793 3465430442816868338345095)
            ·
              refine ⟨5198145664225302507517643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3465430442816868338345095 5198145664225302507517643)
              ·
                refine ⟨7797218496337953761276465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5198145664225302507517643 7797218496337953761276465)
                ·
                  refine ⟨5847913872253465320957349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7797218496337953761276465 5847913872253465320957349)
                  ·
                    refine ⟨1096483851047524747679503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5847913872253465320957349 1096483851047524747679503)
                    ·
                      rfl

theorem cell22_3203092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_3203092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3203092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3203092 prefixEnd_3203092 := by exact prefixLift 3203092
  have htrace : WordTrace (prefixWord ++ tailWord_3203092) baseStart_3203092 baseEnd_3203092 := by
    simpa [prefixWord, tailWord_3203092, baseEnd_3203092] using wordTrace_append hprefix tailTrace_3203092
  have hstable : (prefixWord ++ tailWord_3203092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203092).length < 2 ^ (prefixWord ++ tailWord_3203092).sum := by decide
  have hdescent : baseEnd_3203092 < baseStart_3203092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203118 : List Nat := [4, 1, 3, 1, 1, 2, 3, 2, 5]
def baseStart_3203118 : Nat := 118140960795 + 3203118 * 2 ^ 59
def prefixEnd_3203118 : Nat := 4983230072969 + 3 ^ 40 * 3203118 * 2
def baseEnd_3203118 : Nat := 365497583792956448843141

theorem tailTrace_3203118 : CollatzResearch.WordTrace tailWord_3203118 prefixEnd_3203118 365497583792956448843141 := by
  unfold tailWord_3203118
  simp only [CollatzResearch.WordTrace]
  refine ⟨14603413901207251230839251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77884874139772006564476005 14603413901207251230839251)
  ·
    refine ⟨21905120851810876846258877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14603413901207251230839251 21905120851810876846258877)
    ·
      refine ⟨8214420319429078817347079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21905120851810876846258877 8214420319429078817347079)
      ·
        refine ⟨12321630479143618226020619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8214420319429078817347079 12321630479143618226020619)
        ·
          refine ⟨18482445718715427339030929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12321630479143618226020619 18482445718715427339030929)
          ·
            refine ⟨13861834289036570504273197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18482445718715427339030929 13861834289036570504273197)
            ·
              refine ⟨5198187858388713939102449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13861834289036570504273197 5198187858388713939102449)
              ·
                refine ⟨3898640893791535454326837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5198187858388713939102449 3898640893791535454326837)
                ·
                  refine ⟨365497583792956448843141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3898640893791535454326837 365497583792956448843141)
                  ·
                    rfl

theorem cell22_3203118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_3203118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3203118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3203118 prefixEnd_3203118 := by exact prefixLift 3203118
  have htrace : WordTrace (prefixWord ++ tailWord_3203118) baseStart_3203118 baseEnd_3203118 := by
    simpa [prefixWord, tailWord_3203118, baseEnd_3203118] using wordTrace_append hprefix tailTrace_3203118
  have hstable : (prefixWord ++ tailWord_3203118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203118).length < 2 ^ (prefixWord ++ tailWord_3203118).sum := by decide
  have hdescent : baseEnd_3203118 < baseStart_3203118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203161 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 6, 3]
def baseStart_3203161 : Nat := 118140960795 + 3203161 * 2 ^ 59
def prefixEnd_3203161 : Nat := 4983230072969 + 3 ^ 40 * 3203161 * 2
def baseEnd_3203161 : Nat := 1096507471157631567704291

theorem tailTrace_3203161 : CollatzResearch.WordTrace tailWord_3203161 prefixEnd_3203161 1096507471157631567704291 := by
  unfold tailWord_3203161
  simp only [CollatzResearch.WordTrace]
  refine ⟨116828879548502228190529337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77885919699001485460352891 116828879548502228190529337)
  ·
    refine ⟨87621659661376671142897003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116828879548502228190529337 87621659661376671142897003)
    ·
      refine ⟨131432489492065006714345505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87621659661376671142897003 131432489492065006714345505)
      ·
        refine ⟨98574367119048755035759129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131432489492065006714345505 98574367119048755035759129)
        ·
          refine ⟨73930775339286566276819347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98574367119048755035759129 73930775339286566276819347)
          ·
            refine ⟨110896163008929849415229021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73930775339286566276819347 110896163008929849415229021)
            ·
              refine ⟨41586061128348693530710883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110896163008929849415229021 41586061128348693530710883)
              ·
                refine ⟨62379091692523040296066325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41586061128348693530710883 62379091692523040296066325)
                ·
                  refine ⟨2924019923087017513878109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62379091692523040296066325 2924019923087017513878109)
                  ·
                    refine ⟨1096507471157631567704291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2924019923087017513878109 1096507471157631567704291)
                    ·
                      rfl

theorem cell22_3203161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 6, 3].length) (baseStart_3203161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3203161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3203161 prefixEnd_3203161 := by exact prefixLift 3203161
  have htrace : WordTrace (prefixWord ++ tailWord_3203161) baseStart_3203161 baseEnd_3203161 := by
    simpa [prefixWord, tailWord_3203161, baseEnd_3203161] using wordTrace_append hprefix tailTrace_3203161
  have hstable : (prefixWord ++ tailWord_3203161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203161).length < 2 ^ (prefixWord ++ tailWord_3203161).sum := by decide
  have hdescent : baseEnd_3203161 < baseStart_3203161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203165 : List Nat := [1, 4, 4, 1, 1, 1, 2, 3, 1, 4]
def baseStart_3203165 : Nat := 118140960795 + 3203165 * 2 ^ 59
def prefixEnd_3203165 : Nat := 4983230072969 + 3 ^ 40 * 3203165 * 2
def baseEnd_3203165 : Nat := 1096508840439376890604279

theorem tailTrace_3203165 : CollatzResearch.WordTrace tailWord_3203165 prefixEnd_3203165 1096508840439376890604279 := by
  unfold tailWord_3203165
  simp only [CollatzResearch.WordTrace]
  refine ⟨116829025440487736873674949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77886016960325157915783299 116829025440487736873674949)
  ·
    refine ⟨21905442270091450663814053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116829025440487736873674949 21905442270091450663814053)
    ·
      refine ⟨4107270425642146999465135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21905442270091450663814053 4107270425642146999465135)
      ·
        refine ⟨6160905638463220499197703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4107270425642146999465135 6160905638463220499197703)
        ·
          refine ⟨9241358457694830748796555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6160905638463220499197703 9241358457694830748796555)
          ·
            refine ⟨13862037686542246123194833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9241358457694830748796555 13862037686542246123194833)
            ·
              refine ⟨10396528264906684592396125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13862037686542246123194833 10396528264906684592396125)
              ·
                refine ⟨3898698099340006722148547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10396528264906684592396125 3898698099340006722148547)
                ·
                  refine ⟨5848047149010010083222821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3898698099340006722148547 5848047149010010083222821)
                  ·
                    refine ⟨1096508840439376890604279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5848047149010010083222821 1096508840439376890604279)
                    ·
                      rfl

theorem cell22_3203165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_3203165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3203165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3203165 prefixEnd_3203165 := by exact prefixLift 3203165
  have htrace : WordTrace (prefixWord ++ tailWord_3203165) baseStart_3203165 baseEnd_3203165 := by
    simpa [prefixWord, tailWord_3203165, baseEnd_3203165] using wordTrace_append hprefix tailTrace_3203165
  have hstable : (prefixWord ++ tailWord_3203165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203165).length < 2 ^ (prefixWord ++ tailWord_3203165).sum := by decide
  have hdescent : baseEnd_3203165 < baseStart_3203165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203180 : List Nat := [2, 2, 1, 1, 3, 4, 3, 2, 4]
def baseStart_3203180 : Nat := 118140960795 + 3203180 * 2 ^ 59
def prefixEnd_3203180 : Nat := 4983230072969 + 3 ^ 40 * 3203180 * 2
def baseEnd_3203180 : Nat := 365504658415307283826411

theorem tailTrace_3203180 : CollatzResearch.WordTrace tailWord_3203180 prefixEnd_3203180 365504658415307283826411 := by
  unfold tailWord_3203180
  simp only [CollatzResearch.WordTrace]
  refine ⟨58414786267716697217735497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77886381690288929623647329 58414786267716697217735497)
  ·
    refine ⟨43811089700787522913301623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58414786267716697217735497 43811089700787522913301623)
    ·
      refine ⟨65716634551181284369952435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43811089700787522913301623 65716634551181284369952435)
      ·
        refine ⟨98574951826771926554928653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65716634551181284369952435 98574951826771926554928653)
        ·
          refine ⟨36965606935039472458098245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98574951826771926554928653 36965606935039472458098245)
          ·
            refine ⟨6931051300319901085893421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36965606935039472458098245 6931051300319901085893421)
            ·
              refine ⟨2599144237619962907210033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6931051300319901085893421 2599144237619962907210033)
              ·
                refine ⟨1949358178214972180407525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2599144237619962907210033 1949358178214972180407525)
                ·
                  refine ⟨365504658415307283826411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1949358178214972180407525 365504658415307283826411)
                  ·
                    rfl

theorem cell22_3203180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 2, 4].length) (baseStart_3203180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3203180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3203180 prefixEnd_3203180 := by exact prefixLift 3203180
  have htrace : WordTrace (prefixWord ++ tailWord_3203180) baseStart_3203180 baseEnd_3203180 := by
    simpa [prefixWord, tailWord_3203180, baseEnd_3203180] using wordTrace_append hprefix tailTrace_3203180
  have hstable : (prefixWord ++ tailWord_3203180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203180).length < 2 ^ (prefixWord ++ tailWord_3203180).sum := by decide
  have hdescent : baseEnd_3203180 < baseStart_3203180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203191 : List Nat := [1, 1, 3, 1, 1, 6, 2, 7]
def baseStart_3203191 : Nat := 118140960795 + 3203191 * 2 ^ 59
def prefixEnd_3203191 : Nat := 4983230072969 + 3 ^ 40 * 3203191 * 2
def baseEnd_3203191 : Nat := 121835304530080165494911

theorem tailTrace_3203191 : CollatzResearch.WordTrace tailWord_3203191 prefixEnd_3203191 121835304530080165494911 := by
  unfold tailWord_3203191
  simp only [CollatzResearch.WordTrace]
  refine ⟨116829973738393543314121427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77886649158929028876080951 116829973738393543314121427)
  ·
    refine ⟨175244960607590314971182141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116829973738393543314121427 175244960607590314971182141)
    ·
      refine ⟨65716860227846368114193303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175244960607590314971182141 65716860227846368114193303)
      ·
        refine ⟨98575290341769552171289955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65716860227846368114193303 98575290341769552171289955)
        ·
          refine ⟨147862935512654328256934933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98575290341769552171289955 147862935512654328256934933)
          ·
            refine ⟨6931075102155671637043825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 147862935512654328256934933 6931075102155671637043825)
            ·
              refine ⟨5198306326616753727782869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6931075102155671637043825 5198306326616753727782869)
              ·
                refine ⟨121835304530080165494911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5198306326616753727782869 121835304530080165494911)
                ·
                  rfl

theorem cell22_3203191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 7].length) (baseStart_3203191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3203191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3203191 prefixEnd_3203191 := by exact prefixLift 3203191
  have htrace : WordTrace (prefixWord ++ tailWord_3203191) baseStart_3203191 baseEnd_3203191 := by
    simpa [prefixWord, tailWord_3203191, baseEnd_3203191] using wordTrace_append hprefix tailTrace_3203191
  have hstable : (prefixWord ++ tailWord_3203191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203191).length < 2 ^ (prefixWord ++ tailWord_3203191).sum := by decide
  have hdescent : baseEnd_3203191 < baseStart_3203191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203242 : List Nat := [3, 1, 5, 1, 3, 1, 1, 7]
def baseStart_3203242 : Nat := 118140960795 + 3203242 * 2 ^ 59
def prefixEnd_3203242 : Nat := 4983230072969 + 3 ^ 40 * 3203242 * 2
def baseEnd_3203242 : Nat := 121837244345886039603227

theorem tailTrace_3203242 : CollatzResearch.WordTrace tailWord_3203242 prefixEnd_3203242 121837244345886039603227 := by
  unfold tailWord_3203242
  simp only [CollatzResearch.WordTrace]
  refine ⟨29207958465302194756056995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77887889240805852682818653 29207958465302194756056995)
  ·
    refine ⟨43811937697953292134085493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29207958465302194756056995 43811937697953292134085493)
    ·
      refine ⟨4107369159183121137570515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43811937697953292134085493 4107369159183121137570515)
      ·
        refine ⟨6161053738774681706355773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4107369159183121137570515 6161053738774681706355773)
        ·
          refine ⟨2310395152040505639883415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6161053738774681706355773 2310395152040505639883415)
          ·
            refine ⟨3465592728060758459825123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2310395152040505639883415 3465592728060758459825123)
            ·
              refine ⟨5198389092091137689737685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3465592728060758459825123 5198389092091137689737685)
              ·
                refine ⟨121837244345886039603227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5198389092091137689737685 121837244345886039603227)
                ·
                  rfl

theorem cell22_3203242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 7].length) (baseStart_3203242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3203242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3203242 prefixEnd_3203242 := by exact prefixLift 3203242
  have htrace : WordTrace (prefixWord ++ tailWord_3203242) baseStart_3203242 baseEnd_3203242 := by
    simpa [prefixWord, tailWord_3203242, baseEnd_3203242] using wordTrace_append hprefix tailTrace_3203242
  have hstable : (prefixWord ++ tailWord_3203242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203242).length < 2 ^ (prefixWord ++ tailWord_3203242).sum := by decide
  have hdescent : baseEnd_3203242 < baseStart_3203242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203313 : List Nat := [1, 2, 2, 2, 2, 1, 5, 1, 1, 5]
def baseStart_3203313 : Nat := 118140960795 + 3203313 * 2 ^ 59
def prefixEnd_3203313 : Nat := 4983230072969 + 3 ^ 40 * 3203313 * 2
def baseEnd_3203313 : Nat := 1096559503863953837903825

theorem tailTrace_3203313 : CollatzResearch.WordTrace tailWord_3203313 prefixEnd_3203313 1096559503863953837903825 := by
  unfold tailWord_3203313
  simp only [CollatzResearch.WordTrace]
  refine ⟨116834423443951558150062593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77889615629301038766708395 116834423443951558150062593)
  ·
    refine ⟨87625817582963668612546945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116834423443951558150062593 87625817582963668612546945)
    ·
      refine ⟨65719363187222751459410209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87625817582963668612546945 65719363187222751459410209)
      ·
        refine ⟨49289522390417063594557657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65719363187222751459410209 49289522390417063594557657)
        ·
          refine ⟨36967141792812797695918243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49289522390417063594557657 36967141792812797695918243)
          ·
            refine ⟨55450712689219196543877365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36967141792812797695918243 55450712689219196543877365)
            ·
              refine ⟨5198504314614299675988503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55450712689219196543877365 5198504314614299675988503)
              ·
                refine ⟨7797756471921449513982755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5198504314614299675988503 7797756471921449513982755)
                ·
                  refine ⟨11696634707882174270974133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7797756471921449513982755 11696634707882174270974133)
                  ·
                    refine ⟨1096559503863953837903825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11696634707882174270974133 1096559503863953837903825)
                    ·
                      rfl

theorem cell22_3203313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 5].length) (baseStart_3203313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3203313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3203313 prefixEnd_3203313 := by exact prefixLift 3203313
  have htrace : WordTrace (prefixWord ++ tailWord_3203313) baseStart_3203313 baseEnd_3203313 := by
    simpa [prefixWord, tailWord_3203313, baseEnd_3203313] using wordTrace_append hprefix tailTrace_3203313
  have hstable : (prefixWord ++ tailWord_3203313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203313).length < 2 ^ (prefixWord ++ tailWord_3203313).sum := by decide
  have hdescent : baseEnd_3203313 < baseStart_3203313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203364 : List Nat := [2, 3, 1, 3, 1, 4, 2, 1, 2, 3]
def baseStart_3203364 : Nat := 118140960795 + 3203364 * 2 ^ 59
def prefixEnd_3203364 : Nat := 4983230072969 + 3 ^ 40 * 3203364 * 2
def baseEnd_3203364 : Nat := 1096576962206206704878669

theorem tailTrace_3203364 : CollatzResearch.WordTrace tailWord_3203364 prefixEnd_3203364 1096576962206206704878669 := by
  unfold tailWord_3203364
  simp only [CollatzResearch.WordTrace]
  refine ⟨58418141783383396930084573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77890855711177862573446097 58418141783383396930084573)
  ·
    refine ⟨21906803168768773848781715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58418141783383396930084573 21906803168768773848781715)
    ·
      refine ⟨32860204753153160773172573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21906803168768773848781715 32860204753153160773172573)
      ·
        refine ⟨12322576782432435289939715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32860204753153160773172573 12322576782432435289939715)
        ·
          refine ⟨18483865173648652934909573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12322576782432435289939715 18483865173648652934909573)
          ·
            refine ⟨3465724720059122425295545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18483865173648652934909573 3465724720059122425295545)
            ·
              refine ⟨2599293540044341818971659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3465724720059122425295545 2599293540044341818971659)
              ·
                refine ⟨3898940310066512728457489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2599293540044341818971659 3898940310066512728457489)
                ·
                  refine ⟨2924205232549884546343117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3898940310066512728457489 2924205232549884546343117)
                  ·
                    refine ⟨1096576962206206704878669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2924205232549884546343117 1096576962206206704878669)
                    ·
                      rfl

theorem cell22_3203364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 2, 3].length) (baseStart_3203364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3203364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3203364 prefixEnd_3203364 := by exact prefixLift 3203364
  have htrace : WordTrace (prefixWord ++ tailWord_3203364) baseStart_3203364 baseEnd_3203364 := by
    simpa [prefixWord, tailWord_3203364, baseEnd_3203364] using wordTrace_append hprefix tailTrace_3203364
  have hstable : (prefixWord ++ tailWord_3203364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203364).length < 2 ^ (prefixWord ++ tailWord_3203364).sum := by decide
  have hdescent : baseEnd_3203364 < baseStart_3203364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203409 : List Nat := [1, 2, 2, 1, 4, 2, 4, 2, 1, 3]
def baseStart_3203409 : Nat := 118140960795 + 3203409 * 2 ^ 59
def prefixEnd_3203409 : Nat := 4983230072969 + 3 ^ 40 * 3203409 * 2
def baseEnd_3203409 : Nat := 1096592366625841587503531

theorem tailTrace_3203409 : CollatzResearch.WordTrace tailWord_3203409 prefixEnd_3203409 1096592366625841587503531 := by
  unfold tailWord_3203409
  simp only [CollatzResearch.WordTrace]
  refine ⟨116837924851603766545557281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77891949901069177697038187 116837924851603766545557281)
  ·
    refine ⟨87628443638702824909167961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116837924851603766545557281 87628443638702824909167961)
    ·
      refine ⟨65721332729027118681875971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87628443638702824909167961 65721332729027118681875971)
      ·
        refine ⟨98581999093540678022813957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65721332729027118681875971 98581999093540678022813957)
        ·
          refine ⟨18484124830038877129277617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98581999093540678022813957 18484124830038877129277617)
          ·
            refine ⟨13863093622529157846958213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18484124830038877129277617 13863093622529157846958213)
            ·
              refine ⟨2599330054224217096304665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13863093622529157846958213 2599330054224217096304665)
              ·
                refine ⟨1949497540668162822228499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2599330054224217096304665 1949497540668162822228499)
                ·
                  refine ⟨2924246311002244233342749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1949497540668162822228499 2924246311002244233342749)
                  ·
                    refine ⟨1096592366625841587503531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2924246311002244233342749 1096592366625841587503531)
                    ·
                      rfl

theorem cell22_3203409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 2, 1, 3].length) (baseStart_3203409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3203409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3203409 prefixEnd_3203409 := by exact prefixLift 3203409
  have htrace : WordTrace (prefixWord ++ tailWord_3203409) baseStart_3203409 baseEnd_3203409 := by
    simpa [prefixWord, tailWord_3203409, baseEnd_3203409] using wordTrace_append hprefix tailTrace_3203409
  have hstable : (prefixWord ++ tailWord_3203409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203409).length < 2 ^ (prefixWord ++ tailWord_3203409).sum := by decide
  have hdescent : baseEnd_3203409 < baseStart_3203409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203433 : List Nat := [1, 2, 1, 1, 1, 3, 5, 2, 6]
def baseStart_3203433 : Nat := 118140960795 + 3203433 * 2 ^ 59
def prefixEnd_3203433 : Nat := 4983230072969 + 3 ^ 40 * 3203433 * 2
def baseEnd_3203433 : Nat := 365533527438771174967819

theorem tailTrace_3203433 : CollatzResearch.WordTrace tailWord_3203433 prefixEnd_3203433 365533527438771174967819 := by
  unfold tailWord_3203433
  simp only [CollatzResearch.WordTrace]
  refine ⟨116838800203516818644430953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77892533469011212429620635 116838800203516818644430953)
  ·
    refine ⟨87629100152637613983323215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116838800203516818644430953 87629100152637613983323215)
    ·
      refine ⟨131443650228956420974984823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87629100152637613983323215 131443650228956420974984823)
      ·
        refine ⟨197165475343434631462477235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131443650228956420974984823 197165475343434631462477235)
        ·
          refine ⟨295748213015151947193715853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197165475343434631462477235 295748213015151947193715853)
          ·
            refine ⟨110905579880681980197643445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 295748213015151947193715853 110905579880681980197643445)
            ·
              refine ⟨10397398113813935643529073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110905579880681980197643445 10397398113813935643529073)
              ·
                refine ⟨7798048585360451732646805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10397398113813935643529073 7798048585360451732646805)
                ·
                  refine ⟨365533527438771174967819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7798048585360451732646805 365533527438771174967819)
                  ·
                    rfl

theorem cell22_3203433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 6].length) (baseStart_3203433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3203433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3203433 prefixEnd_3203433 := by exact prefixLift 3203433
  have htrace : WordTrace (prefixWord ++ tailWord_3203433) baseStart_3203433 baseEnd_3203433 := by
    simpa [prefixWord, tailWord_3203433, baseEnd_3203433] using wordTrace_append hprefix tailTrace_3203433
  have hstable : (prefixWord ++ tailWord_3203433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203433).length < 2 ^ (prefixWord ++ tailWord_3203433).sum := by decide
  have hdescent : baseEnd_3203433 < baseStart_3203433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203480 : List Nat := [2, 1, 2, 5, 1, 1, 1, 2, 1, 6]
def baseStart_3203480 : Nat := 118140960795 + 3203480 * 2 ^ 59
def prefixEnd_3203480 : Nat := 4983230072969 + 3 ^ 40 * 3203480 * 2
def baseEnd_3203480 : Nat := 1096616671376821068978313

theorem tailTrace_3203480 : CollatzResearch.WordTrace tailWord_3203480 prefixEnd_3203480 1096616671376821068978313 := by
  unfold tailWord_3203480
  simp only [CollatzResearch.WordTrace]
  refine ⟨58420257217173272835695947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77893676289564363780927929 58420257217173272835695947)
  ·
    refine ⟨87630385825759909253543921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58420257217173272835695947 87630385825759909253543921)
    ·
      refine ⟨65722789369319931940157941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87630385825759909253543921 65722789369319931940157941)
      ·
        refine ⟨6161511503373743619389807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65722789369319931940157941 6161511503373743619389807)
        ·
          refine ⟨9242267255060615429084711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6161511503373743619389807 9242267255060615429084711)
          ·
            refine ⟨13863400882590923143627067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9242267255060615429084711 13863400882590923143627067)
            ·
              refine ⟨20795101323886384715440601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13863400882590923143627067 20795101323886384715440601)
              ·
                refine ⟨15596325992914788536580451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20795101323886384715440601 15596325992914788536580451)
                ·
                  refine ⟨23394488989372182804870677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15596325992914788536580451 23394488989372182804870677)
                  ·
                    refine ⟨1096616671376821068978313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23394488989372182804870677 1096616671376821068978313)
                    ·
                      rfl

theorem cell22_3203480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_3203480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3203480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3203480 prefixEnd_3203480 := by exact prefixLift 3203480
  have htrace : WordTrace (prefixWord ++ tailWord_3203480) baseStart_3203480 baseEnd_3203480 := by
    simpa [prefixWord, tailWord_3203480, baseEnd_3203480] using wordTrace_append hprefix tailTrace_3203480
  have hstable : (prefixWord ++ tailWord_3203480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203480).length < 2 ^ (prefixWord ++ tailWord_3203480).sum := by decide
  have hdescent : baseEnd_3203480 < baseStart_3203480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203482 : List Nat := [3, 1, 1, 4, 1, 4, 1, 1, 1, 5]
def baseStart_3203482 : Nat := 118140960795 + 3203482 * 2 ^ 59
def prefixEnd_3203482 : Nat := 4983230072969 + 3 ^ 40 * 3203482 * 2
def baseEnd_3203482 : Nat := 1096617356017693730428307

theorem tailTrace_3203482 : CollatzResearch.WordTrace tailWord_3203482 prefixEnd_3203482 1096617356017693730428307 := by
  unfold tailWord_3203482
  simp only [CollatzResearch.WordTrace]
  refine ⟨29210146845084825003241175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77893724920226200008643133 29210146845084825003241175)
  ·
    refine ⟨43815220267627237504861763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29210146845084825003241175 43815220267627237504861763)
    ·
      refine ⟨65722830401440856257292645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43815220267627237504861763 65722830401440856257292645)
      ·
        refine ⟨12323030700270160548242371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65722830401440856257292645 12323030700270160548242371)
        ·
          refine ⟨18484546050405240822363557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12323030700270160548242371 18484546050405240822363557)
          ·
            refine ⟨3465852384450982654193167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18484546050405240822363557 3465852384450982654193167)
            ·
              refine ⟨5198778576676473981289751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3465852384450982654193167 5198778576676473981289751)
              ·
                refine ⟨7798167865014710971934627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5198778576676473981289751 7798167865014710971934627)
                ·
                  refine ⟨11697251797522066457901941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7798167865014710971934627 11697251797522066457901941)
                  ·
                    refine ⟨1096617356017693730428307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11697251797522066457901941 1096617356017693730428307)
                    ·
                      rfl

theorem cell22_3203482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 1, 5].length) (baseStart_3203482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3203482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3203482 prefixEnd_3203482 := by exact prefixLift 3203482
  have htrace : WordTrace (prefixWord ++ tailWord_3203482) baseStart_3203482 baseEnd_3203482 := by
    simpa [prefixWord, tailWord_3203482, baseEnd_3203482] using wordTrace_append hprefix tailTrace_3203482
  have hstable : (prefixWord ++ tailWord_3203482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203482).length < 2 ^ (prefixWord ++ tailWord_3203482).sum := by decide
  have hdescent : baseEnd_3203482 < baseStart_3203482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203493 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 2, 7]
def baseStart_3203493 : Nat := 118140960795 + 3203493 * 2 ^ 59
def prefixEnd_3203493 : Nat := 4983230072969 + 3 ^ 40 * 3203493 * 2
def baseEnd_3203493 : Nat := 1096621121542493368403273

theorem tailTrace_3203493 : CollatzResearch.WordTrace tailWord_3203493 prefixEnd_3203493 1096621121542493368403273 := by
  unfold tailWord_3203493
  simp only [CollatzResearch.WordTrace]
  refine ⟨116840988583299448891615133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77893992388866299261076755 116840988583299448891615133)
  ·
    refine ⟨43815370718737293334355675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116840988583299448891615133 43815370718737293334355675)
    ·
      refine ⟨65723056078105940001533513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43815370718737293334355675 65723056078105940001533513)
      ·
        refine ⟨49292292058579455001150135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65723056078105940001533513 49292292058579455001150135)
        ·
          refine ⟨73938438087869182501725203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49292292058579455001150135 73938438087869182501725203)
          ·
            refine ⟨110907657131803773752587805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73938438087869182501725203 110907657131803773752587805)
            ·
              refine ⟨41590371424426415157220427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110907657131803773752587805 41590371424426415157220427)
              ·
                refine ⟨62385557136639622735830641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41590371424426415157220427 62385557136639622735830641)
                ·
                  refine ⟨46789167852479717051872981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62385557136639622735830641 46789167852479717051872981)
                  ·
                    refine ⟨1096621121542493368403273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46789167852479717051872981 1096621121542493368403273)
                    ·
                      rfl

theorem cell22_3203493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_3203493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3203493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3203493 prefixEnd_3203493 := by exact prefixLift 3203493
  have htrace : WordTrace (prefixWord ++ tailWord_3203493) baseStart_3203493 baseEnd_3203493 := by
    simpa [prefixWord, tailWord_3203493, baseEnd_3203493] using wordTrace_append hprefix tailTrace_3203493
  have hstable : (prefixWord ++ tailWord_3203493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203493).length < 2 ^ (prefixWord ++ tailWord_3203493).sum := by decide
  have hdescent : baseEnd_3203493 < baseStart_3203493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203495 : List Nat := [1, 1, 6, 1, 1, 3, 1, 8]
def baseStart_3203495 : Nat := 118140960795 + 3203495 * 2 ^ 59
def prefixEnd_3203495 : Nat := 4983230072969 + 3 ^ 40 * 3203495 * 2
def baseEnd_3203495 : Nat := 121846867353707336650363

theorem tailTrace_3203495 : CollatzResearch.WordTrace tailWord_3203495 prefixEnd_3203495 121846867353707336650363 := by
  unfold tailWord_3203495
  simp only [CollatzResearch.WordTrace]
  refine ⟨116841061529292203233187939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77894041019528135488791959 116841061529292203233187939)
  ·
    refine ⟨175261592293938304849781909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116841061529292203233187939 175261592293938304849781909)
    ·
      refine ⟨8215387138778358039833527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 175261592293938304849781909 8215387138778358039833527)
      ·
        refine ⟨12323080708167537059750291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8215387138778358039833527 12323080708167537059750291)
        ·
          refine ⟨18484621062251305589625437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12323080708167537059750291 18484621062251305589625437)
          ·
            refine ⟨6931732898344239596109539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18484621062251305589625437 6931732898344239596109539)
            ·
              refine ⟨10397599347516359394164309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6931732898344239596109539 10397599347516359394164309)
              ·
                refine ⟨121846867353707336650363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10397599347516359394164309 121846867353707336650363)
                ·
                  rfl

theorem cell22_3203495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 8].length) (baseStart_3203495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3203495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3203495 prefixEnd_3203495 := by exact prefixLift 3203495
  have htrace : WordTrace (prefixWord ++ tailWord_3203495) baseStart_3203495 baseEnd_3203495 := by
    simpa [prefixWord, tailWord_3203495, baseEnd_3203495] using wordTrace_append hprefix tailTrace_3203495
  have hstable : (prefixWord ++ tailWord_3203495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203495).length < 2 ^ (prefixWord ++ tailWord_3203495).sum := by decide
  have hdescent : baseEnd_3203495 < baseStart_3203495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203501 : List Nat := [1, 5, 2, 2, 2, 2, 1, 3, 4]
def baseStart_3203501 : Nat := 118140960795 + 3203501 * 2 ^ 59
def prefixEnd_3203501 : Nat := 4983230072969 + 3 ^ 40 * 3203501 * 2
def baseEnd_3203501 : Nat := 365541286701994671401083

theorem tailTrace_3203501 : CollatzResearch.WordTrace tailWord_3203501 prefixEnd_3203501 365541286701994671401083 := by
  unfold tailWord_3203501
  simp only [CollatzResearch.WordTrace]
  refine ⟨116841280367270466257906357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77894186911513644171937571 116841280367270466257906357)
  ·
    refine ⟨10953870034431606211678721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116841280367270466257906357 10953870034431606211678721)
    ·
      refine ⟨8215402525823704658759041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10953870034431606211678721 8215402525823704658759041)
      ·
        refine ⟨6161551894367778494069281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8215402525823704658759041 6161551894367778494069281)
        ·
          refine ⟨4621163920775833870551961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6161551894367778494069281 4621163920775833870551961)
          ·
            refine ⟨3465872940581875402913971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4621163920775833870551961 3465872940581875402913971)
            ·
              refine ⟨5198809410872813104370957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3465872940581875402913971 5198809410872813104370957)
              ·
                refine ⟨1949553529077304914139109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5198809410872813104370957 1949553529077304914139109)
                ·
                  refine ⟨365541286701994671401083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1949553529077304914139109 365541286701994671401083)
                  ·
                    rfl

theorem cell22_3203501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_3203501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3203501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3203501 prefixEnd_3203501 := by exact prefixLift 3203501
  have htrace : WordTrace (prefixWord ++ tailWord_3203501) baseStart_3203501 baseEnd_3203501 := by
    simpa [prefixWord, tailWord_3203501, baseEnd_3203501] using wordTrace_append hprefix tailTrace_3203501
  have hstable : (prefixWord ++ tailWord_3203501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203501).length < 2 ^ (prefixWord ++ tailWord_3203501).sum := by decide
  have hdescent : baseEnd_3203501 < baseStart_3203501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203527 : List Nat := [1, 1, 4, 1, 1, 4, 3, 1, 3, 3]
def baseStart_3203527 : Nat := 118140960795 + 3203527 * 2 ^ 59
def prefixEnd_3203527 : Nat := 4983230072969 + 3 ^ 40 * 3203527 * 2
def baseEnd_3203527 : Nat := 1096632760437328613053169

theorem tailTrace_3203527 : CollatzResearch.WordTrace tailWord_3203527 prefixEnd_3203527 1096632760437328613053169 := by
  unfold tailWord_3203527
  simp only [CollatzResearch.WordTrace]
  refine ⟨116842228665176272698352835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77894819110117515132235223 116842228665176272698352835)
  ·
    refine ⟨175263342997764409047529253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116842228665176272698352835 175263342997764409047529253)
    ·
      refine ⟨32861876812080826696411735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175263342997764409047529253 32861876812080826696411735)
      ·
        refine ⟨49292815218121240044617603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32861876812080826696411735 49292815218121240044617603)
        ·
          refine ⟨73939222827181860066926405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49292815218121240044617603 73939222827181860066926405)
          ·
            refine ⟨13863604280096598762548701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73939222827181860066926405 13863604280096598762548701)
            ·
              refine ⟨5198851605036224535955763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13863604280096598762548701 5198851605036224535955763)
              ·
                refine ⟨7798277407554336803933645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5198851605036224535955763 7798277407554336803933645)
                ·
                  refine ⟨2924354027832876301475117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7798277407554336803933645 2924354027832876301475117)
                  ·
                    refine ⟨1096632760437328613053169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2924354027832876301475117 1096632760437328613053169)
                    ·
                      rfl

theorem cell22_3203527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_3203527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3203527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3203527 prefixEnd_3203527 := by exact prefixLift 3203527
  have htrace : WordTrace (prefixWord ++ tailWord_3203527) baseStart_3203527 baseEnd_3203527 := by
    simpa [prefixWord, tailWord_3203527, baseEnd_3203527] using wordTrace_append hprefix tailTrace_3203527
  have hstable : (prefixWord ++ tailWord_3203527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203527).length < 2 ^ (prefixWord ++ tailWord_3203527).sum := by decide
  have hdescent : baseEnd_3203527 < baseStart_3203527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203604 : List Nat := [2, 4, 3, 1, 1, 1, 2, 1, 3, 4]
def baseStart_3203604 : Nat := 118140960795 + 3203604 * 2 ^ 59
def prefixEnd_3203604 : Nat := 4983230072969 + 3 ^ 40 * 3203604 * 2
def baseEnd_3203604 : Nat := 1096659119110926078877933

theorem tailTrace_3203604 : CollatzResearch.WordTrace tailWord_3203604 prefixEnd_3203604 1096659119110926078877933 := by
  unfold tailWord_3203604
  simp only [CollatzResearch.WordTrace]
  refine ⟨58422518542948657424452933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77896691390598209899270577 58422518542948657424452933)
  ·
    refine ⟨10954222226802873267084925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58422518542948657424452933 10954222226802873267084925)
    ·
      refine ⟨4107833335051077475156847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10954222226802873267084925 4107833335051077475156847)
      ·
        refine ⟨6161750002576616212735271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4107833335051077475156847 6161750002576616212735271)
        ·
          refine ⟨9242625003864924319102907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6161750002576616212735271 9242625003864924319102907)
          ·
            refine ⟨13863937505797386478654361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9242625003864924319102907 13863937505797386478654361)
            ·
              refine ⟨10397953129348039858990771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13863937505797386478654361 10397953129348039858990771)
              ·
                refine ⟨15596929694022059788486157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10397953129348039858990771 15596929694022059788486157)
                ·
                  refine ⟨5848848635258272420682309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15596929694022059788486157 5848848635258272420682309)
                  ·
                    refine ⟨1096659119110926078877933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5848848635258272420682309 1096659119110926078877933)
                    ·
                      rfl

theorem cell22_3203604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_3203604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3203604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3203604 prefixEnd_3203604 := by exact prefixLift 3203604
  have htrace : WordTrace (prefixWord ++ tailWord_3203604) baseStart_3203604 baseEnd_3203604 := by
    simpa [prefixWord, tailWord_3203604, baseEnd_3203604] using wordTrace_append hprefix tailTrace_3203604
  have hstable : (prefixWord ++ tailWord_3203604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203604).length < 2 ^ (prefixWord ++ tailWord_3203604).sum := by decide
  have hdescent : baseEnd_3203604 < baseStart_3203604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203617 : List Nat := [1, 2, 3, 2, 2, 1, 2, 2, 4, 3]
def baseStart_3203617 : Nat := 118140960795 + 3203617 * 2 ^ 59
def prefixEnd_3203617 : Nat := 4983230072969 + 3 ^ 40 * 3203617 * 2
def baseEnd_3203617 : Nat := 1096663569276598378302893

theorem tailTrace_3203617 : CollatzResearch.WordTrace tailWord_3203617 prefixEnd_3203617 1096663569276598378302893 := by
  unfold tailWord_3203617
  simp only [CollatzResearch.WordTrace]
  refine ⟨116845511234850218069129105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77897007489900145379419403 116845511234850218069129105)
  ·
    refine ⟨87634133426137663551846829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116845511234850218069129105 87634133426137663551846829)
    ·
      refine ⟨32862800034801623831942561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87634133426137663551846829 32862800034801623831942561)
      ·
        refine ⟨24647100026101217873956921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32862800034801623831942561 24647100026101217873956921)
        ·
          refine ⟨18485325019575913405467691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24647100026101217873956921 18485325019575913405467691)
          ·
            refine ⟨27727987529363870108201537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18485325019575913405467691 27727987529363870108201537)
            ·
              refine ⟨20795990647022902581151153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27727987529363870108201537 20795990647022902581151153)
              ·
                refine ⟨15596992985267176935863365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20795990647022902581151153 15596992985267176935863365)
                ·
                  refine ⟨2924436184737595675474381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15596992985267176935863365 2924436184737595675474381)
                  ·
                    refine ⟨1096663569276598378302893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2924436184737595675474381 1096663569276598378302893)
                    ·
                      rfl

theorem cell22_3203617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_3203617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3203617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3203617 prefixEnd_3203617 := by exact prefixLift 3203617
  have htrace : WordTrace (prefixWord ++ tailWord_3203617) baseStart_3203617 baseEnd_3203617 := by
    simpa [prefixWord, tailWord_3203617, baseEnd_3203617] using wordTrace_append hprefix tailTrace_3203617
  have hstable : (prefixWord ++ tailWord_3203617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203617).length < 2 ^ (prefixWord ++ tailWord_3203617).sum := by decide
  have hdescent : baseEnd_3203617 < baseStart_3203617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203619 : List Nat := [1, 1, 1, 4, 4, 2, 2, 3, 4]
def baseStart_3203619 : Nat := 118140960795 + 3203619 * 2 ^ 59
def prefixEnd_3203619 : Nat := 4983230072969 + 3 ^ 40 * 3203619 * 2
def baseEnd_3203619 : Nat := 365554751305823679917629

theorem tailTrace_3203619 : CollatzResearch.WordTrace tailWord_3203619 prefixEnd_3203619 365554751305823679917629 := by
  unfold tailWord_3203619
  simp only [CollatzResearch.WordTrace]
  refine ⟨116845584180842972410701911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77897056120561981607134607 116845584180842972410701911)
  ·
    refine ⟨175268376271264458616052867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116845584180842972410701911 175268376271264458616052867)
    ·
      refine ⟨262902564406896687924079301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175268376271264458616052867 262902564406896687924079301)
      ·
        refine ⟨49294230826293128985764869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 262902564406896687924079301 49294230826293128985764869)
        ·
          refine ⟨9242668279929961684830913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49294230826293128985764869 9242668279929961684830913)
          ·
            refine ⟨6932001209947471263623185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9242668279929961684830913 6932001209947471263623185)
            ·
              refine ⟨5199000907460603447717389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6932001209947471263623185 5199000907460603447717389)
              ·
                refine ⟨1949625340297726292894021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5199000907460603447717389 1949625340297726292894021)
                ·
                  refine ⟨365554751305823679917629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1949625340297726292894021 365554751305823679917629)
                  ·
                    rfl

theorem cell22_3203619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 3, 4].length) (baseStart_3203619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3203619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3203619 prefixEnd_3203619 := by exact prefixLift 3203619
  have htrace : WordTrace (prefixWord ++ tailWord_3203619) baseStart_3203619 baseEnd_3203619 := by
    simpa [prefixWord, tailWord_3203619, baseEnd_3203619] using wordTrace_append hprefix tailTrace_3203619
  have hstable : (prefixWord ++ tailWord_3203619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203619).length < 2 ^ (prefixWord ++ tailWord_3203619).sum := by decide
  have hdescent : baseEnd_3203619 < baseStart_3203619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203634 : List Nat := [3, 2, 1, 1, 2, 1, 5, 2, 2, 3]
def baseStart_3203634 : Nat := 118140960795 + 3203634 * 2 ^ 59
def prefixEnd_3203634 : Nat := 4983230072969 + 3 ^ 40 * 3203634 * 2
def baseEnd_3203634 : Nat := 1096669388724016000627841

theorem tailTrace_3203634 : CollatzResearch.WordTrace tailWord_3203634 prefixEnd_3203634 1096669388724016000627841 := by
  unfold tailWord_3203634
  simp only [CollatzResearch.WordTrace]
  refine ⟨29211532818947157493124489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77897420850525753314998637 29211532818947157493124489)
  ·
    refine ⟨21908649614210368119843367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29211532818947157493124489 21908649614210368119843367)
    ·
      refine ⟨32862974421315552179765051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21908649614210368119843367 32862974421315552179765051)
      ·
        refine ⟨49294461631973328269647577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32862974421315552179765051 49294461631973328269647577)
        ·
          refine ⟨36970846223979996202235683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49294461631973328269647577 36970846223979996202235683)
          ·
            refine ⟨55456269335969994303353525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36970846223979996202235683 55456269335969994303353525)
            ·
              refine ⟨5199025250247186965939393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55456269335969994303353525 5199025250247186965939393)
              ·
                refine ⟨3899268937685390224454545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5199025250247186965939393 3899268937685390224454545)
                ·
                  refine ⟨2924451703264042668340909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3899268937685390224454545 2924451703264042668340909)
                  ·
                    refine ⟨1096669388724016000627841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2924451703264042668340909 1096669388724016000627841)
                    ·
                      rfl

theorem cell22_3203634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_3203634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3203634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3203634 prefixEnd_3203634 := by exact prefixLift 3203634
  have htrace : WordTrace (prefixWord ++ tailWord_3203634) baseStart_3203634 baseEnd_3203634 := by
    simpa [prefixWord, tailWord_3203634, baseEnd_3203634] using wordTrace_append hprefix tailTrace_3203634
  have hstable : (prefixWord ++ tailWord_3203634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203634).length < 2 ^ (prefixWord ++ tailWord_3203634).sum := by decide
  have hdescent : baseEnd_3203634 < baseStart_3203634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203636 : List Nat := [2, 5, 1, 3, 1, 1, 2, 1, 6]
def baseStart_3203636 : Nat := 118140960795 + 3203636 * 2 ^ 59
def prefixEnd_3203636 : Nat := 4983230072969 + 3 ^ 40 * 3203636 * 2
def baseEnd_3203636 : Nat := 365556691121629554025945

theorem tailTrace_3203636 : CollatzResearch.WordTrace tailWord_3203636 prefixEnd_3203636 365556691121629554025945 := by
  unfold tailWord_3203636
  simp only [CollatzResearch.WordTrace]
  refine ⟨58423102110890692157035381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77897469481187589542713841 58423102110890692157035381)
  ·
    refine ⟨5477165822896002389722067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58423102110890692157035381 5477165822896002389722067)
    ·
      refine ⟨8215748734344003584583101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5477165822896002389722067 8215748734344003584583101)
      ·
        refine ⟨3080905775379001344218663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8215748734344003584583101 3080905775379001344218663)
        ·
          refine ⟨4621358663068502016327995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3080905775379001344218663 4621358663068502016327995)
          ·
            refine ⟨6932037994602753024491993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4621358663068502016327995 6932037994602753024491993)
            ·
              refine ⟨5199028495952064768368995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6932037994602753024491993 5199028495952064768368995)
              ·
                refine ⟨7798542743928097152553493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5199028495952064768368995 7798542743928097152553493)
                ·
                  refine ⟨365556691121629554025945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7798542743928097152553493 365556691121629554025945)
                  ·
                    rfl

theorem cell22_3203636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_3203636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3203636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3203636 prefixEnd_3203636 := by exact prefixLift 3203636
  have htrace : WordTrace (prefixWord ++ tailWord_3203636) baseStart_3203636 baseEnd_3203636 := by
    simpa [prefixWord, tailWord_3203636, baseEnd_3203636] using wordTrace_append hprefix tailTrace_3203636
  have hstable : (prefixWord ++ tailWord_3203636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203636).length < 2 ^ (prefixWord ++ tailWord_3203636).sum := by decide
  have hdescent : baseEnd_3203636 < baseStart_3203636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203696 : List Nat := [2, 1, 1, 1, 7, 2, 1, 1, 3, 3]
def baseStart_3203696 : Nat := 118140960795 + 3203696 * 2 ^ 59
def prefixEnd_3203696 : Nat := 4983230072969 + 3 ^ 40 * 3203696 * 2
def baseEnd_3203696 : Nat := 1096690612591068505577651

theorem tailTrace_3203696 : CollatzResearch.WordTrace tailWord_3203696 prefixEnd_3203696 1096690612591068505577651 := by
  unfold tailWord_3203696
  simp only [CollatzResearch.WordTrace]
  refine ⟨58424196300782007280627471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77898928401042676374169961 58424196300782007280627471)
  ·
    refine ⟨87636294451173010920941207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58424196300782007280627471 87636294451173010920941207)
    ·
      refine ⟨131454441676759516381411811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87636294451173010920941207 131454441676759516381411811)
      ·
        refine ⟨197181662515139274572117717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131454441676759516381411811 197181662515139274572117717)
        ·
          refine ⟨4621445215198576747784009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 197181662515139274572117717 4621445215198576747784009)
          ·
            refine ⟨3466083911398932560838007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4621445215198576747784009 3466083911398932560838007)
            ·
              refine ⟨5199125867098398841257011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3466083911398932560838007 5199125867098398841257011)
              ·
                refine ⟨7798688800647598261885517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5199125867098398841257011 7798688800647598261885517)
                ·
                  refine ⟨2924508300242849348207069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7798688800647598261885517 2924508300242849348207069)
                  ·
                    refine ⟨1096690612591068505577651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2924508300242849348207069 1096690612591068505577651)
                    ·
                      rfl

theorem cell22_3203696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 3, 3].length) (baseStart_3203696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3203696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3203696 prefixEnd_3203696 := by exact prefixLift 3203696
  have htrace : WordTrace (prefixWord ++ tailWord_3203696) baseStart_3203696 baseEnd_3203696 := by
    simpa [prefixWord, tailWord_3203696, baseEnd_3203696] using wordTrace_append hprefix tailTrace_3203696
  have hstable : (prefixWord ++ tailWord_3203696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203696).length < 2 ^ (prefixWord ++ tailWord_3203696).sum := by decide
  have hdescent : baseEnd_3203696 < baseStart_3203696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203709 : List Nat := [1, 4, 1, 1, 5, 1, 1, 3, 5]
def baseStart_3203709 : Nat := 118140960795 + 3203709 * 2 ^ 59
def prefixEnd_3203709 : Nat := 4983230072969 + 3 ^ 40 * 3203709 * 2
def baseEnd_3203709 : Nat := 365565020918913601667537

theorem tailTrace_3203709 : CollatzResearch.WordTrace tailWord_3203709 prefixEnd_3203709 365565020918913601667537 := by
  unfold tailWord_3203709
  simp only [CollatzResearch.WordTrace]
  refine ⟨116848866750516917781478181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77899244500344611854318787 116848866750516917781478181)
  ·
    refine ⟨21909162515721922084027159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116848866750516917781478181 21909162515721922084027159)
    ·
      refine ⟨32863743773582883126040739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21909162515721922084027159 32863743773582883126040739)
      ·
        refine ⟨49295615660374324689061109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32863743773582883126040739 49295615660374324689061109)
        ·
          refine ⟨4621463968160092939599479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49295615660374324689061109 4621463968160092939599479)
          ·
            refine ⟨6932195952240139409399219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4621463968160092939599479 6932195952240139409399219)
            ·
              refine ⟨10398293928360209114098829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6932195952240139409399219 10398293928360209114098829)
              ·
                refine ⟨3899360223135078417787061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10398293928360209114098829 3899360223135078417787061)
                ·
                  refine ⟨365565020918913601667537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3899360223135078417787061 365565020918913601667537)
                  ·
                    rfl

theorem cell22_3203709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_3203709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3203709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3203709 prefixEnd_3203709 := by exact prefixLift 3203709
  have htrace : WordTrace (prefixWord ++ tailWord_3203709) baseStart_3203709 baseEnd_3203709 := by
    simpa [prefixWord, tailWord_3203709, baseEnd_3203709] using wordTrace_append hprefix tailTrace_3203709
  have hstable : (prefixWord ++ tailWord_3203709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203709).length < 2 ^ (prefixWord ++ tailWord_3203709).sum := by decide
  have hdescent : baseEnd_3203709 < baseStart_3203709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203784 : List Nat := [2, 1, 3, 1, 2, 3, 3, 1, 2, 4]
def baseStart_3203784 : Nat := 118140960795 + 3203784 * 2 ^ 59
def prefixEnd_3203784 : Nat := 4983230072969 + 3 ^ 40 * 3203784 * 2
def baseEnd_3203784 : Nat := 1096720736789465609377381

theorem tailTrace_3203784 : CollatzResearch.WordTrace tailWord_3203784 prefixEnd_3203784 1096720736789465609377381 := by
  unfold tailWord_3203784
  simp only [CollatzResearch.WordTrace]
  refine ⟨58425801112622602795229203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77901068150163470393638937 58425801112622602795229203)
  ·
    refine ⟨87638701668933904192843805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58425801112622602795229203 87638701668933904192843805)
    ·
      refine ⟨32864513125850214072316427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87638701668933904192843805 32864513125850214072316427)
      ·
        refine ⟨49296769688775321108474641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32864513125850214072316427 49296769688775321108474641)
        ·
          refine ⟨36972577266581490831355981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49296769688775321108474641 36972577266581490831355981)
          ·
            refine ⟨13864716474968059061758493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36972577266581490831355981 13864716474968059061758493)
            ·
              refine ⟨5199268678113022148159435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13864716474968059061758493 5199268678113022148159435)
              ·
                refine ⟨7798903017169533222239153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5199268678113022148159435 7798903017169533222239153)
                ·
                  refine ⟨5849177262877149916679365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7798903017169533222239153 5849177262877149916679365)
                  ·
                    refine ⟨1096720736789465609377381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5849177262877149916679365 1096720736789465609377381)
                    ·
                      rfl

theorem cell22_3203784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_3203784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3203784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3203784 prefixEnd_3203784 := by exact prefixLift 3203784
  have htrace : WordTrace (prefixWord ++ tailWord_3203784) baseStart_3203784 baseEnd_3203784 := by
    simpa [prefixWord, tailWord_3203784, baseEnd_3203784] using wordTrace_append hprefix tailTrace_3203784
  have hstable : (prefixWord ++ tailWord_3203784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203784).length < 2 ^ (prefixWord ++ tailWord_3203784).sum := by decide
  have hdescent : baseEnd_3203784 < baseStart_3203784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203848 : List Nat := [2, 1, 3, 2, 2, 2, 3, 3, 1, 3]
def baseStart_3203848 : Nat := 118140960795 + 3203848 * 2 ^ 59
def prefixEnd_3203848 : Nat := 4983230072969 + 3 ^ 40 * 3203848 * 2
def baseEnd_3203848 : Nat := 1096742645297390775777185

theorem tailTrace_3203848 : CollatzResearch.WordTrace tailWord_3203848 prefixEnd_3203848 1096742645297390775777185 := by
  unfold tailWord_3203848
  simp only [CollatzResearch.WordTrace]
  refine ⟨58426968248506672260394099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77902624331342229680525465 58426968248506672260394099)
  ·
    refine ⟨87640452372760008390591149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58426968248506672260394099 87640452372760008390591149)
    ·
      refine ⟨32865169639785003146471681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87640452372760008390591149 32865169639785003146471681)
      ·
        refine ⟨24648877229838752359853761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32865169639785003146471681 24648877229838752359853761)
        ·
          refine ⟨18486657922379064269890321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24648877229838752359853761 18486657922379064269890321)
          ·
            refine ⟨13864993441784298202417741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18486657922379064269890321 13864993441784298202417741)
            ·
              refine ⟨5199372540669111825906653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13864993441784298202417741 5199372540669111825906653)
              ·
                refine ⟨1949764702750916934714995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5199372540669111825906653 1949764702750916934714995)
                ·
                  refine ⟨2924647054126375402072493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1949764702750916934714995 2924647054126375402072493)
                  ·
                    refine ⟨1096742645297390775777185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2924647054126375402072493 1096742645297390775777185)
                    ·
                      rfl

theorem cell22_3203848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 3, 1, 3].length) (baseStart_3203848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3203848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3203848 prefixEnd_3203848 := by exact prefixLift 3203848
  have htrace : WordTrace (prefixWord ++ tailWord_3203848) baseStart_3203848 baseEnd_3203848 := by
    simpa [prefixWord, tailWord_3203848, baseEnd_3203848] using wordTrace_append hprefix tailTrace_3203848
  have hstable : (prefixWord ++ tailWord_3203848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203848).length < 2 ^ (prefixWord ++ tailWord_3203848).sum := by decide
  have hdescent : baseEnd_3203848 < baseStart_3203848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203891 : List Nat := [1, 1, 1, 2, 6, 1, 3, 2, 1, 4]
def baseStart_3203891 : Nat := 118140960795 + 3203891 * 2 ^ 59
def prefixEnd_3203891 : Nat := 4983230072969 + 3 ^ 40 * 3203891 * 2
def baseEnd_3203891 : Nat := 1096757365076152996952053

theorem tailTrace_3203891 : CollatzResearch.WordTrace tailWord_3203891 prefixEnd_3203891 1096757365076152996952053 := by
  unfold tailWord_3203891
  simp only [CollatzResearch.WordTrace]
  refine ⟨116855504835857562864603527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77903669890571708576402351 116855504835857562864603527)
  ·
    refine ⟨175283257253786344296905291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116855504835857562864603527 175283257253786344296905291)
    ·
      refine ⟨262924885880679516445357937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175283257253786344296905291 262924885880679516445357937)
      ·
        refine ⟨197193664410509637334018453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262924885880679516445357937 197193664410509637334018453)
        ·
          refine ⟨9243453019242639250032115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 197193664410509637334018453 9243453019242639250032115)
          ·
            refine ⟨13865179528863958875048173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9243453019242639250032115 13865179528863958875048173)
            ·
              refine ⟨5199442323323984578143065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13865179528863958875048173 5199442323323984578143065)
              ·
                refine ⟨3899581742492988433607299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5199442323323984578143065 3899581742492988433607299)
                ·
                  refine ⟨5849372613739482650410949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3899581742492988433607299 5849372613739482650410949)
                  ·
                    refine ⟨1096757365076152996952053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5849372613739482650410949 1096757365076152996952053)
                    ·
                      rfl

theorem cell22_3203891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 4].length) (baseStart_3203891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3203891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3203891 prefixEnd_3203891 := by exact prefixLift 3203891
  have htrace : WordTrace (prefixWord ++ tailWord_3203891) baseStart_3203891 baseEnd_3203891 := by
    simpa [prefixWord, tailWord_3203891, baseEnd_3203891] using wordTrace_append hprefix tailTrace_3203891
  have hstable : (prefixWord ++ tailWord_3203891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203891).length < 2 ^ (prefixWord ++ tailWord_3203891).sum := by decide
  have hdescent : baseEnd_3203891 < baseStart_3203891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203904 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 6, 3]
def baseStart_3203904 : Nat := 118140960795 + 3203904 * 2 ^ 59
def prefixEnd_3203904 : Nat := 4983230072969 + 3 ^ 40 * 3203904 * 2
def baseEnd_3203904 : Nat := 1096761815241825296377013

theorem tailTrace_3203904 : CollatzResearch.WordTrace tailWord_3203904 prefixEnd_3203904 1096761815241825296377013 := by
  unfold tailWord_3203904
  simp only [CollatzResearch.WordTrace]
  refine ⟨58427989492405233042413383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77903985989873644056551177 58427989492405233042413383)
  ·
    refine ⟨87641984238607849563620075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58427989492405233042413383 87641984238607849563620075)
    ·
      refine ⟨131462976357911774345430113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87641984238607849563620075 131462976357911774345430113)
      ·
        refine ⟨98597232268433830759072585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131462976357911774345430113 98597232268433830759072585)
        ·
          refine ⟨73947924201325373069304439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98597232268433830759072585 73947924201325373069304439)
          ·
            refine ⟨110921886301988059603956659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73947924201325373069304439 110921886301988059603956659)
            ·
              refine ⟨166382829452982089405934989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110921886301988059603956659 166382829452982089405934989)
              ·
                refine ⟨62393561044868283527225621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166382829452982089405934989 62393561044868283527225621)
                ·
                  refine ⟨2924698173978200790338701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62393561044868283527225621 2924698173978200790338701)
                  ·
                    refine ⟨1096761815241825296377013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2924698173978200790338701 1096761815241825296377013)
                    ·
                      rfl

theorem cell22_3203904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 6, 3].length) (baseStart_3203904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3203904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3203904 prefixEnd_3203904 := by exact prefixLift 3203904
  have htrace : WordTrace (prefixWord ++ tailWord_3203904) baseStart_3203904 baseEnd_3203904 := by
    simpa [prefixWord, tailWord_3203904, baseEnd_3203904] using wordTrace_append hprefix tailTrace_3203904
  have hstable : (prefixWord ++ tailWord_3203904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203904).length < 2 ^ (prefixWord ++ tailWord_3203904).sum := by decide
  have hdescent : baseEnd_3203904 < baseStart_3203904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3203938 : List Nat := [3, 3, 2, 1, 3, 1, 2, 1, 1, 5]
def baseStart_3203938 : Nat := 118140960795 + 3203938 * 2 ^ 59
def prefixEnd_3203938 : Nat := 4983230072969 + 3 ^ 40 * 3203938 * 2
def baseEnd_3203938 : Nat := 1096773454136660541026909

theorem tailTrace_3203938 : CollatzResearch.WordTrace tailWord_3203938 prefixEnd_3203938 1096773454136660541026909 := by
  unfold tailWord_3203938
  simp only [CollatzResearch.WordTrace]
  refine ⟨29214304766671822472891117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77904812711124859927709645 29214304766671822472891117)
  ·
    refine ⟨10955364287501933427334169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29214304766671822472891117 10955364287501933427334169)
    ·
      refine ⟨8216523215626450070500627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10955364287501933427334169 8216523215626450070500627)
      ·
        refine ⟨12324784823439675105750941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8216523215626450070500627 12324784823439675105750941)
        ·
          refine ⟨4621794308789878164656603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12324784823439675105750941 4621794308789878164656603)
          ·
            refine ⟨6932691463184817246984905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4621794308789878164656603 6932691463184817246984905)
            ·
              refine ⟨5199518597388612935238679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6932691463184817246984905 5199518597388612935238679)
              ·
                refine ⟨7799277896082919402858019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5199518597388612935238679 7799277896082919402858019)
                ·
                  refine ⟨11698916844124379104287029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7799277896082919402858019 11698916844124379104287029)
                  ·
                    refine ⟨1096773454136660541026909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11698916844124379104287029 1096773454136660541026909)
                    ·
                      rfl

theorem cell22_3203938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_3203938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3203938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3203938 prefixEnd_3203938 := by exact prefixLift 3203938
  have htrace : WordTrace (prefixWord ++ tailWord_3203938) baseStart_3203938 baseEnd_3203938 := by
    simpa [prefixWord, tailWord_3203938, baseEnd_3203938] using wordTrace_append hprefix tailTrace_3203938
  have hstable : (prefixWord ++ tailWord_3203938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3203938).length < 2 ^ (prefixWord ++ tailWord_3203938).sum := by decide
  have hdescent : baseEnd_3203938 < baseStart_3203938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3203938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204017 : List Nat := [1, 2, 2, 4, 3, 2, 1, 3, 1, 3]
def baseStart_3204017 : Nat := 118140960795 + 3204017 * 2 ^ 59
def prefixEnd_3204017 : Nat := 4983230072969 + 3 ^ 40 * 3204017 * 2
def baseEnd_3204017 : Nat := 1096800497451130668301667

theorem tailTrace_3204017 : CollatzResearch.WordTrace tailWord_3204017 prefixEnd_3204017 1096800497451130668301667 := by
  unfold tailWord_3204017
  simp only [CollatzResearch.WordTrace]
  refine ⟨116860100433401086383690305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77906733622267390922460203 116860100433401086383690305)
  ·
    refine ⟨87645075325050814787767729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116860100433401086383690305 87645075325050814787767729)
    ·
      refine ⟨65733806493788111090825797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87645075325050814787767729 65733806493788111090825797)
      ·
        refine ⟨12325088717585270829529837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65733806493788111090825797 12325088717585270829529837)
        ·
          refine ⟨4621908269094476561073689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12325088717585270829529837 4621908269094476561073689)
          ·
            refine ⟨3466431201820857420805267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4621908269094476561073689 3466431201820857420805267)
            ·
              refine ⟨5199646802731286131207901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3466431201820857420805267 5199646802731286131207901)
              ·
                refine ⟨1949867551024232299202963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5199646802731286131207901 1949867551024232299202963)
                ·
                  refine ⟨2924801326536348448804445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1949867551024232299202963 2924801326536348448804445)
                  ·
                    refine ⟨1096800497451130668301667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2924801326536348448804445 1096800497451130668301667)
                    ·
                      rfl

theorem cell22_3204017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 3, 1, 3].length) (baseStart_3204017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3204017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3204017 prefixEnd_3204017 := by exact prefixLift 3204017
  have htrace : WordTrace (prefixWord ++ tailWord_3204017) baseStart_3204017 baseEnd_3204017 := by
    simpa [prefixWord, tailWord_3204017, baseEnd_3204017] using wordTrace_append hprefix tailTrace_3204017
  have hstable : (prefixWord ++ tailWord_3204017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204017).length < 2 ^ (prefixWord ++ tailWord_3204017).sum := by decide
  have hdescent : baseEnd_3204017 < baseStart_3204017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204026 : List Nat := [3, 1, 1, 1, 2, 1, 3, 5, 1, 4]
def baseStart_3204026 : Nat := 118140960795 + 3204026 * 2 ^ 59
def prefixEnd_3204026 : Nat := 4983230072969 + 3 ^ 40 * 3204026 * 2
def baseEnd_3204026 : Nat := 1096803578335057644826639

theorem tailTrace_3204026 : CollatzResearch.WordTrace tailWord_3204026 prefixEnd_3204026 1096803578335057644826639 := by
  unfold tailWord_3204026
  simp only [CollatzResearch.WordTrace]
  refine ⟨29215107172592120230191983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77906952460245653947178621 29215107172592120230191983)
  ·
    refine ⟨43822660758888180345287975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29215107172592120230191983 43822660758888180345287975)
    ·
      refine ⟨65733991138332270517931963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43822660758888180345287975 65733991138332270517931963)
      ·
        refine ⟨98600986707498405776897945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65733991138332270517931963 98600986707498405776897945)
        ·
          refine ⟨73950740030623804332673459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98600986707498405776897945 73950740030623804332673459)
          ·
            refine ⟨110926110045935706499010189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73950740030623804332673459 110926110045935706499010189)
            ·
              refine ⟨41597291267225889937128821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110926110045935706499010189 41597291267225889937128821)
              ·
                refine ⟨3899746056302427181605827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41597291267225889937128821 3899746056302427181605827)
                ·
                  refine ⟨5849619084453640772408741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3899746056302427181605827 5849619084453640772408741)
                  ·
                    refine ⟨1096803578335057644826639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5849619084453640772408741 1096803578335057644826639)
                    ·
                      rfl

theorem cell22_3204026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 1, 4].length) (baseStart_3204026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3204026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3204026 prefixEnd_3204026 := by exact prefixLift 3204026
  have htrace : WordTrace (prefixWord ++ tailWord_3204026) baseStart_3204026 baseEnd_3204026 := by
    simpa [prefixWord, tailWord_3204026, baseEnd_3204026] using wordTrace_append hprefix tailTrace_3204026
  have hstable : (prefixWord ++ tailWord_3204026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204026).length < 2 ^ (prefixWord ++ tailWord_3204026).sum := by decide
  have hdescent : baseEnd_3204026 < baseStart_3204026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204086 : List Nat := [5, 1, 1, 1, 3, 11]
def baseStart_3204086 : Nat := 118140960795 + 3204086 * 2 ^ 59
def prefixEnd_3204086 : Nat := 4983230072969 + 3 ^ 40 * 3204086 * 2
def baseEnd_3204086 : Nat := 13541038488410339362055

theorem tailTrace_3204086 : CollatzResearch.WordTrace tailWord_3204086 prefixEnd_3204086 13541038488410339362055 := by
  unfold tailWord_3204086
  simp only [CollatzResearch.WordTrace]
  refine ⟨7303913566884444447997007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77908411380100740778634741 7303913566884444447997007)
  ·
    refine ⟨10955870350326666671995511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7303913566884444447997007 10955870350326666671995511)
    ·
      refine ⟨16433805525490000007993267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10955870350326666671995511 16433805525490000007993267)
      ·
        refine ⟨24650708288235000011989901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16433805525490000007993267 24650708288235000011989901)
        ·
          refine ⟨9244015608088125004496213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24650708288235000011989901 9244015608088125004496213)
          ·
            refine ⟨13541038488410339362055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9244015608088125004496213 13541038488410339362055)
            ·
              rfl

theorem cell22_3204086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 11].length) (baseStart_3204086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3204086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3204086 prefixEnd_3204086 := by exact prefixLift 3204086
  have htrace : WordTrace (prefixWord ++ tailWord_3204086) baseStart_3204086 baseEnd_3204086 := by
    simpa [prefixWord, tailWord_3204086, baseEnd_3204086] using wordTrace_append hprefix tailTrace_3204086
  have hstable : (prefixWord ++ tailWord_3204086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204086).length < 2 ^ (prefixWord ++ tailWord_3204086).sum := by decide
  have hdescent : baseEnd_3204086 < baseStart_3204086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204146 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 4, 5]
def baseStart_3204146 : Nat := 118140960795 + 3204146 * 2 ^ 59
def prefixEnd_3204146 : Nat := 4983230072969 + 3 ^ 40 * 3204146 * 2
def baseEnd_3204146 : Nat := 1096844656787417331826271

theorem tailTrace_3204146 : CollatzResearch.WordTrace tailWord_3204146 prefixEnd_3204146 1096844656787417331826271 := by
  unfold tailWord_3204146
  simp only [CollatzResearch.WordTrace]
  refine ⟨29216201362483435353784073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77909870299955827610090861 29216201362483435353784073)
  ·
    refine ⟨21912151021862576515338055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29216201362483435353784073 21912151021862576515338055)
    ·
      refine ⟨32868226532793864773007083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21912151021862576515338055 32868226532793864773007083)
      ·
        refine ⟨49302339799190797159510625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32868226532793864773007083 49302339799190797159510625)
        ·
          refine ⟨36976754849393097869632969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49302339799190797159510625 36976754849393097869632969)
          ·
            refine ⟨27732566137044823402224727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36976754849393097869632969 27732566137044823402224727)
            ·
              refine ⟨41598849205567235103337091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27732566137044823402224727 41598849205567235103337091)
              ·
                refine ⟨62398273808350852655005637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41598849205567235103337091 62398273808350852655005637)
                ·
                  refine ⟨11699676339065784872813557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62398273808350852655005637 11699676339065784872813557)
                  ·
                    refine ⟨1096844656787417331826271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11699676339065784872813557 1096844656787417331826271)
                    ·
                      rfl

theorem cell22_3204146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_3204146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3204146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3204146 prefixEnd_3204146 := by exact prefixLift 3204146
  have htrace : WordTrace (prefixWord ++ tailWord_3204146) baseStart_3204146 baseEnd_3204146 := by
    simpa [prefixWord, tailWord_3204146, baseEnd_3204146] using wordTrace_append hprefix tailTrace_3204146
  have hstable : (prefixWord ++ tailWord_3204146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204146).length < 2 ^ (prefixWord ++ tailWord_3204146).sum := by decide
  have hdescent : baseEnd_3204146 < baseStart_3204146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204191 : List Nat := [1, 1, 2, 3, 1, 1, 4, 1, 3, 5]
def baseStart_3204191 : Nat := 118140960795 + 3204191 * 2 ^ 59
def prefixEnd_3204191 : Nat := 4983230072969 + 3 ^ 40 * 3204191 * 2
def baseEnd_3204191 : Nat := 1096860061207052214451133

theorem tailTrace_3204191 : CollatzResearch.WordTrace tailWord_3204191 prefixEnd_3204191 1096860061207052214451133 := by
  unfold tailWord_3204191
  simp only [CollatzResearch.WordTrace]
  refine ⟨116866446734770714100524427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77910964489847142733682951 116866446734770714100524427)
  ·
    refine ⟨175299670102156071150786641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116866446734770714100524427 175299670102156071150786641)
    ·
      refine ⟨131474752576617053363089981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175299670102156071150786641 131474752576617053363089981)
      ·
        refine ⟨49303032216231395011158743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131474752576617053363089981 49303032216231395011158743)
        ·
          refine ⟨73954548324347092516738115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49303032216231395011158743 73954548324347092516738115)
          ·
            refine ⟨110931822486520638775107173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73954548324347092516738115 110931822486520638775107173)
            ·
              refine ⟨20799716716222619770332595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110931822486520638775107173 20799716716222619770332595)
              ·
                refine ⟨31199575074333929655498893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20799716716222619770332595 31199575074333929655498893)
                ·
                  refine ⟨11699840652875223620812085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31199575074333929655498893 11699840652875223620812085)
                  ·
                    refine ⟨1096860061207052214451133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11699840652875223620812085 1096860061207052214451133)
                    ·
                      rfl

theorem cell22_3204191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 5].length) (baseStart_3204191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3204191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3204191 prefixEnd_3204191 := by exact prefixLift 3204191
  have htrace : WordTrace (prefixWord ++ tailWord_3204191) baseStart_3204191 baseEnd_3204191 := by
    simpa [prefixWord, tailWord_3204191, baseEnd_3204191] using wordTrace_append hprefix tailTrace_3204191
  have hstable : (prefixWord ++ tailWord_3204191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204191).length < 2 ^ (prefixWord ++ tailWord_3204191).sum := by decide
  have hdescent : baseEnd_3204191 < baseStart_3204191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204208 : List Nat := [2, 1, 1, 1, 5, 1, 1, 3, 4, 3]
def baseStart_3204208 : Nat := 118140960795 + 3204208 * 2 ^ 59
def prefixEnd_3204208 : Nat := 4983230072969 + 3 ^ 40 * 3204208 * 2
def baseEnd_3204208 : Nat := 1096865880654469836776081

theorem tailTrace_3204208 : CollatzResearch.WordTrace tailWord_3204208 prefixEnd_3204208 1096865880654469836776081 := by
  unfold tailWord_3204208
  simp only [CollatzResearch.WordTrace]
  refine ⟨58433533387854563001946639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77911377850472750669262185 58433533387854563001946639)
  ·
    refine ⟨87650300081781844502919959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58433533387854563001946639 87650300081781844502919959)
    ·
      refine ⟨131475450122672766754379939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87650300081781844502919959 131475450122672766754379939)
      ·
        refine ⟨197213175184009150131569909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131475450122672766754379939 197213175184009150131569909)
        ·
          refine ⟨18488735173500857824834679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 197213175184009150131569909 18488735173500857824834679)
          ·
            refine ⟨27733102760251286737252019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18488735173500857824834679 27733102760251286737252019)
            ·
              refine ⟨41599654140376930105878029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27733102760251286737252019 41599654140376930105878029)
              ·
                refine ⟨15599870302641348789704261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41599654140376930105878029 15599870302641348789704261)
                ·
                  refine ⟨2924975681745252898069549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15599870302641348789704261 2924975681745252898069549)
                  ·
                    refine ⟨1096865880654469836776081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2924975681745252898069549 1096865880654469836776081)
                    ·
                      rfl

theorem cell22_3204208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 4, 3].length) (baseStart_3204208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3204208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3204208 prefixEnd_3204208 := by exact prefixLift 3204208
  have htrace : WordTrace (prefixWord ++ tailWord_3204208) baseStart_3204208 baseEnd_3204208 := by
    simpa [prefixWord, tailWord_3204208, baseEnd_3204208] using wordTrace_append hprefix tailTrace_3204208
  have hstable : (prefixWord ++ tailWord_3204208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204208).length < 2 ^ (prefixWord ++ tailWord_3204208).sum := by decide
  have hdescent : baseEnd_3204208 < baseStart_3204208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204236 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 2, 7]
def baseStart_3204236 : Nat := 118140960795 + 3204236 * 2 ^ 59
def prefixEnd_3204236 : Nat := 4983230072969 + 3 ^ 40 * 3204236 * 2
def baseEnd_3204236 : Nat := 1096875465626687097075995

theorem tailTrace_3204236 : CollatzResearch.WordTrace tailWord_3204236 prefixEnd_3204236 1096875465626687097075995 := by
  unfold tailWord_3204236
  simp only [CollatzResearch.WordTrace]
  refine ⟨58434044009803843392956281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77912058679738457857275041 58434044009803843392956281)
  ·
    refine ⟨43825533007352882544717211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58434044009803843392956281 43825533007352882544717211)
    ·
      refine ⟨65738299511029323817075817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43825533007352882544717211 65738299511029323817075817)
      ·
        refine ⟨49303724633271992862806863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65738299511029323817075817 49303724633271992862806863)
        ·
          refine ⟨73955586949907989294210295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49303724633271992862806863 73955586949907989294210295)
          ·
            refine ⟨110933380424861983941315443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73955586949907989294210295 110933380424861983941315443)
            ·
              refine ⟨166400070637292975911973165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110933380424861983941315443 166400070637292975911973165)
              ·
                refine ⟨62400026488984865966989937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166400070637292975911973165 62400026488984865966989937)
                ·
                  refine ⟨46800019866738649475242453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62400026488984865966989937 46800019866738649475242453)
                  ·
                    refine ⟨1096875465626687097075995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46800019866738649475242453 1096875465626687097075995)
                    ·
                      rfl

theorem cell22_3204236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_3204236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3204236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3204236 prefixEnd_3204236 := by exact prefixLift 3204236
  have htrace : WordTrace (prefixWord ++ tailWord_3204236) baseStart_3204236 baseEnd_3204236 := by
    simpa [prefixWord, tailWord_3204236, baseEnd_3204236] using wordTrace_append hprefix tailTrace_3204236
  have hstable : (prefixWord ++ tailWord_3204236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204236).length < 2 ^ (prefixWord ++ tailWord_3204236).sum := by decide
  have hdescent : baseEnd_3204236 < baseStart_3204236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204238 : List Nat := [4, 1, 1, 3, 2, 1, 2, 8]
def baseStart_3204238 : Nat := 118140960795 + 3204238 * 2 ^ 59
def prefixEnd_3204238 : Nat := 4983230072969 + 3 ^ 40 * 3204238 * 2
def baseEnd_3204238 : Nat := 121875127807506639836221

theorem tailTrace_3204238 : CollatzResearch.WordTrace tailWord_3204238 prefixEnd_3204238 121875127807506639836221 := by
  unfold tailWord_3204238
  simp only [CollatzResearch.WordTrace]
  refine ⟨14608520120700055140935671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77912107310400294084990245 14608520120700055140935671)
  ·
    refine ⟨21912780181050082711403507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14608520120700055140935671 21912780181050082711403507)
    ·
      refine ⟨32869170271575124067105261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21912780181050082711403507 32869170271575124067105261)
      ·
        refine ⟨12325938851840671525164473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32869170271575124067105261 12325938851840671525164473)
        ·
          refine ⟨9244454138880503643873355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12325938851840671525164473 9244454138880503643873355)
          ·
            refine ⟨13866681208320755465810033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9244454138880503643873355 13866681208320755465810033)
            ·
              refine ⟨10400010906240566599357525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13866681208320755465810033 10400010906240566599357525)
              ·
                refine ⟨121875127807506639836221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10400010906240566599357525 121875127807506639836221)
                ·
                  rfl

theorem cell22_3204238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 8].length) (baseStart_3204238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3204238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3204238 prefixEnd_3204238 := by exact prefixLift 3204238
  have htrace : WordTrace (prefixWord ++ tailWord_3204238) baseStart_3204238 baseEnd_3204238 := by
    simpa [prefixWord, tailWord_3204238, baseEnd_3204238] using wordTrace_append hprefix tailTrace_3204238
  have hstable : (prefixWord ++ tailWord_3204238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204238).length < 2 ^ (prefixWord ++ tailWord_3204238).sum := by decide
  have hdescent : baseEnd_3204238 < baseStart_3204238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204375 : List Nat := [1, 1, 3, 4, 1, 1, 3, 2, 2, 4]
def baseStart_3204375 : Nat := 118140960795 + 3204375 * 2 ^ 59
def prefixEnd_3204375 : Nat := 4983230072969 + 3 ^ 40 * 3204375 * 2
def baseEnd_3204375 : Nat := 1096923048167337067850569

theorem tailTrace_3204375 : CollatzResearch.WordTrace tailWord_3204375 prefixEnd_3204375 1096923048167337067850569 := by
  unfold tailWord_3204375
  simp only [CollatzResearch.WordTrace]
  refine ⟨116873157766104113525222579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77915438510736075683481719 116873157766104113525222579)
  ·
    refine ⟨175309736649156170287833869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116873157766104113525222579 175309736649156170287833869)
    ·
      refine ⟨65741151243433563857937701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175309736649156170287833869 65741151243433563857937701)
      ·
        refine ⟨12326465858143793223363319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65741151243433563857937701 12326465858143793223363319)
        ·
          refine ⟨18489698787215689835044979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12326465858143793223363319 18489698787215689835044979)
          ·
            refine ⟨27734548180823534752567469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18489698787215689835044979 27734548180823534752567469)
            ·
              refine ⟨10400455567808825532212801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27734548180823534752567469 10400455567808825532212801)
              ·
                refine ⟨7800341675856619149159601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10400455567808825532212801 7800341675856619149159601)
                ·
                  refine ⟨5850256256892464361869701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7800341675856619149159601 5850256256892464361869701)
                  ·
                    refine ⟨1096923048167337067850569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5850256256892464361869701 1096923048167337067850569)
                    ·
                      rfl

theorem cell22_3204375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_3204375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3204375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3204375 prefixEnd_3204375 := by exact prefixLift 3204375
  have htrace : WordTrace (prefixWord ++ tailWord_3204375) baseStart_3204375 baseEnd_3204375 := by
    simpa [prefixWord, tailWord_3204375, baseEnd_3204375] using wordTrace_append hprefix tailTrace_3204375
  have hstable : (prefixWord ++ tailWord_3204375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204375).length < 2 ^ (prefixWord ++ tailWord_3204375).sum := by decide
  have hdescent : baseEnd_3204375 < baseStart_3204375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204394 : List Nat := [3, 1, 4, 2, 1, 2, 1, 3, 2, 3]
def baseStart_3204394 : Nat := 118140960795 + 3204394 * 2 ^ 59
def prefixEnd_3204394 : Nat := 4983230072969 + 3 ^ 40 * 3204394 * 2
def baseEnd_3204394 : Nat := 1096929552255627351625511

theorem tailTrace_3204394 : CollatzResearch.WordTrace tailWord_3204394 prefixEnd_3204394 1096929552255627351625511 := by
  unfold tailWord_3204394
  simp only [CollatzResearch.WordTrace]
  refine ⟨29218462688258819942541059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77915900502023519846776157 29218462688258819942541059)
  ·
    refine ⟨43827694032388229913811589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29218462688258819942541059 43827694032388229913811589)
    ·
      refine ⟨8217692631072793108839673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43827694032388229913811589 8217692631072793108839673)
      ·
        refine ⟨6163269473304594831629755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8217692631072793108839673 6163269473304594831629755)
        ·
          refine ⟨9244904209956892247444633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6163269473304594831629755 9244904209956892247444633)
          ·
            refine ⟨6933678157467669185583475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9244904209956892247444633 6933678157467669185583475)
            ·
              refine ⟨10400517236201503778375213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6933678157467669185583475 10400517236201503778375213)
              ·
                refine ⟨3900193963575563916890705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10400517236201503778375213 3900193963575563916890705)
                ·
                  refine ⟨2925145472681672937668029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3900193963575563916890705 2925145472681672937668029)
                  ·
                    refine ⟨1096929552255627351625511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2925145472681672937668029 1096929552255627351625511)
                    ·
                      rfl

theorem cell22_3204394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_3204394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3204394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3204394 prefixEnd_3204394 := by exact prefixLift 3204394
  have htrace : WordTrace (prefixWord ++ tailWord_3204394) baseStart_3204394 baseEnd_3204394 := by
    simpa [prefixWord, tailWord_3204394, baseEnd_3204394] using wordTrace_append hprefix tailTrace_3204394
  have hstable : (prefixWord ++ tailWord_3204394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204394).length < 2 ^ (prefixWord ++ tailWord_3204394).sum := by decide
  have hdescent : baseEnd_3204394 < baseStart_3204394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204435 : List Nat := [1, 1, 1, 2, 1, 1, 8, 2, 5]
def baseStart_3204435 : Nat := 118140960795 + 3204435 * 2 ^ 59
def prefixEnd_3204435 : Nat := 4983230072969 + 3 ^ 40 * 3204435 * 2
def baseEnd_3204435 : Nat := 365647862464505637116795

theorem tailTrace_3204435 : CollatzResearch.WordTrace tailWord_3204435 prefixEnd_3204435 365647862464505637116795 := by
  unfold tailWord_3204435
  simp only [CollatzResearch.WordTrace]
  refine ⟨116875346145886743772406759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77916897430591162514937839 116875346145886743772406759)
  ·
    refine ⟨175313019218830115658610139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116875346145886743772406759 175313019218830115658610139)
    ·
      refine ⟨262969528828245173487915209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175313019218830115658610139 262969528828245173487915209)
      ·
        refine ⟨197227146621183880115936407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262969528828245173487915209 197227146621183880115936407)
        ·
          refine ⟨295840719931775820173904611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197227146621183880115936407 295840719931775820173904611)
          ·
            refine ⟨443761079897663730260856917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295840719931775820173904611 443761079897663730260856917)
            ·
              refine ⟨5200325155050746838994417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 443761079897663730260856917 5200325155050746838994417)
              ·
                refine ⟨3900243866288060129245813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5200325155050746838994417 3900243866288060129245813)
                ·
                  refine ⟨365647862464505637116795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3900243866288060129245813 365647862464505637116795)
                  ·
                    rfl

theorem cell22_3204435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 5].length) (baseStart_3204435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3204435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3204435 prefixEnd_3204435 := by exact prefixLift 3204435
  have htrace : WordTrace (prefixWord ++ tailWord_3204435) baseStart_3204435 baseEnd_3204435 := by
    simpa [prefixWord, tailWord_3204435, baseEnd_3204435] using wordTrace_append hprefix tailTrace_3204435
  have hstable : (prefixWord ++ tailWord_3204435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204435).length < 2 ^ (prefixWord ++ tailWord_3204435).sum := by decide
  have hdescent : baseEnd_3204435 < baseStart_3204435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204439 : List Nat := [1, 1, 3, 2, 3, 3, 1, 4, 1, 3]
def baseStart_3204439 : Nat := 118140960795 + 3204439 * 2 ^ 59
def prefixEnd_3204439 : Nat := 4983230072969 + 3 ^ 40 * 3204439 * 2
def baseEnd_3204439 : Nat := 1096944956675262234250373

theorem tailTrace_3204439 : CollatzResearch.WordTrace tailWord_3204439 prefixEnd_3204439 1096944956675262234250373 := by
  unfold tailWord_3204439
  simp only [CollatzResearch.WordTrace]
  refine ⟨116875492037872252455552371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77916994691914834970368247 116875492037872252455552371)
  ·
    refine ⟨175313238056808378683328557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116875492037872252455552371 175313238056808378683328557)
    ·
      refine ⟨65742464271303142006248209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175313238056808378683328557 65742464271303142006248209)
      ·
        refine ⟨49306848203477356504686157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65742464271303142006248209 49306848203477356504686157)
        ·
          refine ⟨18490068076304008689257309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49306848203477356504686157 18490068076304008689257309)
          ·
            refine ⟨6933775528614003258471491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18490068076304008689257309 6933775528614003258471491)
            ·
              refine ⟨10400663292921004887707237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6933775528614003258471491 10400663292921004887707237)
              ·
                refine ⟨1950124367422688416445107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10400663292921004887707237 1950124367422688416445107)
                ·
                  refine ⟨2925186551134032624667661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1950124367422688416445107 2925186551134032624667661)
                  ·
                    refine ⟨1096944956675262234250373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2925186551134032624667661 1096944956675262234250373)
                    ·
                      rfl

theorem cell22_3204439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 4, 1, 3].length) (baseStart_3204439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3204439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3204439 prefixEnd_3204439 := by exact prefixLift 3204439
  have htrace : WordTrace (prefixWord ++ tailWord_3204439) baseStart_3204439 baseEnd_3204439 := by
    simpa [prefixWord, tailWord_3204439, baseEnd_3204439] using wordTrace_append hprefix tailTrace_3204439
  have hstable : (prefixWord ++ tailWord_3204439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204439).length < 2 ^ (prefixWord ++ tailWord_3204439).sum := by decide
  have hdescent : baseEnd_3204439 < baseStart_3204439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204465 : List Nat := [1, 2, 2, 2, 1, 2, 4, 1, 3, 4]
def baseStart_3204465 : Nat := 118140960795 + 3204465 * 2 ^ 59
def prefixEnd_3204465 : Nat := 4983230072969 + 3 ^ 40 * 3204465 * 2
def baseEnd_3204465 : Nat := 1096953857006606833100293

theorem tailTrace_3204465 : CollatzResearch.WordTrace tailWord_3204465 prefixEnd_3204465 1096953857006606833100293 := by
  unfold tailWord_3204465
  simp only [CollatzResearch.WordTrace]
  refine ⟨116876440335778058895998849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77917626890518705930665899 116876440335778058895998849)
  ·
    refine ⟨87657330251833544171999137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116876440335778058895998849 87657330251833544171999137)
    ·
      refine ⟨65742997688875158128999353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87657330251833544171999137 65742997688875158128999353)
      ·
        refine ⟨49307248266656368596749515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65742997688875158128999353 49307248266656368596749515)
        ·
          refine ⟨73960872399984552895124273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49307248266656368596749515 73960872399984552895124273)
          ·
            refine ⟨55470654299988414671343205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73960872399984552895124273 55470654299988414671343205)
            ·
              refine ⟨10400747681247827750876851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55470654299988414671343205 10400747681247827750876851)
              ·
                refine ⟨15601121521871741626315277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10400747681247827750876851 15601121521871741626315277)
                ·
                  refine ⟨5850420570701903109868229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15601121521871741626315277 5850420570701903109868229)
                  ·
                    refine ⟨1096953857006606833100293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5850420570701903109868229 1096953857006606833100293)
                    ·
                      rfl

theorem cell22_3204465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_3204465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3204465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3204465 prefixEnd_3204465 := by exact prefixLift 3204465
  have htrace : WordTrace (prefixWord ++ tailWord_3204465) baseStart_3204465 baseEnd_3204465 := by
    simpa [prefixWord, tailWord_3204465, baseEnd_3204465] using wordTrace_append hprefix tailTrace_3204465
  have hstable : (prefixWord ++ tailWord_3204465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204465).length < 2 ^ (prefixWord ++ tailWord_3204465).sum := by decide
  have hdescent : baseEnd_3204465 < baseStart_3204465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204664 : List Nat := [2, 1, 2, 1, 4, 3, 1, 1, 4, 3]
def baseStart_3204664 : Nat := 118140960795 + 3204664 * 2 ^ 59
def prefixEnd_3204664 : Nat := 4983230072969 + 3 ^ 40 * 3204664 * 2
def baseEnd_3204664 : Nat := 1097021978773436647374683

theorem tailTrace_3204664 : CollatzResearch.WordTrace tailWord_3204664 prefixEnd_3204664 1097021978773436647374683 := by
  unfold tailWord_3204664
  simp only [CollatzResearch.WordTrace]
  refine ⟨58441849231028557941246523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77922465641371410588328697 58441849231028557941246523)
  ·
    refine ⟨87662773846542836911869785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58441849231028557941246523 87662773846542836911869785)
    ·
      refine ⟨65747080384907127683902339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87662773846542836911869785 65747080384907127683902339)
      ·
        refine ⟨98620620577360691525853509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65747080384907127683902339 98620620577360691525853509)
        ·
          refine ⟨18491366358255129661097533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98620620577360691525853509 18491366358255129661097533)
          ·
            refine ⟨6934262384345673622911575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18491366358255129661097533 6934262384345673622911575)
            ·
              refine ⟨10401393576518510434367363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6934262384345673622911575 10401393576518510434367363)
              ·
                refine ⟨15602090364777765651551045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10401393576518510434367363 15602090364777765651551045)
                ·
                  refine ⟨2925391943395831059665821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15602090364777765651551045 2925391943395831059665821)
                  ·
                    refine ⟨1097021978773436647374683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2925391943395831059665821 1097021978773436647374683)
                    ·
                      rfl

theorem cell22_3204664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 4, 3].length) (baseStart_3204664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3204664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3204664 prefixEnd_3204664 := by exact prefixLift 3204664
  have htrace : WordTrace (prefixWord ++ tailWord_3204664) baseStart_3204664 baseEnd_3204664 := by
    simpa [prefixWord, tailWord_3204664, baseEnd_3204664] using wordTrace_append hprefix tailTrace_3204664
  have hstable : (prefixWord ++ tailWord_3204664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204664).length < 2 ^ (prefixWord ++ tailWord_3204664).sum := by decide
  have hdescent : baseEnd_3204664 < baseStart_3204664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204692 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 2, 7]
def baseStart_3204692 : Nat := 118140960795 + 3204692 * 2 ^ 59
def prefixEnd_3204692 : Nat := 4983230072969 + 3 ^ 40 * 3204692 * 2
def baseEnd_3204692 : Nat := 1097031563745653907674597

theorem tailTrace_3204692 : CollatzResearch.WordTrace tailWord_3204692 prefixEnd_3204692 1097031563745653907674597 := by
  unfold tailWord_3204692
  simp only [CollatzResearch.WordTrace]
  refine ⟨58442359852977838332256165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77923146470637117776341553 58442359852977838332256165)
  ·
    refine ⟨10957942472433344687298031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58442359852977838332256165 10957942472433344687298031)
    ·
      refine ⟨16436913708650017030947047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10957942472433344687298031 16436913708650017030947047)
      ·
        refine ⟨24655370562975025546420571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16436913708650017030947047 24655370562975025546420571)
        ·
          refine ⟨36983055844462538319630857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24655370562975025546420571 36983055844462538319630857)
          ·
            refine ⟨27737291883346903739723143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36983055844462538319630857 27737291883346903739723143)
            ·
              refine ⟨41605937825020355609584715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27737291883346903739723143 41605937825020355609584715)
              ·
                refine ⟨62408906737530533414377073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41605937825020355609584715 62408906737530533414377073)
                ·
                  refine ⟨46806680053147900060782805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62408906737530533414377073 46806680053147900060782805)
                  ·
                    refine ⟨1097031563745653907674597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46806680053147900060782805 1097031563745653907674597)
                    ·
                      rfl

theorem cell22_3204692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_3204692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3204692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3204692 prefixEnd_3204692 := by exact prefixLift 3204692
  have htrace : WordTrace (prefixWord ++ tailWord_3204692) baseStart_3204692 baseEnd_3204692 := by
    simpa [prefixWord, tailWord_3204692, baseEnd_3204692] using wordTrace_append hprefix tailTrace_3204692
  have hstable : (prefixWord ++ tailWord_3204692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204692).length < 2 ^ (prefixWord ++ tailWord_3204692).sum := by decide
  have hdescent : baseEnd_3204692 < baseStart_3204692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204799 : List Nat := [1, 1, 2, 2, 2, 3, 4, 1, 1, 5]
def baseStart_3204799 : Nat := 118140960795 + 3204799 * 2 ^ 59
def prefixEnd_3204799 : Nat := 4983230072969 + 3 ^ 40 * 3204799 * 2
def baseEnd_3204799 : Nat := 1097068192032341295249269

theorem tailTrace_3204799 : CollatzResearch.WordTrace tailWord_3204799 prefixEnd_3204799 1097068192032341295249269 := by
  unfold tailWord_3204799
  simp only [CollatzResearch.WordTrace]
  refine ⟨116888622316568033938657451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77925748211045355959104967 116888622316568033938657451)
  ·
    refine ⟨175332933474852050907986177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116888622316568033938657451 175332933474852050907986177)
    ·
      refine ⟨131499700106139038180989633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175332933474852050907986177 131499700106139038180989633)
      ·
        refine ⟨98624775079604278635742225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131499700106139038180989633 98624775079604278635742225)
        ·
          refine ⟨73968581309703208976806669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98624775079604278635742225 73968581309703208976806669)
          ·
            refine ⟨27738217991138703366302501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73968581309703208976806669 27738217991138703366302501)
            ·
              refine ⟨5200915873338506881181719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27738217991138703366302501 5200915873338506881181719)
              ·
                refine ⟨7801373810007760321772579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5200915873338506881181719 7801373810007760321772579)
                ·
                  refine ⟨11702060715011640482658869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7801373810007760321772579 11702060715011640482658869)
                  ·
                    refine ⟨1097068192032341295249269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11702060715011640482658869 1097068192032341295249269)
                    ·
                      rfl

theorem cell22_3204799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 5].length) (baseStart_3204799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3204799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3204799 prefixEnd_3204799 := by exact prefixLift 3204799
  have htrace : WordTrace (prefixWord ++ tailWord_3204799) baseStart_3204799 baseEnd_3204799 := by
    simpa [prefixWord, tailWord_3204799, baseEnd_3204799] using wordTrace_append hprefix tailTrace_3204799
  have hstable : (prefixWord ++ tailWord_3204799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204799).length < 2 ^ (prefixWord ++ tailWord_3204799).sum := by decide
  have hdescent : baseEnd_3204799 < baseStart_3204799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204814 : List Nat := [4, 1, 1, 1, 3, 1, 3, 1, 1, 6]
def baseStart_3204814 : Nat := 118140960795 + 3204814 * 2 ^ 59
def prefixEnd_3204814 : Nat := 4983230072969 + 3 ^ 40 * 3204814 * 2
def baseEnd_3204814 : Nat := 1097073326838886256124223

theorem tailTrace_3204814 : CollatzResearch.WordTrace tailWord_3204814 prefixEnd_3204814 1097073326838886256124223 := by
  unfold tailWord_3204814
  simp only [CollatzResearch.WordTrace]
  refine ⟨14611146176439211437556687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77926112941009127666968997 14611146176439211437556687)
  ·
    refine ⟨21916719264658817156335031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14611146176439211437556687 21916719264658817156335031)
    ·
      refine ⟨32875078896988225734502547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21916719264658817156335031 32875078896988225734502547)
      ·
        refine ⟨49312618345482338601753821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32875078896988225734502547 49312618345482338601753821)
        ·
          refine ⟨18492231879555876975657683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49312618345482338601753821 18492231879555876975657683)
          ·
            refine ⟨27738347819333815463486525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18492231879555876975657683 27738347819333815463486525)
            ·
              refine ⟨10401880432250180798807447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27738347819333815463486525 10401880432250180798807447)
              ·
                refine ⟨15602820648375271198211171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10401880432250180798807447 15602820648375271198211171)
                ·
                  refine ⟨23404230972562906797316757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15602820648375271198211171 23404230972562906797316757)
                  ·
                    refine ⟨1097073326838886256124223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23404230972562906797316757 1097073326838886256124223)
                    ·
                      rfl

theorem cell22_3204814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_3204814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3204814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3204814 prefixEnd_3204814 := by exact prefixLift 3204814
  have htrace : WordTrace (prefixWord ++ tailWord_3204814) baseStart_3204814 baseEnd_3204814 := by
    simpa [prefixWord, tailWord_3204814, baseEnd_3204814] using wordTrace_append hprefix tailTrace_3204814
  have hstable : (prefixWord ++ tailWord_3204814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204814).length < 2 ^ (prefixWord ++ tailWord_3204814).sum := by decide
  have hdescent : baseEnd_3204814 < baseStart_3204814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204818 : List Nat := [3, 2, 2, 2, 2, 2, 2, 3, 4]
def baseStart_3204818 : Nat := 118140960795 + 3204818 * 2 ^ 59
def prefixEnd_3204818 : Nat := 4983230072969 + 3 ^ 40 * 3204818 * 2
def baseEnd_3204818 : Nat := 365691565373543859674737

theorem tailTrace_3204818 : CollatzResearch.WordTrace tailWord_3204818 prefixEnd_3204818 365691565373543859674737 := by
  unfold tailWord_3204818
  simp only [CollatzResearch.WordTrace]
  refine ⟨29222328825874800045899777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77926210202332800122399405 29222328825874800045899777)
  ·
    refine ⟨21916746619406100034424833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29222328825874800045899777 21916746619406100034424833)
    ·
      refine ⟨16437559964554575025818625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21916746619406100034424833 16437559964554575025818625)
      ·
        refine ⟨12328169973415931269363969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16437559964554575025818625 12328169973415931269363969)
        ·
          refine ⟨9246127480061948452022977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12328169973415931269363969 9246127480061948452022977)
          ·
            refine ⟨6934595610046461339017233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9246127480061948452022977 6934595610046461339017233)
            ·
              refine ⟨5200946707534846004262925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6934595610046461339017233 5200946707534846004262925)
              ·
                refine ⟨1950355015325567251598597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5200946707534846004262925 1950355015325567251598597)
                ·
                  refine ⟨365691565373543859674737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1950355015325567251598597 365691565373543859674737)
                  ·
                    rfl

theorem cell22_3204818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_3204818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3204818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3204818 prefixEnd_3204818 := by exact prefixLift 3204818
  have htrace : WordTrace (prefixWord ++ tailWord_3204818) baseStart_3204818 baseEnd_3204818 := by
    simpa [prefixWord, tailWord_3204818, baseEnd_3204818] using wordTrace_append hprefix tailTrace_3204818
  have hstable : (prefixWord ++ tailWord_3204818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204818).length < 2 ^ (prefixWord ++ tailWord_3204818).sum := by decide
  have hdescent : baseEnd_3204818 < baseStart_3204818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204820 : List Nat := [2, 4, 1, 3, 1, 3, 2, 1, 1, 4]
def baseStart_3204820 : Nat := 118140960795 + 3204820 * 2 ^ 59
def prefixEnd_3204820 : Nat := 4983230072969 + 3 ^ 40 * 3204820 * 2
def baseEnd_3204820 : Nat := 1097075380761504240474205

theorem tailTrace_3204820 : CollatzResearch.WordTrace tailWord_3204820 prefixEnd_3204820 1097075380761504240474205 := by
  unfold tailWord_3204820
  simp only [CollatzResearch.WordTrace]
  refine ⟨58444694124745977262585957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77926258832994636350114609 58444694124745977262585957)
  ·
    refine ⟨10958380148389870736734867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58444694124745977262585957 10958380148389870736734867)
    ·
      refine ⟨16437570222584806105102301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10958380148389870736734867 16437570222584806105102301)
      ·
        refine ⟨6164088833469302289413363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16437570222584806105102301 6164088833469302289413363)
        ·
          refine ⟨9246133250203953434120045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6164088833469302289413363 9246133250203953434120045)
          ·
            refine ⟨3467299968826482537795017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9246133250203953434120045 3467299968826482537795017)
            ·
              refine ⟨2600474976619861903346263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3467299968826482537795017 2600474976619861903346263)
              ·
                refine ⟨3900712464929792855019395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2600474976619861903346263 3900712464929792855019395)
                ·
                  refine ⟨5851068697394689282529093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3900712464929792855019395 5851068697394689282529093)
                  ·
                    refine ⟨1097075380761504240474205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5851068697394689282529093 1097075380761504240474205)
                    ·
                      rfl

theorem cell22_3204820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_3204820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3204820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3204820 prefixEnd_3204820 := by exact prefixLift 3204820
  have htrace : WordTrace (prefixWord ++ tailWord_3204820) baseStart_3204820 baseEnd_3204820 := by
    simpa [prefixWord, tailWord_3204820, baseEnd_3204820] using wordTrace_append hprefix tailTrace_3204820
  have hstable : (prefixWord ++ tailWord_3204820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204820).length < 2 ^ (prefixWord ++ tailWord_3204820).sum := by decide
  have hdescent : baseEnd_3204820 < baseStart_3204820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204874 : List Nat := [3, 1, 2, 2, 1, 3, 1, 2, 7]
def baseStart_3204874 : Nat := 118140960795 + 3204874 * 2 ^ 59
def prefixEnd_3204874 : Nat := 4983230072969 + 3 ^ 40 * 3204874 * 2
def baseEnd_3204874 : Nat := 365697955355022033208013

theorem tailTrace_3204874 : CollatzResearch.WordTrace tailWord_3204874 prefixEnd_3204874 365697955355022033208013 := by
  unfold tailWord_3204874
  simp only [CollatzResearch.WordTrace]
  refine ⟨29222839447824080436909419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77927571860864214498425117 29222839447824080436909419)
  ·
    refine ⟨43834259171736120655364129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29222839447824080436909419 43834259171736120655364129)
    ·
      refine ⟨32875694378802090491523097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43834259171736120655364129 32875694378802090491523097)
      ·
        refine ⟨24656770784101567868642323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32875694378802090491523097 24656770784101567868642323)
        ·
          refine ⟨36985156176152351802963485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24656770784101567868642323 36985156176152351802963485)
          ·
            refine ⟨13869433566057131926111307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36985156176152351802963485 13869433566057131926111307)
            ·
              refine ⟨20804150349085697889166961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13869433566057131926111307 20804150349085697889166961)
              ·
                refine ⟨15603112761814273416875221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20804150349085697889166961 15603112761814273416875221)
                ·
                  refine ⟨365697955355022033208013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15603112761814273416875221 365697955355022033208013)
                  ·
                    rfl

theorem cell22_3204874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 7].length) (baseStart_3204874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3204874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3204874 prefixEnd_3204874 := by exact prefixLift 3204874
  have htrace : WordTrace (prefixWord ++ tailWord_3204874) baseStart_3204874 baseEnd_3204874 := by
    simpa [prefixWord, tailWord_3204874, baseEnd_3204874] using wordTrace_append hprefix tailTrace_3204874
  have hstable : (prefixWord ++ tailWord_3204874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204874).length < 2 ^ (prefixWord ++ tailWord_3204874).sum := by decide
  have hdescent : baseEnd_3204874 < baseStart_3204874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204895 : List Nat := [1, 1, 2, 4, 2, 1, 5, 2, 1, 3]
def baseStart_3204895 : Nat := 118140960795 + 3204895 * 2 ^ 59
def prefixEnd_3204895 : Nat := 4983230072969 + 3 ^ 40 * 3204895 * 2
def baseEnd_3204895 : Nat := 1097101054794229044848975

theorem tailTrace_3204895 : CollatzResearch.WordTrace tailWord_3204895 prefixEnd_3204895 1097101054794229044848975 := by
  unfold tailWord_3204895
  simp only [CollatzResearch.WordTrace]
  refine ⟨116892123724220242334152139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77928082482813494889434759 116892123724220242334152139)
  ·
    refine ⟨175338185586330363501228209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116892123724220242334152139 175338185586330363501228209)
    ·
      refine ⟨131503639189747772625921157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175338185586330363501228209 131503639189747772625921157)
      ·
        refine ⟨24656932348077707367360217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131503639189747772625921157 24656932348077707367360217)
        ·
          refine ⟨18492699261058280525520163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24656932348077707367360217 18492699261058280525520163)
          ·
            refine ⟨27739048891587420788280245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18492699261058280525520163 27739048891587420788280245)
            ·
              refine ⟨2600535833586320698901273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27739048891587420788280245 2600535833586320698901273)
              ·
                refine ⟨1950401875189740524175955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2600535833586320698901273 1950401875189740524175955)
                ·
                  refine ⟨2925602812784610786263933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1950401875189740524175955 2925602812784610786263933)
                  ·
                    refine ⟨1097101054794229044848975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2925602812784610786263933 1097101054794229044848975)
                    ·
                      rfl

theorem cell22_3204895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 2, 1, 3].length) (baseStart_3204895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3204895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3204895 prefixEnd_3204895 := by exact prefixLift 3204895
  have htrace : WordTrace (prefixWord ++ tailWord_3204895) baseStart_3204895 baseEnd_3204895 := by
    simpa [prefixWord, tailWord_3204895, baseEnd_3204895] using wordTrace_append hprefix tailTrace_3204895
  have hstable : (prefixWord ++ tailWord_3204895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204895).length < 2 ^ (prefixWord ++ tailWord_3204895).sum := by decide
  have hdescent : baseEnd_3204895 < baseStart_3204895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204908 : List Nat := [2, 2, 1, 1, 1, 7, 2, 1, 5]
def baseStart_3204908 : Nat := 118140960795 + 3204908 * 2 ^ 59
def prefixEnd_3204908 : Nat := 4983230072969 + 3 ^ 40 * 3204908 * 2
def baseEnd_3204908 : Nat := 365701834986633781424645

theorem tailTrace_3204908 : CollatzResearch.WordTrace tailWord_3204908 prefixEnd_3204908 365701834986633781424645 := by
  unfold tailWord_3204908
  simp only [CollatzResearch.WordTrace]
  refine ⟨58446298936586572777187689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77928398582115430369583585 58446298936586572777187689)
  ·
    refine ⟨43834724202439929582890767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58446298936586572777187689 43834724202439929582890767)
    ·
      refine ⟨65752086303659894374336151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43834724202439929582890767 65752086303659894374336151)
      ·
        refine ⟨98628129455489841561504227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65752086303659894374336151 98628129455489841561504227)
        ·
          refine ⟨147942194183234762342256341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98628129455489841561504227 147942194183234762342256341)
          ·
            refine ⟨3467395176169564742396633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 147942194183234762342256341 3467395176169564742396633)
            ·
              refine ⟨2600546382127173556797475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3467395176169564742396633 2600546382127173556797475)
              ·
                refine ⟨3900819573190760335196213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2600546382127173556797475 3900819573190760335196213)
                ·
                  refine ⟨365701834986633781424645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3900819573190760335196213 365701834986633781424645)
                  ·
                    rfl

theorem cell22_3204908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 5].length) (baseStart_3204908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3204908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3204908 prefixEnd_3204908 := by exact prefixLift 3204908
  have htrace : WordTrace (prefixWord ++ tailWord_3204908) baseStart_3204908 baseEnd_3204908 := by
    simpa [prefixWord, tailWord_3204908, baseEnd_3204908] using wordTrace_append hprefix tailTrace_3204908
  have hstable : (prefixWord ++ tailWord_3204908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204908).length < 2 ^ (prefixWord ++ tailWord_3204908).sum := by decide
  have hdescent : baseEnd_3204908 < baseStart_3204908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204938 : List Nat := [3, 1, 2, 1, 1, 1, 7, 1, 1, 4]
def baseStart_3204938 : Nat := 118140960795 + 3204938 * 2 ^ 59
def prefixEnd_3204938 : Nat := 4983230072969 + 3 ^ 40 * 3204938 * 2
def baseEnd_3204938 : Nat := 1097115774572991266023843

theorem tailTrace_3204938 : CollatzResearch.WordTrace tailWord_3204938 prefixEnd_3204938 1097115774572991266023843 := by
  unfold tailWord_3204938
  simp only [CollatzResearch.WordTrace]
  refine ⟨29223423015766115169491867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77929128042042973785311645 29223423015766115169491867)
  ·
    refine ⟨43835134523649172754237801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29223423015766115169491867 43835134523649172754237801)
    ·
      refine ⟨32876350892736879565678351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43835134523649172754237801 32876350892736879565678351)
      ·
        refine ⟨49314526339105319348517527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32876350892736879565678351 49314526339105319348517527)
        ·
          refine ⟨73971789508657979022776291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49314526339105319348517527 73971789508657979022776291)
          ·
            refine ⟨110957684262986968534164437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73971789508657979022776291 110957684262986968534164437)
            ·
              refine ⟨2600570724913757075019479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 110957684262986968534164437 2600570724913757075019479)
              ·
                refine ⟨3900856087370635612529219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2600570724913757075019479 3900856087370635612529219)
                ·
                  refine ⟨5851284131055953418793829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3900856087370635612529219 5851284131055953418793829)
                  ·
                    refine ⟨1097115774572991266023843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5851284131055953418793829 1097115774572991266023843)
                    ·
                      rfl

theorem cell22_3204938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 1, 4].length) (baseStart_3204938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3204938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3204938 prefixEnd_3204938 := by exact prefixLift 3204938
  have htrace : WordTrace (prefixWord ++ tailWord_3204938) baseStart_3204938 baseEnd_3204938 := by
    simpa [prefixWord, tailWord_3204938, baseEnd_3204938] using wordTrace_append hprefix tailTrace_3204938
  have hstable : (prefixWord ++ tailWord_3204938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204938).length < 2 ^ (prefixWord ++ tailWord_3204938).sum := by decide
  have hdescent : baseEnd_3204938 < baseStart_3204938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204968 : List Nat := [2, 1, 4, 2, 1, 1, 1, 5, 2, 3]
def baseStart_3204968 : Nat := 118140960795 + 3204968 * 2 ^ 59
def prefixEnd_3204968 : Nat := 4983230072969 + 3 ^ 40 * 3204968 * 2
def baseEnd_3204968 : Nat := 1097126044186081187773751

theorem tailTrace_3204968 : CollatzResearch.WordTrace tailWord_3204968 prefixEnd_3204968 1097126044186081187773751 := by
  unfold tailWord_3204968
  simp only [CollatzResearch.WordTrace]
  refine ⟨58447393126477887900779779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77929857501970517201039705 58447393126477887900779779)
  ·
    refine ⟨87671089689716831851169669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58447393126477887900779779 87671089689716831851169669)
    ·
      refine ⟨16438329316821905972094313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87671089689716831851169669 16438329316821905972094313)
      ·
        refine ⟨12328746987616429479070735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16438329316821905972094313 12328746987616429479070735)
        ·
          refine ⟨18493120481424644218606103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12328746987616429479070735 18493120481424644218606103)
          ·
            refine ⟨27739680722136966327909155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18493120481424644218606103 27739680722136966327909155)
            ·
              refine ⟨41609521083205449491863733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27739680722136966327909155 41609521083205449491863733)
              ·
                refine ⟨3900892601550510889862225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41609521083205449491863733 3900892601550510889862225)
                ·
                  refine ⟨2925669451162883167396669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3900892601550510889862225 2925669451162883167396669)
                  ·
                    refine ⟨1097126044186081187773751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2925669451162883167396669 1097126044186081187773751)
                    ·
                      rfl

theorem cell22_3204968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_3204968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3204968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3204968 prefixEnd_3204968 := by exact prefixLift 3204968
  have htrace : WordTrace (prefixWord ++ tailWord_3204968) baseStart_3204968 baseEnd_3204968 := by
    simpa [prefixWord, tailWord_3204968, baseEnd_3204968] using wordTrace_append hprefix tailTrace_3204968
  have hstable : (prefixWord ++ tailWord_3204968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204968).length < 2 ^ (prefixWord ++ tailWord_3204968).sum := by decide
  have hdescent : baseEnd_3204968 < baseStart_3204968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205002 : List Nat := [3, 1, 2, 4, 2, 2, 1, 2, 2, 3]
def baseStart_3205002 : Nat := 118140960795 + 3205002 * 2 ^ 59
def prefixEnd_3205002 : Nat := 4983230072969 + 3 ^ 40 * 3205002 * 2
def baseEnd_3205002 : Nat := 1097137683080916432423647

theorem tailTrace_3205002 : CollatzResearch.WordTrace tailWord_3205002 prefixEnd_3205002 1097137683080916432423647 := by
  unfold tailWord_3205002
  simp only [CollatzResearch.WordTrace]
  refine ⟨29224006583708149902074315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77930684223221733072198173 29224006583708149902074315)
  ·
    refine ⟨43836009875562224853111473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29224006583708149902074315 43836009875562224853111473)
    ·
      refine ⟨32877007406671668639833605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43836009875562224853111473 32877007406671668639833605)
      ·
        refine ⟨6164438888750937869968801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32877007406671668639833605 6164438888750937869968801)
        ·
          refine ⟨4623329166563203402476601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6164438888750937869968801 4623329166563203402476601)
          ·
            refine ⟨3467496874922402551857451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4623329166563203402476601 3467496874922402551857451)
            ·
              refine ⟨5201245312383603827786177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3467496874922402551857451 5201245312383603827786177)
              ·
                refine ⟨3900933984287702870839633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5201245312383603827786177 3900933984287702870839633)
                ·
                  refine ⟨2925700488215777153129725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3900933984287702870839633 2925700488215777153129725)
                  ·
                    refine ⟨1097137683080916432423647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2925700488215777153129725 1097137683080916432423647)
                    ·
                      rfl

theorem cell22_3205002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_3205002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3205002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3205002 prefixEnd_3205002 := by exact prefixLift 3205002
  have htrace : WordTrace (prefixWord ++ tailWord_3205002) baseStart_3205002 baseEnd_3205002 := by
    simpa [prefixWord, tailWord_3205002, baseEnd_3205002] using wordTrace_append hprefix tailTrace_3205002
  have hstable : (prefixWord ++ tailWord_3205002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205002).length < 2 ^ (prefixWord ++ tailWord_3205002).sum := by decide
  have hdescent : baseEnd_3205002 < baseStart_3205002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205013 : List Nat := [1, 3, 2, 1, 1, 3, 4, 1, 3, 3]
def baseStart_3205013 : Nat := 118140960795 + 3205013 * 2 ^ 59
def prefixEnd_3205013 : Nat := 4983230072969 + 3 ^ 40 * 3205013 * 2
def baseEnd_3205013 : Nat := 1097141448605716070398613

theorem tailTrace_3205013 : CollatzResearch.WordTrace tailWord_3205013 prefixEnd_3205013 1097141448605716070398613 := by
  unfold tailWord_3205013
  simp only [CollatzResearch.WordTrace]
  refine ⟨116896427537792748486947693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77930951691861832324631795 116896427537792748486947693)
  ·
    refine ⟨43836160326672280682605385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116896427537792748486947693 43836160326672280682605385)
    ·
      refine ⟨32877120245004210511954039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43836160326672280682605385 32877120245004210511954039)
      ·
        refine ⟨49315680367506315767931059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32877120245004210511954039 49315680367506315767931059)
        ·
          refine ⟨73973520551259473651896589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49315680367506315767931059 73973520551259473651896589)
          ·
            refine ⟨27740070206722302619461221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73973520551259473651896589 27740070206722302619461221)
            ·
              refine ⟨5201263163760431741148979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27740070206722302619461221 5201263163760431741148979)
              ·
                refine ⟨7801894745640647611723469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5201263163760431741148979 7801894745640647611723469)
                ·
                  refine ⟨2925710529615242854396301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7801894745640647611723469 2925710529615242854396301)
                  ·
                    refine ⟨1097141448605716070398613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2925710529615242854396301 1097141448605716070398613)
                    ·
                      rfl

theorem cell22_3205013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_3205013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3205013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3205013 prefixEnd_3205013 := by exact prefixLift 3205013
  have htrace : WordTrace (prefixWord ++ tailWord_3205013) baseStart_3205013 baseEnd_3205013 := by
    simpa [prefixWord, tailWord_3205013, baseEnd_3205013] using wordTrace_append hprefix tailTrace_3205013
  have hstable : (prefixWord ++ tailWord_3205013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205013).length < 2 ^ (prefixWord ++ tailWord_3205013).sum := by decide
  have hdescent : baseEnd_3205013 < baseStart_3205013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205032 : List Nat := [2, 1, 6, 2, 1, 2, 2, 6]
def baseStart_3205032 : Nat := 118140960795 + 3205032 * 2 ^ 59
def prefixEnd_3205032 : Nat := 4983230072969 + 3 ^ 40 * 3205032 * 2
def baseEnd_3205032 : Nat := 121905328077111817130395

theorem tailTrace_3205032 : CollatzResearch.WordTrace tailWord_3205032 prefixEnd_3205032 121905328077111817130395 := by
  unfold tailWord_3205032
  simp only [CollatzResearch.WordTrace]
  refine ⟨58448560262361957365944675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77931413683149276487926233 58448560262361957365944675)
  ·
    refine ⟨87672840393542936048917013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58448560262361957365944675 87672840393542936048917013)
    ·
      refine ⟨4109664393447325127292985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 87672840393542936048917013 4109664393447325127292985)
      ·
        refine ⟨3082248295085493845469739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4109664393447325127292985 3082248295085493845469739)
        ·
          refine ⟨4623372442628240768204609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3082248295085493845469739 4623372442628240768204609)
          ·
            refine ⟨3467529331971180576153457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4623372442628240768204609 3467529331971180576153457)
            ·
              refine ⟨2600646998978385432115093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3467529331971180576153457 2600646998978385432115093)
              ·
                refine ⟨121905328077111817130395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2600646998978385432115093 121905328077111817130395)
                ·
                  rfl

theorem cell22_3205032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 6].length) (baseStart_3205032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3205032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3205032 prefixEnd_3205032 := by exact prefixLift 3205032
  have htrace : WordTrace (prefixWord ++ tailWord_3205032) baseStart_3205032 baseEnd_3205032 := by
    simpa [prefixWord, tailWord_3205032, baseEnd_3205032] using wordTrace_append hprefix tailTrace_3205032
  have hstable : (prefixWord ++ tailWord_3205032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205032).length < 2 ^ (prefixWord ++ tailWord_3205032).sum := by decide
  have hdescent : baseEnd_3205032 < baseStart_3205032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205298 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 1, 8]
def baseStart_3205298 : Nat := 118140960795 + 3205298 * 2 ^ 59
def prefixEnd_3205298 : Nat := 4983230072969 + 3 ^ 40 * 3205298 * 2
def baseEnd_3205298 : Nat := 1097239009930070327022739

theorem tailTrace_3205298 : CollatzResearch.WordTrace tailWord_3205298 prefixEnd_3205298 1097239009930070327022739 := by
  unfold tailWord_3205298
  simp only [CollatzResearch.WordTrace]
  refine ⟨29226705585440060540268137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77937881561173494774048365 29226705585440060540268137)
  ·
    refine ⟨21920029189080045405201103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29226705585440060540268137 21920029189080045405201103)
    ·
      refine ⟨32880043783620068107801655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21920029189080045405201103 32880043783620068107801655)
      ·
        refine ⟨49320065675430102161702483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32880043783620068107801655 49320065675430102161702483)
        ·
          refine ⟨73980098513145153242553725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49320065675430102161702483 73980098513145153242553725)
          ·
            refine ⟨27742536942429432465957647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73980098513145153242553725 27742536942429432465957647)
            ·
              refine ⟨41613805413644148698936471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27742536942429432465957647 41613805413644148698936471)
              ·
                refine ⟨62420708120466223048404707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41613805413644148698936471 62420708120466223048404707)
                ·
                  refine ⟨93631062180699334572607061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62420708120466223048404707 93631062180699334572607061)
                  ·
                    refine ⟨1097239009930070327022739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93631062180699334572607061 1097239009930070327022739)
                    ·
                      rfl

theorem cell22_3205298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_3205298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3205298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3205298 prefixEnd_3205298 := by exact prefixLift 3205298
  have htrace : WordTrace (prefixWord ++ tailWord_3205298) baseStart_3205298 baseEnd_3205298 := by
    simpa [prefixWord, tailWord_3205298, baseEnd_3205298] using wordTrace_append hprefix tailTrace_3205298
  have hstable : (prefixWord ++ tailWord_3205298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205298).length < 2 ^ (prefixWord ++ tailWord_3205298).sum := by decide
  have hdescent : baseEnd_3205298 < baseStart_3205298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205347 : List Nat := [1, 1, 1, 8, 1, 1, 1, 1, 7]
def baseStart_3205347 : Nat := 118140960795 + 3205347 * 2 ^ 59
def prefixEnd_3205347 : Nat := 4983230072969 + 3 ^ 40 * 3205347 * 2
def baseEnd_3205347 : Nat := 365751927877150177515863

theorem tailTrace_3205347 : CollatzResearch.WordTrace tailWord_3205347 prefixEnd_3205347 365751927877150177515863 := by
  unfold tailWord_3205347
  simp only [CollatzResearch.WordTrace]
  refine ⟨116908609518582723529606295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77939073012388482353070863 116908609518582723529606295)
  ·
    refine ⟨175362914277874085294409443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116908609518582723529606295 175362914277874085294409443)
    ·
      refine ⟨263044371416811127941614165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175362914277874085294409443 263044371416811127941614165)
      ·
        refine ⟨3082551227540755405565791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 263044371416811127941614165 3082551227540755405565791)
        ·
          refine ⟨4623826841311133108348687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3082551227540755405565791 4623826841311133108348687)
          ·
            refine ⟨6935740261966699662523031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4623826841311133108348687 6935740261966699662523031)
            ·
              refine ⟨10403610392950049493784547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6935740261966699662523031 10403610392950049493784547)
              ·
                refine ⟨15605415589425074240676821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10403610392950049493784547 15605415589425074240676821)
                ·
                  refine ⟨365751927877150177515863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15605415589425074240676821 365751927877150177515863)
                  ·
                    rfl

theorem cell22_3205347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 7].length) (baseStart_3205347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3205347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3205347 prefixEnd_3205347 := by exact prefixLift 3205347
  have htrace : WordTrace (prefixWord ++ tailWord_3205347) baseStart_3205347 baseEnd_3205347 := by
    simpa [prefixWord, tailWord_3205347, baseEnd_3205347] using wordTrace_append hprefix tailTrace_3205347
  have hstable : (prefixWord ++ tailWord_3205347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205347).length < 2 ^ (prefixWord ++ tailWord_3205347).sum := by decide
  have hdescent : baseEnd_3205347 < baseStart_3205347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205377 : List Nat := [1, 2, 4, 1, 1, 2, 4, 2, 1, 4]
def baseStart_3205377 : Nat := 118140960795 + 3205377 * 2 ^ 59
def prefixEnd_3205377 : Nat := 4983230072969 + 3 ^ 40 * 3205377 * 2
def baseEnd_3205377 : Nat := 1097266053244540454297497

theorem tailTrace_3205377 : CollatzResearch.WordTrace tailWord_3205377 prefixEnd_3205377 1097266053244540454297497 := by
  unfold tailWord_3205377
  simp only [CollatzResearch.WordTrace]
  refine ⟨116909703708474038653198385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77939802472316025768798923 116909703708474038653198385)
  ·
    refine ⟨87682277781355528989898789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116909703708474038653198385 87682277781355528989898789)
    ·
      refine ⟨16440427084004161685606023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87682277781355528989898789 16440427084004161685606023)
      ·
        refine ⟨24660640626006242528409035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16440427084004161685606023 24660640626006242528409035)
        ·
          refine ⟨36990960939009363792613553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24660640626006242528409035 36990960939009363792613553)
          ·
            refine ⟨27743220704257022844460165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36990960939009363792613553 27743220704257022844460165)
            ·
              refine ⟨5201853882048191783336281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27743220704257022844460165 5201853882048191783336281)
              ·
                refine ⟨3901390411536143837502211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5201853882048191783336281 3901390411536143837502211)
                ·
                  refine ⟨5852085617304215756253317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3901390411536143837502211 5852085617304215756253317)
                  ·
                    refine ⟨1097266053244540454297497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5852085617304215756253317 1097266053244540454297497)
                    ·
                      rfl

theorem cell22_3205377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_3205377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3205377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3205377 prefixEnd_3205377 := by exact prefixLift 3205377
  have htrace : WordTrace (prefixWord ++ tailWord_3205377) baseStart_3205377 baseEnd_3205377 := by
    simpa [prefixWord, tailWord_3205377, baseEnd_3205377] using wordTrace_append hprefix tailTrace_3205377
  have hstable : (prefixWord ++ tailWord_3205377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205377).length < 2 ^ (prefixWord ++ tailWord_3205377).sum := by decide
  have hdescent : baseEnd_3205377 < baseStart_3205377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205390 : List Nat := [4, 1, 1, 2, 1, 2, 2, 1, 3, 5]
def baseStart_3205390 : Nat := 118140960795 + 3205390 * 2 ^ 59
def prefixEnd_3205390 : Nat := 4983230072969 + 3 ^ 40 * 3205390 * 2
def baseEnd_3205390 : Nat := 1097270503410212753722457

theorem tailTrace_3205390 : CollatzResearch.WordTrace tailWord_3205390 prefixEnd_3205390 1097270503410212753722457 := by
  unfold tailWord_3205390
  simp only [CollatzResearch.WordTrace]
  refine ⟨14613772232178367734177703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77940118571617961248947749 14613772232178367734177703)
  ·
    refine ⟨21920658348267551601266555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14613772232178367734177703 21920658348267551601266555)
    ·
      refine ⟨32880987522401327401899833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21920658348267551601266555 32880987522401327401899833)
      ·
        refine ⟨24660740641800995551424875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32880987522401327401899833 24660740641800995551424875)
        ·
          refine ⟨36991110962701493327137313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24660740641800995551424875 36991110962701493327137313)
          ·
            refine ⟨27743333222026119995352985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36991110962701493327137313 27743333222026119995352985)
            ·
              refine ⟨20807499916519589996514739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27743333222026119995352985 20807499916519589996514739)
              ·
                refine ⟨31211249874779384994772109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20807499916519589996514739 31211249874779384994772109)
                ·
                  refine ⟨11704218703042269373039541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31211249874779384994772109 11704218703042269373039541)
                  ·
                    refine ⟨1097270503410212753722457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11704218703042269373039541 1097270503410212753722457)
                    ·
                      rfl

theorem cell22_3205390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_3205390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3205390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3205390 prefixEnd_3205390 := by exact prefixLift 3205390
  have htrace : WordTrace (prefixWord ++ tailWord_3205390) baseStart_3205390 baseEnd_3205390 := by
    simpa [prefixWord, tailWord_3205390, baseEnd_3205390] using wordTrace_append hprefix tailTrace_3205390
  have hstable : (prefixWord ++ tailWord_3205390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205390).length < 2 ^ (prefixWord ++ tailWord_3205390).sum := by decide
  have hdescent : baseEnd_3205390 < baseStart_3205390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205403 : List Nat := [1, 1, 1, 1, 1, 1, 16]
def baseStart_3205403 : Nat := 118140960795 + 3205403 * 2 ^ 59
def prefixEnd_3205403 : Nat := 4983230072969 + 3 ^ 40 * 3205403 * 2
def baseEnd_3205403 : Nat := 40639813095403150116571

theorem tailTrace_3205403 : CollatzResearch.WordTrace tailWord_3205403 prefixEnd_3205403 40639813095403150116571 := by
  unfold tailWord_3205403
  simp only [CollatzResearch.WordTrace]
  refine ⟨116910652006379845093644863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77940434670919896729096575 116910652006379845093644863)
  ·
    refine ⟨175365978009569767640467295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116910652006379845093644863 175365978009569767640467295)
    ·
      refine ⟨263048967014354651460700943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175365978009569767640467295 263048967014354651460700943)
      ·
        refine ⟨394573450521531977191051415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263048967014354651460700943 394573450521531977191051415)
        ·
          refine ⟨591860175782297965786577123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394573450521531977191051415 591860175782297965786577123)
          ·
            refine ⟨887790263673446948679865685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591860175782297965786577123 887790263673446948679865685)
            ·
              refine ⟨40639813095403150116571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 16 887790263673446948679865685 40639813095403150116571)
              ·
                rfl

theorem cell22_3205403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 16].length) (baseStart_3205403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3205403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3205403 prefixEnd_3205403 := by exact prefixLift 3205403
  have htrace : WordTrace (prefixWord ++ tailWord_3205403) baseStart_3205403 baseEnd_3205403 := by
    simpa [prefixWord, tailWord_3205403, baseEnd_3205403] using wordTrace_append hprefix tailTrace_3205403
  have hstable : (prefixWord ++ tailWord_3205403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205403).length < 2 ^ (prefixWord ++ tailWord_3205403).sum := by decide
  have hdescent : baseEnd_3205403 < baseStart_3205403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205407 : List Nat := [1, 1, 2, 4, 3, 1, 2, 1, 4, 3]
def baseStart_3205407 : Nat := 118140960795 + 3205407 * 2 ^ 59
def prefixEnd_3205407 : Nat := 4983230072969 + 3 ^ 40 * 3205407 * 2
def baseEnd_3205407 : Nat := 1097276322857630376047405

theorem tailTrace_3205407 : CollatzResearch.WordTrace tailWord_3205407 prefixEnd_3205407 1097276322857630376047405 := by
  unfold tailWord_3205407
  simp only [CollatzResearch.WordTrace]
  refine ⟨116910797898365353776790475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77940531932243569184526983 116910797898365353776790475)
  ·
    refine ⟨175366196847548030665185713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116910797898365353776790475 175366196847548030665185713)
    ·
      refine ⟨131524647635661022998889285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175366196847548030665185713 131524647635661022998889285)
      ·
        refine ⟨24660871431686441812291741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131524647635661022998889285 24660871431686441812291741)
        ·
          refine ⟨9247826786882415679609403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24660871431686441812291741 9247826786882415679609403)
          ·
            refine ⟨13871740180323623519414105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9247826786882415679609403 13871740180323623519414105)
            ·
              refine ⟨10403805135242717639560579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13871740180323623519414105 10403805135242717639560579)
              ·
                refine ⟨15605707702864076459340869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10403805135242717639560579 15605707702864076459340869)
                ·
                  refine ⟨2926070194287014336126413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15605707702864076459340869 2926070194287014336126413)
                  ·
                    refine ⟨1097276322857630376047405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2926070194287014336126413 1097276322857630376047405)
                    ·
                      rfl

theorem cell22_3205407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 4, 3].length) (baseStart_3205407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3205407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3205407 prefixEnd_3205407 := by exact prefixLift 3205407
  have htrace : WordTrace (prefixWord ++ tailWord_3205407) baseStart_3205407 baseEnd_3205407 := by
    simpa [prefixWord, tailWord_3205407, baseEnd_3205407] using wordTrace_append hprefix tailTrace_3205407
  have hstable : (prefixWord ++ tailWord_3205407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205407).length < 2 ^ (prefixWord ++ tailWord_3205407).sum := by decide
  have hdescent : baseEnd_3205407 < baseStart_3205407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205415 : List Nat := [1, 1, 8, 1, 2, 1, 2, 1, 5]
def baseStart_3205415 : Nat := 118140960795 + 3205415 * 2 ^ 59
def prefixEnd_3205415 : Nat := 4983230072969 + 3 ^ 40 * 3205415 * 2
def baseEnd_3205415 : Nat := 365759687140373673949127

theorem tailTrace_3205415 : CollatzResearch.WordTrace tailWord_3205415 prefixEnd_3205415 365759687140373673949127 := by
  unfold tailWord_3205415
  simp only [CollatzResearch.WordTrace]
  refine ⟨116911089682336371143081699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77940726454890914095387799 116911089682336371143081699)
  ·
    refine ⟨175366634523504556714622549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116911089682336371143081699 175366634523504556714622549)
    ·
      refine ⟨2055077748322319023999483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 175366634523504556714622549 2055077748322319023999483)
      ·
        refine ⟨3082616622483478535999225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2055077748322319023999483 3082616622483478535999225)
        ·
          refine ⟨2311962466862608901999419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3082616622483478535999225 2311962466862608901999419)
          ·
            refine ⟨3467943700293913352999129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2311962466862608901999419 3467943700293913352999129)
            ·
              refine ⟨2600957775220435014749347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3467943700293913352999129 2600957775220435014749347)
              ·
                refine ⟨3901436662830652522124021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2600957775220435014749347 3901436662830652522124021)
                ·
                  refine ⟨365759687140373673949127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3901436662830652522124021 365759687140373673949127)
                  ·
                    rfl

theorem cell22_3205415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 5].length) (baseStart_3205415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3205415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3205415 prefixEnd_3205415 := by exact prefixLift 3205415
  have htrace : WordTrace (prefixWord ++ tailWord_3205415) baseStart_3205415 baseEnd_3205415 := by
    simpa [prefixWord, tailWord_3205415, baseEnd_3205415] using wordTrace_append hprefix tailTrace_3205415
  have hstable : (prefixWord ++ tailWord_3205415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205415).length < 2 ^ (prefixWord ++ tailWord_3205415).sum := by decide
  have hdescent : baseEnd_3205415 < baseStart_3205415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205544 : List Nat := [2, 1, 6, 1, 1, 1, 2, 2, 6]
def baseStart_3205544 : Nat := 118140960795 + 3205544 * 2 ^ 59
def prefixEnd_3205544 : Nat := 4983230072969 + 3 ^ 40 * 3205544 * 2
def baseEnd_3205544 : Nat := 365774406919135895123995

theorem tailTrace_3205544 : CollatzResearch.WordTrace tailWord_3205544 prefixEnd_3205544 365774406919135895123995 := by
  unfold tailWord_3205544
  simp only [CollatzResearch.WordTrace]
  refine ⟨58457897349434513087263843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77943863132579350783018457 58457897349434513087263843)
  ·
    refine ⟨87686846024151769630895765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58457897349434513087263843 87686846024151769630895765)
    ·
      refine ⟨4110320907382114201448239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 87686846024151769630895765 4110320907382114201448239)
      ·
        refine ⟨6165481361073171302172359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4110320907382114201448239 6165481361073171302172359)
        ·
          refine ⟨9248222041609756953258539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6165481361073171302172359 9248222041609756953258539)
          ·
            refine ⟨13872333062414635429887809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9248222041609756953258539 13872333062414635429887809)
            ·
              refine ⟨10404249796810976572415857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13872333062414635429887809 10404249796810976572415857)
              ·
                refine ⟨7803187347608232429311893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10404249796810976572415857 7803187347608232429311893)
                ·
                  refine ⟨365774406919135895123995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7803187347608232429311893 365774406919135895123995)
                  ·
                    rfl

theorem cell22_3205544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 6].length) (baseStart_3205544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3205544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3205544 prefixEnd_3205544 := by exact prefixLift 3205544
  have htrace : WordTrace (prefixWord ++ tailWord_3205544) baseStart_3205544 baseEnd_3205544 := by
    simpa [prefixWord, tailWord_3205544, baseEnd_3205544] using wordTrace_append hprefix tailTrace_3205544
  have hstable : (prefixWord ++ tailWord_3205544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205544).length < 2 ^ (prefixWord ++ tailWord_3205544).sum := by decide
  have hdescent : baseEnd_3205544 < baseStart_3205544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205561 : List Nat := [1, 2, 1, 4, 3, 3, 1, 3, 4]
def baseStart_3205561 : Nat := 118140960795 + 3205561 * 2 ^ 59
def prefixEnd_3205561 : Nat := 4983230072969 + 3 ^ 40 * 3205561 * 2
def baseEnd_3205561 : Nat := 365776346734941769232311

theorem tailTrace_3205561 : CollatzResearch.WordTrace tailWord_3205561 prefixEnd_3205561 365776346734941769232311 := by
  unfold tailWord_3205561
  simp only [CollatzResearch.WordTrace]
  refine ⟨116916414739807438077896537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77944276493204958718597691 116916414739807438077896537)
  ·
    refine ⟨87687311054855578558422403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116916414739807438077896537 87687311054855578558422403)
    ·
      refine ⟨131530966582283367837633605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87687311054855578558422403 131530966582283367837633605)
      ·
        refine ⟨24662056234178131469556301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131530966582283367837633605 24662056234178131469556301)
        ·
          refine ⟨9248271087816799301083613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24662056234178131469556301 9248271087816799301083613)
          ·
            refine ⟨3468101657931299737906355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9248271087816799301083613 3468101657931299737906355)
            ·
              refine ⟨5202152486896949606859533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3468101657931299737906355 5202152486896949606859533)
              ·
                refine ⟨1950807182586356102572325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5202152486896949606859533 1950807182586356102572325)
                ·
                  refine ⟨365776346734941769232311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1950807182586356102572325 365776346734941769232311)
                  ·
                    rfl

theorem cell22_3205561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 3, 4].length) (baseStart_3205561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3205561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3205561 prefixEnd_3205561 := by exact prefixLift 3205561
  have htrace : WordTrace (prefixWord ++ tailWord_3205561) baseStart_3205561 baseEnd_3205561 := by
    simpa [prefixWord, tailWord_3205561, baseEnd_3205561] using wordTrace_append hprefix tailTrace_3205561
  have hstable : (prefixWord ++ tailWord_3205561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205561).length < 2 ^ (prefixWord ++ tailWord_3205561).sum := by decide
  have hdescent : baseEnd_3205561 < baseStart_3205561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205647 : List Nat := [1, 1, 2, 1, 1, 1, 2, 6, 3, 4]
def baseStart_3205647 : Nat := 118140960795 + 3205647 * 2 ^ 59
def prefixEnd_3205647 : Nat := 4983230072969 + 3 ^ 40 * 3205647 * 2
def baseEnd_3205647 : Nat := 1097358479762349750046669

theorem tailTrace_3205647 : CollatzResearch.WordTrace tailWord_3205647 prefixEnd_3205647 1097358479762349750046669 := by
  unfold tailWord_3205647
  simp only [CollatzResearch.WordTrace]
  refine ⟨116919551417495874765527195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77946367611663916510351463 116919551417495874765527195)
  ·
    refine ⟨175379327126243812148290793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116919551417495874765527195 175379327126243812148290793)
    ·
      refine ⟨131534495344682859111218095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175379327126243812148290793 131534495344682859111218095)
      ·
        refine ⟨197301743017024288666827143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131534495344682859111218095 197301743017024288666827143)
        ·
          refine ⟨295952614525536433000240715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197301743017024288666827143 295952614525536433000240715)
          ·
            refine ⟨443928921788304649500361073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295952614525536433000240715 443928921788304649500361073)
            ·
              refine ⟨332946691341228487125270805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 443928921788304649500361073 332946691341228487125270805)
              ·
                refine ⟨15606876156620085333997069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 332946691341228487125270805 15606876156620085333997069)
                ·
                  refine ⟨5852578558732532000248901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15606876156620085333997069 5852578558732532000248901)
                  ·
                    refine ⟨1097358479762349750046669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5852578558732532000248901 1097358479762349750046669)
                    ·
                      rfl

theorem cell22_3205647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 4].length) (baseStart_3205647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3205647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3205647 prefixEnd_3205647 := by exact prefixLift 3205647
  have htrace : WordTrace (prefixWord ++ tailWord_3205647) baseStart_3205647 baseEnd_3205647 := by
    simpa [prefixWord, tailWord_3205647, baseEnd_3205647] using wordTrace_append hprefix tailTrace_3205647
  have hstable : (prefixWord ++ tailWord_3205647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205647).length < 2 ^ (prefixWord ++ tailWord_3205647).sum := by decide
  have hdescent : baseEnd_3205647 < baseStart_3205647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205681 : List Nat := [1, 2, 2, 3, 1, 1, 6, 1, 1, 4]
def baseStart_3205681 : Nat := 118140960795 + 3205681 * 2 ^ 59
def prefixEnd_3205681 : Nat := 4983230072969 + 3 ^ 40 * 3205681 * 2
def baseEnd_3205681 : Nat := 1097370118657184994696565

theorem tailTrace_3205681 : CollatzResearch.WordTrace tailWord_3205681 prefixEnd_3205681 1097370118657184994696565 := by
  unfold tailWord_3205681
  simp only [CollatzResearch.WordTrace]
  refine ⟨116920791499372698572264897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77947194332915132381509931 116920791499372698572264897)
  ·
    refine ⟨87690593624529523929198673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116920791499372698572264897 87690593624529523929198673)
    ·
      refine ⟨65767945218397142946899005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87690593624529523929198673 65767945218397142946899005)
      ·
        refine ⟨24662979456898928605087127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65767945218397142946899005 24662979456898928605087127)
        ·
          refine ⟨36994469185348392907630691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24662979456898928605087127 36994469185348392907630691)
          ·
            refine ⟨55491703778022589361446037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36994469185348392907630691 55491703778022589361446037)
            ·
              refine ⟨2601173614594808876317783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55491703778022589361446037 2601173614594808876317783)
              ·
                refine ⟨3901760421892213314476675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2601173614594808876317783 3901760421892213314476675)
                ·
                  refine ⟨5852640632838319971715013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3901760421892213314476675 5852640632838319971715013)
                  ·
                    refine ⟨1097370118657184994696565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5852640632838319971715013 1097370118657184994696565)
                    ·
                      rfl

theorem cell22_3205681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 1, 4].length) (baseStart_3205681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3205681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3205681 prefixEnd_3205681 := by exact prefixLift 3205681
  have htrace : WordTrace (prefixWord ++ tailWord_3205681) baseStart_3205681 baseEnd_3205681 := by
    simpa [prefixWord, tailWord_3205681, baseEnd_3205681] using wordTrace_append hprefix tailTrace_3205681
  have hstable : (prefixWord ++ tailWord_3205681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205681).length < 2 ^ (prefixWord ++ tailWord_3205681).sum := by decide
  have hdescent : baseEnd_3205681 < baseStart_3205681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205737 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 1, 8]
def baseStart_3205737 : Nat := 118140960795 + 3205737 * 2 ^ 59
def prefixEnd_3205737 : Nat := 4983230072969 + 3 ^ 40 * 3205737 * 2
def baseEnd_3205737 : Nat := 1097389288601619515296393

theorem tailTrace_3205737 : CollatzResearch.WordTrace tailWord_3205737 prefixEnd_3205737 1097389288601619515296393 := by
  unfold tailWord_3205737
  simp only [CollatzResearch.WordTrace]
  refine ⟨116922833987169820136303465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77948555991446546757535643 116922833987169820136303465)
  ·
    refine ⟨87692125490377365102227599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116922833987169820136303465 87692125490377365102227599)
    ·
      refine ⟨131538188235566047653341399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87692125490377365102227599 131538188235566047653341399)
      ·
        refine ⟨197307282353349071480012099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131538188235566047653341399 197307282353349071480012099)
        ·
          refine ⟨295960923530023607220018149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197307282353349071480012099 295960923530023607220018149)
          ·
            refine ⟨55492673161879426353753403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 295960923530023607220018149 55492673161879426353753403)
            ·
              refine ⟨83239009742819139530630105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55492673161879426353753403 83239009742819139530630105)
              ·
                refine ⟨62429257307114354647972579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83239009742819139530630105 62429257307114354647972579)
                ·
                  refine ⟨93643885960671531971958869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62429257307114354647972579 93643885960671531971958869)
                  ·
                    refine ⟨1097389288601619515296393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93643885960671531971958869 1097389288601619515296393)
                    ·
                      rfl

theorem cell22_3205737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 8].length) (baseStart_3205737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3205737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3205737 prefixEnd_3205737 := by exact prefixLift 3205737
  have htrace : WordTrace (prefixWord ++ tailWord_3205737) baseStart_3205737 baseEnd_3205737 := by
    simpa [prefixWord, tailWord_3205737, baseEnd_3205737] using wordTrace_append hprefix tailTrace_3205737
  have hstable : (prefixWord ++ tailWord_3205737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205737).length < 2 ^ (prefixWord ++ tailWord_3205737).sum := by decide
  have hdescent : baseEnd_3205737 < baseStart_3205737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205756 : List Nat := [2, 2, 2, 1, 1, 2, 5, 1, 3, 3]
def baseStart_3205756 : Nat := 118140960795 + 3205756 * 2 ^ 59
def prefixEnd_3205756 : Nat := 4983230072969 + 3 ^ 40 * 3205756 * 2
def baseEnd_3205756 : Nat := 1097395792689909799071335

theorem tailTrace_3205756 : CollatzResearch.WordTrace tailWord_3205756 prefixEnd_3205756 1097395792689909799071335 := by
  unfold tailWord_3205756
  simp only [CollatzResearch.WordTrace]
  refine ⟨58461763487050493190622561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77949017982733990920830081 58461763487050493190622561)
  ·
    refine ⟨43846322615287869892966921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58461763487050493190622561 43846322615287869892966921)
    ·
      refine ⟨32884741961465902419725191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43846322615287869892966921 32884741961465902419725191)
      ·
        refine ⟨49327112942198853629587787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32884741961465902419725191 49327112942198853629587787)
        ·
          refine ⟨73990669413298280444381681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49327112942198853629587787 73990669413298280444381681)
          ·
            refine ⟨55493002059973710333286261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73990669413298280444381681 55493002059973710333286261)
            ·
              refine ⟨5202468943122535343745587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55493002059973710333286261 5202468943122535343745587)
              ·
                refine ⟨7803703414683803015618381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5202468943122535343745587 7803703414683803015618381)
                ·
                  refine ⟨2926388780506426130856893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7803703414683803015618381 2926388780506426130856893)
                  ·
                    refine ⟨1097395792689909799071335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2926388780506426130856893 1097395792689909799071335)
                    ·
                      rfl

theorem cell22_3205756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_3205756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3205756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3205756 prefixEnd_3205756 := by exact prefixLift 3205756
  have htrace : WordTrace (prefixWord ++ tailWord_3205756) baseStart_3205756 baseEnd_3205756 := by
    simpa [prefixWord, tailWord_3205756, baseEnd_3205756] using wordTrace_append hprefix tailTrace_3205756
  have hstable : (prefixWord ++ tailWord_3205756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205756).length < 2 ^ (prefixWord ++ tailWord_3205756).sum := by decide
  have hdescent : baseEnd_3205756 < baseStart_3205756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205790 : List Nat := [4, 3, 1, 1, 1, 1, 2, 5, 1, 3]
def baseStart_3205790 : Nat := 118140960795 + 3205790 * 2 ^ 59
def prefixEnd_3205790 : Nat := 4983230072969 + 3 ^ 40 * 3205790 * 2
def baseEnd_3205790 : Nat := 1097407431584745043721231

theorem tailTrace_3205790 : CollatzResearch.WordTrace tailWord_3205790 prefixEnd_3205790 1097407431584745043721231 := by
  unfold tailWord_3205790
  simp only [CollatzResearch.WordTrace]
  refine ⟨14615595881997226273497853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77949844703985206791988549 14615595881997226273497853)
  ·
    refine ⟨5480848455748959852561695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14615595881997226273497853 5480848455748959852561695)
    ·
      refine ⟨8221272683623439778842543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5480848455748959852561695 8221272683623439778842543)
      ·
        refine ⟨12331909025435159668263815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8221272683623439778842543 12331909025435159668263815)
        ·
          refine ⟨18497863538152739502395723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12331909025435159668263815 18497863538152739502395723)
          ·
            refine ⟨27746795307229109253593585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18497863538152739502395723 27746795307229109253593585)
            ·
              refine ⟨20810096480421831940195189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27746795307229109253593585 20810096480421831940195189)
              ·
                refine ⟨1950946545039546744393299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20810096480421831940195189 1950946545039546744393299)
                ·
                  refine ⟨2926419817559320116589949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1950946545039546744393299 2926419817559320116589949)
                  ·
                    refine ⟨1097407431584745043721231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2926419817559320116589949 1097407431584745043721231)
                    ·
                      rfl

theorem cell22_3205790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_3205790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3205790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3205790 prefixEnd_3205790 := by exact prefixLift 3205790
  have htrace : WordTrace (prefixWord ++ tailWord_3205790) baseStart_3205790 baseEnd_3205790 := by
    simpa [prefixWord, tailWord_3205790, baseEnd_3205790] using wordTrace_append hprefix tailTrace_3205790
  have hstable : (prefixWord ++ tailWord_3205790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205790).length < 2 ^ (prefixWord ++ tailWord_3205790).sum := by decide
  have hdescent : baseEnd_3205790 < baseStart_3205790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205848 : List Nat := [2, 1, 2, 2, 3, 3, 2, 3, 4]
def baseStart_3205848 : Nat := 118140960795 + 3205848 * 2 ^ 59
def prefixEnd_3205848 : Nat := 4983230072969 + 3 ^ 40 * 3205848 * 2
def baseEnd_3205848 : Nat := 365809095390017408590351

theorem tailTrace_3205848 : CollatzResearch.WordTrace tailWord_3205848 prefixEnd_3205848 365809095390017408590351 := by
  unfold tailWord_3205848
  simp only [CollatzResearch.WordTrace]
  refine ⟨58463441244883843046797099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77951254993178457395729465 58463441244883843046797099)
  ·
    refine ⟨87695161867325764570195649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58463441244883843046797099 87695161867325764570195649)
    ·
      refine ⟨65771371400494323427646737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87695161867325764570195649 65771371400494323427646737)
      ·
        refine ⟨49328528550370742570735053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65771371400494323427646737 49328528550370742570735053)
        ·
          refine ⟨18498198206389028464025645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49328528550370742570735053 18498198206389028464025645)
          ·
            refine ⟨6936824327395885674009617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18498198206389028464025645 6936824327395885674009617)
            ·
              refine ⟨5202618245546914255507213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6936824327395885674009617 5202618245546914255507213)
              ·
                refine ⟨1950981842080092845815205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5202618245546914255507213 1950981842080092845815205)
                ·
                  refine ⟨365809095390017408590351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1950981842080092845815205 365809095390017408590351)
                  ·
                    rfl

theorem cell22_3205848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 3, 4].length) (baseStart_3205848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3205848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3205848 prefixEnd_3205848 := by exact prefixLift 3205848
  have htrace : WordTrace (prefixWord ++ tailWord_3205848) baseStart_3205848 baseEnd_3205848 := by
    simpa [prefixWord, tailWord_3205848, baseEnd_3205848] using wordTrace_append hprefix tailTrace_3205848
  have hstable : (prefixWord ++ tailWord_3205848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205848).length < 2 ^ (prefixWord ++ tailWord_3205848).sum := by decide
  have hdescent : baseEnd_3205848 < baseStart_3205848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205921 : List Nat := [1, 2, 3, 2, 1, 2, 2, 4, 5]
def baseStart_3205921 : Nat := 118140960795 + 3205921 * 2 ^ 59
def prefixEnd_3205921 : Nat := 4983230072969 + 3 ^ 40 * 3205921 * 2
def baseEnd_3205921 : Nat := 365817425187301456231943

theorem tailTrace_3205921 : CollatzResearch.WordTrace tailWord_3205921 prefixEnd_3205921 365817425187301456231943 := by
  unfold tailWord_3205921
  simp only [CollatzResearch.WordTrace]
  refine ⟨116929545018503219561001617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77953030012335479707334411 116929545018503219561001617)
  ·
    refine ⟨87697158763877414670751213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116929545018503219561001617 87697158763877414670751213)
    ·
      refine ⟨32886434536454030501531705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87697158763877414670751213 32886434536454030501531705)
      ·
        refine ⟨24664825902340522876148779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32886434536454030501531705 24664825902340522876148779)
        ·
          refine ⟨36997238853510784314223169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24664825902340522876148779 36997238853510784314223169)
          ·
            refine ⟨27747929140133088235667377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36997238853510784314223169 27747929140133088235667377)
            ·
              refine ⟨20810946855099816176750533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27747929140133088235667377 20810946855099816176750533)
              ·
                refine ⟨3902052535331215533140725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20810946855099816176750533 3902052535331215533140725)
                ·
                  refine ⟨365817425187301456231943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3902052535331215533140725 365817425187301456231943)
                  ·
                    rfl

theorem cell22_3205921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 4, 5].length) (baseStart_3205921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3205921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3205921 prefixEnd_3205921 := by exact prefixLift 3205921
  have htrace : WordTrace (prefixWord ++ tailWord_3205921) baseStart_3205921 baseEnd_3205921 := by
    simpa [prefixWord, tailWord_3205921, baseEnd_3205921] using wordTrace_append hprefix tailTrace_3205921
  have hstable : (prefixWord ++ tailWord_3205921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205921).length < 2 ^ (prefixWord ++ tailWord_3205921).sum := by decide
  have hdescent : baseEnd_3205921 < baseStart_3205921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205983 : List Nat := [1, 1, 2, 3, 1, 3, 3, 4, 4]
def baseStart_3205983 : Nat := 118140960795 + 3205983 * 2 ^ 59
def prefixEnd_3205983 : Nat := 4983230072969 + 3 ^ 40 * 3205983 * 2
def baseEnd_3205983 : Nat := 365824499809652291215213

theorem tailTrace_3205983 : CollatzResearch.WordTrace tailWord_3205983 prefixEnd_3205983 365824499809652291215213 := by
  unfold tailWord_3205983
  simp only [CollatzResearch.WordTrace]
  refine ⟨116931806344278604149758603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77954537562852402766505735 116931806344278604149758603)
  ·
    refine ⟨175397709516417906224637905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116931806344278604149758603 175397709516417906224637905)
    ·
      refine ⟨131548282137313429668478429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175397709516417906224637905 131548282137313429668478429)
      ·
        refine ⟨49330605801492536125679411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131548282137313429668478429 49330605801492536125679411)
        ·
          refine ⟨73995908702238804188519117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49330605801492536125679411 73995908702238804188519117)
          ·
            refine ⟨27748465763339551570694669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73995908702238804188519117 27748465763339551570694669)
            ·
              refine ⟨10405674661252331839010501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27748465763339551570694669 10405674661252331839010501)
              ·
                refine ⟨1951063998984812219814469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10405674661252331839010501 1951063998984812219814469)
                ·
                  refine ⟨365824499809652291215213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1951063998984812219814469 365824499809652291215213)
                  ·
                    rfl

theorem cell22_3205983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 4, 4].length) (baseStart_3205983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3205983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3205983 prefixEnd_3205983 := by exact prefixLift 3205983
  have htrace : WordTrace (prefixWord ++ tailWord_3205983) baseStart_3205983 baseEnd_3205983 := by
    simpa [prefixWord, tailWord_3205983, baseEnd_3205983] using wordTrace_append hprefix tailTrace_3205983
  have hstable : (prefixWord ++ tailWord_3205983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205983).length < 2 ^ (prefixWord ++ tailWord_3205983).sum := by decide
  have hdescent : baseEnd_3205983 < baseStart_3205983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205996 : List Nat := [2, 2, 1, 1, 4, 1, 2, 2, 1, 6]
def baseStart_3205996 : Nat := 118140960795 + 3205996 * 2 ^ 59
def prefixEnd_3205996 : Nat := 4983230072969 + 3 ^ 40 * 3205996 * 2
def baseEnd_3205996 : Nat := 1097477949594629173070599

theorem tailTrace_3205996 : CollatzResearch.WordTrace tailWord_3205996 prefixEnd_3205996 1097477949594629173070599 := by
  unfold tailWord_3205996
  simp only [CollatzResearch.WordTrace]
  refine ⟨58466140246615753684990921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77954853662154338246654561 58466140246615753684990921)
  ·
    refine ⟨43849605184961815263743191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58466140246615753684990921 43849605184961815263743191)
    ·
      refine ⟨65774407777442722895614787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43849605184961815263743191 65774407777442722895614787)
      ·
        refine ⟨98661611666164084343422181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65774407777442722895614787 98661611666164084343422181)
        ·
          refine ⟨18499052187405765814391659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98661611666164084343422181 18499052187405765814391659)
          ·
            refine ⟨27748578281108648721587489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18499052187405765814391659 27748578281108648721587489)
            ·
              refine ⟨20811433710831486541190617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27748578281108648721587489 20811433710831486541190617)
              ·
                refine ⟨15608575283123614905892963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20811433710831486541190617 15608575283123614905892963)
                ·
                  refine ⟨23412862924685422358839445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15608575283123614905892963 23412862924685422358839445)
                  ·
                    refine ⟨1097477949594629173070599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23412862924685422358839445 1097477949594629173070599)
                    ·
                      rfl

theorem cell22_3205996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_3205996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3205996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3205996 prefixEnd_3205996 := by exact prefixLift 3205996
  have htrace : WordTrace (prefixWord ++ tailWord_3205996) baseStart_3205996 baseEnd_3205996 := by
    simpa [prefixWord, tailWord_3205996, baseEnd_3205996] using wordTrace_append hprefix tailTrace_3205996
  have hstable : (prefixWord ++ tailWord_3205996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205996).length < 2 ^ (prefixWord ++ tailWord_3205996).sum := by decide
  have hdescent : baseEnd_3205996 < baseStart_3205996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206013 : List Nat := [1, 4, 1, 1, 2, 1, 5, 1, 2, 4]
def baseStart_3206013 : Nat := 118140960795 + 3206013 * 2 ^ 59
def prefixEnd_3206013 : Nat := 4983230072969 + 3 ^ 40 * 3206013 * 2
def baseEnd_3206013 : Nat := 1097483769042046795395547

theorem tailTrace_3206013 : CollatzResearch.WordTrace tailWord_3206013 prefixEnd_3206013 1097483769042046795395547 := by
  unfold tailWord_3206013
  simp only [CollatzResearch.WordTrace]
  refine ⟨116932900534169919273350693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77955267022779946182233795 116932900534169919273350693)
  ·
    refine ⟨21924918850156859863753255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116932900534169919273350693 21924918850156859863753255)
    ·
      refine ⟨32887378275235289795629883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21924918850156859863753255 32887378275235289795629883)
      ·
        refine ⟨49331067412852934693444825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32887378275235289795629883 49331067412852934693444825)
        ·
          refine ⟨36998300559639701020083619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49331067412852934693444825 36998300559639701020083619)
          ·
            refine ⟨55497450839459551530125429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36998300559639701020083619 55497450839459551530125429)
            ·
              refine ⟨5202886016199332955949259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55497450839459551530125429 5202886016199332955949259)
              ·
                refine ⟨7804329024298999433923889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5202886016199332955949259 7804329024298999433923889)
                ·
                  refine ⟨5853246768224249575442917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7804329024298999433923889 5853246768224249575442917)
                  ·
                    refine ⟨1097483769042046795395547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5853246768224249575442917 1097483769042046795395547)
                    ·
                      rfl

theorem cell22_3206013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_3206013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3206013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3206013 prefixEnd_3206013 := by exact prefixLift 3206013
  have htrace : WordTrace (prefixWord ++ tailWord_3206013) baseStart_3206013 baseEnd_3206013 := by
    simpa [prefixWord, tailWord_3206013, baseEnd_3206013] using wordTrace_append hprefix tailTrace_3206013
  have hstable : (prefixWord ++ tailWord_3206013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206013).length < 2 ^ (prefixWord ++ tailWord_3206013).sum := by decide
  have hdescent : baseEnd_3206013 < baseStart_3206013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206071 : List Nat := [1, 1, 3, 1, 3, 1, 2, 2, 1, 7]
def baseStart_3206071 : Nat := 118140960795 + 3206071 * 2 ^ 59
def prefixEnd_3206071 : Nat := 4983230072969 + 3 ^ 40 * 3206071 * 2
def baseEnd_3206071 : Nat := 1097503623627353977445369

theorem tailTrace_3206071 : CollatzResearch.WordTrace tailWord_3206071 prefixEnd_3206071 1097503623627353977445369 := by
  unfold tailWord_3206071
  simp only [CollatzResearch.WordTrace]
  refine ⟨116935015967959795178962067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77956677311973196785974711 116935015967959795178962067)
  ·
    refine ⟨175402523951939692768443101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116935015967959795178962067 175402523951939692768443101)
    ·
      refine ⟨65775946481977384788166163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175402523951939692768443101 65775946481977384788166163)
      ·
        refine ⟨98663919722966077182249245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65775946481977384788166163 98663919722966077182249245)
        ·
          refine ⟨36998969896112278943343467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98663919722966077182249245 36998969896112278943343467)
          ·
            refine ⟨55498454844168418415015201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36998969896112278943343467 55498454844168418415015201)
            ·
              refine ⟨41623841133126313811261401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55498454844168418415015201 41623841133126313811261401)
              ·
                refine ⟨31217880849844735358446051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41623841133126313811261401 31217880849844735358446051)
                ·
                  refine ⟨46826821274767103037669077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31217880849844735358446051 46826821274767103037669077)
                  ·
                    refine ⟨1097503623627353977445369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46826821274767103037669077 1097503623627353977445369)
                    ·
                      rfl

theorem cell22_3206071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_3206071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3206071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3206071 prefixEnd_3206071 := by exact prefixLift 3206071
  have htrace : WordTrace (prefixWord ++ tailWord_3206071) baseStart_3206071 baseEnd_3206071 := by
    simpa [prefixWord, tailWord_3206071, baseEnd_3206071] using wordTrace_append hprefix tailTrace_3206071
  have hstable : (prefixWord ++ tailWord_3206071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206071).length < 2 ^ (prefixWord ++ tailWord_3206071).sum := by decide
  have hdescent : baseEnd_3206071 < baseStart_3206071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206094 : List Nat := [4, 1, 1, 1, 2, 4, 3, 2, 1, 3]
def baseStart_3206094 : Nat := 118140960795 + 3206094 * 2 ^ 59
def prefixEnd_3206094 : Nat := 4983230072969 + 3 ^ 40 * 3206094 * 2
def baseEnd_3206094 : Nat := 1097511496997389584120299

theorem tailTrace_3206094 : CollatzResearch.WordTrace tailWord_3206094 prefixEnd_3206094 1097511496997389584120299 := by
  unfold tailWord_3206094
  simp only [CollatzResearch.WordTrace]
  refine ⟨14616981855859558763381167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77957236564584313404699557 14616981855859558763381167)
  ·
    refine ⟨21925472783789338145071751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14616981855859558763381167 21925472783789338145071751)
    ·
      refine ⟨32888209175684007217607627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21925472783789338145071751 32888209175684007217607627)
      ·
        refine ⟨49332313763526010826411441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32888209175684007217607627 49332313763526010826411441)
        ·
          refine ⟨36999235322644508119808581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49332313763526010826411441 36999235322644508119808581)
          ·
            refine ⟨6937356622995845272464109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36999235322644508119808581 6937356622995845272464109)
            ·
              refine ⟨2601508733623441977174041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6937356622995845272464109 2601508733623441977174041)
              ·
                refine ⟨1951131550217581482880531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2601508733623441977174041 1951131550217581482880531)
                ·
                  refine ⟨2926697325326372224320797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1951131550217581482880531 2926697325326372224320797)
                  ·
                    refine ⟨1097511496997389584120299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2926697325326372224320797 1097511496997389584120299)
                    ·
                      rfl

theorem cell22_3206094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 2, 1, 3].length) (baseStart_3206094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3206094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3206094 prefixEnd_3206094 := by exact prefixLift 3206094
  have htrace : WordTrace (prefixWord ++ tailWord_3206094) baseStart_3206094 baseEnd_3206094 := by
    simpa [prefixWord, tailWord_3206094, baseEnd_3206094] using wordTrace_append hprefix tailTrace_3206094
  have hstable : (prefixWord ++ tailWord_3206094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206094).length < 2 ^ (prefixWord ++ tailWord_3206094).sum := by decide
  have hdescent : baseEnd_3206094 < baseStart_3206094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206120 : List Nat := [2, 1, 4, 1, 1, 1, 5, 2, 1, 4]
def baseStart_3206120 : Nat := 118140960795 + 3206120 * 2 ^ 59
def prefixEnd_3206120 : Nat := 4983230072969 + 3 ^ 40 * 3206120 * 2
def baseEnd_3206120 : Nat := 1097520397328734182970219

theorem tailTrace_3206120 : CollatzResearch.WordTrace tailWord_3206120 prefixEnd_3206120 1097520397328734182970219 := by
  unfold tailWord_3206120
  simp only [CollatzResearch.WordTrace]
  refine ⟨58468401572391138273747907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77957868763188184364997209 58468401572391138273747907)
  ·
    refine ⟨87702602358586707410621861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58468401572391138273747907 87702602358586707410621861)
    ·
      refine ⟨16444237942235007639491599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87702602358586707410621861 16444237942235007639491599)
      ·
        refine ⟨24666356913352511459237399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16444237942235007639491599 24666356913352511459237399)
        ·
          refine ⟨36999535370028767188856099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24666356913352511459237399 36999535370028767188856099)
          ·
            refine ⟨55499303055043150783284149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36999535370028767188856099 55499303055043150783284149)
            ·
              refine ⟨5203059661410295385932889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55499303055043150783284149 5203059661410295385932889)
              ·
                refine ⟨3902294746057721539449667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5203059661410295385932889 3902294746057721539449667)
                ·
                  refine ⟨5853442119086582309174501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3902294746057721539449667 5853442119086582309174501)
                  ·
                    refine ⟨1097520397328734182970219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5853442119086582309174501 1097520397328734182970219)
                    ·
                      rfl

theorem cell22_3206120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_3206120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3206120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3206120 prefixEnd_3206120 := by exact prefixLift 3206120
  have htrace : WordTrace (prefixWord ++ tailWord_3206120) baseStart_3206120 baseEnd_3206120 := by
    simpa [prefixWord, tailWord_3206120, baseEnd_3206120] using wordTrace_append hprefix tailTrace_3206120
  have hstable : (prefixWord ++ tailWord_3206120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206120).length < 2 ^ (prefixWord ++ tailWord_3206120).sum := by decide
  have hdescent : baseEnd_3206120 < baseStart_3206120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206152 : List Nat := [2, 1, 3, 2, 1, 3, 4, 2, 4]
def baseStart_3206152 : Nat := 118140960795 + 3206152 * 2 ^ 59
def prefixEnd_3206152 : Nat := 4983230072969 + 3 ^ 40 * 3206152 * 2
def baseEnd_3206152 : Nat := 365843783860898922056707

theorem tailTrace_3206152 : CollatzResearch.WordTrace tailWord_3206152 prefixEnd_3206152 365843783860898922056707 := by
  unfold tailWord_3206152
  simp only [CollatzResearch.WordTrace]
  refine ⟨58468985140333173006330355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77958646853777564008440473 58468985140333173006330355)
  ·
    refine ⟨87703477710499759509495533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58468985140333173006330355 87703477710499759509495533)
    ·
      refine ⟨32888804141437409816060825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87703477710499759509495533 32888804141437409816060825)
      ·
        refine ⟨24666603106078057362045619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32888804141437409816060825 24666603106078057362045619)
        ·
          refine ⟨36999904659117086043068429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24666603106078057362045619 36999904659117086043068429)
          ·
            refine ⟨13874964247168907266150661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36999904659117086043068429 13874964247168907266150661)
            ·
              refine ⟨2601555796344170112403249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13874964247168907266150661 2601555796344170112403249)
              ·
                refine ⟨1951166847258127584302437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2601555796344170112403249 1951166847258127584302437)
                ·
                  refine ⟨365843783860898922056707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1951166847258127584302437 365843783860898922056707)
                  ·
                    rfl

theorem cell22_3206152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 2, 4].length) (baseStart_3206152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3206152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3206152 prefixEnd_3206152 := by exact prefixLift 3206152
  have htrace : WordTrace (prefixWord ++ tailWord_3206152) baseStart_3206152 baseEnd_3206152 := by
    simpa [prefixWord, tailWord_3206152, baseEnd_3206152] using wordTrace_append hprefix tailTrace_3206152
  have hstable : (prefixWord ++ tailWord_3206152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206152).length < 2 ^ (prefixWord ++ tailWord_3206152).sum := by decide
  have hdescent : baseEnd_3206152 < baseStart_3206152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206167 : List Nat := [1, 1, 3, 5, 1, 1, 2, 3, 2, 3]
def baseStart_3206167 : Nat := 118140960795 + 3206167 * 2 ^ 59
def prefixEnd_3206167 : Nat := 4983230072969 + 3 ^ 40 * 3206167 * 2
def baseEnd_3206167 : Nat := 1097536486389241727045075

theorem tailTrace_3206167 : CollatzResearch.WordTrace tailWord_3206167 prefixEnd_3206167 1097536486389241727045075 := by
  unfold tailWord_3206167
  simp only [CollatzResearch.WordTrace]
  refine ⟨116938517375612003574456755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77959011583741335716304503 116938517375612003574456755)
  ·
    refine ⟨175407776063418005361685133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116938517375612003574456755 175407776063418005361685133)
    ·
      refine ⟨65777916023781752010631925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175407776063418005361685133 65777916023781752010631925)
      ·
        refine ⟨6166679627229539250996743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65777916023781752010631925 6166679627229539250996743)
        ·
          refine ⟨9250019440844308876495115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6166679627229539250996743 9250019440844308876495115)
          ·
            refine ⟨13875029161266463314742673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9250019440844308876495115 13875029161266463314742673)
            ·
              refine ⟨10406271870949847486057005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13875029161266463314742673 10406271870949847486057005)
              ·
                refine ⟨3902351951606192807271377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10406271870949847486057005 3902351951606192807271377)
                ·
                  refine ⟨2926763963704644605453533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3902351951606192807271377 2926763963704644605453533)
                  ·
                    refine ⟨1097536486389241727045075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2926763963704644605453533 1097536486389241727045075)
                    ·
                      rfl

theorem cell22_3206167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 2, 3].length) (baseStart_3206167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3206167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3206167 prefixEnd_3206167 := by exact prefixLift 3206167
  have htrace : WordTrace (prefixWord ++ tailWord_3206167) baseStart_3206167 baseEnd_3206167 := by
    simpa [prefixWord, tailWord_3206167, baseEnd_3206167] using wordTrace_append hprefix tailTrace_3206167
  have hstable : (prefixWord ++ tailWord_3206167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206167).length < 2 ^ (prefixWord ++ tailWord_3206167).sum := by decide
  have hdescent : baseEnd_3206167 < baseStart_3206167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206208 : List Nat := [2, 1, 1, 2, 2, 3, 3, 1, 7]
def baseStart_3206208 : Nat := 118140960795 + 3206208 * 2 ^ 59
def prefixEnd_3206208 : Nat := 4983230072969 + 3 ^ 40 * 3206208 * 2
def baseEnd_3206208 : Nat := 365850173842377095589983

theorem tailTrace_3206208 : CollatzResearch.WordTrace tailWord_3206208 prefixEnd_3206208 365850173842377095589983 := by
  unfold tailWord_3206208
  simp only [CollatzResearch.WordTrace]
  refine ⟨58470006384231733788349639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77960008512308978384466185 58470006384231733788349639)
  ·
    refine ⟨87705009576347600682524459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58470006384231733788349639 87705009576347600682524459)
    ·
      refine ⟨131557514364521401023786689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87705009576347600682524459 131557514364521401023786689)
      ·
        refine ⟨98668135773391050767840017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131557514364521401023786689 98668135773391050767840017)
        ·
          refine ⟨74001101830043288075880013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98668135773391050767840017 74001101830043288075880013)
          ·
            refine ⟨27750413186266233028455005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74001101830043288075880013 27750413186266233028455005)
            ·
              refine ⟨10406404944849837385670627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27750413186266233028455005 10406404944849837385670627)
              ·
                refine ⟨15609607417274756078505941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10406404944849837385670627 15609607417274756078505941)
                ·
                  refine ⟨365850173842377095589983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15609607417274756078505941 365850173842377095589983)
                  ·
                    rfl

theorem cell22_3206208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 7].length) (baseStart_3206208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3206208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3206208 prefixEnd_3206208 := by exact prefixLift 3206208
  have htrace : WordTrace (prefixWord ++ tailWord_3206208) baseStart_3206208 baseEnd_3206208 := by
    simpa [prefixWord, tailWord_3206208, baseEnd_3206208] using wordTrace_append hprefix tailTrace_3206208
  have hstable : (prefixWord ++ tailWord_3206208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206208).length < 2 ^ (prefixWord ++ tailWord_3206208).sum := by decide
  have hdescent : baseEnd_3206208 < baseStart_3206208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206255 : List Nat := [1, 1, 2, 1, 3, 3, 1, 5, 1, 4]
def baseStart_3206255 : Nat := 118140960795 + 3206255 * 2 ^ 59
def prefixEnd_3206255 : Nat := 4983230072969 + 3 ^ 40 * 3206255 * 2
def baseEnd_3206255 : Nat := 1097566610587638830844805

theorem tailTrace_3206255 : CollatzResearch.WordTrace tailWord_3206255 prefixEnd_3206255 1097566610587638830844805 := by
  unfold tailWord_3206255
  simp only [CollatzResearch.WordTrace]
  refine ⟨116941726999293194603660219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77961151332862129735773479 116941726999293194603660219)
  ·
    refine ⟨175412590498939791905490329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116941726999293194603660219 175412590498939791905490329)
    ·
      refine ⟨131559442874204843929117747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175412590498939791905490329 131559442874204843929117747)
      ·
        refine ⟨197339164311307265893676621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131559442874204843929117747 197339164311307265893676621)
        ·
          refine ⟨74002186616740224710128733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197339164311307265893676621 74002186616740224710128733)
          ·
            refine ⟨27750819981277584266298275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74002186616740224710128733 27750819981277584266298275)
            ·
              refine ⟨41626229971916376399447413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27750819981277584266298275 41626229971916376399447413)
              ·
                refine ⟨3902459059867160287448195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41626229971916376399447413 3902459059867160287448195)
                ·
                  refine ⟨5853688589800740431172293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3902459059867160287448195 5853688589800740431172293)
                  ·
                    refine ⟨1097566610587638830844805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5853688589800740431172293 1097566610587638830844805)
                    ·
                      rfl

theorem cell22_3206255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 4].length) (baseStart_3206255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3206255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3206255 prefixEnd_3206255 := by exact prefixLift 3206255
  have htrace : WordTrace (prefixWord ++ tailWord_3206255) baseStart_3206255 baseEnd_3206255 := by
    simpa [prefixWord, tailWord_3206255, baseEnd_3206255] using wordTrace_append hprefix tailTrace_3206255
  have hstable : (prefixWord ++ tailWord_3206255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206255).length < 2 ^ (prefixWord ++ tailWord_3206255).sum := by decide
  have hdescent : baseEnd_3206255 < baseStart_3206255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206283 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 3, 6]
def baseStart_3206283 : Nat := 118140960795 + 3206283 * 2 ^ 59
def prefixEnd_3206283 : Nat := 4983230072969 + 3 ^ 40 * 3206283 * 2
def baseEnd_3206283 : Nat := 1097576195559856091144719

theorem tailTrace_3206283 : CollatzResearch.WordTrace tailWord_3206283 prefixEnd_3206283 1097576195559856091144719 := by
  unfold tailWord_3206283
  simp only [CollatzResearch.WordTrace]
  refine ⟨116942748243191755385679503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77961832162127836923786335 116942748243191755385679503)
  ·
    refine ⟨175414122364787633078519255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116942748243191755385679503 175414122364787633078519255)
    ·
      refine ⟨263121183547181449617778883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175414122364787633078519255 263121183547181449617778883)
      ·
        refine ⟨394681775320772174426668325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263121183547181449617778883 394681775320772174426668325)
        ·
          refine ⟨74002832872644782705000311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 394681775320772174426668325 74002832872644782705000311)
          ·
            refine ⟨111004249308967174057500467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74002832872644782705000311 111004249308967174057500467)
            ·
              refine ⟨166506373963450761086250701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111004249308967174057500467 166506373963450761086250701)
              ·
                refine ⟨62439890236294035407344013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166506373963450761086250701 62439890236294035407344013)
                ·
                  refine ⟨23414958838610263277754005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62439890236294035407344013 23414958838610263277754005)
                  ·
                    refine ⟨1097576195559856091144719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23414958838610263277754005 1097576195559856091144719)
                    ·
                      rfl

theorem cell22_3206283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 6].length) (baseStart_3206283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3206283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3206283 prefixEnd_3206283 := by exact prefixLift 3206283
  have htrace : WordTrace (prefixWord ++ tailWord_3206283) baseStart_3206283 baseEnd_3206283 := by
    simpa [prefixWord, tailWord_3206283, baseEnd_3206283] using wordTrace_append hprefix tailTrace_3206283
  have hstable : (prefixWord ++ tailWord_3206283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206283).length < 2 ^ (prefixWord ++ tailWord_3206283).sum := by decide
  have hdescent : baseEnd_3206283 < baseStart_3206283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206302 : List Nat := [4, 3, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_3206302 : Nat := 118140960795 + 3206302 * 2 ^ 59
def prefixEnd_3206302 : Nat := 4983230072969 + 3 ^ 40 * 3206302 * 2
def baseEnd_3206302 : Nat := 1097582699648146374919661

theorem tailTrace_3206302 : CollatzResearch.WordTrace tailWord_3206302 prefixEnd_3206302 1097582699648146374919661 := by
  unfold tailWord_3206302
  simp only [CollatzResearch.WordTrace]
  refine ⟨14617930153765365203827645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77962294153415281087080773 14617930153765365203827645)
  ·
    refine ⟨5481723807662011951435367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14617930153765365203827645 5481723807662011951435367)
    ·
      refine ⟨8222585711493017927153051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5481723807662011951435367 8222585711493017927153051)
      ·
        refine ⟨12333878567239526890729577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8222585711493017927153051 12333878567239526890729577)
        ·
          refine ⟨9250408925429645168047183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12333878567239526890729577 9250408925429645168047183)
          ·
            refine ⟨13875613388144467752070775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9250408925429645168047183 13875613388144467752070775)
            ·
              refine ⟨20813420082216701628106163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13875613388144467752070775 20813420082216701628106163)
              ·
                refine ⟨31220130123325052442159245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20813420082216701628106163 31220130123325052442159245)
                ·
                  refine ⟨11707548796246894665809717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31220130123325052442159245 11707548796246894665809717)
                  ·
                    refine ⟨1097582699648146374919661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11707548796246894665809717 1097582699648146374919661)
                    ·
                      rfl

theorem cell22_3206302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_3206302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3206302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3206302 prefixEnd_3206302 := by exact prefixLift 3206302
  have htrace : WordTrace (prefixWord ++ tailWord_3206302) baseStart_3206302 baseEnd_3206302 := by
    simpa [prefixWord, tailWord_3206302, baseEnd_3206302] using wordTrace_append hprefix tailTrace_3206302
  have hstable : (prefixWord ++ tailWord_3206302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206302).length < 2 ^ (prefixWord ++ tailWord_3206302).sum := by decide
  have hdescent : baseEnd_3206302 < baseStart_3206302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206306 : List Nat := [3, 3, 1, 3, 2, 1, 3, 1, 1, 4]
def baseStart_3206306 : Nat := 118140960795 + 3206306 * 2 ^ 59
def prefixEnd_3206306 : Nat := 4983230072969 + 3 ^ 40 * 3206306 * 2
def baseEnd_3206306 : Nat := 1097584068929891697819649

theorem tailTrace_3206306 : CollatzResearch.WordTrace tailWord_3206306 prefixEnd_3206306 1097584068929891697819649 := by
  unfold tailWord_3206306
  simp only [CollatzResearch.WordTrace]
  refine ⟨29235896780527107578441693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77962391414738953542511181 29235896780527107578441693)
  ·
    refine ⟨10963461292697665341915635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29235896780527107578441693 10963461292697665341915635)
    ·
      refine ⟨16445191939046498012873453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10963461292697665341915635 16445191939046498012873453)
      ·
        refine ⟨6166946977142436754827545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16445191939046498012873453 6166946977142436754827545)
        ·
          refine ⟨4625210232856827566120659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6166946977142436754827545 4625210232856827566120659)
          ·
            refine ⟨6937815349285241349180989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4625210232856827566120659 6937815349285241349180989)
            ·
              refine ⟨2601680755981965505942871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6937815349285241349180989 2601680755981965505942871)
              ·
                refine ⟨3902521133972948258914307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2601680755981965505942871 3902521133972948258914307)
                ·
                  refine ⟨5853781700959422388371461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3902521133972948258914307 5853781700959422388371461)
                  ·
                    refine ⟨1097584068929891697819649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5853781700959422388371461 1097584068929891697819649)
                    ·
                      rfl

theorem cell22_3206306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_3206306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3206306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3206306 prefixEnd_3206306 := by exact prefixLift 3206306
  have htrace : WordTrace (prefixWord ++ tailWord_3206306) baseStart_3206306 baseEnd_3206306 := by
    simpa [prefixWord, tailWord_3206306, baseEnd_3206306] using wordTrace_append hprefix tailTrace_3206306
  have hstable : (prefixWord ++ tailWord_3206306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206306).length < 2 ^ (prefixWord ++ tailWord_3206306).sum := by decide
  have hdescent : baseEnd_3206306 < baseStart_3206306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206313 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 3, 9]
def baseStart_3206313 : Nat := 118140960795 + 3206313 * 2 ^ 59
def prefixEnd_3206313 : Nat := 4983230072969 + 3 ^ 40 * 3206313 * 2
def baseEnd_3206313 : Nat := 1097586465172946012894627

theorem tailTrace_3206313 : CollatzResearch.WordTrace tailWord_3206313 prefixEnd_3206313 1097586465172946012894627 := by
  unfold tailWord_3206313
  simp only [CollatzResearch.WordTrace]
  refine ⟨116943842433083070509271593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77962561622055380339514395 116943842433083070509271593)
  ·
    refine ⟨87707881824812302881953695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116943842433083070509271593 87707881824812302881953695)
    ·
      refine ⟨131561822737218454322930543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87707881824812302881953695 131561822737218454322930543)
      ·
        refine ⟨197342734105827681484395815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131561822737218454322930543 197342734105827681484395815)
        ·
          refine ⟨296014101158741522226593723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197342734105827681484395815 296014101158741522226593723)
          ·
            refine ⟨444021151738112283339890585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296014101158741522226593723 444021151738112283339890585)
            ·
              refine ⟨333015863803584212504917939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 444021151738112283339890585 333015863803584212504917939)
              ·
                refine ⟨499523795705376318757376909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 333015863803584212504917939 499523795705376318757376909)
                ·
                  refine ⟨187321423389516119534016341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 499523795705376318757376909 187321423389516119534016341)
                  ·
                    refine ⟨1097586465172946012894627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 187321423389516119534016341 1097586465172946012894627)
                    ·
                      rfl

theorem cell22_3206313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 9].length) (baseStart_3206313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3206313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3206313 prefixEnd_3206313 := by exact prefixLift 3206313
  have htrace : WordTrace (prefixWord ++ tailWord_3206313) baseStart_3206313 baseEnd_3206313 := by
    simpa [prefixWord, tailWord_3206313, baseEnd_3206313] using wordTrace_append hprefix tailTrace_3206313
  have hstable : (prefixWord ++ tailWord_3206313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206313).length < 2 ^ (prefixWord ++ tailWord_3206313).sum := by decide
  have hdescent : baseEnd_3206313 < baseStart_3206313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206321 : List Nat := [1, 2, 2, 5, 1, 3, 2, 2, 4]
def baseStart_3206321 : Nat := 118140960795 + 3206321 * 2 ^ 59
def prefixEnd_3206321 : Nat := 4983230072969 + 3 ^ 40 * 3206321 * 2
def baseEnd_3206321 : Nat := 365863067912145552898201

theorem tailTrace_3206321 : CollatzResearch.WordTrace tailWord_3206321 prefixEnd_3206321 365863067912145552898201 := by
  unfold tailWord_3206321
  simp only [CollatzResearch.WordTrace]
  refine ⟨116944134217054087875562817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77962756144702725250375211 116944134217054087875562817)
  ·
    refine ⟨87708100662790565906672113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116944134217054087875562817 87708100662790565906672113)
    ·
      refine ⟨65781075497092924430004085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87708100662790565906672113 65781075497092924430004085)
      ·
        refine ⟨6166975827852461665312883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65781075497092924430004085 6166975827852461665312883)
        ·
          refine ⟨9250463741778692497969325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6166975827852461665312883 9250463741778692497969325)
          ·
            refine ⟨3468923903167009686738497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9250463741778692497969325 3468923903167009686738497)
            ·
              refine ⟨2601692927375257265053873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3468923903167009686738497 2601692927375257265053873)
              ·
                refine ⟨1951269695531442948790405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2601692927375257265053873 1951269695531442948790405)
                ·
                  refine ⟨365863067912145552898201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1951269695531442948790405 365863067912145552898201)
                  ·
                    rfl

theorem cell22_3206321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 2, 4].length) (baseStart_3206321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3206321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3206321 prefixEnd_3206321 := by exact prefixLift 3206321
  have htrace : WordTrace (prefixWord ++ tailWord_3206321) baseStart_3206321 baseEnd_3206321 := by
    simpa [prefixWord, tailWord_3206321, baseEnd_3206321] using wordTrace_append hprefix tailTrace_3206321
  have hstable : (prefixWord ++ tailWord_3206321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206321).length < 2 ^ (prefixWord ++ tailWord_3206321).sum := by decide
  have hdescent : baseEnd_3206321 < baseStart_3206321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206332 : List Nat := [2, 2, 2, 3, 2, 3, 1, 7]
def baseStart_3206332 : Nat := 118140960795 + 3206332 * 2 ^ 59
def prefixEnd_3206332 : Nat := 4983230072969 + 3 ^ 40 * 3206332 * 2
def baseEnd_3206332 : Nat := 121954774362359588518841

theorem tailTrace_3206332 : CollatzResearch.WordTrace tailWord_3206332 prefixEnd_3206332 121954774362359588518841 := by
  unfold tailWord_3206332
  simp only [CollatzResearch.WordTrace]
  refine ⟨58472267710007118377106625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77963023613342824502808833 58472267710007118377106625)
  ·
    refine ⟨43854200782505338782829969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58472267710007118377106625 43854200782505338782829969)
    ·
      refine ⟨32890650586879004087122477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43854200782505338782829969 32890650586879004087122477)
      ·
        refine ⟨12333993970079626532670929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32890650586879004087122477 12333993970079626532670929)
        ·
          refine ⟨9250495477559719899503197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12333993970079626532670929 9250495477559719899503197)
          ·
            refine ⟨3468935804084894962313699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9250495477559719899503197 3468935804084894962313699)
            ·
              refine ⟨5203403706127342443470549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3468935804084894962313699 5203403706127342443470549)
              ·
                refine ⟨121954774362359588518841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5203403706127342443470549 121954774362359588518841)
                ·
                  rfl

theorem cell22_3206332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 7].length) (baseStart_3206332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3206332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3206332 prefixEnd_3206332 := by exact prefixLift 3206332
  have htrace : WordTrace (prefixWord ++ tailWord_3206332) baseStart_3206332 baseEnd_3206332 := by
    simpa [prefixWord, tailWord_3206332, baseEnd_3206332] using wordTrace_append hprefix tailTrace_3206332
  have hstable : (prefixWord ++ tailWord_3206332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206332).length < 2 ^ (prefixWord ++ tailWord_3206332).sum := by decide
  have hdescent : baseEnd_3206332 < baseStart_3206332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206381 : List Nat := [1, 5, 1, 2, 2, 1, 2, 4, 1, 3]
def baseStart_3206381 : Nat := 118140960795 + 3206381 * 2 ^ 59
def prefixEnd_3206381 : Nat := 4983230072969 + 3 ^ 40 * 3206381 * 2
def baseEnd_3206381 : Nat := 1097609742962616502194419

theorem tailTrace_3206381 : CollatzResearch.WordTrace tailWord_3206381 prefixEnd_3206381 1097609742962616502194419 := by
  unfold tailWord_3206381
  simp only [CollatzResearch.WordTrace]
  refine ⟨116946322596836718122746997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77964215064557812081831331 116946322596836718122746997)
  ·
    refine ⟨10963717743453442324007531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116946322596836718122746997 10963717743453442324007531)
    ·
      refine ⟨16445576615180163486011297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10963717743453442324007531 16445576615180163486011297)
      ·
        refine ⟨12334182461385122614508473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16445576615180163486011297 12334182461385122614508473)
        ·
          refine ⟨9250636846038841960881355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12334182461385122614508473 9250636846038841960881355)
          ·
            refine ⟨13875955269058262941322033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9250636846038841960881355 13875955269058262941322033)
            ·
              refine ⟨10406966451793697205991525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13875955269058262941322033 10406966451793697205991525)
              ·
                refine ⟨1951306209711318226123411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10406966451793697205991525 1951306209711318226123411)
                ·
                  refine ⟨2926959314566977339185117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1951306209711318226123411 2926959314566977339185117)
                  ·
                    refine ⟨1097609742962616502194419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2926959314566977339185117 1097609742962616502194419)
                    ·
                      rfl

theorem cell22_3206381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_3206381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3206381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3206381 prefixEnd_3206381 := by exact prefixLift 3206381
  have htrace : WordTrace (prefixWord ++ tailWord_3206381) baseStart_3206381 baseEnd_3206381 := by
    simpa [prefixWord, tailWord_3206381, baseEnd_3206381] using wordTrace_append hprefix tailTrace_3206381
  have hstable : (prefixWord ++ tailWord_3206381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206381).length < 2 ^ (prefixWord ++ tailWord_3206381).sum := by decide
  have hdescent : baseEnd_3206381 < baseStart_3206381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206405 : List Nat := [1, 3, 1, 1, 2, 1, 3, 4, 6]
def baseStart_3206405 : Nat := 118140960795 + 3206405 * 2 ^ 59
def prefixEnd_3206405 : Nat := 4983230072969 + 3 ^ 40 * 3206405 * 2
def baseEnd_3206405 : Nat := 365872652884362813198115

theorem tailTrace_3206405 : CollatzResearch.WordTrace tailWord_3206405 prefixEnd_3206405 365872652884362813198115 := by
  unfold tailWord_3206405
  simp only [CollatzResearch.WordTrace]
  refine ⟨116947197948749770221620669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77964798632499846814413779 116947197948749770221620669)
  ·
    refine ⟨43855199230781163833107751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116947197948749770221620669 43855199230781163833107751)
    ·
      refine ⟨65782798846171745749661627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43855199230781163833107751 65782798846171745749661627)
      ·
        refine ⟨98674198269257618624492441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65782798846171745749661627 98674198269257618624492441)
        ·
          refine ⟨74005648701943213968369331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98674198269257618624492441 74005648701943213968369331)
          ·
            refine ⟨111008473052914820952553997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74005648701943213968369331 111008473052914820952553997)
            ·
              refine ⟨41628177394843057857207749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111008473052914820952553997 41628177394843057857207749)
              ·
                refine ⟨7805283261533073348226453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41628177394843057857207749 7805283261533073348226453)
                ·
                  refine ⟨365872652884362813198115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7805283261533073348226453 365872652884362813198115)
                  ·
                    rfl

theorem cell22_3206405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 6].length) (baseStart_3206405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3206405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3206405 prefixEnd_3206405 := by exact prefixLift 3206405
  have htrace : WordTrace (prefixWord ++ tailWord_3206405) baseStart_3206405 baseEnd_3206405 := by
    simpa [prefixWord, tailWord_3206405, baseEnd_3206405] using wordTrace_append hprefix tailTrace_3206405
  have hstable : (prefixWord ++ tailWord_3206405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206405).length < 2 ^ (prefixWord ++ tailWord_3206405).sum := by decide
  have hdescent : baseEnd_3206405 < baseStart_3206405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206512 : List Nat := [2, 1, 1, 1, 4, 2, 1, 5, 5]
def baseStart_3206512 : Nat := 118140960795 + 3206512 * 2 ^ 59
def prefixEnd_3206512 : Nat := 4983230072969 + 3 ^ 40 * 3206512 * 2
def baseEnd_3206512 : Nat := 365884862313258609056339

theorem tailTrace_3206512 : CollatzResearch.WordTrace tailWord_3206512 prefixEnd_3206512 365884862313258609056339 := by
  unfold tailWord_3206512
  simp only [CollatzResearch.WordTrace]
  refine ⟨58475550279681063747882895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77967400372908084997177193 58475550279681063747882895)
  ·
    refine ⟨87713325419521595621824343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58475550279681063747882895 87713325419521595621824343)
    ·
      refine ⟨131569988129282393432736515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87713325419521595621824343 131569988129282393432736515)
      ·
        refine ⟨197354982193923590149104773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131569988129282393432736515 197354982193923590149104773)
        ·
          refine ⟨37004059161360673152957145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197354982193923590149104773 37004059161360673152957145)
          ·
            refine ⟨27753044371020504864717859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37004059161360673152957145 27753044371020504864717859)
            ·
              refine ⟨41629566556530757297076789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27753044371020504864717859 41629566556530757297076789)
              ·
                refine ⟨3902771864674758496600949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41629566556530757297076789 3902771864674758496600949)
                ·
                  refine ⟨365884862313258609056339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3902771864674758496600949 365884862313258609056339)
                  ·
                    rfl

theorem cell22_3206512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 5].length) (baseStart_3206512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3206512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3206512 prefixEnd_3206512 := by exact prefixLift 3206512
  have htrace : WordTrace (prefixWord ++ tailWord_3206512) baseStart_3206512 baseEnd_3206512 := by
    simpa [prefixWord, tailWord_3206512, baseEnd_3206512] using wordTrace_append hprefix tailTrace_3206512
  have hstable : (prefixWord ++ tailWord_3206512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206512).length < 2 ^ (prefixWord ++ tailWord_3206512).sum := by decide
  have hdescent : baseEnd_3206512 < baseStart_3206512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206546 : List Nat := [3, 2, 3, 3, 1, 1, 1, 1, 7]
def baseStart_3206546 : Nat := 118140960795 + 3206546 * 2 ^ 59
def prefixEnd_3206546 : Nat := 4983230072969 + 3 ^ 40 * 3206546 * 2
def baseEnd_3206546 : Nat := 365888741944870357272971

theorem tailTrace_3206546 : CollatzResearch.WordTrace tailWord_3206546 prefixEnd_3206546 365888741944870357272971 := by
  unfold tailWord_3206546
  simp only [CollatzResearch.WordTrace]
  refine ⟨29238085160309737825625873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77968227094159300868335661 29238085160309737825625873)
  ·
    refine ⟨21928563870232303369219405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29238085160309737825625873 21928563870232303369219405)
    ·
      refine ⟨8223211451337113763457277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21928563870232303369219405 8223211451337113763457277)
      ·
        refine ⟨3083704294251417661296479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8223211451337113763457277 3083704294251417661296479)
        ·
          refine ⟨4625556441377126491944719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3083704294251417661296479 4625556441377126491944719)
          ·
            refine ⟨6938334662065689737917079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4625556441377126491944719 6938334662065689737917079)
            ·
              refine ⟨10407501993098534606875619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6938334662065689737917079 10407501993098534606875619)
              ·
                refine ⟨15611252989647801910313429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10407501993098534606875619 15611252989647801910313429)
                ·
                  refine ⟨365888741944870357272971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15611252989647801910313429 365888741944870357272971)
                  ·
                    rfl

theorem cell22_3206546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_3206546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3206546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3206546 prefixEnd_3206546 := by exact prefixLift 3206546
  have htrace : WordTrace (prefixWord ++ tailWord_3206546) baseStart_3206546 baseEnd_3206546 := by
    simpa [prefixWord, tailWord_3206546, baseEnd_3206546] using wordTrace_append hprefix tailTrace_3206546
  have hstable : (prefixWord ++ tailWord_3206546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206546).length < 2 ^ (prefixWord ++ tailWord_3206546).sum := by decide
  have hdescent : baseEnd_3206546 < baseStart_3206546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206589 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 6, 3]
def baseStart_3206589 : Nat := 118140960795 + 3206589 * 2 ^ 59
def prefixEnd_3206589 : Nat := 4983230072969 + 3 ^ 40 * 3206589 * 2
def baseEnd_3206589 : Nat := 1097680945613373292993781

theorem tailTrace_3206589 : CollatzResearch.WordTrace tailWord_3206589 prefixEnd_3206589 1097680945613373292993781 := by
  unfold tailWord_3206589
  simp only [CollatzResearch.WordTrace]
  refine ⟨116953908980083169646318821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77969272653388779764212547 116953908980083169646318821)
  ·
    refine ⟨21928857933765594308684779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116953908980083169646318821 21928857933765594308684779)
    ·
      refine ⟨32893286900648391463027169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21928857933765594308684779 32893286900648391463027169)
      ·
        refine ⟨24669965175486293597270377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32893286900648391463027169 24669965175486293597270377)
        ·
          refine ⟨18502473881614720197952783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24669965175486293597270377 18502473881614720197952783)
          ·
            refine ⟨27753710822422080296929175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18502473881614720197952783 27753710822422080296929175)
            ·
              refine ⟨41630566233633120445393763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27753710822422080296929175 41630566233633120445393763)
              ·
                refine ⟨62445849350449680668090645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41630566233633120445393763 62445849350449680668090645)
                ·
                  refine ⟨2927149188302328781316749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62445849350449680668090645 2927149188302328781316749)
                  ·
                    refine ⟨1097680945613373292993781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2927149188302328781316749 1097680945613373292993781)
                    ·
                      rfl

theorem cell22_3206589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_3206589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3206589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3206589 prefixEnd_3206589 := by exact prefixLift 3206589
  have htrace : WordTrace (prefixWord ++ tailWord_3206589) baseStart_3206589 baseEnd_3206589 := by
    simpa [prefixWord, tailWord_3206589, baseEnd_3206589] using wordTrace_append hprefix tailTrace_3206589
  have hstable : (prefixWord ++ tailWord_3206589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206589).length < 2 ^ (prefixWord ++ tailWord_3206589).sum := by decide
  have hdescent : baseEnd_3206589 < baseStart_3206589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206602 : List Nat := [3, 1, 2, 1, 2, 3, 10]
def baseStart_3206602 : Nat := 118140960795 + 3206602 * 2 ^ 59
def prefixEnd_3206602 : Nat := 4983230072969 + 3 ^ 40 * 3206602 * 2
def baseEnd_3206602 : Nat := 40655014658483170089583

theorem tailTrace_3206602 : CollatzResearch.WordTrace tailWord_3206602 prefixEnd_3206602 40655014658483170089583 := by
  unfold tailWord_3206602
  simp only [CollatzResearch.WordTrace]
  refine ⟨29238595782259018216635515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77969588752690715244361373 29238595782259018216635515)
  ·
    refine ⟨43857893673388527324953273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29238595782259018216635515 43857893673388527324953273)
    ·
      refine ⟨32893420255041395493714955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43857893673388527324953273 32893420255041395493714955)
      ·
        refine ⟨49340130382562093240572433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32893420255041395493714955 49340130382562093240572433)
        ·
          refine ⟨37005097786921569930429325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49340130382562093240572433 37005097786921569930429325)
          ·
            refine ⟨13876911670095588723910997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37005097786921569930429325 13876911670095588723910997)
            ·
              refine ⟨40655014658483170089583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13876911670095588723910997 40655014658483170089583)
              ·
                rfl

theorem cell22_3206602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 10].length) (baseStart_3206602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3206602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3206602 prefixEnd_3206602 := by exact prefixLift 3206602
  have htrace : WordTrace (prefixWord ++ tailWord_3206602) baseStart_3206602 baseEnd_3206602 := by
    simpa [prefixWord, tailWord_3206602, baseEnd_3206602] using wordTrace_append hprefix tailTrace_3206602
  have hstable : (prefixWord ++ tailWord_3206602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206602).length < 2 ^ (prefixWord ++ tailWord_3206602).sum := by decide
  have hdescent : baseEnd_3206602 < baseStart_3206602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206604 : List Nat := [2, 2, 1, 4, 2, 1, 1, 1, 4, 4]
def baseStart_3206604 : Nat := 118140960795 + 3206604 * 2 ^ 59
def prefixEnd_3206604 : Nat := 4983230072969 + 3 ^ 40 * 3206604 * 2
def baseEnd_3206604 : Nat := 1097686080419918253868735

theorem tailTrace_3206604 : CollatzResearch.WordTrace tailWord_3206604 prefixEnd_3206604 1097686080419918253868735 := by
  unfold tailWord_3206604
  simp only [CollatzResearch.WordTrace]
  refine ⟨58477228037514413604057433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77969637383352551472076577 58477228037514413604057433)
  ·
    refine ⟨43857921028135810203043075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58477228037514413604057433 43857921028135810203043075)
    ·
      refine ⟨65786881542203715304564613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43857921028135810203043075 65786881542203715304564613)
      ·
        refine ⟨12335040289163196619605865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65786881542203715304564613 12335040289163196619605865)
        ·
          refine ⟨9251280216872397464704399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12335040289163196619605865 9251280216872397464704399)
          ·
            refine ⟨13876920325308596197056599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9251280216872397464704399 13876920325308596197056599)
            ·
              refine ⟨20815380487962894295584899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13876920325308596197056599 20815380487962894295584899)
              ·
                refine ⟨31223070731944341443377349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20815380487962894295584899 31223070731944341443377349)
                ·
                  refine ⟨5854325762239564020633253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31223070731944341443377349 5854325762239564020633253)
                  ·
                    refine ⟨1097686080419918253868735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5854325762239564020633253 1097686080419918253868735)
                    ·
                      rfl

theorem cell22_3206604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_3206604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3206604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3206604 prefixEnd_3206604 := by exact prefixLift 3206604
  have htrace : WordTrace (prefixWord ++ tailWord_3206604) baseStart_3206604 baseEnd_3206604 := by
    simpa [prefixWord, tailWord_3206604, baseEnd_3206604] using wordTrace_append hprefix tailTrace_3206604
  have hstable : (prefixWord ++ tailWord_3206604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206604).length < 2 ^ (prefixWord ++ tailWord_3206604).sum := by decide
  have hdescent : baseEnd_3206604 < baseStart_3206604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206647 : List Nat := [1, 1, 3, 1, 1, 1, 1, 6, 7]
def baseStart_3206647 : Nat := 118140960795 + 3206647 * 2 ^ 59
def prefixEnd_3206647 : Nat := 4983230072969 + 3 ^ 40 * 3206647 * 2
def baseEnd_3206647 : Nat := 365900266732893491681201

theorem tailTrace_3206647 : CollatzResearch.WordTrace tailWord_3206647 prefixEnd_3206647 365900266732893491681201 := by
  unfold tailWord_3206647
  simp only [CollatzResearch.WordTrace]
  refine ⟨116956024413873045551930195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77970682942582030367953463 116956024413873045551930195)
  ·
    refine ⟨175434036620809568327895293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116956024413873045551930195 175434036620809568327895293)
    ·
      refine ⟨65787763732803588122960735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175434036620809568327895293 65787763732803588122960735)
      ·
        refine ⟨98681645599205382184441103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65787763732803588122960735 98681645599205382184441103)
        ·
          refine ⟨148022468398808073276661655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98681645599205382184441103 148022468398808073276661655)
          ·
            refine ⟨222033702598212109914992483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148022468398808073276661655 222033702598212109914992483)
            ·
              refine ⟨333050553897318164872488725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222033702598212109914992483 333050553897318164872488725)
              ·
                refine ⟨15611744713936788978397909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 333050553897318164872488725 15611744713936788978397909)
                ·
                  refine ⟨365900266732893491681201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15611744713936788978397909 365900266732893491681201)
                  ·
                    rfl

theorem cell22_3206647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 7].length) (baseStart_3206647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3206647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3206647 prefixEnd_3206647 := by exact prefixLift 3206647
  have htrace : WordTrace (prefixWord ++ tailWord_3206647) baseStart_3206647 baseEnd_3206647 := by
    simpa [prefixWord, tailWord_3206647, baseEnd_3206647] using wordTrace_append hprefix tailTrace_3206647
  have hstable : (prefixWord ++ tailWord_3206647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206647).length < 2 ^ (prefixWord ++ tailWord_3206647).sum := by decide
  have hdescent : baseEnd_3206647 < baseStart_3206647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206664 : List Nat := [2, 1, 3, 2, 1, 1, 3, 4, 5]
def baseStart_3206664 : Nat := 118140960795 + 3206664 * 2 ^ 59
def prefixEnd_3206664 : Nat := 4983230072969 + 3 ^ 40 * 3206664 * 2
def baseEnd_3206664 : Nat := 365902206548699365789517

theorem tailTrace_3206664 : CollatzResearch.WordTrace tailWord_3206664 prefixEnd_3206664 365902206548699365789517 := by
  unfold tailWord_3206664
  simp only [CollatzResearch.WordTrace]
  refine ⟨58478322227405728727649523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77971096303207638303532697 58478322227405728727649523)
  ·
    refine ⟨87717483341108593091474285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58478322227405728727649523 87717483341108593091474285)
    ·
      refine ⟨32894056252915722409302857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87717483341108593091474285 32894056252915722409302857)
      ·
        refine ⟨24670542189686791806977143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32894056252915722409302857 24670542189686791806977143)
        ·
          refine ⟨37005813284530187710465715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24670542189686791806977143 37005813284530187710465715)
          ·
            refine ⟨55508719926795281565698573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37005813284530187710465715 55508719926795281565698573)
            ·
              refine ⟨20815769972548230587136965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55508719926795281565698573 20815769972548230587136965)
              ·
                refine ⟨3902956869852793235088181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20815769972548230587136965 3902956869852793235088181)
                ·
                  refine ⟨365902206548699365789517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3902956869852793235088181 365902206548699365789517)
                  ·
                    rfl

theorem cell22_3206664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 5].length) (baseStart_3206664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3206664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3206664 prefixEnd_3206664 := by exact prefixLift 3206664
  have htrace : WordTrace (prefixWord ++ tailWord_3206664) baseStart_3206664 baseEnd_3206664 := by
    simpa [prefixWord, tailWord_3206664, baseEnd_3206664] using wordTrace_append hprefix tailTrace_3206664
  have hstable : (prefixWord ++ tailWord_3206664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206664).length < 2 ^ (prefixWord ++ tailWord_3206664).sum := by decide
  have hdescent : baseEnd_3206664 < baseStart_3206664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206711 : List Nat := [1, 1, 3, 1, 2, 5, 1, 3, 1, 4]
def baseStart_3206711 : Nat := 118140960795 + 3206711 * 2 ^ 59
def prefixEnd_3206711 : Nat := 4983230072969 + 3 ^ 40 * 3206711 * 2
def baseEnd_3206711 : Nat := 1097722708706605641443407

theorem tailTrace_3206711 : CollatzResearch.WordTrace tailWord_3206711 prefixEnd_3206711 1097722708706605641443407 := by
  unfold tailWord_3206711
  simp only [CollatzResearch.WordTrace]
  refine ⟨116958358685641184482259987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77972239123760789654839991 116958358685641184482259987)
  ·
    refine ⟨175437538028461776723389981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116958358685641184482259987 175437538028461776723389981)
    ·
      refine ⟨65789076760673166271271243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175437538028461776723389981 65789076760673166271271243)
      ·
        refine ⟨98683615141009749406906865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65789076760673166271271243 98683615141009749406906865)
        ·
          refine ⟨74012711355757312055180149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98683615141009749406906865 74012711355757312055180149)
          ·
            refine ⟨6938691689602248005173139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74012711355757312055180149 6938691689602248005173139)
            ·
              refine ⟨10408037534403372007759709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6938691689602248005173139 10408037534403372007759709)
              ·
                refine ⟨3903014075401264502909891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10408037534403372007759709 3903014075401264502909891)
                ·
                  refine ⟨5854521113101896754364837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3903014075401264502909891 5854521113101896754364837)
                  ·
                    refine ⟨1097722708706605641443407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5854521113101896754364837 1097722708706605641443407)
                    ·
                      rfl

theorem cell22_3206711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 4].length) (baseStart_3206711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3206711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3206711 prefixEnd_3206711 := by exact prefixLift 3206711
  have htrace : WordTrace (prefixWord ++ tailWord_3206711) baseStart_3206711 baseEnd_3206711 := by
    simpa [prefixWord, tailWord_3206711, baseEnd_3206711] using wordTrace_append hprefix tailTrace_3206711
  have hstable : (prefixWord ++ tailWord_3206711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206711).length < 2 ^ (prefixWord ++ tailWord_3206711).sum := by decide
  have hdescent : baseEnd_3206711 < baseStart_3206711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206760 : List Nat := [2, 1, 4, 3, 1, 3, 1, 3, 4]
def baseStart_3206760 : Nat := 118140960795 + 3206760 * 2 ^ 59
def prefixEnd_3206760 : Nat := 4983230072969 + 3 ^ 40 * 3206760 * 2
def baseEnd_3206760 : Nat := 365913160802661948989419

theorem tailTrace_3206760 : CollatzResearch.WordTrace tailWord_3206760 prefixEnd_3206760 365913160802661948989419 := by
  unfold tailWord_3206760
  simp only [CollatzResearch.WordTrace]
  refine ⟨58480072931231832925396867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77973430574975777233862489 58480072931231832925396867)
  ·
    refine ⟨87720109396847749388095301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58480072931231832925396867 87720109396847749388095301)
    ·
      refine ⟨16447520511908953010267869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87720109396847749388095301 16447520511908953010267869)
      ·
        refine ⟨6167820191965857378850451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16447520511908953010267869 6167820191965857378850451)
        ·
          refine ⟨9251730287948786068275677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6167820191965857378850451 9251730287948786068275677)
          ·
            refine ⟨3469398857980794775603379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9251730287948786068275677 3469398857980794775603379)
            ·
              refine ⟨5204098286971192163405069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3469398857980794775603379 5204098286971192163405069)
              ·
                refine ⟨1951536857614197061276901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5204098286971192163405069 1951536857614197061276901)
                ·
                  refine ⟨365913160802661948989419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1951536857614197061276901 365913160802661948989419)
                  ·
                    rfl

theorem cell22_3206760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 3, 4].length) (baseStart_3206760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3206760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3206760 prefixEnd_3206760 := by exact prefixLift 3206760
  have htrace : WordTrace (prefixWord ++ tailWord_3206760) baseStart_3206760 baseEnd_3206760 := by
    simpa [prefixWord, tailWord_3206760, baseEnd_3206760] using wordTrace_append hprefix tailTrace_3206760
  have hstable : (prefixWord ++ tailWord_3206760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206760).length < 2 ^ (prefixWord ++ tailWord_3206760).sum := by decide
  have hdescent : baseEnd_3206760 < baseStart_3206760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206773 : List Nat := [1, 3, 4, 2, 1, 2, 1, 2, 2, 4]
def baseStart_3206773 : Nat := 118140960795 + 3206773 * 2 ^ 59
def prefixEnd_3206773 : Nat := 4983230072969 + 3 ^ 40 * 3206773 * 2
def baseEnd_3206773 : Nat := 1097743932573658146393217

theorem tailTrace_3206773 : CollatzResearch.WordTrace tailWord_3206773 prefixEnd_3206773 1097743932573658146393217 := by
  unfold tailWord_3206773
  simp only [CollatzResearch.WordTrace]
  refine ⟨116960620011416569071016973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77973746674277712714011315 116960620011416569071016973)
  ·
    refine ⟨43860232504281213401631365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116960620011416569071016973 43860232504281213401631365)
    ·
      refine ⟨8223793594552727512805881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43860232504281213401631365 8223793594552727512805881)
      ·
        refine ⟨6167845195914545634604411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8223793594552727512805881 6167845195914545634604411)
        ·
          refine ⟨9251767793871818451906617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6167845195914545634604411 9251767793871818451906617)
          ·
            refine ⟨6938825845403863838929963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9251767793871818451906617 6938825845403863838929963)
            ·
              refine ⟨10408238768105795758394945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6938825845403863838929963 10408238768105795758394945)
              ·
                refine ⟨7806179076079346818796209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10408238768105795758394945 7806179076079346818796209)
                ·
                  refine ⟨5854634307059510114097157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7806179076079346818796209 5854634307059510114097157)
                  ·
                    refine ⟨1097743932573658146393217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5854634307059510114097157 1097743932573658146393217)
                    ·
                      rfl

theorem cell22_3206773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_3206773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3206773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3206773 prefixEnd_3206773 := by exact prefixLift 3206773
  have htrace : WordTrace (prefixWord ++ tailWord_3206773) baseStart_3206773 baseEnd_3206773 := by
    simpa [prefixWord, tailWord_3206773, baseEnd_3206773] using wordTrace_append hprefix tailTrace_3206773
  have hstable : (prefixWord ++ tailWord_3206773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206773).length < 2 ^ (prefixWord ++ tailWord_3206773).sum := by decide
  have hdescent : baseEnd_3206773 < baseStart_3206773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206784 : List Nat := [2, 1, 1, 2, 1, 4, 2, 1, 2, 6]
def baseStart_3206784 : Nat := 118140960795 + 3206784 * 2 ^ 59
def prefixEnd_3206784 : Nat := 4983230072969 + 3 ^ 40 * 3206784 * 2
def baseEnd_3206784 : Nat := 1097747698098457784368183

theorem tailTrace_3206784 : CollatzResearch.WordTrace tailWord_3206784 prefixEnd_3206784 1097747698098457784368183 := by
  unfold tailWord_3206784
  simp only [CollatzResearch.WordTrace]
  refine ⟨58480510607188358974833703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77974014142917811966444937 58480510607188358974833703)
  ·
    refine ⟨87720765910782538462250555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58480510607188358974833703 87720765910782538462250555)
    ·
      refine ⟨131581148866173807693375833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87720765910782538462250555 131581148866173807693375833)
      ·
        refine ⟨98685861649630355770031875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131581148866173807693375833 98685861649630355770031875)
        ·
          refine ⟨148028792474445533655047813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98685861649630355770031875 148028792474445533655047813)
          ·
            refine ⟨27755398588958537560321465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148028792474445533655047813 27755398588958537560321465)
            ·
              refine ⟨20816548941718903170241099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27755398588958537560321465 20816548941718903170241099)
              ·
                refine ⟨31224823412578354755361649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20816548941718903170241099 31224823412578354755361649)
                ·
                  refine ⟨23418617559433766066521237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31224823412578354755361649 23418617559433766066521237)
                  ·
                    refine ⟨1097747698098457784368183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23418617559433766066521237 1097747698098457784368183)
                    ·
                      rfl

theorem cell22_3206784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 2, 6].length) (baseStart_3206784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3206784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3206784 prefixEnd_3206784 := by exact prefixLift 3206784
  have htrace : WordTrace (prefixWord ++ tailWord_3206784) baseStart_3206784 baseEnd_3206784 := by
    simpa [prefixWord, tailWord_3206784, baseEnd_3206784] using wordTrace_append hprefix tailTrace_3206784
  have hstable : (prefixWord ++ tailWord_3206784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206784).length < 2 ^ (prefixWord ++ tailWord_3206784).sum := by decide
  have hdescent : baseEnd_3206784 < baseStart_3206784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206837 : List Nat := [1, 3, 3, 3, 2, 1, 1, 4, 1, 3]
def baseStart_3206837 : Nat := 118140960795 + 3206837 * 2 ^ 59
def prefixEnd_3206837 : Nat := 4983230072969 + 3 ^ 40 * 3206837 * 2
def baseEnd_3206837 : Nat := 1097765841081583312793021

theorem tailTrace_3206837 : CollatzResearch.WordTrace tailWord_3206837 prefixEnd_3206837 1097765841081583312793021 := by
  unfold tailWord_3206837
  simp only [CollatzResearch.WordTrace]
  refine ⟨116962954283184708001346765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77975302855456472000897843 116962954283184708001346765)
  ·
    refine ⟨43861107856194265500505037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116962954283184708001346765 43861107856194265500505037)
    ·
      refine ⟨16447915446072849562689389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43861107856194265500505037 16447915446072849562689389)
      ·
        refine ⟨6167968292277318586008521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16447915446072849562689389 6167968292277318586008521)
        ·
          refine ⟨4625976219207988939506391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6167968292277318586008521 4625976219207988939506391)
          ·
            refine ⟨6938964328811983409259587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4625976219207988939506391 6938964328811983409259587)
            ·
              refine ⟨10408446493217975113889381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6938964328811983409259587 10408446493217975113889381)
              ·
                refine ⟨1951583717478370333854259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10408446493217975113889381 1951583717478370333854259)
                ·
                  refine ⟨2927375576217555500781389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1951583717478370333854259 2927375576217555500781389)
                  ·
                    refine ⟨1097765841081583312793021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2927375576217555500781389 1097765841081583312793021)
                    ·
                      rfl

theorem cell22_3206837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_3206837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3206837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3206837 prefixEnd_3206837 := by exact prefixLift 3206837
  have htrace : WordTrace (prefixWord ++ tailWord_3206837) baseStart_3206837 baseEnd_3206837 := by
    simpa [prefixWord, tailWord_3206837, baseEnd_3206837] using wordTrace_append hprefix tailTrace_3206837
  have hstable : (prefixWord ++ tailWord_3206837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206837).length < 2 ^ (prefixWord ++ tailWord_3206837).sum := by decide
  have hdescent : baseEnd_3206837 < baseStart_3206837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206891 : List Nat := [1, 1, 1, 1, 2, 4, 2, 4, 2, 4]
def baseStart_3206891 : Nat := 118140960795 + 3206891 * 2 ^ 59
def prefixEnd_3206891 : Nat := 4983230072969 + 3 ^ 40 * 3206891 * 2
def baseEnd_3206891 : Nat := 1097784326385145171942855

theorem tailTrace_3206891 : CollatzResearch.WordTrace tailWord_3206891 prefixEnd_3206891 1097784326385145171942855 := by
  unfold tailWord_3206891
  simp only [CollatzResearch.WordTrace]
  refine ⟨116964923824989075223812527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77976615883326050149208351 116964923824989075223812527)
  ·
    refine ⟨175447385737483612835718791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116964923824989075223812527 175447385737483612835718791)
    ·
      refine ⟨263171078606225419253578187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175447385737483612835718791 263171078606225419253578187)
      ·
        refine ⟨394756617909338128880367281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263171078606225419253578187 394756617909338128880367281)
        ·
          refine ⟨296067463432003596660275461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394756617909338128880367281 296067463432003596660275461)
          ·
            refine ⟨55512649393500674373801649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 296067463432003596660275461 55512649393500674373801649)
            ·
              refine ⟨41634487045125505780351237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55512649393500674373801649 41634487045125505780351237)
              ·
                refine ⟨7806466320961032333815857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41634487045125505780351237 7806466320961032333815857)
                ·
                  refine ⟨5854849740720774250361893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7806466320961032333815857 5854849740720774250361893)
                  ·
                    refine ⟨1097784326385145171942855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5854849740720774250361893 1097784326385145171942855)
                    ·
                      rfl

theorem cell22_3206891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 4].length) (baseStart_3206891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3206891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3206891 prefixEnd_3206891 := by exact prefixLift 3206891
  have htrace : WordTrace (prefixWord ++ tailWord_3206891) baseStart_3206891 baseEnd_3206891 := by
    simpa [prefixWord, tailWord_3206891, baseEnd_3206891] using wordTrace_append hprefix tailTrace_3206891
  have hstable : (prefixWord ++ tailWord_3206891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206891).length < 2 ^ (prefixWord ++ tailWord_3206891).sum := by decide
  have hdescent : baseEnd_3206891 < baseStart_3206891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206968 : List Nat := [2, 1, 2, 1, 3, 4, 1, 3, 5]
def baseStart_3206968 : Nat := 118140960795 + 3206968 * 2 ^ 59
def prefixEnd_3206968 : Nat := 4983230072969 + 3 ^ 40 * 3206968 * 2
def baseEnd_3206968 : Nat := 365936895019580879255873

theorem tailTrace_3206968 : CollatzResearch.WordTrace tailWord_3206968 prefixEnd_3206968 365936895019580879255873 := by
  unfold tailWord_3206968
  simp only [CollatzResearch.WordTrace]
  refine ⟨58483866122855058687182779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77978488163806744916243705 58483866122855058687182779)
  ·
    refine ⟨87725799184282588030774169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58483866122855058687182779 87725799184282588030774169)
    ·
      refine ⟨65794349388211941023080627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87725799184282588030774169 65794349388211941023080627)
      ·
        refine ⟨98691524082317911534620941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65794349388211941023080627 98691524082317911534620941)
        ·
          refine ⟨37009321530869216825482853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98691524082317911534620941 37009321530869216825482853)
          ·
            refine ⟨6939247787037978154778035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37009321530869216825482853 6939247787037978154778035)
            ·
              refine ⟨10408871680556967232167053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6939247787037978154778035 10408871680556967232167053)
              ·
                refine ⟨3903326880208862712062645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10408871680556967232167053 3903326880208862712062645)
                ·
                  refine ⟨365936895019580879255873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3903326880208862712062645 365936895019580879255873)
                  ·
                    rfl

theorem cell22_3206968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 5].length) (baseStart_3206968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3206968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3206968 prefixEnd_3206968 := by exact prefixLift 3206968
  have htrace : WordTrace (prefixWord ++ tailWord_3206968) baseStart_3206968 baseEnd_3206968 := by
    simpa [prefixWord, tailWord_3206968, baseEnd_3206968] using wordTrace_append hprefix tailTrace_3206968
  have hstable : (prefixWord ++ tailWord_3206968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206968).length < 2 ^ (prefixWord ++ tailWord_3206968).sum := by decide
  have hdescent : baseEnd_3206968 < baseStart_3206968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207043 : List Nat := [1, 1, 1, 3, 4, 3, 1, 1, 1, 6]
def baseStart_3207043 : Nat := 118140960795 + 3207043 * 2 ^ 59
def prefixEnd_3207043 : Nat := 4983230072969 + 3 ^ 40 * 3207043 * 2
def baseEnd_3207043 : Nat := 1097836359091467442142389

theorem tailTrace_3207043 : CollatzResearch.WordTrace tailWord_3207043 prefixEnd_3207043 1097836359091467442142389 := by
  unfold tailWord_3207043
  simp only [CollatzResearch.WordTrace]
  refine ⟨116970467720438405183345783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77980311813625603455563855 116970467720438405183345783)
  ·
    refine ⟨175455701580657607775018675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116970467720438405183345783 175455701580657607775018675)
    ·
      refine ⟨263183552370986411662528013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175455701580657607775018675 263183552370986411662528013)
      ·
        refine ⟨98693832139119904373448005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263183552370986411662528013 98693832139119904373448005)
        ·
          refine ⟨18505093526084982070021501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98693832139119904373448005 18505093526084982070021501)
          ·
            refine ⟨6939410072281868276258063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18505093526084982070021501 6939410072281868276258063)
            ·
              refine ⟨10409115108422802414387095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6939410072281868276258063 10409115108422802414387095)
              ·
                refine ⟨15613672662634203621580643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10409115108422802414387095 15613672662634203621580643)
                ·
                  refine ⟨23420508993951305432370965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15613672662634203621580643 23420508993951305432370965)
                  ·
                    refine ⟨1097836359091467442142389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23420508993951305432370965 1097836359091467442142389)
                    ·
                      rfl

theorem cell22_3207043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 6].length) (baseStart_3207043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3207043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3207043 prefixEnd_3207043 := by exact prefixLift 3207043
  have htrace : WordTrace (prefixWord ++ tailWord_3207043) baseStart_3207043 baseEnd_3207043 := by
    simpa [prefixWord, tailWord_3207043, baseEnd_3207043] using wordTrace_append hprefix tailTrace_3207043
  have hstable : (prefixWord ++ tailWord_3207043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207043).length < 2 ^ (prefixWord ++ tailWord_3207043).sum := by decide
  have hdescent : baseEnd_3207043 < baseStart_3207043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207047 : List Nat := [1, 1, 4, 2, 4, 1, 2, 3, 4]
def baseStart_3207047 : Nat := 118140960795 + 3207047 * 2 ^ 59
def prefixEnd_3207047 : Nat := 4983230072969 + 3 ^ 40 * 3207047 * 2
def baseEnd_3207047 : Nat := 365945909457737588347459

theorem tailTrace_3207047 : CollatzResearch.WordTrace tailWord_3207047 prefixEnd_3207047 365945909457737588347459 := by
  unfold tailWord_3207047
  simp only [CollatzResearch.WordTrace]
  refine ⟨116970613612423913866491395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77980409074949275910994263 116970613612423913866491395)
  ·
    refine ⟨175455920418635870799737093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116970613612423913866491395 175455920418635870799737093)
    ·
      refine ⟨32897985078494225774950705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175455920418635870799737093 32897985078494225774950705)
      ·
        refine ⟨24673488808870669331213029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32897985078494225774950705 24673488808870669331213029)
        ·
          refine ⟨4626279151663250499602443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24673488808870669331213029 4626279151663250499602443)
          ·
            refine ⟨6939418727494875749403665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4626279151663250499602443 6939418727494875749403665)
            ·
              refine ⟨5204564045621156812052749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6939418727494875749403665 5204564045621156812052749)
              ·
                refine ⟨1951711517107933804519781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5204564045621156812052749 1951711517107933804519781)
                ·
                  refine ⟨365945909457737588347459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1951711517107933804519781 365945909457737588347459)
                  ·
                    rfl

theorem cell22_3207047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 3, 4].length) (baseStart_3207047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3207047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3207047 prefixEnd_3207047 := by exact prefixLift 3207047
  have htrace : WordTrace (prefixWord ++ tailWord_3207047) baseStart_3207047 baseEnd_3207047 := by
    simpa [prefixWord, tailWord_3207047, baseEnd_3207047] using wordTrace_append hprefix tailTrace_3207047
  have hstable : (prefixWord ++ tailWord_3207047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207047).length < 2 ^ (prefixWord ++ tailWord_3207047).sum := by decide
  have hdescent : baseEnd_3207047 < baseStart_3207047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207079 : List Nat := [1, 1, 6, 1, 2, 2, 3, 1, 2, 3]
def baseStart_3207079 : Nat := 118140960795 + 3207079 * 2 ^ 59
def prefixEnd_3207079 : Nat := 4983230072969 + 3 ^ 40 * 3207079 * 2
def baseEnd_3207079 : Nat := 1097848682627175348242279

theorem tailTrace_3207079 : CollatzResearch.WordTrace tailWord_3207079 prefixEnd_3207079 1097848682627175348242279 := by
  unfold tailWord_3207079
  simp only [CollatzResearch.WordTrace]
  refine ⟨116971780748307983331656291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77981187165538655554437527 116971780748307983331656291)
  ·
    refine ⟨175457671122461974997484437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116971780748307983331656291 175457671122461974997484437)
    ·
      refine ⟨8224578333865405078007083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 175457671122461974997484437 8224578333865405078007083)
      ·
        refine ⟨12336867500798107617010625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8224578333865405078007083 12336867500798107617010625)
        ·
          refine ⟨9252650625598580712757969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12336867500798107617010625 9252650625598580712757969)
          ·
            refine ⟨6939487969198935534568477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9252650625598580712757969 6939487969198935534568477)
            ·
              refine ⟨2602307988449600825463179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6939487969198935534568477 2602307988449600825463179)
              ·
                refine ⟨3903461982674401238194769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2602307988449600825463179 3903461982674401238194769)
                ·
                  refine ⟨2927596487005800928646077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3903461982674401238194769 2927596487005800928646077)
                  ·
                    refine ⟨1097848682627175348242279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2927596487005800928646077 1097848682627175348242279)
                    ·
                      rfl

theorem cell22_3207079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_3207079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3207079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3207079 prefixEnd_3207079 := by exact prefixLift 3207079
  have htrace : WordTrace (prefixWord ++ tailWord_3207079) baseStart_3207079 baseEnd_3207079 := by
    simpa [prefixWord, tailWord_3207079, baseEnd_3207079] using wordTrace_append hprefix tailTrace_3207079
  have hstable : (prefixWord ++ tailWord_3207079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207079).length < 2 ^ (prefixWord ++ tailWord_3207079).sum := by decide
  have hdescent : baseEnd_3207079 < baseStart_3207079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207092 : List Nat := [2, 5, 2, 1, 2, 1, 1, 8]
def baseStart_3207092 : Nat := 118140960795 + 3207092 * 2 ^ 59
def prefixEnd_3207092 : Nat := 4983230072969 + 3 ^ 40 * 3207092 * 2
def baseEnd_3207092 : Nat := 121983681421427516407471

theorem tailTrace_3207092 : CollatzResearch.WordTrace tailWord_3207092 prefixEnd_3207092 121983681421427516407471 := by
  unfold tailWord_3207092
  simp only [CollatzResearch.WordTrace]
  refine ⟨58486127448630443275939765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77981503264840591034586353 58486127448630443275939765)
  ·
    refine ⟨5483074448309104057119353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58486127448630443275939765 5483074448309104057119353)
    ·
      refine ⟨4112305836231828042839515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5483074448309104057119353 4112305836231828042839515)
      ·
        refine ⟨6168458754347742064259273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4112305836231828042839515 6168458754347742064259273)
        ·
          refine ⟨4626344065760806548194455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6168458754347742064259273 4626344065760806548194455)
          ·
            refine ⟨6939516098641209822291683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4626344065760806548194455 6939516098641209822291683)
            ·
              refine ⟨10409274147961814733437525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6939516098641209822291683 10409274147961814733437525)
              ·
                refine ⟨121983681421427516407471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10409274147961814733437525 121983681421427516407471)
                ·
                  rfl

theorem cell22_3207092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 8].length) (baseStart_3207092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3207092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3207092 prefixEnd_3207092 := by exact prefixLift 3207092
  have htrace : WordTrace (prefixWord ++ tailWord_3207092) baseStart_3207092 baseEnd_3207092 := by
    simpa [prefixWord, tailWord_3207092, baseEnd_3207092] using wordTrace_append hprefix tailTrace_3207092
  have hstable : (prefixWord ++ tailWord_3207092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207092).length < 2 ^ (prefixWord ++ tailWord_3207092).sum := by decide
  have hdescent : baseEnd_3207092 < baseStart_3207092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207148 : List Nat := [2, 2, 1, 1, 2, 1, 1, 6, 6]
def baseStart_3207148 : Nat := 118140960795 + 3207148 * 2 ^ 59
def prefixEnd_3207148 : Nat := 4983230072969 + 3 ^ 40 * 3207148 * 2
def baseEnd_3207148 : Nat := 365957434245760722755689

theorem tailTrace_3207148 : CollatzResearch.WordTrace tailWord_3207148 prefixEnd_3207148 365957434245760722755689 := by
  unfold tailWord_3207148
  simp only [CollatzResearch.WordTrace]
  refine ⟨58487148692529004057959049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77982864923372005410612065 58487148692529004057959049)
  ·
    refine ⟨43865361519396753043469287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58487148692529004057959049 43865361519396753043469287)
    ·
      refine ⟨65798042279095129565203931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43865361519396753043469287 65798042279095129565203931)
      ·
        refine ⟨98697063418642694347805897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65798042279095129565203931 98697063418642694347805897)
        ·
          refine ⟨74022797563982020760854423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98697063418642694347805897 74022797563982020760854423)
          ·
            refine ⟨111034196345973031141281635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74022797563982020760854423 111034196345973031141281635)
            ·
              refine ⟨166551294518959546711922453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111034196345973031141281635 166551294518959546711922453)
              ·
                refine ⟨7807091930576228752121365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 166551294518959546711922453 7807091930576228752121365)
                ·
                  refine ⟨365957434245760722755689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7807091930576228752121365 365957434245760722755689)
                  ·
                    rfl

theorem cell22_3207148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 6].length) (baseStart_3207148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3207148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3207148 prefixEnd_3207148 := by exact prefixLift 3207148
  have htrace : WordTrace (prefixWord ++ tailWord_3207148) baseStart_3207148 baseEnd_3207148 := by
    simpa [prefixWord, tailWord_3207148, baseEnd_3207148] using wordTrace_append hprefix tailTrace_3207148
  have hstable : (prefixWord ++ tailWord_3207148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207148).length < 2 ^ (prefixWord ++ tailWord_3207148).sum := by decide
  have hdescent : baseEnd_3207148 < baseStart_3207148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207163 : List Nat := [1, 1, 1, 1, 1, 3, 5, 1, 3, 5]
def baseStart_3207163 : Nat := 118140960795 + 3207163 * 2 ^ 59
def prefixEnd_3207163 : Nat := 4983230072969 + 3 ^ 40 * 3207163 * 2
def baseEnd_3207163 : Nat := 1097877437543827129142021

theorem tailTrace_3207163 : CollatzResearch.WordTrace tailWord_3207163 prefixEnd_3207163 1097877437543827129142021 := by
  unfold tailWord_3207163
  simp only [CollatzResearch.WordTrace]
  refine ⟨116974844480003665677714143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77983229653335777118476095 116974844480003665677714143)
  ·
    refine ⟨175462266720005498516571215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116974844480003665677714143 175462266720005498516571215)
    ·
      refine ⟨263193400080008247774856823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175462266720005498516571215 263193400080008247774856823)
      ·
        refine ⟨394790100120012371662285235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263193400080008247774856823 394790100120012371662285235)
        ·
          refine ⟨592185150180018557493427853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394790100120012371662285235 592185150180018557493427853)
          ·
            refine ⟨222069431317506959060035445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 592185150180018557493427853 222069431317506959060035445)
            ·
              refine ⟨20819009186016277411878323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 222069431317506959060035445 20819009186016277411878323)
              ·
                refine ⟨31228513779024416117817485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20819009186016277411878323 31228513779024416117817485)
                ·
                  refine ⟨11710692667134156044181557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31228513779024416117817485 11710692667134156044181557)
                  ·
                    refine ⟨1097877437543827129142021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11710692667134156044181557 1097877437543827129142021)
                    ·
                      rfl

theorem cell22_3207163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 5].length) (baseStart_3207163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3207163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3207163 prefixEnd_3207163 := by exact prefixLift 3207163
  have htrace : WordTrace (prefixWord ++ tailWord_3207163) baseStart_3207163 baseEnd_3207163 := by
    simpa [prefixWord, tailWord_3207163, baseEnd_3207163] using wordTrace_append hprefix tailTrace_3207163
  have hstable : (prefixWord ++ tailWord_3207163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207163).length < 2 ^ (prefixWord ++ tailWord_3207163).sum := by decide
  have hdescent : baseEnd_3207163 < baseStart_3207163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207182 : List Nat := [4, 1, 1, 2, 2, 1, 3, 4, 4]
def baseStart_3207182 : Nat := 118140960795 + 3207182 * 2 ^ 59
def prefixEnd_3207182 : Nat := 4983230072969 + 3 ^ 40 * 3207182 * 2
def baseEnd_3207182 : Nat := 365961313877372470972321

theorem tailTrace_3207182 : CollatzResearch.WordTrace tailWord_3207182 prefixEnd_3207182 365961313877372470972321 := by
  unfold tailWord_3207182
  simp only [CollatzResearch.WordTrace]
  refine ⟨14621942183366853990331975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77983691644623221281770533 14621942183366853990331975)
  ·
    refine ⟨21932913275050280985497963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14621942183366853990331975 21932913275050280985497963)
    ·
      refine ⟨32899369912575421478246945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21932913275050280985497963 32899369912575421478246945)
      ·
        refine ⟨24674527434431566108685209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32899369912575421478246945 24674527434431566108685209)
        ·
          refine ⟨18505895575823674581513907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24674527434431566108685209 18505895575823674581513907)
          ·
            refine ⟨27758843363735511872270861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18505895575823674581513907 27758843363735511872270861)
            ·
              refine ⟨10409566261400816952101573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27758843363735511872270861 10409566261400816952101573)
              ·
                refine ⟨1951793674012653178519045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10409566261400816952101573 1951793674012653178519045)
                ·
                  refine ⟨365961313877372470972321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1951793674012653178519045 365961313877372470972321)
                  ·
                    rfl

theorem cell22_3207182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_3207182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3207182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3207182 prefixEnd_3207182 := by exact prefixLift 3207182
  have htrace : WordTrace (prefixWord ++ tailWord_3207182) baseStart_3207182 baseEnd_3207182 := by
    simpa [prefixWord, tailWord_3207182, baseEnd_3207182] using wordTrace_append hprefix tailTrace_3207182
  have hstable : (prefixWord ++ tailWord_3207182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207182).length < 2 ^ (prefixWord ++ tailWord_3207182).sum := by decide
  have hdescent : baseEnd_3207182 < baseStart_3207182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207197 : List Nat := [1, 4, 2, 2, 2, 2, 2, 1, 1, 5]
def baseStart_3207197 : Nat := 118140960795 + 3207197 * 2 ^ 59
def prefixEnd_3207197 : Nat := 4983230072969 + 3 ^ 40 * 3207197 * 2
def baseEnd_3207197 : Nat := 1097889076438662373791917

theorem tailTrace_3207197 : CollatzResearch.WordTrace tailWord_3207197 prefixEnd_3207197 1097889076438662373791917 := by
  unfold tailWord_3207197
  simp only [CollatzResearch.WordTrace]
  refine ⟨116976084561880489484451845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77984056374586992989634563 116976084561880489484451845)
  ·
    refine ⟨21933015855352591778334721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116976084561880489484451845 21933015855352591778334721)
    ·
      refine ⟨16449761891514443833751041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21933015855352591778334721 16449761891514443833751041)
      ·
        refine ⟨12337321418635832875313281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16449761891514443833751041 12337321418635832875313281)
        ·
          refine ⟨9252991063976874656484961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12337321418635832875313281 9252991063976874656484961)
          ·
            refine ⟨6939743297982655992363721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9252991063976874656484961 6939743297982655992363721)
            ·
              refine ⟨5204807473486991994272791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6939743297982655992363721 5204807473486991994272791)
              ·
                refine ⟨7807211210230487991409187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5204807473486991994272791 7807211210230487991409187)
                ·
                  refine ⟨11710816815345731987113781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7807211210230487991409187 11710816815345731987113781)
                  ·
                    refine ⟨1097889076438662373791917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11710816815345731987113781 1097889076438662373791917)
                    ·
                      rfl

theorem cell22_3207197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_3207197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3207197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3207197 prefixEnd_3207197 := by exact prefixLift 3207197
  have htrace : WordTrace (prefixWord ++ tailWord_3207197) baseStart_3207197 baseEnd_3207197 := by
    simpa [prefixWord, tailWord_3207197, baseEnd_3207197] using wordTrace_append hprefix tailTrace_3207197
  have hstable : (prefixWord ++ tailWord_3207197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207197).length < 2 ^ (prefixWord ++ tailWord_3207197).sum := by decide
  have hdescent : baseEnd_3207197 < baseStart_3207197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207255 : List Nat := [1, 1, 3, 2, 2, 1, 2, 5, 5]
def baseStart_3207255 : Nat := 118140960795 + 3207255 * 2 ^ 59
def prefixEnd_3207255 : Nat := 4983230072969 + 3 ^ 40 * 3207255 * 2
def baseEnd_3207255 : Nat := 365969643674656518613913

theorem tailTrace_3207255 : CollatzResearch.WordTrace tailWord_3207255 prefixEnd_3207255 365969643674656518613913 := by
  unfold tailWord_3207255
  simp only [CollatzResearch.WordTrace]
  refine ⟨116978199995670365390063219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77985466663780243593375479 116978199995670365390063219)
  ·
    refine ⟨175467299993505548085094829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116978199995670365390063219 175467299993505548085094829)
    ·
      refine ⟨65800237497564580531910561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175467299993505548085094829 65800237497564580531910561)
      ·
        refine ⟨49350178123173435398932921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65800237497564580531910561 49350178123173435398932921)
        ·
          refine ⟨37012633592380076549199691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49350178123173435398932921 37012633592380076549199691)
          ·
            refine ⟨55518950388570114823799537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37012633592380076549199691 55518950388570114823799537)
            ·
              refine ⟨41639212791427586117849653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55518950388570114823799537 41639212791427586117849653)
              ·
                refine ⟨3903676199196336198548405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41639212791427586117849653 3903676199196336198548405)
                ·
                  refine ⟨365969643674656518613913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3903676199196336198548405 365969643674656518613913)
                  ·
                    rfl

theorem cell22_3207255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 5].length) (baseStart_3207255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3207255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3207255 prefixEnd_3207255 := by exact prefixLift 3207255
  have htrace : WordTrace (prefixWord ++ tailWord_3207255) baseStart_3207255 baseEnd_3207255 := by
    simpa [prefixWord, tailWord_3207255, baseEnd_3207255] using wordTrace_append hprefix tailTrace_3207255
  have hstable : (prefixWord ++ tailWord_3207255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207255).length < 2 ^ (prefixWord ++ tailWord_3207255).sum := by decide
  have hdescent : baseEnd_3207255 < baseStart_3207255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207276 : List Nat := [2, 2, 1, 1, 3, 5, 1, 3, 1, 3]
def baseStart_3207276 : Nat := 118140960795 + 3207276 * 2 ^ 59
def prefixEnd_3207276 : Nat := 4983230072969 + 3 ^ 40 * 3207276 * 2
def baseEnd_3207276 : Nat := 1097916119753132501066675

theorem tailTrace_3207276 : CollatzResearch.WordTrace tailWord_3207276 prefixEnd_3207276 1097916119753132501066675 := by
  unfold tailWord_3207276
  simp only [CollatzResearch.WordTrace]
  refine ⟨58489482964297142988288841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77985977285729523984385121 58489482964297142988288841)
  ·
    refine ⟨43867112223222857241216631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58489482964297142988288841 43867112223222857241216631)
    ·
      refine ⟨65800668334834285861824947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43867112223222857241216631 65800668334834285861824947)
      ·
        refine ⟨98701002502251428792737421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65800668334834285861824947 98701002502251428792737421)
        ·
          refine ⟨37012875938344285797276533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98701002502251428792737421 37012875938344285797276533)
          ·
            refine ⟨3469957119219776793494675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37012875938344285797276533 3469957119219776793494675)
            ·
              refine ⟨5204935678829665190242013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3469957119219776793494675 5204935678829665190242013)
              ·
                refine ⟨1951850879561124446340755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5204935678829665190242013 1951850879561124446340755)
                ·
                  refine ⟨2927776319341686669511133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1951850879561124446340755 2927776319341686669511133)
                  ·
                    refine ⟨1097916119753132501066675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2927776319341686669511133 1097916119753132501066675)
                    ·
                      rfl

theorem cell22_3207276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 3, 1, 3].length) (baseStart_3207276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3207276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3207276 prefixEnd_3207276 := by exact prefixLift 3207276
  have htrace : WordTrace (prefixWord ++ tailWord_3207276) baseStart_3207276 baseEnd_3207276 := by
    simpa [prefixWord, tailWord_3207276, baseEnd_3207276] using wordTrace_append hprefix tailTrace_3207276
  have hstable : (prefixWord ++ tailWord_3207276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207276).length < 2 ^ (prefixWord ++ tailWord_3207276).sum := by decide
  have hdescent : baseEnd_3207276 < baseStart_3207276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207315 : List Nat := [1, 1, 1, 2, 1, 2, 3, 5, 1, 5]
def baseStart_3207315 : Nat := 118140960795 + 3207315 * 2 ^ 59
def prefixEnd_3207315 : Nat := 4983230072969 + 3 ^ 40 * 3207315 * 2
def baseEnd_3207315 : Nat := 1097929470250149399341555

theorem tailTrace_3207315 : CollatzResearch.WordTrace tailWord_3207315 prefixEnd_3207315 1097929470250149399341555 := by
  unfold tailWord_3207315
  simp only [CollatzResearch.WordTrace]
  refine ⟨116980388375452995637247399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77986925583635330424831599 116980388375452995637247399)
  ·
    refine ⟨175470582563179493455871099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116980388375452995637247399 175470582563179493455871099)
    ·
      refine ⟨263205873844769240183806649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175470582563179493455871099 263205873844769240183806649)
      ·
        refine ⟨197404405383576930137854987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263205873844769240183806649 197404405383576930137854987)
        ·
          refine ⟨296106608075365395206782481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197404405383576930137854987 296106608075365395206782481)
          ·
            refine ⟨222079956056524046405086861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296106608075365395206782481 222079956056524046405086861)
            ·
              refine ⟨83279983521196517401907573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 222079956056524046405086861 83279983521196517401907573)
              ·
                refine ⟨7807498455112173506428835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83279983521196517401907573 7807498455112173506428835)
                ·
                  refine ⟨11711247682668260259643253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7807498455112173506428835 11711247682668260259643253)
                  ·
                    refine ⟨1097929470250149399341555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11711247682668260259643253 1097929470250149399341555)
                    ·
                      rfl

theorem cell22_3207315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 5].length) (baseStart_3207315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3207315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3207315 prefixEnd_3207315 := by exact prefixLift 3207315
  have htrace : WordTrace (prefixWord ++ tailWord_3207315) baseStart_3207315 baseEnd_3207315 := by
    simpa [prefixWord, tailWord_3207315, baseEnd_3207315] using wordTrace_append hprefix tailTrace_3207315
  have hstable : (prefixWord ++ tailWord_3207315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207315).length < 2 ^ (prefixWord ++ tailWord_3207315).sum := by decide
  have hdescent : baseEnd_3207315 < baseStart_3207315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207345 : List Nat := [1, 2, 2, 5, 12]
def baseStart_3207345 : Nat := 118140960795 + 3207345 * 2 ^ 59
def prefixEnd_3207345 : Nat := 4983230072969 + 3 ^ 40 * 3207345 * 2
def baseEnd_3207345 : Nat := 4518270534416622720541

theorem tailTrace_3207345 : CollatzResearch.WordTrace tailWord_3207345 prefixEnd_3207345 4518270534416622720541 := by
  unfold tailWord_3207345
  simp only [CollatzResearch.WordTrace]
  refine ⟨116981482565344310760839489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77987655043562873840559659 116981482565344310760839489)
  ·
    refine ⟨87736111924008233070629617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116981482565344310760839489 87736111924008233070629617)
    ·
      refine ⟨65802083943006174802972213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87736111924008233070629617 65802083943006174802972213)
      ·
        refine ⟨6168945369656828887778645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65802083943006174802972213 6168945369656828887778645)
        ·
          refine ⟨4518270534416622720541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 6168945369656828887778645 4518270534416622720541)
          ·
            rfl

theorem cell22_3207345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 12].length) (baseStart_3207345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3207345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3207345 prefixEnd_3207345 := by exact prefixLift 3207345
  have htrace : WordTrace (prefixWord ++ tailWord_3207345) baseStart_3207345 baseEnd_3207345 := by
    simpa [prefixWord, tailWord_3207345, baseEnd_3207345] using wordTrace_append hprefix tailTrace_3207345
  have hstable : (prefixWord ++ tailWord_3207345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207345).length < 2 ^ (prefixWord ++ tailWord_3207345).sum := by decide
  have hdescent : baseEnd_3207345 < baseStart_3207345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207351 : List Nat := [1, 1, 3, 1, 4, 4, 2, 2, 4]
def baseStart_3207351 : Nat := 118140960795 + 3207351 * 2 ^ 59
def prefixEnd_3207351 : Nat := 4983230072969 + 3 ^ 40 * 3207351 * 2
def baseEnd_3207351 : Nat := 365980597928619101813815

theorem tailTrace_3207351 : CollatzResearch.WordTrace tailWord_3207351 prefixEnd_3207351 365980597928619101813815 := by
  unfold tailWord_3207351
  simp only [CollatzResearch.WordTrace]
  refine ⟨116981701403322573785557907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77987800935548382523705271 116981701403322573785557907)
  ·
    refine ⟨175472552104983860678336861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116981701403322573785557907 175472552104983860678336861)
    ·
      refine ⟨65802207039368947754376323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175472552104983860678336861 65802207039368947754376323)
      ·
        refine ⟨98703310559053421631564485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65802207039368947754376323 98703310559053421631564485)
        ·
          refine ⟨18506870729822516555918341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98703310559053421631564485 18506870729822516555918341)
          ·
            refine ⟨3470038261841721854234689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18506870729822516555918341 3470038261841721854234689)
            ·
              refine ⟨2602528696381291390676017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3470038261841721854234689 2602528696381291390676017)
              ·
                refine ⟨1951896522285968543007013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2602528696381291390676017 1951896522285968543007013)
                ·
                  refine ⟨365980597928619101813815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1951896522285968543007013 365980597928619101813815)
                  ·
                    rfl

theorem cell22_3207351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 2, 4].length) (baseStart_3207351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3207351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3207351 prefixEnd_3207351 := by exact prefixLift 3207351
  have htrace : WordTrace (prefixWord ++ tailWord_3207351) baseStart_3207351 baseEnd_3207351 := by
    simpa [prefixWord, tailWord_3207351, baseEnd_3207351] using wordTrace_append hprefix tailTrace_3207351
  have hstable : (prefixWord ++ tailWord_3207351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207351).length < 2 ^ (prefixWord ++ tailWord_3207351).sum := by decide
  have hdescent : baseEnd_3207351 < baseStart_3207351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207375 : List Nat := [1, 1, 2, 1, 1, 3, 3, 2, 2, 6]
def baseStart_3207375 : Nat := 118140960795 + 3207375 * 2 ^ 59
def prefixEnd_3207375 : Nat := 4983230072969 + 3 ^ 40 * 3207375 * 2
def baseEnd_3207375 : Nat := 1097950009476329242841371

theorem tailTrace_3207375 : CollatzResearch.WordTrace tailWord_3207375 prefixEnd_3207375 1097950009476329242841371 := by
  unfold tailWord_3207375
  simp only [CollatzResearch.WordTrace]
  refine ⟨116982576755235625884431579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77988384503490417256287719 116982576755235625884431579)
  ·
    refine ⟨175473865132853438826647369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116982576755235625884431579 175473865132853438826647369)
    ·
      refine ⟨131605398849640079119985527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175473865132853438826647369 131605398849640079119985527)
      ·
        refine ⟨197408098274460118679978291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131605398849640079119985527 197408098274460118679978291)
        ·
          refine ⟨296112147411690178019967437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197408098274460118679978291 296112147411690178019967437)
          ·
            refine ⟨111042055279383816757487789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 296112147411690178019967437 111042055279383816757487789)
            ·
              refine ⟨41640770729768931284057921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111042055279383816757487789 41640770729768931284057921)
              ·
                refine ⟨31230578047326698463043441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41640770729768931284057921 31230578047326698463043441)
                ·
                  refine ⟨23422933535495023847282581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31230578047326698463043441 23422933535495023847282581)
                  ·
                    refine ⟨1097950009476329242841371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23422933535495023847282581 1097950009476329242841371)
                    ·
                      rfl

theorem cell22_3207375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 6].length) (baseStart_3207375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3207375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3207375 prefixEnd_3207375 := by exact prefixLift 3207375
  have htrace : WordTrace (prefixWord ++ tailWord_3207375) baseStart_3207375 baseEnd_3207375 := by
    simpa [prefixWord, tailWord_3207375, baseEnd_3207375] using wordTrace_append hprefix tailTrace_3207375
  have hstable : (prefixWord ++ tailWord_3207375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207375).length < 2 ^ (prefixWord ++ tailWord_3207375).sum := by decide
  have hdescent : baseEnd_3207375 < baseStart_3207375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207377 : List Nat := [1, 2, 2, 1, 2, 2, 3, 1, 5, 3]
def baseStart_3207377 : Nat := 118140960795 + 3207377 * 2 ^ 59
def prefixEnd_3207377 : Nat := 4983230072969 + 3 ^ 40 * 3207377 * 2
def baseEnd_3207377 : Nat := 1097950694117201904291365

theorem tailTrace_3207377 : CollatzResearch.WordTrace tailWord_3207377 prefixEnd_3207377 1097950694117201904291365 := by
  unfold tailWord_3207377
  simp only [CollatzResearch.WordTrace]
  refine ⟨116982649701228380226004385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77988433134152253484002923 116982649701228380226004385)
  ·
    refine ⟨87736987275921285169503289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116982649701228380226004385 87736987275921285169503289)
    ·
      refine ⟨65802740456940963877127467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87736987275921285169503289 65802740456940963877127467)
      ·
        refine ⟨98704110685411445815691201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65802740456940963877127467 98704110685411445815691201)
        ·
          refine ⟨74028083014058584361768401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98704110685411445815691201 74028083014058584361768401)
          ·
            refine ⟨55521062260543938271326301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74028083014058584361768401 55521062260543938271326301)
            ·
              refine ⟨20820398347703976851747363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55521062260543938271326301 20820398347703976851747363)
              ·
                refine ⟨31230597521555965277621045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20820398347703976851747363 31230597521555965277621045)
                ·
                  refine ⟨2927868517645871744776973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31230597521555965277621045 2927868517645871744776973)
                  ·
                    refine ⟨1097950694117201904291365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2927868517645871744776973 1097950694117201904291365)
                    ·
                      rfl

theorem cell22_3207377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 5, 3].length) (baseStart_3207377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3207377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3207377 prefixEnd_3207377 := by exact prefixLift 3207377
  have htrace : WordTrace (prefixWord ++ tailWord_3207377) baseStart_3207377 baseEnd_3207377 := by
    simpa [prefixWord, tailWord_3207377, baseEnd_3207377] using wordTrace_append hprefix tailTrace_3207377
  have hstable : (prefixWord ++ tailWord_3207377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207377).length < 2 ^ (prefixWord ++ tailWord_3207377).sum := by decide
  have hdescent : baseEnd_3207377 < baseStart_3207377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207381 : List Nat := [1, 3, 2, 4, 2, 2, 1, 1, 2, 4]
def baseStart_3207381 : Nat := 118140960795 + 3207381 * 2 ^ 59
def prefixEnd_3207381 : Nat := 4983230072969 + 3 ^ 40 * 3207381 * 2
def baseEnd_3207381 : Nat := 1097952063398947227191353

theorem tailTrace_3207381 : CollatzResearch.WordTrace tailWord_3207381 prefixEnd_3207381 1097952063398947227191353 := by
  unfold tailWord_3207381
  simp only [CollatzResearch.WordTrace]
  refine ⟨116982795593213888909149997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77988530395475925939433331 116982795593213888909149997)
  ·
    refine ⟨43868548347455208340931249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116982795593213888909149997 43868548347455208340931249)
    ·
      refine ⟨32901411260591406255698437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43868548347455208340931249 32901411260591406255698437)
      ·
        refine ⟨6169014611360888672943457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32901411260591406255698437 6169014611360888672943457)
        ·
          refine ⟨4626760958520666504707593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6169014611360888672943457 4626760958520666504707593)
          ·
            refine ⟨3470070718890499878530695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4626760958520666504707593 3470070718890499878530695)
            ·
              refine ⟨5205106078335749817796043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3470070718890499878530695 5205106078335749817796043)
              ·
                refine ⟨7807659117503624726694065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5205106078335749817796043 7807659117503624726694065)
                ·
                  refine ⟨5855744338127718545020549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7807659117503624726694065 5855744338127718545020549)
                  ·
                    refine ⟨1097952063398947227191353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5855744338127718545020549 1097952063398947227191353)
                    ·
                      rfl

theorem cell22_3207381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_3207381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3207381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3207381 prefixEnd_3207381 := by exact prefixLift 3207381
  have htrace : WordTrace (prefixWord ++ tailWord_3207381) baseStart_3207381 baseEnd_3207381 := by
    simpa [prefixWord, tailWord_3207381, baseEnd_3207381] using wordTrace_append hprefix tailTrace_3207381
  have hstable : (prefixWord ++ tailWord_3207381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207381).length < 2 ^ (prefixWord ++ tailWord_3207381).sum := by decide
  have hdescent : baseEnd_3207381 < baseStart_3207381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207407 : List Nat := [1, 1, 2, 1, 6, 2, 1, 1, 7]
def baseStart_3207407 : Nat := 118140960795 + 3207407 * 2 ^ 59
def prefixEnd_3207407 : Nat := 4983230072969 + 3 ^ 40 * 3207407 * 2
def baseEnd_3207407 : Nat := 365986987910097275347091

theorem tailTrace_3207407 : CollatzResearch.WordTrace tailWord_3207407 prefixEnd_3207407 365986987910097275347091 := by
  unfold tailWord_3207407
  simp only [CollatzResearch.WordTrace]
  refine ⟨116983743891119695349596475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77989162594079796899730983 116983743891119695349596475)
  ·
    refine ⟨175475615836679543024394713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116983743891119695349596475 175475615836679543024394713)
    ·
      refine ⟨131606711877509657268296035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175475615836679543024394713 131606711877509657268296035)
      ·
        refine ⟨197410067816264485902444053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131606711877509657268296035 197410067816264485902444053)
        ·
          refine ⟨9253596928887397776677065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 197410067816264485902444053 9253596928887397776677065)
          ·
            refine ⟨6940197696665548332507799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9253596928887397776677065 6940197696665548332507799)
            ·
              refine ⟨10410296544998322498761699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6940197696665548332507799 10410296544998322498761699)
              ·
                refine ⟨15615444817497483748142549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10410296544998322498761699 15615444817497483748142549)
                ·
                  refine ⟨365986987910097275347091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15615444817497483748142549 365986987910097275347091)
                  ·
                    rfl

theorem cell22_3207407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 7].length) (baseStart_3207407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3207407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3207407 prefixEnd_3207407 := by exact prefixLift 3207407
  have htrace : WordTrace (prefixWord ++ tailWord_3207407) baseStart_3207407 baseEnd_3207407 := by
    simpa [prefixWord, tailWord_3207407, baseEnd_3207407] using wordTrace_append hprefix tailTrace_3207407
  have hstable : (prefixWord ++ tailWord_3207407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207407).length < 2 ^ (prefixWord ++ tailWord_3207407).sum := by decide
  have hdescent : baseEnd_3207407 < baseStart_3207407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207520 : List Nat := [2, 1, 1, 3, 6, 1, 2, 2, 4]
def baseStart_3207520 : Nat := 118140960795 + 3207520 * 2 ^ 59
def prefixEnd_3207520 : Nat := 4983230072969 + 3 ^ 40 * 3207520 * 2
def baseEnd_3207520 : Nat := 365999881979865732655309

theorem tailTrace_3207520 : CollatzResearch.WordTrace tailWord_3207520 prefixEnd_3207520 365999881979865732655309 := by
  unfold tailWord_3207520
  simp only [CollatzResearch.WordTrace]
  refine ⟨58493932669855157824230007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77991910226473543765640009 58493932669855157824230007)
  ·
    refine ⟨87740899004782736736345011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58493932669855157824230007 87740899004782736736345011)
    ·
      refine ⟨131611348507174105104517517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87740899004782736736345011 131611348507174105104517517)
      ·
        refine ⟨49354255690190289414194069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131611348507174105104517517 49354255690190289414194069)
        ·
          refine ⟨2313480735477669816290347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49354255690190289414194069 2313480735477669816290347)
          ·
            refine ⟨3470221103216504724435521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2313480735477669816290347 3470221103216504724435521)
            ·
              refine ⟨2602665827412378543326641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3470221103216504724435521 2602665827412378543326641)
              ·
                refine ⟨1951999370559283907494981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2602665827412378543326641 1951999370559283907494981)
                ·
                  refine ⟨365999881979865732655309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1951999370559283907494981 365999881979865732655309)
                  ·
                    rfl

theorem cell22_3207520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 2, 4].length) (baseStart_3207520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3207520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3207520 prefixEnd_3207520 := by exact prefixLift 3207520
  have htrace : WordTrace (prefixWord ++ tailWord_3207520) baseStart_3207520 baseEnd_3207520 := by
    simpa [prefixWord, tailWord_3207520, baseEnd_3207520] using wordTrace_append hprefix tailTrace_3207520
  have hstable : (prefixWord ++ tailWord_3207520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207520).length < 2 ^ (prefixWord ++ tailWord_3207520).sum := by decide
  have hdescent : baseEnd_3207520 < baseStart_3207520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207529 : List Nat := [1, 2, 1, 1, 1, 3, 4, 3, 3, 3]
def baseStart_3207529 : Nat := 118140960795 + 3207529 * 2 ^ 59
def prefixEnd_3207529 : Nat := 4983230072969 + 3 ^ 40 * 3207529 * 2
def baseEnd_3207529 : Nat := 1098002726823524174490899

theorem tailTrace_3207529 : CollatzResearch.WordTrace tailWord_3207529 prefixEnd_3207529 1098002726823524174490899 := by
  unfold tailWord_3207529
  simp only [CollatzResearch.WordTrace]
  refine ⟨116988193596677710185537641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77992129064451806790358427 116988193596677710185537641)
  ·
    refine ⟨87741145197508282639153231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116988193596677710185537641 87741145197508282639153231)
    ·
      refine ⟨131611717796262423958729847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87741145197508282639153231 131611717796262423958729847)
      ·
        refine ⟨197417576694393635938094771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131611717796262423958729847 197417576694393635938094771)
        ·
          refine ⟨296126365041590453907142157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197417576694393635938094771 296126365041590453907142157)
          ·
            refine ⟨111047386890596420215178309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 296126365041590453907142157 111047386890596420215178309)
            ·
              refine ⟨20821385041986828790345933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111047386890596420215178309 20821385041986828790345933)
              ·
                refine ⟨7808019390745060796379725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20821385041986828790345933 7808019390745060796379725)
                ·
                  refine ⟨2928007271529397798642397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7808019390745060796379725 2928007271529397798642397)
                  ·
                    refine ⟨1098002726823524174490899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2928007271529397798642397 1098002726823524174490899)
                    ·
                      rfl

theorem cell22_3207529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 3, 3].length) (baseStart_3207529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3207529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3207529 prefixEnd_3207529 := by exact prefixLift 3207529
  have htrace : WordTrace (prefixWord ++ tailWord_3207529) baseStart_3207529 baseEnd_3207529 := by
    simpa [prefixWord, tailWord_3207529, baseEnd_3207529] using wordTrace_append hprefix tailTrace_3207529
  have hstable : (prefixWord ++ tailWord_3207529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207529).length < 2 ^ (prefixWord ++ tailWord_3207529).sum := by decide
  have hdescent : baseEnd_3207529 < baseStart_3207529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207557 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 3, 7]
def baseStart_3207557 : Nat := 118140960795 + 3207557 * 2 ^ 59
def prefixEnd_3207557 : Nat := 4983230072969 + 3 ^ 40 * 3207557 * 2
def baseEnd_3207557 : Nat := 1098012311795741434790813

theorem tailTrace_3207557 : CollatzResearch.WordTrace tailWord_3207557 prefixEnd_3207557 1098012311795741434790813 := by
  unfold tailWord_3207557
  simp only [CollatzResearch.WordTrace]
  refine ⟨116989214840576270967556925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77992809893717513978371283 116989214840576270967556925)
  ·
    refine ⟨43870955565216101612833847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116989214840576270967556925 43870955565216101612833847)
    ·
      refine ⟨65806433347824152419250771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43870955565216101612833847 65806433347824152419250771)
      ·
        refine ⟨98709650021736228628876157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65806433347824152419250771 98709650021736228628876157)
        ·
          refine ⟨37016118758151085735828559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98709650021736228628876157 37016118758151085735828559)
          ·
            refine ⟨55524178137226628603742839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37016118758151085735828559 55524178137226628603742839)
            ·
              refine ⟨83286267205839942905614259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55524178137226628603742839 83286267205839942905614259)
              ·
                refine ⟨124929400808759914358421389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83286267205839942905614259 124929400808759914358421389)
                ·
                  refine ⟨46848525303284967884408021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124929400808759914358421389 46848525303284967884408021)
                  ·
                    refine ⟨1098012311795741434790813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46848525303284967884408021 1098012311795741434790813)
                    ·
                      rfl

theorem cell22_3207557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_3207557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3207557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3207557 prefixEnd_3207557 := by exact prefixLift 3207557
  have htrace : WordTrace (prefixWord ++ tailWord_3207557) baseStart_3207557 baseEnd_3207557 := by
    simpa [prefixWord, tailWord_3207557, baseEnd_3207557] using wordTrace_append hprefix tailTrace_3207557
  have hstable : (prefixWord ++ tailWord_3207557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207557).length < 2 ^ (prefixWord ++ tailWord_3207557).sum := by decide
  have hdescent : baseEnd_3207557 < baseStart_3207557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207563 : List Nat := [1, 1, 1, 1, 4, 5, 2, 3, 1, 3]
def baseStart_3207563 : Nat := 118140960795 + 3207563 * 2 ^ 59
def prefixEnd_3207563 : Nat := 4983230072969 + 3 ^ 40 * 3207563 * 2
def baseEnd_3207563 : Nat := 1098014365718359419140795

theorem tailTrace_3207563 : CollatzResearch.WordTrace tailWord_3207563 prefixEnd_3207563 1098014365718359419140795 := by
  unfold tailWord_3207563
  simp only [CollatzResearch.WordTrace]
  refine ⟨116989433678554533992275343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77992955785703022661516895 116989433678554533992275343)
  ·
    refine ⟨175484150517831800988413015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116989433678554533992275343 175484150517831800988413015)
    ·
      refine ⟨263226225776747701482619523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175484150517831800988413015 263226225776747701482619523)
      ·
        refine ⟨394839338665121552223929285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263226225776747701482619523 394839338665121552223929285)
        ·
          refine ⟨74032375999710291041986741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 394839338665121552223929285 74032375999710291041986741)
          ·
            refine ⟨6940535249972839785186257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74032375999710291041986741 6940535249972839785186257)
            ·
              refine ⟨5205401437479629838889693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6940535249972839785186257 5205401437479629838889693)
              ·
                refine ⟨1952025539054861189583635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5205401437479629838889693 1952025539054861189583635)
                ·
                  refine ⟨2928038308582291784375453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1952025539054861189583635 2928038308582291784375453)
                  ·
                    refine ⟨1098014365718359419140795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2928038308582291784375453 1098014365718359419140795)
                    ·
                      rfl

theorem cell22_3207563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 3, 1, 3].length) (baseStart_3207563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3207563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3207563 prefixEnd_3207563 := by exact prefixLift 3207563
  have htrace : WordTrace (prefixWord ++ tailWord_3207563) baseStart_3207563 baseEnd_3207563 := by
    simpa [prefixWord, tailWord_3207563, baseEnd_3207563] using wordTrace_append hprefix tailTrace_3207563
  have hstable : (prefixWord ++ tailWord_3207563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207563).length < 2 ^ (prefixWord ++ tailWord_3207563).sum := by decide
  have hdescent : baseEnd_3207563 < baseStart_3207563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207576 : List Nat := [2, 1, 2, 5, 1, 1, 3, 2, 5]
def baseStart_3207576 : Nat := 118140960795 + 3207576 * 2 ^ 59
def prefixEnd_3207576 : Nat := 4983230072969 + 3 ^ 40 * 3207576 * 2
def baseEnd_3207576 : Nat := 366006271961343906188585

theorem tailTrace_3207576 : CollatzResearch.WordTrace tailWord_3207576 prefixEnd_3207576 366006271961343906188585 := by
  unfold tailWord_3207576
  simp only [CollatzResearch.WordTrace]
  refine ⟨58494953913753718606249291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77993271885004958141665721 58494953913753718606249291)
  ·
    refine ⟨87742430870630577909373937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58494953913753718606249291 87742430870630577909373937)
    ·
      refine ⟨65806823152972933432030453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87742430870630577909373937 65806823152972933432030453)
      ·
        refine ⟨6169389670591212509252855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65806823152972933432030453 6169389670591212509252855)
        ·
          refine ⟨9254084505886818763879283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6169389670591212509252855 9254084505886818763879283)
          ·
            refine ⟨13881126758830228145818925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9254084505886818763879283 13881126758830228145818925)
            ·
              refine ⟨5205422534561335554682097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13881126758830228145818925 5205422534561335554682097)
              ·
                refine ⟨3904066900921001666011573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5205422534561335554682097 3904066900921001666011573)
                ·
                  refine ⟨366006271961343906188585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3904066900921001666011573 366006271961343906188585)
                  ·
                    rfl

theorem cell22_3207576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 5].length) (baseStart_3207576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3207576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3207576 prefixEnd_3207576 := by exact prefixLift 3207576
  have htrace : WordTrace (prefixWord ++ tailWord_3207576) baseStart_3207576 baseEnd_3207576 := by
    simpa [prefixWord, tailWord_3207576, baseEnd_3207576] using wordTrace_append hprefix tailTrace_3207576
  have hstable : (prefixWord ++ tailWord_3207576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207576).length < 2 ^ (prefixWord ++ tailWord_3207576).sum := by decide
  have hdescent : baseEnd_3207576 < baseStart_3207576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207649 : List Nat := [1, 2, 3, 1, 2, 2, 4, 7]
def baseStart_3207649 : Nat := 118140960795 + 3207649 * 2 ^ 59
def prefixEnd_3207649 : Nat := 4983230072969 + 3 ^ 40 * 3207649 * 2
def baseEnd_3207649 : Nat := 122004867252875984610059

theorem tailTrace_3207649 : CollatzResearch.WordTrace tailWord_3207649 prefixEnd_3207649 122004867252875984610059 := by
  unfold tailWord_3207649
  simp only [CollatzResearch.WordTrace]
  refine ⟨116992570356242970679906001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77995046904161980453270667 116992570356242970679906001)
  ·
    refine ⟨87744427767182228009929501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116992570356242970679906001 87744427767182228009929501)
    ·
      refine ⟨32904160412693335503723563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87744427767182228009929501 32904160412693335503723563)
      ·
        refine ⟨49356240619040003255585345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32904160412693335503723563 49356240619040003255585345)
        ·
          refine ⟨37017180464280002441689009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49356240619040003255585345 37017180464280002441689009)
          ·
            refine ⟨27762885348210001831266757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37017180464280002441689009 27762885348210001831266757)
            ·
              refine ⟨5205541002789375343362517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27762885348210001831266757 5205541002789375343362517)
              ·
                refine ⟨122004867252875984610059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5205541002789375343362517 122004867252875984610059)
                ·
                  rfl

theorem cell22_3207649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 7].length) (baseStart_3207649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3207649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3207649 prefixEnd_3207649 := by exact prefixLift 3207649
  have htrace : WordTrace (prefixWord ++ tailWord_3207649) baseStart_3207649 baseEnd_3207649 := by
    simpa [prefixWord, tailWord_3207649, baseEnd_3207649] using wordTrace_append hprefix tailTrace_3207649
  have hstable : (prefixWord ++ tailWord_3207649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207649).length < 2 ^ (prefixWord ++ tailWord_3207649).sum := by decide
  have hdescent : baseEnd_3207649 < baseStart_3207649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207756 : List Nat := [2, 2, 1, 3, 1, 2, 4, 1, 6]
def baseStart_3207756 : Nat := 118140960795 + 3207756 * 2 ^ 59
def prefixEnd_3207756 : Nat := 4983230072969 + 3 ^ 40 * 3207756 * 2
def baseEnd_3207756 : Nat := 366026811187523749688401

theorem tailTrace_3207756 : CollatzResearch.WordTrace tailWord_3207756 prefixEnd_3207756 366026811187523749688401 := by
  unfold tailWord_3207756
  simp only [CollatzResearch.WordTrace]
  refine ⟨58498236483427663977025561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77997648644570218636034081 58498236483427663977025561)
  ·
    refine ⟨43873677362570747982769171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58498236483427663977025561 43873677362570747982769171)
    ·
      refine ⟨65810516043856121974153757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43873677362570747982769171 65810516043856121974153757)
      ·
        refine ⟨24678943516446045740307659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65810516043856121974153757 24678943516446045740307659)
        ·
          refine ⟨37018415274669068610461489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24678943516446045740307659 37018415274669068610461489)
          ·
            refine ⟨27763811456001801457846117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37018415274669068610461489 27763811456001801457846117)
            ·
              refine ⟨5205714648000337773346147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27763811456001801457846117 5205714648000337773346147)
              ·
                refine ⟨7808571972000506660019221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5205714648000337773346147 7808571972000506660019221)
                ·
                  refine ⟨366026811187523749688401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7808571972000506660019221 366026811187523749688401)
                  ·
                    rfl

theorem cell22_3207756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 6].length) (baseStart_3207756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3207756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3207756 prefixEnd_3207756 := by exact prefixLift 3207756
  have htrace : WordTrace (prefixWord ++ tailWord_3207756) baseStart_3207756 baseEnd_3207756 := by
    simpa [prefixWord, tailWord_3207756, baseEnd_3207756] using wordTrace_append hprefix tailTrace_3207756
  have hstable : (prefixWord ++ tailWord_3207756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207756).length < 2 ^ (prefixWord ++ tailWord_3207756).sum := by decide
  have hdescent : baseEnd_3207756 < baseStart_3207756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207786 : List Nat := [3, 1, 3, 2, 1, 1, 1, 3, 1, 6]
def baseStart_3207786 : Nat := 118140960795 + 3207786 * 2 ^ 59
def prefixEnd_3207786 : Nat := 4983230072969 + 3 ^ 40 * 3207786 * 2
def baseEnd_3207786 : Nat := 1098090703175661170815111

theorem tailTrace_3207786 : CollatzResearch.WordTrace tailWord_3207786 prefixEnd_3207786 1098090703175661170815111 := by
  unfold tailWord_3207786
  simp only [CollatzResearch.WordTrace]
  refine ⟨29249391789186660769410803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77998378104497762051762141 29249391789186660769410803)
  ·
    refine ⟨43874087683779991154116205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29249391789186660769410803 43874087683779991154116205)
    ·
      refine ⟨16452782881417496682793577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43874087683779991154116205 16452782881417496682793577)
      ·
        refine ⟨12339587161063122512095183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16452782881417496682793577 12339587161063122512095183)
        ·
          refine ⟨18509380741594683768142775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12339587161063122512095183 18509380741594683768142775)
          ·
            refine ⟨27764071112392025652214163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18509380741594683768142775 27764071112392025652214163)
            ·
              refine ⟨41646106668588038478321245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27764071112392025652214163 41646106668588038478321245)
              ·
                refine ⟨15617290000720514429370467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41646106668588038478321245 15617290000720514429370467)
                ·
                  refine ⟨23425935001080771644055701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15617290000720514429370467 23425935001080771644055701)
                  ·
                    refine ⟨1098090703175661170815111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23425935001080771644055701 1098090703175661170815111)
                    ·
                      rfl

theorem cell22_3207786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_3207786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3207786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3207786 prefixEnd_3207786 := by exact prefixLift 3207786
  have htrace : WordTrace (prefixWord ++ tailWord_3207786) baseStart_3207786 baseEnd_3207786 := by
    simpa [prefixWord, tailWord_3207786, baseEnd_3207786] using wordTrace_append hprefix tailTrace_3207786
  have hstable : (prefixWord ++ tailWord_3207786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207786).length < 2 ^ (prefixWord ++ tailWord_3207786).sum := by decide
  have hdescent : baseEnd_3207786 < baseStart_3207786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207790 : List Nat := [4, 1, 2, 2, 2, 1, 3, 3, 4]
def baseStart_3207790 : Nat := 118140960795 + 3207790 * 2 ^ 59
def prefixEnd_3207790 : Nat := 4983230072969 + 3 ^ 40 * 3207790 * 2
def baseEnd_3207790 : Nat := 366030690819135497905033

theorem tailTrace_3207790 : CollatzResearch.WordTrace tailWord_3207790 prefixEnd_3207790 366030690819135497905033 := by
  unfold tailWord_3207790
  simp only [CollatzResearch.WordTrace]
  refine ⟨14624714131091518970098603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77998475365821434507192549 14624714131091518970098603)
  ·
    refine ⟨21937071196637278455147905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14624714131091518970098603 21937071196637278455147905)
    ·
      refine ⟨16452803397477958841360929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21937071196637278455147905 16452803397477958841360929)
      ·
        refine ⟨12339602548108469131020697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16452803397477958841360929 12339602548108469131020697)
        ·
          refine ⟨9254701911081351848265523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12339602548108469131020697 9254701911081351848265523)
          ·
            refine ⟨13882052866622027772398285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9254701911081351848265523 13882052866622027772398285)
            ·
              refine ⟨5205769824983260414649357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13882052866622027772398285 5205769824983260414649357)
              ·
                refine ⟨1952163684368722655493509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5205769824983260414649357 1952163684368722655493509)
                ·
                  refine ⟨366030690819135497905033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1952163684368722655493509 366030690819135497905033)
                  ·
                    rfl

theorem cell22_3207790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_3207790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3207790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3207790 prefixEnd_3207790 := by exact prefixLift 3207790
  have htrace : WordTrace (prefixWord ++ tailWord_3207790) baseStart_3207790 baseEnd_3207790 := by
    simpa [prefixWord, tailWord_3207790, baseEnd_3207790] using wordTrace_append hprefix tailTrace_3207790
  have hstable : (prefixWord ++ tailWord_3207790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207790).length < 2 ^ (prefixWord ++ tailWord_3207790).sum := by decide
  have hdescent : baseEnd_3207790 < baseStart_3207790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207801 : List Nat := [1, 2, 1, 3, 3, 4, 8]
def baseStart_3207801 : Nat := 118140960795 + 3207801 * 2 ^ 59
def prefixEnd_3207801 : Nat := 4983230072969 + 3 ^ 40 * 3207801 * 2
def baseEnd_3207801 : Nat := 40670216221563190062595

theorem tailTrace_3207801 : CollatzResearch.WordTrace tailWord_3207801 prefixEnd_3207801 40670216221563190062595 := by
  unfold tailWord_3207801
  simp only [CollatzResearch.WordTrace]
  refine ⟨116998114251692300639439257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77998742834461533759626171 116998114251692300639439257)
  ·
    refine ⟨87748585688769225479579443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116998114251692300639439257 87748585688769225479579443)
    ·
      refine ⟨131622878533153838219369165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87748585688769225479579443 131622878533153838219369165)
      ·
        refine ⟨49358579449932689332263437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131622878533153838219369165 49358579449932689332263437)
        ·
          refine ⟨18509467293724758499598789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49358579449932689332263437 18509467293724758499598789)
          ·
            refine ⟨3470525117573392218674773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18509467293724758499598789 3470525117573392218674773)
            ·
              refine ⟨40670216221563190062595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3470525117573392218674773 40670216221563190062595)
              ·
                rfl

theorem cell22_3207801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 8].length) (baseStart_3207801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3207801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3207801 prefixEnd_3207801 := by exact prefixLift 3207801
  have htrace : WordTrace (prefixWord ++ tailWord_3207801) baseStart_3207801 baseEnd_3207801 := by
    simpa [prefixWord, tailWord_3207801, baseEnd_3207801] using wordTrace_append hprefix tailTrace_3207801
  have hstable : (prefixWord ++ tailWord_3207801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207801).length < 2 ^ (prefixWord ++ tailWord_3207801).sum := by decide
  have hdescent : baseEnd_3207801 < baseStart_3207801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207818 : List Nat := [3, 1, 2, 3, 3, 1, 2, 7]
def baseStart_3207818 : Nat := 118140960795 + 3207818 * 2 ^ 59
def prefixEnd_3207818 : Nat := 4983230072969 + 3 ^ 40 * 3207818 * 2
def baseEnd_3207818 : Nat := 122011295269958194890557

theorem tailTrace_3207818 : CollatzResearch.WordTrace tailWord_3207818 prefixEnd_3207818 122011295269958194890557 := by
  unfold tailWord_3207818
  simp only [CollatzResearch.WordTrace]
  refine ⟨29249683573157678135702027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77999156195087141695205405 29249683573157678135702027)
  ·
    refine ⟨43874525359736517203553041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29249683573157678135702027 43874525359736517203553041)
    ·
      refine ⟨32905894019802387902664781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43874525359736517203553041 32905894019802387902664781)
      ·
        refine ⟨12339710257425895463499293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32905894019802387902664781 12339710257425895463499293)
        ·
          refine ⟨4627391346534710798812235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12339710257425895463499293 4627391346534710798812235)
          ·
            refine ⟨6941087019802066198218353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4627391346534710798812235 6941087019802066198218353)
            ·
              refine ⟨5205815264851549648663765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6941087019802066198218353 5205815264851549648663765)
              ·
                refine ⟨122011295269958194890557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5205815264851549648663765 122011295269958194890557)
                ·
                  rfl

theorem cell22_3207818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 7].length) (baseStart_3207818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3207818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3207818 prefixEnd_3207818 := by exact prefixLift 3207818
  have htrace : WordTrace (prefixWord ++ tailWord_3207818) baseStart_3207818 baseEnd_3207818 := by
    simpa [prefixWord, tailWord_3207818, baseEnd_3207818] using wordTrace_append hprefix tailTrace_3207818
  have hstable : (prefixWord ++ tailWord_3207818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207818).length < 2 ^ (prefixWord ++ tailWord_3207818).sum := by decide
  have hdescent : baseEnd_3207818 < baseStart_3207818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207951 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 2, 7]
def baseStart_3207951 : Nat := 118140960795 + 3207951 * 2 ^ 59
def prefixEnd_3207951 : Nat := 4983230072969 + 3 ^ 40 * 3207951 * 2
def baseEnd_3207951 : Nat := 1098147186047655740439605

theorem tailTrace_3207951 : CollatzResearch.WordTrace tailWord_3207951 prefixEnd_3207951 1098147186047655740439605 := by
  unfold tailWord_3207951
  simp only [CollatzResearch.WordTrace]
  refine ⟨117003585201148876257399707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78002390134099250838266471 117003585201148876257399707)
  ·
    refine ⟨175505377801723314386099561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117003585201148876257399707 175505377801723314386099561)
    ·
      refine ⟨131629033351292485789574671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175505377801723314386099561 131629033351292485789574671)
      ·
        refine ⟨197443550026938728684362007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131629033351292485789574671 197443550026938728684362007)
        ·
          refine ⟨296165325040408093026543011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197443550026938728684362007 296165325040408093026543011)
          ·
            refine ⟨444247987560612139539814517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296165325040408093026543011 444247987560612139539814517)
            ·
              refine ⟨41648248833807388081857611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 444247987560612139539814517 41648248833807388081857611)
              ·
                refine ⟨62472373250711082122786417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41648248833807388081857611 62472373250711082122786417)
                ·
                  refine ⟨46854279938033311592089813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62472373250711082122786417 46854279938033311592089813)
                  ·
                    refine ⟨1098147186047655740439605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46854279938033311592089813 1098147186047655740439605)
                    ·
                      rfl

theorem cell22_3207951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 7].length) (baseStart_3207951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3207951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3207951 prefixEnd_3207951 := by exact prefixLift 3207951
  have htrace : WordTrace (prefixWord ++ tailWord_3207951) baseStart_3207951 baseEnd_3207951 := by
    simpa [prefixWord, tailWord_3207951, baseEnd_3207951] using wordTrace_append hprefix tailTrace_3207951
  have hstable : (prefixWord ++ tailWord_3207951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207951).length < 2 ^ (prefixWord ++ tailWord_3207951).sum := by decide
  have hdescent : baseEnd_3207951 < baseStart_3207951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207953 : List Nat := [1, 2, 2, 1, 1, 3, 6, 6]
def baseStart_3207953 : Nat := 118140960795 + 3207953 * 2 ^ 59
def prefixEnd_3207953 : Nat := 4983230072969 + 3 ^ 40 * 3207953 * 2
def baseEnd_3207953 : Nat := 122016430076503155765511

theorem tailTrace_3207953 : CollatzResearch.WordTrace tailWord_3207953 prefixEnd_3207953 122016430076503155765511 := by
  unfold tailWord_3207953
  simp only [CollatzResearch.WordTrace]
  refine ⟨117003658147141630598972513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78002438764761087065981675 117003658147141630598972513)
  ·
    refine ⟨87752743610356222949229385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117003658147141630598972513 87752743610356222949229385)
    ·
      refine ⟨65814557707767167211922039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87752743610356222949229385 65814557707767167211922039)
      ·
        refine ⟨98721836561650750817883059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65814557707767167211922039 98721836561650750817883059)
        ·
          refine ⟨148082754842476126226824589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98721836561650750817883059 148082754842476126226824589)
          ·
            refine ⟨55531033065928547335059221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148082754842476126226824589 55531033065928547335059221)
            ·
              refine ⟨2603017174965400656330901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55531033065928547335059221 2603017174965400656330901)
              ·
                refine ⟨122016430076503155765511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2603017174965400656330901 122016430076503155765511)
                ·
                  rfl

theorem cell22_3207953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 6].length) (baseStart_3207953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3207953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3207953 prefixEnd_3207953 := by exact prefixLift 3207953
  have htrace : WordTrace (prefixWord ++ tailWord_3207953) baseStart_3207953 baseEnd_3207953 := by
    simpa [prefixWord, tailWord_3207953, baseEnd_3207953] using wordTrace_append hprefix tailTrace_3207953
  have hstable : (prefixWord ++ tailWord_3207953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207953).length < 2 ^ (prefixWord ++ tailWord_3207953).sum := by decide
  have hdescent : baseEnd_3207953 < baseStart_3207953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207959 : List Nat := [1, 1, 3, 4, 4, 1, 1, 3, 4]
def baseStart_3207959 : Nat := 118140960795 + 3207959 * 2 ^ 59
def prefixEnd_3207959 : Nat := 4983230072969 + 3 ^ 40 * 3207959 * 2
def baseEnd_3207959 : Nat := 366049974870382128746527

theorem tailTrace_3207959 : CollatzResearch.WordTrace tailWord_3207959 prefixEnd_3207959 366049974870382128746527 := by
  unfold tailWord_3207959
  simp only [CollatzResearch.WordTrace]
  refine ⟨117003876985119893623690931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78002584656746595749127287 117003876985119893623690931)
  ·
    refine ⟨175505815477679840435536397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117003876985119893623690931 175505815477679840435536397)
    ·
      refine ⟨65814680804129940163326149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175505815477679840435536397 65814680804129940163326149)
      ·
        refine ⟨12340252650774363780623653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65814680804129940163326149 12340252650774363780623653)
        ·
          refine ⟨2313797372020193208866935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12340252650774363780623653 2313797372020193208866935)
          ·
            refine ⟨3470696058030289813300403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2313797372020193208866935 3470696058030289813300403)
            ·
              refine ⟨5206044087045434719950605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3470696058030289813300403 5206044087045434719950605)
              ·
                refine ⟨1952266532642038019981477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5206044087045434719950605 1952266532642038019981477)
                ·
                  refine ⟨366049974870382128746527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1952266532642038019981477 366049974870382128746527)
                  ·
                    rfl

theorem cell22_3207959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 3, 4].length) (baseStart_3207959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3207959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3207959 prefixEnd_3207959 := by exact prefixLift 3207959
  have htrace : WordTrace (prefixWord ++ tailWord_3207959) baseStart_3207959 baseEnd_3207959 := by
    simpa [prefixWord, tailWord_3207959, baseEnd_3207959] using wordTrace_append hprefix tailTrace_3207959
  have hstable : (prefixWord ++ tailWord_3207959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207959).length < 2 ^ (prefixWord ++ tailWord_3207959).sum := by decide
  have hdescent : baseEnd_3207959 < baseStart_3207959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208036 : List Nat := [2, 3, 1, 1, 4, 3, 2, 2, 1, 3]
def baseStart_3208036 : Nat := 118140960795 + 3208036 * 2 ^ 59
def prefixEnd_3208036 : Nat := 4983230072969 + 3 ^ 40 * 3208036 * 2
def baseEnd_3208036 : Nat := 1098176283284743852064345

theorem tailTrace_3208036 : CollatzResearch.WordTrace tailWord_3208036 prefixEnd_3208036 1098176283284743852064345 := by
  unfold tailWord_3208036
  simp only [CollatzResearch.WordTrace]
  refine ⟨58503342702920467887121981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78004456937227290516162641 58503342702920467887121981)
  ·
    refine ⟨21938753513595175457670743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58503342702920467887121981 21938753513595175457670743)
    ·
      refine ⟨32908130270392763186506115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21938753513595175457670743 32908130270392763186506115)
      ·
        refine ⟨49362195405589144779759173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32908130270392763186506115 49362195405589144779759173)
        ·
          refine ⟨9255411638547964646204845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49362195405589144779759173 9255411638547964646204845)
          ·
            refine ⟨3470779364455486742326817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9255411638547964646204845 3470779364455486742326817)
            ·
              refine ⟨2603084523341615056745113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3470779364455486742326817 2603084523341615056745113)
              ·
                refine ⟨1952313392506211292558835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2603084523341615056745113 1952313392506211292558835)
                ·
                  refine ⟨2928470088759316938838253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1952313392506211292558835 2928470088759316938838253)
                  ·
                    refine ⟨1098176283284743852064345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2928470088759316938838253 1098176283284743852064345)
                    ·
                      rfl

theorem cell22_3208036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 2, 1, 3].length) (baseStart_3208036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3208036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3208036 prefixEnd_3208036 := by exact prefixLift 3208036
  have htrace : WordTrace (prefixWord ++ tailWord_3208036) baseStart_3208036 baseEnd_3208036 := by
    simpa [prefixWord, tailWord_3208036, baseEnd_3208036] using wordTrace_append hprefix tailTrace_3208036
  have hstable : (prefixWord ++ tailWord_3208036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208036).length < 2 ^ (prefixWord ++ tailWord_3208036).sum := by decide
  have hdescent : baseEnd_3208036 < baseStart_3208036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208154 : List Nat := [3, 1, 1, 2, 4, 3, 1, 1, 3, 3]
def baseStart_3208154 : Nat := 118140960795 + 3208154 * 2 ^ 59
def prefixEnd_3208154 : Nat := 4983230072969 + 3 ^ 40 * 3208154 * 2
def baseEnd_3208154 : Nat := 1098216677096230877613983

theorem tailTrace_3208154 : CollatzResearch.WordTrace tailWord_3208154 prefixEnd_3208154 1098216677096230877613983 := by
  unfold tailWord_3208154
  simp only [CollatzResearch.WordTrace]
  refine ⟨29252747304853360481759879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78007326146275627951359677 29252747304853360481759879)
  ·
    refine ⟨43879120957280040722639819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29252747304853360481759879 43879120957280040722639819)
    ·
      refine ⟨65818681435920061083959729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43879120957280040722639819 65818681435920061083959729)
      ·
        refine ⟨49364011076940045812969797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65818681435920061083959729 49364011076940045812969797)
        ·
          refine ⟨9255752076926258589931837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49364011076940045812969797 9255752076926258589931837)
          ·
            refine ⟨3470907028847346971224439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9255752076926258589931837 3470907028847346971224439)
            ·
              refine ⟨5206360543271020456836659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3470907028847346971224439 5206360543271020456836659)
              ·
                refine ⟨7809540814906530685254989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5206360543271020456836659 7809540814906530685254989)
                ·
                  refine ⟨2928577805589949006970621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7809540814906530685254989 2928577805589949006970621)
                  ·
                    refine ⟨1098216677096230877613983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2928577805589949006970621 1098216677096230877613983)
                    ·
                      rfl

theorem cell22_3208154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 3, 3].length) (baseStart_3208154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3208154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3208154 prefixEnd_3208154 := by exact prefixLift 3208154
  have htrace : WordTrace (prefixWord ++ tailWord_3208154) baseStart_3208154 baseEnd_3208154 := by
    simpa [prefixWord, tailWord_3208154, baseEnd_3208154] using wordTrace_append hprefix tailTrace_3208154
  have hstable : (prefixWord ++ tailWord_3208154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208154).length < 2 ^ (prefixWord ++ tailWord_3208154).sum := by decide
  have hdescent : baseEnd_3208154 < baseStart_3208154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208167 : List Nat := [1, 1, 5, 2, 2, 2, 1, 3, 5]
def baseStart_3208167 : Nat := 118140960795 + 3208167 * 2 ^ 59
def prefixEnd_3208167 : Nat := 4983230072969 + 3 ^ 40 * 3208167 * 2
def baseEnd_3208167 : Nat := 366073709087301059012981

theorem tailTrace_3208167 : CollatzResearch.WordTrace tailWord_3208167 prefixEnd_3208167 366073709087301059012981 := by
  unfold tailWord_3208167
  simp only [CollatzResearch.WordTrace]
  refine ⟨117011463368366345147262755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78007642245577563431508503 117011463368366345147262755)
  ·
    refine ⟨175517195052549517720894133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117011463368366345147262755 175517195052549517720894133)
    ·
      refine ⟨16454737036176517286333825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 175517195052549517720894133 16454737036176517286333825)
      ·
        refine ⟨12341052777132387964750369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16454737036176517286333825 12341052777132387964750369)
        ·
          refine ⟨9255789582849290973562777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12341052777132387964750369 9255789582849290973562777)
          ·
            refine ⟨6941842187136968230172083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9255789582849290973562777 6941842187136968230172083)
            ·
              refine ⟨10412763280705452345258125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6941842187136968230172083 10412763280705452345258125)
              ·
                refine ⟨3904786230264544629471797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10412763280705452345258125 3904786230264544629471797)
                ·
                  refine ⟨366073709087301059012981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3904786230264544629471797 366073709087301059012981)
                  ·
                    rfl

theorem cell22_3208167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 5].length) (baseStart_3208167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3208167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3208167 prefixEnd_3208167 := by exact prefixLift 3208167
  have htrace : WordTrace (prefixWord ++ tailWord_3208167) baseStart_3208167 baseEnd_3208167 := by
    simpa [prefixWord, tailWord_3208167, baseEnd_3208167] using wordTrace_append hprefix tailTrace_3208167
  have hstable : (prefixWord ++ tailWord_3208167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208167).length < 2 ^ (prefixWord ++ tailWord_3208167).sum := by decide
  have hdescent : baseEnd_3208167 < baseStart_3208167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208227 : List Nat := [1, 1, 1, 4, 3, 3, 2, 1, 1, 5]
def baseStart_3208227 : Nat := 118140960795 + 3208227 * 2 ^ 59
def prefixEnd_3208227 : Nat := 4983230072969 + 3 ^ 40 * 3208227 * 2
def baseEnd_3208227 : Nat := 1098241666488083020538759

theorem tailTrace_3208227 : CollatzResearch.WordTrace tailWord_3208227 prefixEnd_3208227 1098241666488083020538759 := by
  unfold tailWord_3208227
  simp only [CollatzResearch.WordTrace]
  refine ⟨117013651748148975394446935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78009101165432650262964623 117013651748148975394446935)
  ·
    refine ⟨175520477622223463091670403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117013651748148975394446935 175520477622223463091670403)
    ·
      refine ⟨263280716433335194637505605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175520477622223463091670403 263280716433335194637505605)
      ·
        refine ⟨49365134331250348994532301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 263280716433335194637505605 49365134331250348994532301)
        ·
          refine ⟨18511925374218880872949613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49365134331250348994532301 18511925374218880872949613)
          ·
            refine ⟨6941972015332080327356105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18511925374218880872949613 6941972015332080327356105)
            ·
              refine ⟨5206479011499060245517079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6941972015332080327356105 5206479011499060245517079)
              ·
                refine ⟨7809718517248590368275619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5206479011499060245517079 7809718517248590368275619)
                ·
                  refine ⟨11714577775872885552413429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7809718517248590368275619 11714577775872885552413429)
                  ·
                    refine ⟨1098241666488083020538759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11714577775872885552413429 1098241666488083020538759)
                    ·
                      rfl

theorem cell22_3208227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 5].length) (baseStart_3208227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3208227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3208227 prefixEnd_3208227 := by exact prefixLift 3208227
  have htrace : WordTrace (prefixWord ++ tailWord_3208227) baseStart_3208227 baseEnd_3208227 := by
    simpa [prefixWord, tailWord_3208227, baseEnd_3208227] using wordTrace_append hprefix tailTrace_3208227
  have hstable : (prefixWord ++ tailWord_3208227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208227).length < 2 ^ (prefixWord ++ tailWord_3208227).sum := by decide
  have hdescent : baseEnd_3208227 < baseStart_3208227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208244 : List Nat := [2, 5, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_3208244 : Nat := 118140960795 + 3208244 * 2 ^ 59
def prefixEnd_3208244 : Nat := 4983230072969 + 3 ^ 40 * 3208244 * 2
def baseEnd_3208244 : Nat := 1098247485935500642863707

theorem tailTrace_3208244 : CollatzResearch.WordTrace tailWord_3208244 prefixEnd_3208244 1098247485935500642863707 := by
  unfold tailWord_3208244
  simp only [CollatzResearch.WordTrace]
  refine ⟨58507135894543693648907893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78009514526058258198543857 58507135894543693648907893)
  ·
    refine ⟨5485043990113471279585115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58507135894543693648907893 5485043990113471279585115)
    ·
      refine ⟨8227565985170206919377673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5485043990113471279585115 8227565985170206919377673)
      ·
        refine ⟨6170674488877655189533255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8227565985170206919377673 6170674488877655189533255)
        ·
          refine ⟨9256011733316482784299883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6170674488877655189533255 9256011733316482784299883)
          ·
            refine ⟨13884017599974724176449825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9256011733316482784299883 13884017599974724176449825)
            ·
              refine ⟨10413013199981043132337369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13884017599974724176449825 10413013199981043132337369)
              ·
                refine ⟨7809759899985782349253027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10413013199981043132337369 7809759899985782349253027)
                ·
                  refine ⟨11714639849978673523879541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7809759899985782349253027 11714639849978673523879541)
                  ·
                    refine ⟨1098247485935500642863707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11714639849978673523879541 1098247485935500642863707)
                    ·
                      rfl

theorem cell22_3208244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_3208244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3208244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3208244 prefixEnd_3208244 := by exact prefixLift 3208244
  have htrace : WordTrace (prefixWord ++ tailWord_3208244) baseStart_3208244 baseEnd_3208244 := by
    simpa [prefixWord, tailWord_3208244, baseEnd_3208244] using wordTrace_append hprefix tailTrace_3208244
  have hstable : (prefixWord ++ tailWord_3208244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208244).length < 2 ^ (prefixWord ++ tailWord_3208244).sum := by decide
  have hdescent : baseEnd_3208244 < baseStart_3208244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208246 : List Nat := [5, 1, 2, 1, 1, 3, 2, 3, 4]
def baseStart_3208246 : Nat := 118140960795 + 3208246 * 2 ^ 59
def prefixEnd_3208246 : Nat := 4983230072969 + 3 ^ 40 * 3208246 * 2
def baseEnd_3208246 : Nat := 366082723525457768104567

theorem tailTrace_3208246 : CollatzResearch.WordTrace tailWord_3208246 prefixEnd_3208246 366082723525457768104567 := by
  unfold tailWord_3208246
  simp only [CollatzResearch.WordTrace]
  refine ⟨7313396545942508852461787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78009563156720094426259061 7313396545942508852461787)
  ·
    refine ⟨10970094818913763278692681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7313396545942508852461787 10970094818913763278692681)
    ·
      refine ⟨8227571114185322459019511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10970094818913763278692681 8227571114185322459019511)
      ·
        refine ⟨12341356671277983688529267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8227571114185322459019511 12341356671277983688529267)
        ·
          refine ⟨18512035006916975532793901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12341356671277983688529267 18512035006916975532793901)
          ·
            refine ⟨6942013127593865824797713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18512035006916975532793901 6942013127593865824797713)
            ·
              refine ⟨5206509845695399368598285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6942013127593865824797713 5206509845695399368598285)
              ·
                refine ⟨1952441192135774763224357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5206509845695399368598285 1952441192135774763224357)
                ·
                  refine ⟨366082723525457768104567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1952441192135774763224357 366082723525457768104567)
                  ·
                    rfl

theorem cell22_3208246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_3208246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3208246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3208246 prefixEnd_3208246 := by exact prefixLift 3208246
  have htrace : WordTrace (prefixWord ++ tailWord_3208246) baseStart_3208246 baseEnd_3208246 := by
    simpa [prefixWord, tailWord_3208246, baseEnd_3208246] using wordTrace_append hprefix tailTrace_3208246
  have hstable : (prefixWord ++ tailWord_3208246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208246).length < 2 ^ (prefixWord ++ tailWord_3208246).sum := by decide
  have hdescent : baseEnd_3208246 < baseStart_3208246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208257 : List Nat := [1, 2, 5, 1, 3, 1, 9]
def baseStart_3208257 : Nat := 118140960795 + 3208257 * 2 ^ 59
def prefixEnd_3208257 : Nat := 4983230072969 + 3 ^ 40 * 3208257 * 2
def baseEnd_3208257 : Nat := 40675997633376775640321

theorem tailTrace_3208257 : CollatzResearch.WordTrace tailWord_3208257 prefixEnd_3208257 40675997633376775640321 := by
  unfold tailWord_3208257
  simp only [CollatzResearch.WordTrace]
  refine ⟨117014745938040290518039025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78009830625360193678692683 117014745938040290518039025)
  ·
    refine ⟨87761059453530217888529269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117014745938040290518039025 87761059453530217888529269)
    ·
      refine ⟨8227599323768457927049619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87761059453530217888529269 8227599323768457927049619)
      ·
        refine ⟨12341398985652686890574429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8227599323768457927049619 12341398985652686890574429)
        ·
          refine ⟨4628024619619757583965411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12341398985652686890574429 4628024619619757583965411)
          ·
            refine ⟨6942036929429636375948117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4628024619619757583965411 6942036929429636375948117)
            ·
              refine ⟨40675997633376775640321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6942036929429636375948117 40675997633376775640321)
              ·
                rfl

theorem cell22_3208257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 9].length) (baseStart_3208257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3208257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3208257 prefixEnd_3208257 := by exact prefixLift 3208257
  have htrace : WordTrace (prefixWord ++ tailWord_3208257) baseStart_3208257 baseEnd_3208257 := by
    simpa [prefixWord, tailWord_3208257, baseEnd_3208257] using wordTrace_append hprefix tailTrace_3208257
  have hstable : (prefixWord ++ tailWord_3208257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208257).length < 2 ^ (prefixWord ++ tailWord_3208257).sum := by decide
  have hdescent : baseEnd_3208257 < baseStart_3208257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208278 : List Nat := [5, 2, 2, 1, 2, 2, 1, 1, 1, 5]
def baseStart_3208278 : Nat := 118140960795 + 3208278 * 2 ^ 59
def prefixEnd_3208278 : Nat := 4983230072969 + 3 ^ 40 * 3208278 * 2
def baseEnd_3208278 : Nat := 1098259124830335887513603

theorem tailTrace_3208278 : CollatzResearch.WordTrace tailWord_3208278 prefixEnd_3208278 1098259124830335887513603 := by
  unfold tailWord_3208278
  simp only [CollatzResearch.WordTrace]
  refine ⟨7313469491935263194034593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78010341247309474069702325 7313469491935263194034593)
  ·
    refine ⟨5485102118951447395525945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7313469491935263194034593 5485102118951447395525945)
    ·
      refine ⟨4113826589213585546644459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5485102118951447395525945 4113826589213585546644459)
      ·
        refine ⟨6170739883820378319966689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4113826589213585546644459 6170739883820378319966689)
        ·
          refine ⟨4628054912865283739975017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6170739883820378319966689 4628054912865283739975017)
          ·
            refine ⟨3471041184648962804981263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4628054912865283739975017 3471041184648962804981263)
            ·
              refine ⟨5206561776973444207471895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3471041184648962804981263 5206561776973444207471895)
              ·
                refine ⟨7809842665460166311207843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5206561776973444207471895 7809842665460166311207843)
                ·
                  refine ⟨11714763998190249466811765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7809842665460166311207843 11714763998190249466811765)
                  ·
                    refine ⟨1098259124830335887513603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11714763998190249466811765 1098259124830335887513603)
                    ·
                      rfl

theorem cell22_3208278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_3208278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3208278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3208278 prefixEnd_3208278 := by exact prefixLift 3208278
  have htrace : WordTrace (prefixWord ++ tailWord_3208278) baseStart_3208278 baseEnd_3208278 := by
    simpa [prefixWord, tailWord_3208278, baseEnd_3208278] using wordTrace_append hprefix tailTrace_3208278
  have hstable : (prefixWord ++ tailWord_3208278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208278).length < 2 ^ (prefixWord ++ tailWord_3208278).sum := by decide
  have hdescent : baseEnd_3208278 < baseStart_3208278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208302 : List Nat := [4, 1, 2, 2, 1, 2, 1, 2, 7]
def baseStart_3208302 : Nat := 118140960795 + 3208302 * 2 ^ 59
def prefixEnd_3208302 : Nat := 4983230072969 + 3 ^ 40 * 3208302 * 2
def baseEnd_3208302 : Nat := 366089113506935941637843

theorem tailTrace_3208302 : CollatzResearch.WordTrace tailWord_3208302 prefixEnd_3208302 366089113506935941637843 := by
  unfold tailWord_3208302
  simp only [CollatzResearch.WordTrace]
  refine ⟨14627048402859657900428395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78010924815251508802284773 14627048402859657900428395)
  ·
    refine ⟨21940572604289486850642593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14627048402859657900428395 21940572604289486850642593)
    ·
      refine ⟨16455429453217115137981945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21940572604289486850642593 16455429453217115137981945)
      ·
        refine ⟨12341572089912836353486459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16455429453217115137981945 12341572089912836353486459)
        ·
          refine ⟨18512358134869254530229689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12341572089912836353486459 18512358134869254530229689)
          ·
            refine ⟨13884268601151940897672267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18512358134869254530229689 13884268601151940897672267)
            ·
              refine ⟨20826402901727911346508401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13884268601151940897672267 20826402901727911346508401)
              ·
                refine ⟨15619802176295933509881301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20826402901727911346508401 15619802176295933509881301)
                ·
                  refine ⟨366089113506935941637843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15619802176295933509881301 366089113506935941637843)
                  ·
                    rfl

theorem cell22_3208302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_3208302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3208302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3208302 prefixEnd_3208302 := by exact prefixLift 3208302
  have htrace : WordTrace (prefixWord ++ tailWord_3208302) baseStart_3208302 baseEnd_3208302 := by
    simpa [prefixWord, tailWord_3208302, baseEnd_3208302] using wordTrace_append hprefix tailTrace_3208302
  have hstable : (prefixWord ++ tailWord_3208302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208302).length < 2 ^ (prefixWord ++ tailWord_3208302).sum := by decide
  have hdescent : baseEnd_3208302 < baseStart_3208302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208374 : List Nat := [5, 1, 3, 2, 1, 2, 2, 2, 1, 3]
def baseStart_3208374 : Nat := 118140960795 + 3208374 * 2 ^ 59
def prefixEnd_3208374 : Nat := 4983230072969 + 3 ^ 40 * 3208374 * 2
def baseEnd_3208374 : Nat := 1098291987592223637113309

theorem tailTrace_3208374 : CollatzResearch.WordTrace tailWord_3208374 prefixEnd_3208374 1098291987592223637113309 := by
  unfold tailWord_3208374
  simp only [CollatzResearch.WordTrace]
  refine ⟨7313688329913526218753011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78012675519077613000032117 7313688329913526218753011)
  ·
    refine ⟨10970532494870289328129517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7313688329913526218753011 10970532494870289328129517)
    ·
      refine ⟨4113949685576358498048569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10970532494870289328129517 4113949685576358498048569)
      ·
        refine ⟨3085462264182268873536427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4113949685576358498048569 3085462264182268873536427)
        ·
          refine ⟨4628193396273403310304641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3085462264182268873536427 4628193396273403310304641)
          ·
            refine ⟨3471145047205052482728481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4628193396273403310304641 3471145047205052482728481)
            ·
              refine ⟨2603358785403789362046361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3471145047205052482728481 2603358785403789362046361)
              ·
                refine ⟨1952519089052842021534771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2603358785403789362046361 1952519089052842021534771)
                ·
                  refine ⟨2928778633579263032302157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1952519089052842021534771 2928778633579263032302157)
                  ·
                    refine ⟨1098291987592223637113309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2928778633579263032302157 1098291987592223637113309)
                    ·
                      rfl

theorem cell22_3208374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_3208374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3208374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3208374 prefixEnd_3208374 := by exact prefixLift 3208374
  have htrace : WordTrace (prefixWord ++ tailWord_3208374) baseStart_3208374 baseEnd_3208374 := by
    simpa [prefixWord, tailWord_3208374, baseEnd_3208374] using wordTrace_append hprefix tailTrace_3208374
  have hstable : (prefixWord ++ tailWord_3208374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208374).length < 2 ^ (prefixWord ++ tailWord_3208374).sum := by decide
  have hdescent : baseEnd_3208374 < baseStart_3208374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208381 : List Nat := [1, 4, 1, 2, 1, 1, 6, 2, 4]
def baseStart_3208381 : Nat := 118140960795 + 3208381 * 2 ^ 59
def prefixEnd_3208381 : Nat := 4983230072969 + 3 ^ 40 * 3208381 * 2
def baseEnd_3208381 : Nat := 366098127945092650729429

theorem tailTrace_3208381 : CollatzResearch.WordTrace tailWord_3208381 prefixEnd_3208381 366098127945092650729429 := by
  unfold tailWord_3208381
  simp only [CollatzResearch.WordTrace]
  refine ⟨117019268589591059695552997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78012845726394039797035331 117019268589591059695552997)
  ·
    refine ⟨21941112860548323692916187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117019268589591059695552997 21941112860548323692916187)
    ·
      refine ⟨32911669290822485539374281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21941112860548323692916187 32911669290822485539374281)
      ·
        refine ⟨24683751968116864154530711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32911669290822485539374281 24683751968116864154530711)
        ·
          refine ⟨37025627952175296231796067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24683751968116864154530711 37025627952175296231796067)
          ·
            refine ⟨55538441928262944347694101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37025627952175296231796067 55538441928262944347694101)
            ·
              refine ⟨2603364465387325516298161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55538441928262944347694101 2603364465387325516298161)
              ·
                refine ⟨1952523349040494137223621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2603364465387325516298161 1952523349040494137223621)
                ·
                  refine ⟨366098127945092650729429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1952523349040494137223621 366098127945092650729429)
                  ·
                    rfl

theorem cell22_3208381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_3208381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3208381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3208381 prefixEnd_3208381 := by exact prefixLift 3208381
  have htrace : WordTrace (prefixWord ++ tailWord_3208381) baseStart_3208381 baseEnd_3208381 := by
    simpa [prefixWord, tailWord_3208381, baseEnd_3208381] using wordTrace_append hprefix tailTrace_3208381
  have hstable : (prefixWord ++ tailWord_3208381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208381).length < 2 ^ (prefixWord ++ tailWord_3208381).sum := by decide
  have hdescent : baseEnd_3208381 < baseStart_3208381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208392 : List Nat := [2, 1, 3, 1, 2, 1, 5, 7]
def baseStart_3208392 : Nat := 118140960795 + 3208392 * 2 ^ 59
def prefixEnd_3208392 : Nat := 4983230072969 + 3 ^ 40 * 3208392 * 2
def baseEnd_3208392 : Nat := 122033127706675287795917

theorem tailTrace_3208392 : CollatzResearch.WordTrace tailWord_3208392 prefixEnd_3208392 122033127706675287795917 := by
  unfold tailWord_3208392
  simp only [CollatzResearch.WordTrace]
  refine ⟨58509834896275604287101715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78013113195034139049468953 58509834896275604287101715)
  ·
    refine ⟨87764752344413406430652573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58509834896275604287101715 87764752344413406430652573)
    ·
      refine ⟨32911782129155027411494715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87764752344413406430652573 32911782129155027411494715)
      ·
        refine ⟨49367673193732541117242073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32911782129155027411494715 49367673193732541117242073)
        ·
          refine ⟨37025754895299405837931555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49367673193732541117242073 37025754895299405837931555)
          ·
            refine ⟨55538632342949108756897333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37025754895299405837931555 55538632342949108756897333)
            ·
              refine ⟨5206746782151478945959125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55538632342949108756897333 5206746782151478945959125)
              ·
                refine ⟨122033127706675287795917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5206746782151478945959125 122033127706675287795917)
                ·
                  rfl

theorem cell22_3208392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 7].length) (baseStart_3208392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3208392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3208392 prefixEnd_3208392 := by exact prefixLift 3208392
  have htrace : WordTrace (prefixWord ++ tailWord_3208392) baseStart_3208392 baseEnd_3208392 := by
    simpa [prefixWord, tailWord_3208392, baseEnd_3208392] using wordTrace_append hprefix tailTrace_3208392
  have hstable : (prefixWord ++ tailWord_3208392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208392).length < 2 ^ (prefixWord ++ tailWord_3208392).sum := by decide
  have hdescent : baseEnd_3208392 < baseStart_3208392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208424 : List Nat := [2, 1, 4, 1, 2, 1, 1, 2, 5, 3]
def baseStart_3208424 : Nat := 118140960795 + 3208424 * 2 ^ 59
def prefixEnd_3208424 : Nat := 4983230072969 + 3 ^ 40 * 3208424 * 2
def baseEnd_3208424 : Nat := 1098309103614040173363155

theorem tailTrace_3208424 : CollatzResearch.WordTrace tailWord_3208424 prefixEnd_3208424 1098309103614040173363155 := by
  unfold tailWord_3208424
  simp only [CollatzResearch.WordTrace]
  refine ⟨58510418464217639019684163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78013891285623518692912217 58510418464217639019684163)
  ·
    refine ⟨87765627696326458529526245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58510418464217639019684163 87765627696326458529526245)
    ·
      refine ⟨16456055193061210974286171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87765627696326458529526245 16456055193061210974286171)
      ·
        refine ⟨24684082789591816461429257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16456055193061210974286171 24684082789591816461429257)
        ·
          refine ⟨18513062092193862346071943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24684082789591816461429257 18513062092193862346071943)
          ·
            refine ⟨27769593138290793519107915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18513062092193862346071943 27769593138290793519107915)
            ·
              refine ⟨41654389707436190278661873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27769593138290793519107915 41654389707436190278661873)
              ·
                refine ⟨31240792280577142708996405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41654389707436190278661873 31240792280577142708996405)
                ·
                  refine ⟨2928824276304107128968413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31240792280577142708996405 2928824276304107128968413)
                  ·
                    refine ⟨1098309103614040173363155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2928824276304107128968413 1098309103614040173363155)
                    ·
                      rfl

theorem cell22_3208424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_3208424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3208424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3208424 prefixEnd_3208424 := by exact prefixLift 3208424
  have htrace : WordTrace (prefixWord ++ tailWord_3208424) baseStart_3208424 baseEnd_3208424 := by
    simpa [prefixWord, tailWord_3208424, baseEnd_3208424] using wordTrace_append hprefix tailTrace_3208424
  have hstable : (prefixWord ++ tailWord_3208424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208424).length < 2 ^ (prefixWord ++ tailWord_3208424).sum := by decide
  have hdescent : baseEnd_3208424 < baseStart_3208424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208441 : List Nat := [1, 2, 1, 3, 1, 1, 3, 6, 1, 3]
def baseStart_3208441 : Nat := 118140960795 + 3208441 * 2 ^ 59
def prefixEnd_3208441 : Nat := 4983230072969 + 3 ^ 40 * 3208441 * 2
def baseEnd_3208441 : Nat := 1098314923061457795688103

theorem tailTrace_3208441 : CollatzResearch.WordTrace tailWord_3208441 prefixEnd_3208441 1098314923061457795688103 := by
  unfold tailWord_3208441
  simp only [CollatzResearch.WordTrace]
  refine ⟨117021456969373689942737177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78014304646249126628491451 117021456969373689942737177)
  ·
    refine ⟨87766092727030267457052883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117021456969373689942737177 87766092727030267457052883)
    ·
      refine ⟨131649139090545401185579325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87766092727030267457052883 131649139090545401185579325)
      ·
        refine ⟨49368427158954525444592247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131649139090545401185579325 49368427158954525444592247)
        ·
          refine ⟨74052640738431788166888371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49368427158954525444592247 74052640738431788166888371)
          ·
            refine ⟨111078961107647682250332557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74052640738431788166888371 111078961107647682250332557)
            ·
              refine ⟨41654610415367880843874709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111078961107647682250332557 41654610415367880843874709)
              ·
                refine ⟨1952559863220369414556627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41654610415367880843874709 1952559863220369414556627)
                ·
                  refine ⟨2928839794830554121834941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1952559863220369414556627 2928839794830554121834941)
                  ·
                    refine ⟨1098314923061457795688103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2928839794830554121834941 1098314923061457795688103)
                    ·
                      rfl

theorem cell22_3208441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 6, 1, 3].length) (baseStart_3208441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3208441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3208441 prefixEnd_3208441 := by exact prefixLift 3208441
  have htrace : WordTrace (prefixWord ++ tailWord_3208441) baseStart_3208441 baseEnd_3208441 := by
    simpa [prefixWord, tailWord_3208441, baseEnd_3208441] using wordTrace_append hprefix tailTrace_3208441
  have hstable : (prefixWord ++ tailWord_3208441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208441).length < 2 ^ (prefixWord ++ tailWord_3208441).sum := by decide
  have hdescent : baseEnd_3208441 < baseStart_3208441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208499 : List Nat := [1, 1, 1, 2, 5, 2, 3, 1, 6]
def baseStart_3208499 : Nat := 118140960795 + 3208499 * 2 ^ 59
def prefixEnd_3208499 : Nat := 4983230072969 + 3 ^ 40 * 3208499 * 2
def baseEnd_3208499 : Nat := 366111592548921659245975

theorem tailTrace_3208499 : CollatzResearch.WordTrace tailWord_3208499 prefixEnd_3208499 366111592548921659245975 := by
  unfold tailWord_3208499
  simp only [CollatzResearch.WordTrace]
  refine ⟨117023572403163565848348551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78015714935442377232232367 117023572403163565848348551)
  ·
    refine ⟨175535358604745348772522827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117023572403163565848348551 175535358604745348772522827)
    ·
      refine ⟨263303037907118023158784241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175535358604745348772522827 263303037907118023158784241)
      ·
        refine ⟨197477278430338517369088181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263303037907118023158784241 197477278430338517369088181)
        ·
          refine ⟨18513494852844236003352017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 197477278430338517369088181 18513494852844236003352017)
          ·
            refine ⟨13885121139633177002514013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18513494852844236003352017 13885121139633177002514013)
            ·
              refine ⟨5206920427362441375942755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13885121139633177002514013 5206920427362441375942755)
              ·
                refine ⟨7810380641043662063914133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5206920427362441375942755 7810380641043662063914133)
                ·
                  refine ⟨366111592548921659245975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7810380641043662063914133 366111592548921659245975)
                  ·
                    rfl

theorem cell22_3208499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 6].length) (baseStart_3208499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3208499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3208499 prefixEnd_3208499 := by exact prefixLift 3208499
  have htrace : WordTrace (prefixWord ++ tailWord_3208499) baseStart_3208499 baseEnd_3208499 := by
    simpa [prefixWord, tailWord_3208499, baseEnd_3208499] using wordTrace_append hprefix tailTrace_3208499
  have hstable : (prefixWord ++ tailWord_3208499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208499).length < 2 ^ (prefixWord ++ tailWord_3208499).sum := by decide
  have hdescent : baseEnd_3208499 < baseStart_3208499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208505 : List Nat := [1, 2, 1, 6, 3, 1, 2, 1, 5]
def baseStart_3208505 : Nat := 118140960795 + 3208505 * 2 ^ 59
def prefixEnd_3208505 : Nat := 4983230072969 + 3 ^ 40 * 3208505 * 2
def baseEnd_3208505 : Nat := 366112277189794320695969

theorem tailTrace_3208505 : CollatzResearch.WordTrace tailWord_3208505 prefixEnd_3208505 366112277189794320695969 := by
  unfold tailWord_3208505
  simp only [CollatzResearch.WordTrace]
  refine ⟨117023791241141828873066969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78015860827427885915377979 117023791241141828873066969)
  ·
    refine ⟨87767843430856371654800227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117023791241141828873066969 87767843430856371654800227)
    ·
      refine ⟨131651765146284557482200341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87767843430856371654800227 131651765146284557482200341)
      ·
        refine ⟨6171176491232088631978141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 131651765146284557482200341 6171176491232088631978141)
        ·
          refine ⟨2314191184212033236991803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6171176491232088631978141 2314191184212033236991803)
          ·
            refine ⟨3471286776318049855487705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2314191184212033236991803 3471286776318049855487705)
            ·
              refine ⟨2603465082238537391615779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3471286776318049855487705 2603465082238537391615779)
              ·
                refine ⟨3905197623357806087423669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2603465082238537391615779 3905197623357806087423669)
                ·
                  refine ⟨366112277189794320695969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3905197623357806087423669 366112277189794320695969)
                  ·
                    rfl

theorem cell22_3208505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 5].length) (baseStart_3208505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3208505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3208505 prefixEnd_3208505 := by exact prefixLift 3208505
  have htrace : WordTrace (prefixWord ++ tailWord_3208505) baseStart_3208505 baseEnd_3208505 := by
    simpa [prefixWord, tailWord_3208505, baseEnd_3208505] using wordTrace_append hprefix tailTrace_3208505
  have hstable : (prefixWord ++ tailWord_3208505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208505).length < 2 ^ (prefixWord ++ tailWord_3208505).sum := by decide
  have hdescent : baseEnd_3208505 < baseStart_3208505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208546 : List Nat := [3, 3, 2, 1, 1, 1, 1, 4, 2, 4]
def baseStart_3208546 : Nat := 118140960795 + 3208546 * 2 ^ 59
def prefixEnd_3208546 : Nat := 4983230072969 + 3 ^ 40 * 3208546 * 2
def baseEnd_3208546 : Nat := 1098350866707272521812781

theorem tailTrace_3208546 : CollatzResearch.WordTrace tailWord_3208546 prefixEnd_3208546 1098350866707272521812781 := by
  unfold tailWord_3208546
  simp only [CollatzResearch.WordTrace]
  refine ⟨29256321658498323218827373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78016857755995528583539661 29256321658498323218827373)
  ·
    refine ⟨10971120621936871207060265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29256321658498323218827373 10971120621936871207060265)
    ·
      refine ⟨8228340466452653405295199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10971120621936871207060265 8228340466452653405295199)
      ·
        refine ⟨12342510699678980107942799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8228340466452653405295199 12342510699678980107942799)
        ·
          refine ⟨18513766049518470161914199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12342510699678980107942799 18513766049518470161914199)
          ·
            refine ⟨27770649074277705242871299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18513766049518470161914199 27770649074277705242871299)
            ·
              refine ⟨41655973611416557864306949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27770649074277705242871299 41655973611416557864306949)
              ·
                refine ⟨7810495052140604599557553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41655973611416557864306949 7810495052140604599557553)
                ·
                  refine ⟨5857871289105453449668165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7810495052140604599557553 5857871289105453449668165)
                  ·
                    refine ⟨1098350866707272521812781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5857871289105453449668165 1098350866707272521812781)
                    ·
                      rfl

theorem cell22_3208546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_3208546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3208546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3208546 prefixEnd_3208546 := by exact prefixLift 3208546
  have htrace : WordTrace (prefixWord ++ tailWord_3208546) baseStart_3208546 baseEnd_3208546 := by
    simpa [prefixWord, tailWord_3208546, baseEnd_3208546] using wordTrace_append hprefix tailTrace_3208546
  have hstable : (prefixWord ++ tailWord_3208546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208546).length < 2 ^ (prefixWord ++ tailWord_3208546).sum := by decide
  have hdescent : baseEnd_3208546 < baseStart_3208546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208548 : List Nat := [2, 3, 1, 1, 3, 3, 2, 2, 2, 3]
def baseStart_3208548 : Nat := 118140960795 + 3208548 * 2 ^ 59
def prefixEnd_3208548 : Nat := 4983230072969 + 3 ^ 40 * 3208548 * 2
def baseEnd_3208548 : Nat := 1098351551348145183262775

theorem tailTrace_3208548 : CollatzResearch.WordTrace tailWord_3208548 prefixEnd_3208548 1098351551348145183262775 := by
  unfold tailWord_3208548
  simp only [CollatzResearch.WordTrace]
  refine ⟨58512679789993023608441149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78016906386657364811254865 58512679789993023608441149)
  ·
    refine ⟨21942254921247383853165431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58512679789993023608441149 21942254921247383853165431)
    ·
      refine ⟨32913382381871075779748147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21942254921247383853165431 32913382381871075779748147)
      ·
        refine ⟨49370073572806613669622221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32913382381871075779748147 49370073572806613669622221)
        ·
          refine ⟨18513777589802480126108333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49370073572806613669622221 18513777589802480126108333)
          ·
            refine ⟨6942666596175930047290625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18513777589802480126108333 6942666596175930047290625)
            ·
              refine ⟨5206999947131947535467969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6942666596175930047290625 5206999947131947535467969)
              ·
                refine ⟨3905249960348960651600977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5206999947131947535467969 3905249960348960651600977)
                ·
                  refine ⟨2928937470261720488700733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3905249960348960651600977 2928937470261720488700733)
                  ·
                    refine ⟨1098351551348145183262775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2928937470261720488700733 1098351551348145183262775)
                    ·
                      rfl

theorem cell22_3208548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_3208548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3208548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3208548 prefixEnd_3208548 := by exact prefixLift 3208548
  have htrace : WordTrace (prefixWord ++ tailWord_3208548) baseStart_3208548 baseEnd_3208548 := by
    simpa [prefixWord, tailWord_3208548, baseEnd_3208548] using wordTrace_append hprefix tailTrace_3208548
  have hstable : (prefixWord ++ tailWord_3208548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208548).length < 2 ^ (prefixWord ++ tailWord_3208548).sum := by decide
  have hdescent : baseEnd_3208548 < baseStart_3208548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208610 : List Nat := [3, 3, 1, 2, 1, 2, 2, 4, 1, 3]
def baseStart_3208610 : Nat := 118140960795 + 3208610 * 2 ^ 59
def prefixEnd_3208610 : Nat := 4983230072969 + 3 ^ 40 * 3208610 * 2
def baseEnd_3208610 : Nat := 1098372775215197688212585

theorem tailTrace_3208610 : CollatzResearch.WordTrace tailWord_3208610 prefixEnd_3208610 1098372775215197688212585 := by
  unfold tailWord_3208610
  simp only [CollatzResearch.WordTrace]
  refine ⟨29256905226440357951409821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78018413937174287870426189 29256905226440357951409821)
  ·
    refine ⟨10971339459915134231778683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29256905226440357951409821 10971339459915134231778683)
    ·
      refine ⟨16457009189872701347668025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10971339459915134231778683 16457009189872701347668025)
      ·
        refine ⟨12342756892404526010751019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16457009189872701347668025 12342756892404526010751019)
        ·
          refine ⟨18514135338606789016126529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12342756892404526010751019 18514135338606789016126529)
          ·
            refine ⟨13885601503955091762094897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18514135338606789016126529 13885601503955091762094897)
            ·
              refine ⟨10414201127966318821571173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13885601503955091762094897 10414201127966318821571173)
              ·
                refine ⟨1952662711493684779044595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10414201127966318821571173 1952662711493684779044595)
                ·
                  refine ⟨2928994067240527168566893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1952662711493684779044595 2928994067240527168566893)
                  ·
                    refine ⟨1098372775215197688212585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2928994067240527168566893 1098372775215197688212585)
                    ·
                      rfl

theorem cell22_3208610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_3208610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3208610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3208610 prefixEnd_3208610 := by exact prefixLift 3208610
  have htrace : WordTrace (prefixWord ++ tailWord_3208610) baseStart_3208610 baseEnd_3208610 := by
    simpa [prefixWord, tailWord_3208610, baseEnd_3208610] using wordTrace_append hprefix tailTrace_3208610
  have hstable : (prefixWord ++ tailWord_3208610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208610).length < 2 ^ (prefixWord ++ tailWord_3208610).sum := by decide
  have hdescent : baseEnd_3208610 < baseStart_3208610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208649 : List Nat := [1, 2, 1, 1, 2, 1, 3, 3, 3, 5]
def baseStart_3208649 : Nat := 118140960795 + 3208649 * 2 ^ 59
def prefixEnd_3208649 : Nat := 4983230072969 + 3 ^ 40 * 3208649 * 2
def baseEnd_3208649 : Nat := 1098386125712214586487465

theorem tailTrace_3208649 : CollatzResearch.WordTrace tailWord_3208649 prefixEnd_3208649 1098386125712214586487465 := by
  unfold tailWord_3208649
  simp only [CollatzResearch.WordTrace]
  refine ⟨117029043352620141466309001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78019362235080094310872667 117029043352620141466309001)
  ·
    refine ⟨87771782514465106099731751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117029043352620141466309001 87771782514465106099731751)
    ·
      refine ⟨131657673771697659149597627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87771782514465106099731751 131657673771697659149597627)
      ·
        refine ⟨197486510657546488724396441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131657673771697659149597627 197486510657546488724396441)
        ·
          refine ⟨148114882993159866543297331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197486510657546488724396441 148114882993159866543297331)
          ·
            refine ⟨222172324489739799814945997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148114882993159866543297331 222172324489739799814945997)
            ·
              refine ⟨83314621683652424930604749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 222172324489739799814945997 83314621683652424930604749)
              ·
                refine ⟨31242983131369659348976781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83314621683652424930604749 31242983131369659348976781)
                ·
                  refine ⟨11716118674263622255866293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31242983131369659348976781 11716118674263622255866293)
                  ·
                    refine ⟨1098386125712214586487465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11716118674263622255866293 1098386125712214586487465)
                    ·
                      rfl

theorem cell22_3208649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 5].length) (baseStart_3208649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3208649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3208649 prefixEnd_3208649 := by exact prefixLift 3208649
  have htrace : WordTrace (prefixWord ++ tailWord_3208649) baseStart_3208649 baseEnd_3208649 := by
    simpa [prefixWord, tailWord_3208649, baseEnd_3208649] using wordTrace_append hprefix tailTrace_3208649
  have hstable : (prefixWord ++ tailWord_3208649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208649).length < 2 ^ (prefixWord ++ tailWord_3208649).sum := by decide
  have hdescent : baseEnd_3208649 < baseStart_3208649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208734 : List Nat := [4, 3, 3, 1, 1, 1, 2, 1, 1, 5]
def baseStart_3208734 : Nat := 118140960795 + 3208734 * 2 ^ 59
def prefixEnd_3208734 : Nat := 4983230072969 + 3 ^ 40 * 3208734 * 2
def baseEnd_3208734 : Nat := 1098415222949302698112205

theorem tailTrace_3208734 : CollatzResearch.WordTrace tailWord_3208734 prefixEnd_3208734 1098415222949302698112205 := by
  unfold tailWord_3208734
  simp only [CollatzResearch.WordTrace]
  refine ⟨14629017944664025122894157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78021429038208133988768837 14629017944664025122894157)
  ·
    refine ⟨5485881729249009421085309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14629017944664025122894157 5485881729249009421085309)
    ·
      refine ⟨2057205648468378532906991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5485881729249009421085309 2057205648468378532906991)
      ·
        refine ⟨3085808472702567799360487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2057205648468378532906991 3085808472702567799360487)
        ·
          refine ⟨4628712709053851699040731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3085808472702567799360487 4628712709053851699040731)
          ·
            refine ⟨6943069063580777548561097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4628712709053851699040731 6943069063580777548561097)
            ·
              refine ⟨5207301797685583161420823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6943069063580777548561097 5207301797685583161420823)
              ·
                refine ⟨7810952696528374742131235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5207301797685583161420823 7810952696528374742131235)
                ·
                  refine ⟨11716429044792562113196853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7810952696528374742131235 11716429044792562113196853)
                  ·
                    refine ⟨1098415222949302698112205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11716429044792562113196853 1098415222949302698112205)
                    ·
                      rfl

theorem cell22_3208734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_3208734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3208734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3208734 prefixEnd_3208734 := by exact prefixLift 3208734
  have htrace : WordTrace (prefixWord ++ tailWord_3208734) baseStart_3208734 baseEnd_3208734 := by
    simpa [prefixWord, tailWord_3208734, baseEnd_3208734] using wordTrace_append hprefix tailTrace_3208734
  have hstable : (prefixWord ++ tailWord_3208734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208734).length < 2 ^ (prefixWord ++ tailWord_3208734).sum := by decide
  have hdescent : baseEnd_3208734 < baseStart_3208734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208775 : List Nat := [1, 1, 4, 1, 5, 2, 1, 2, 5]
def baseStart_3208775 : Nat := 118140960795 + 3208775 * 2 ^ 59
def prefixEnd_3208775 : Nat := 4983230072969 + 3 ^ 40 * 3208775 * 2
def baseEnd_3208775 : Nat := 366143086029064085945693

theorem tailTrace_3208775 : CollatzResearch.WordTrace tailWord_3208775 prefixEnd_3208775 366143086029064085945693 := by
  unfold tailWord_3208775
  simp only [CollatzResearch.WordTrace]
  refine ⟨117033638950163664985395779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78022425966775776656930519 117033638950163664985395779)
  ·
    refine ⟨175550458425245497478093669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117033638950163664985395779 175550458425245497478093669)
    ·
      refine ⟨32915710954733530777142563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175550458425245497478093669 32915710954733530777142563)
      ·
        refine ⟨49373566432100296165713845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32915710954733530777142563 49373566432100296165713845)
        ·
          refine ⟨4628771853009402765535673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49373566432100296165713845 4628771853009402765535673)
          ·
            refine ⟨3471578889757052074151755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4628771853009402765535673 3471578889757052074151755)
            ·
              refine ⟨5207368334635578111227633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3471578889757052074151755 5207368334635578111227633)
              ·
                refine ⟨3905526250976683583420725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5207368334635578111227633 3905526250976683583420725)
                ·
                  refine ⟨366143086029064085945693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3905526250976683583420725 366143086029064085945693)
                  ·
                    rfl

theorem cell22_3208775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 5].length) (baseStart_3208775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3208775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3208775 prefixEnd_3208775 := by exact prefixLift 3208775
  have htrace : WordTrace (prefixWord ++ tailWord_3208775) baseStart_3208775 baseEnd_3208775 := by
    simpa [prefixWord, tailWord_3208775, baseEnd_3208775] using wordTrace_append hprefix tailTrace_3208775
  have hstable : (prefixWord ++ tailWord_3208775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208775).length < 2 ^ (prefixWord ++ tailWord_3208775).sum := by decide
  have hdescent : baseEnd_3208775 < baseStart_3208775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208805 : List Nat := [1, 3, 1, 3, 3, 2, 2, 2, 1, 4]
def baseStart_3208805 : Nat := 118140960795 + 3208805 * 2 ^ 59
def prefixEnd_3208805 : Nat := 4983230072969 + 3 ^ 40 * 3208805 * 2
def baseEnd_3208805 : Nat := 1098439527700282179586987

theorem tailTrace_3208805 : CollatzResearch.WordTrace tailWord_3208805 prefixEnd_3208805 1098439527700282179586987 := by
  unfold tailWord_3208805
  simp only [CollatzResearch.WordTrace]
  refine ⟨117034733140054980108987869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78023155426703320072658579 117034733140054980108987869)
  ·
    refine ⟨43888024927520617540870451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117034733140054980108987869 43888024927520617540870451)
    ·
      refine ⟨65832037391280926311305677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43888024927520617540870451 65832037391280926311305677)
      ·
        refine ⟨24687014021730347366739629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65832037391280926311305677 24687014021730347366739629)
        ·
          refine ⟨9257630258148880262527361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24687014021730347366739629 9257630258148880262527361)
          ·
            refine ⟨6943222693611660196895521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9257630258148880262527361 6943222693611660196895521)
            ·
              refine ⟨5207417020208745147671641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6943222693611660196895521 5207417020208745147671641)
              ·
                refine ⟨3905562765156558860753731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5207417020208745147671641 3905562765156558860753731)
                ·
                  refine ⟨5858344147734838291130597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3905562765156558860753731 5858344147734838291130597)
                  ·
                    refine ⟨1098439527700282179586987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5858344147734838291130597 1098439527700282179586987)
                    ·
                      rfl

theorem cell22_3208805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 4].length) (baseStart_3208805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3208805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3208805 prefixEnd_3208805 := by exact prefixLift 3208805
  have htrace : WordTrace (prefixWord ++ tailWord_3208805) baseStart_3208805 baseEnd_3208805 := by
    simpa [prefixWord, tailWord_3208805, baseEnd_3208805] using wordTrace_append hprefix tailTrace_3208805
  have hstable : (prefixWord ++ tailWord_3208805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208805).length < 2 ^ (prefixWord ++ tailWord_3208805).sum := by decide
  have hdescent : baseEnd_3208805 < baseStart_3208805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208833 : List Nat := [1, 2, 4, 2, 1, 2, 1, 1, 4, 4]
def baseStart_3208833 : Nat := 118140960795 + 3208833 * 2 ^ 59
def prefixEnd_3208833 : Nat := 4983230072969 + 3 ^ 40 * 3208833 * 2
def baseEnd_3208833 : Nat := 1098449112672499439886901

theorem tailTrace_3208833 : CollatzResearch.WordTrace tailWord_3208833 prefixEnd_3208833 1098449112672499439886901 := by
  unfold tailWord_3208833
  simp only [CollatzResearch.WordTrace]
  refine ⟨117035754383953540891007153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78023836255969027260671435 117035754383953540891007153)
  ·
    refine ⟨87776815787965155668255365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117035754383953540891007153 87776815787965155668255365)
    ·
      refine ⟨16458152960243466687797881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87776815787965155668255365 16458152960243466687797881)
      ·
        refine ⟨12343614720182600015848411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16458152960243466687797881 12343614720182600015848411)
        ·
          refine ⟨18515422080273900023772617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12343614720182600015848411 18515422080273900023772617)
          ·
            refine ⟨13886566560205425017829463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18515422080273900023772617 13886566560205425017829463)
            ·
              refine ⟨20829849840308137526744195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13886566560205425017829463 20829849840308137526744195)
              ·
                refine ⟨31244774760462206290116293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20829849840308137526744195 31244774760462206290116293)
                ·
                  refine ⟨5858395267586663679396805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31244774760462206290116293 5858395267586663679396805)
                  ·
                    refine ⟨1098449112672499439886901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5858395267586663679396805 1098449112672499439886901)
                    ·
                      rfl

theorem cell22_3208833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_3208833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3208833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3208833 prefixEnd_3208833 := by exact prefixLift 3208833
  have htrace : WordTrace (prefixWord ++ tailWord_3208833) baseStart_3208833 baseEnd_3208833 := by
    simpa [prefixWord, tailWord_3208833, baseEnd_3208833] using wordTrace_append hprefix tailTrace_3208833
  have hstable : (prefixWord ++ tailWord_3208833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208833).length < 2 ^ (prefixWord ++ tailWord_3208833).sum := by decide
  have hdescent : baseEnd_3208833 < baseStart_3208833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208891 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 3, 7]
def baseStart_3208891 : Nat := 118140960795 + 3208891 * 2 ^ 59
def prefixEnd_3208891 : Nat := 4983230072969 + 3 ^ 40 * 3208891 * 2
def baseEnd_3208891 : Nat := 1098468967257806621936723

theorem tailTrace_3208891 : CollatzResearch.WordTrace tailWord_3208891 prefixEnd_3208891 1098468967257806621936723 := by
  unfold tailWord_3208891
  simp only [CollatzResearch.WordTrace]
  refine ⟨117037869817743416796618527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78025246545162277864412351 117037869817743416796618527)
  ·
    refine ⟨175556804726615125194927791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117037869817743416796618527 175556804726615125194927791)
    ·
      refine ⟨263335207089922687792391687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175556804726615125194927791 263335207089922687792391687)
      ·
        refine ⟨395002810634884031688587531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263335207089922687792391687 395002810634884031688587531)
        ·
          refine ⟨592504215952326047532881297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395002810634884031688587531 592504215952326047532881297)
          ·
            refine ⟨444378161964244535649660973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 592504215952326047532881297 444378161964244535649660973)
            ·
              refine ⟨166641810736591700868622865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 444378161964244535649660973 166641810736591700868622865)
              ·
                refine ⟨124981358052443775651467149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166641810736591700868622865 124981358052443775651467149)
                ·
                  refine ⟨46868009269666415869300181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124981358052443775651467149 46868009269666415869300181)
                  ·
                    refine ⟨1098468967257806621936723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46868009269666415869300181 1098468967257806621936723)
                    ·
                      rfl

theorem cell22_3208891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 7].length) (baseStart_3208891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3208891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3208891 prefixEnd_3208891 := by exact prefixLift 3208891
  have htrace : WordTrace (prefixWord ++ tailWord_3208891) baseStart_3208891 baseEnd_3208891 := by
    simpa [prefixWord, tailWord_3208891, baseEnd_3208891] using wordTrace_append hprefix tailTrace_3208891
  have hstable : (prefixWord ++ tailWord_3208891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208891).length < 2 ^ (prefixWord ++ tailWord_3208891).sum := by decide
  have hdescent : baseEnd_3208891 < baseStart_3208891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208968 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 3, 6]
def baseStart_3208968 : Nat := 118140960795 + 3208968 * 2 ^ 59
def prefixEnd_3208968 : Nat := 4983230072969 + 3 ^ 40 * 3208968 * 2
def baseEnd_3208968 : Nat := 1098495325931404087761487

theorem tailTrace_3208968 : CollatzResearch.WordTrace tailWord_3208968 prefixEnd_3208968 1098495325931404087761487 := by
  unfold tailWord_3208968
  simp only [CollatzResearch.WordTrace]
  refine ⟨58520339119232229473585779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78027118825642972631447705 58520339119232229473585779)
  ·
    refine ⟨87780508678848344210378669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58520339119232229473585779 87780508678848344210378669)
    ·
      refine ⟨32917690754568129078892001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87780508678848344210378669 32917690754568129078892001)
      ·
        refine ⟨24688268065926096809169001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32917690754568129078892001 24688268065926096809169001)
        ·
          refine ⟨18516201049444572606876751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24688268065926096809169001 18516201049444572606876751)
          ·
            refine ⟨27774301574166858910315127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18516201049444572606876751 27774301574166858910315127)
            ·
              refine ⟨41661452361250288365472691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27774301574166858910315127 41661452361250288365472691)
              ·
                refine ⟨62492178541875432548209037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41661452361250288365472691 62492178541875432548209037)
                ·
                  refine ⟨23434566953203287205578389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62492178541875432548209037 23434566953203287205578389)
                  ·
                    refine ⟨1098495325931404087761487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23434566953203287205578389 1098495325931404087761487)
                    ·
                      rfl

theorem cell22_3208968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_3208968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3208968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3208968 prefixEnd_3208968 := by exact prefixLift 3208968
  have htrace : WordTrace (prefixWord ++ tailWord_3208968) baseStart_3208968 baseEnd_3208968 := by
    simpa [prefixWord, tailWord_3208968, baseEnd_3208968] using wordTrace_append hprefix tailTrace_3208968
  have hstable : (prefixWord ++ tailWord_3208968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208968).length < 2 ^ (prefixWord ++ tailWord_3208968).sum := by decide
  have hdescent : baseEnd_3208968 < baseStart_3208968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208970 : List Nat := [3, 1, 2, 2, 1, 3, 3, 1, 1, 5]
def baseStart_3208970 : Nat := 118140960795 + 3208970 * 2 ^ 59
def prefixEnd_3208970 : Nat := 4983230072969 + 3 ^ 40 * 3208970 * 2
def baseEnd_3208970 : Nat := 1098496010572276749211481

theorem tailTrace_3208970 : CollatzResearch.WordTrace tailWord_3208970 prefixEnd_3208970 1098496010572276749211481 := by
  unfold tailWord_3208970
  simp only [CollatzResearch.WordTrace]
  refine ⟨29260187796114303322186091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78027167456304808859162909 29260187796114303322186091)
  ·
    refine ⟨43890281694171454983279137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29260187796114303322186091 43890281694171454983279137)
    ·
      refine ⟨32917711270628591237459353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43890281694171454983279137 32917711270628591237459353)
      ·
        refine ⟨24688283452971443428094515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32917711270628591237459353 24688283452971443428094515)
        ·
          refine ⟨37032425179457165142141773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24688283452971443428094515 37032425179457165142141773)
          ·
            refine ⟨13887159442296436928303165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37032425179457165142141773 13887159442296436928303165)
            ·
              refine ⟨5207684790861163848113687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13887159442296436928303165 5207684790861163848113687)
              ·
                refine ⟨7811527186291745772170531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5207684790861163848113687 7811527186291745772170531)
                ·
                  refine ⟨11717290779437618658255797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7811527186291745772170531 11717290779437618658255797)
                  ·
                    refine ⟨1098496010572276749211481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11717290779437618658255797 1098496010572276749211481)
                    ·
                      rfl

theorem cell22_3208970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_3208970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3208970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3208970 prefixEnd_3208970 := by exact prefixLift 3208970
  have htrace : WordTrace (prefixWord ++ tailWord_3208970) baseStart_3208970 baseEnd_3208970 := by
    simpa [prefixWord, tailWord_3208970, baseEnd_3208970] using wordTrace_append hprefix tailTrace_3208970
  have hstable : (prefixWord ++ tailWord_3208970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208970).length < 2 ^ (prefixWord ++ tailWord_3208970).sum := by decide
  have hdescent : baseEnd_3208970 < baseStart_3208970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209000 : List Nat := [2, 1, 5, 1, 1, 4, 8]
def baseStart_3209000 : Nat := 118140960795 + 3209000 * 2 ^ 59
def prefixEnd_3209000 : Nat := 4983230072969 + 3 ^ 40 * 3209000 * 2
def baseEnd_3209000 : Nat := 40685417784643210035607

theorem tailTrace_3209000 : CollatzResearch.WordTrace tailWord_3209000 prefixEnd_3209000 40685417784643210035607 := by
  unfold tailWord_3209000
  simp only [CollatzResearch.WordTrace]
  refine ⟨58520922687174264206168227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78027896916232352274890969 58520922687174264206168227)
  ·
    refine ⟨87781384030761396309252341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58520922687174264206168227 87781384030761396309252341)
    ·
      refine ⟨8229504752883880903992407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87781384030761396309252341 8229504752883880903992407)
      ·
        refine ⟨12344257129325821355988611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8229504752883880903992407 12344257129325821355988611)
        ·
          refine ⟨18516385693988732033982917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12344257129325821355988611 18516385693988732033982917)
          ·
            refine ⟨3471822317622887256371797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18516385693988732033982917 3471822317622887256371797)
            ·
              refine ⟨40685417784643210035607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3471822317622887256371797 40685417784643210035607)
              ·
                rfl

theorem cell22_3209000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 8].length) (baseStart_3209000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3209000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3209000 prefixEnd_3209000 := by exact prefixLift 3209000
  have htrace : WordTrace (prefixWord ++ tailWord_3209000) baseStart_3209000 baseEnd_3209000 := by
    simpa [prefixWord, tailWord_3209000, baseEnd_3209000] using wordTrace_append hprefix tailTrace_3209000
  have hstable : (prefixWord ++ tailWord_3209000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209000).length < 2 ^ (prefixWord ++ tailWord_3209000).sum := by decide
  have hdescent : baseEnd_3209000 < baseStart_3209000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209006 : List Nat := [4, 1, 3, 2, 2, 1, 3, 2, 4]
def baseStart_3209006 : Nat := 118140960795 + 3209006 * 2 ^ 59
def prefixEnd_3209006 : Nat := 4983230072969 + 3 ^ 40 * 3209006 * 2
def baseEnd_3209006 : Nat := 366169444702661551770457

theorem tailTrace_3209006 : CollatzResearch.WordTrace tailWord_3209006 prefixEnd_3209006 366169444702661551770457 := by
  unfold tailWord_3209006
  simp only [CollatzResearch.WordTrace]
  refine ⟨14630258026540848929631859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78028042808217860958036581 14630258026540848929631859)
  ·
    refine ⟨21945387039811273394447789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14630258026540848929631859 21945387039811273394447789)
    ·
      refine ⟨8229520139929227522917921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21945387039811273394447789 8229520139929227522917921)
      ·
        refine ⟨6172140104946920642188441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8229520139929227522917921 6172140104946920642188441)
        ·
          refine ⟨4629105078710190481641331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6172140104946920642188441 4629105078710190481641331)
          ·
            refine ⟨6943657618065285722461997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4629105078710190481641331 6943657618065285722461997)
            ·
              refine ⟨2603871606774482145923249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6943657618065285722461997 2603871606774482145923249)
              ·
                refine ⟨1952903705080861609442437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2603871606774482145923249 1952903705080861609442437)
                ·
                  refine ⟨366169444702661551770457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1952903705080861609442437 366169444702661551770457)
                  ·
                    rfl

theorem cell22_3209006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_3209006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3209006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3209006 prefixEnd_3209006 := by exact prefixLift 3209006
  have htrace : WordTrace (prefixWord ++ tailWord_3209006) baseStart_3209006 baseEnd_3209006 := by
    simpa [prefixWord, tailWord_3209006, baseEnd_3209006] using wordTrace_append hprefix tailTrace_3209006
  have hstable : (prefixWord ++ tailWord_3209006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209006).length < 2 ^ (prefixWord ++ tailWord_3209006).sum := by decide
  have hdescent : baseEnd_3209006 < baseStart_3209006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209015 : List Nat := [1, 1, 3, 1, 2, 1, 2, 5, 3, 3]
def baseStart_3209015 : Nat := 118140960795 + 3209015 * 2 ^ 59
def prefixEnd_3209015 : Nat := 4983230072969 + 3 ^ 40 * 3209015 * 2
def baseEnd_3209015 : Nat := 1098511414991911631836343

theorem tailTrace_3209015 : CollatzResearch.WordTrace tailWord_3209015 prefixEnd_3209015 1098511414991911631836343 := by
  unfold tailWord_3209015
  simp only [CollatzResearch.WordTrace]
  refine ⟨117042392469294185974132499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78028261646196123982754999 117042392469294185974132499)
  ·
    refine ⟨175563588703941278961198749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117042392469294185974132499 175563588703941278961198749)
    ·
      refine ⟨65836345763977979610449531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175563588703941278961198749 65836345763977979610449531)
      ·
        refine ⟨98754518645966969415674297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65836345763977979610449531 98754518645966969415674297)
        ·
          refine ⟨74065888984475227061755723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98754518645966969415674297 74065888984475227061755723)
          ·
            refine ⟨111098833476712840592633585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74065888984475227061755723 111098833476712840592633585)
            ·
              refine ⟨83324125107534630444475189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111098833476712840592633585 83324125107534630444475189)
              ·
                refine ⟨7811636728831371604169549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83324125107534630444475189 7811636728831371604169549)
                ·
                  refine ⟨2929363773311764351563581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7811636728831371604169549 2929363773311764351563581)
                  ·
                    refine ⟨1098511414991911631836343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2929363773311764351563581 1098511414991911631836343)
                    ·
                      rfl

theorem cell22_3209015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 3, 3].length) (baseStart_3209015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3209015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3209015 prefixEnd_3209015 := by exact prefixLift 3209015
  have htrace : WordTrace (prefixWord ++ tailWord_3209015) baseStart_3209015 baseEnd_3209015 := by
    simpa [prefixWord, tailWord_3209015, baseEnd_3209015] using wordTrace_append hprefix tailTrace_3209015
  have hstable : (prefixWord ++ tailWord_3209015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209015).length < 2 ^ (prefixWord ++ tailWord_3209015).sum := by decide
  have hdescent : baseEnd_3209015 < baseStart_3209015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209017 : List Nat := [1, 2, 1, 7, 1, 1, 2, 7]
def baseStart_3209017 : Nat := 118140960795 + 3209017 * 2 ^ 59
def prefixEnd_3209017 : Nat := 4983230072969 + 3 ^ 40 * 3209017 * 2
def baseEnd_3209017 : Nat := 122056899959198254809593

theorem tailTrace_3209017 : CollatzResearch.WordTrace tailWord_3209017 prefixEnd_3209017 122056899959198254809593 := by
  unfold tailWord_3209017
  simp only [CollatzResearch.WordTrace]
  refine ⟨117042465415286940315705305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78028310276857960210470203 117042465415286940315705305)
  ·
    refine ⟨87781849061465205236778979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117042465415286940315705305 87781849061465205236778979)
    ·
      refine ⟨131672773592197807855168469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87781849061465205236778979 131672773592197807855168469)
      ·
        refine ⟨3086080631067136121605511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 131672773592197807855168469 3086080631067136121605511)
        ·
          refine ⟨4629120946600704182408267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3086080631067136121605511 4629120946600704182408267)
          ·
            refine ⟨6943681419901056273612401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4629120946600704182408267 6943681419901056273612401)
            ·
              refine ⟨5207761064925792205209301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6943681419901056273612401 5207761064925792205209301)
              ·
                refine ⟨122056899959198254809593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5207761064925792205209301 122056899959198254809593)
                ·
                  rfl

theorem cell22_3209017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 7].length) (baseStart_3209017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3209017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3209017 prefixEnd_3209017 := by exact prefixLift 3209017
  have htrace : WordTrace (prefixWord ++ tailWord_3209017) baseStart_3209017 baseEnd_3209017 := by
    simpa [prefixWord, tailWord_3209017, baseEnd_3209017] using wordTrace_append hprefix tailTrace_3209017
  have hstable : (prefixWord ++ tailWord_3209017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209017).length < 2 ^ (prefixWord ++ tailWord_3209017).sum := by decide
  have hdescent : baseEnd_3209017 < baseStart_3209017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209021 : List Nat := [1, 4, 1, 4, 1, 3, 2, 1, 2, 3]
def baseStart_3209021 : Nat := 118140960795 + 3209021 * 2 ^ 59
def prefixEnd_3209021 : Nat := 4983230072969 + 3 ^ 40 * 3209021 * 2
def baseEnd_3209021 : Nat := 1098513468914529616186325

theorem tailTrace_3209021 : CollatzResearch.WordTrace tailWord_3209021 prefixEnd_3209021 1098513468914529616186325 := by
  unfold tailWord_3209021
  simp only [CollatzResearch.WordTrace]
  refine ⟨117042611307272448998850917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78028407538181632665900611 117042611307272448998850917)
  ·
    refine ⟨21945489620113584187284547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117042611307272448998850917 21945489620113584187284547)
    ·
      refine ⟨32918234430170376280926821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21945489620113584187284547 32918234430170376280926821)
      ·
        refine ⟨6172168955656945552673779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32918234430170376280926821 6172168955656945552673779)
        ·
          refine ⟨9258253433485418329010669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6172168955656945552673779 9258253433485418329010669)
          ·
            refine ⟨3471845037557031873379001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9258253433485418329010669 3471845037557031873379001)
            ·
              refine ⟨2603883778167773905034251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3471845037557031873379001 2603883778167773905034251)
              ·
                refine ⟨3905825667251660857551377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2603883778167773905034251 3905825667251660857551377)
                ·
                  refine ⟨2929369250438745643163533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3905825667251660857551377 2929369250438745643163533)
                  ·
                    refine ⟨1098513468914529616186325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2929369250438745643163533 1098513468914529616186325)
                    ·
                      rfl

theorem cell22_3209021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 2, 3].length) (baseStart_3209021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3209021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3209021 prefixEnd_3209021 := by exact prefixLift 3209021
  have htrace : WordTrace (prefixWord ++ tailWord_3209021) baseStart_3209021 baseEnd_3209021 := by
    simpa [prefixWord, tailWord_3209021, baseEnd_3209021] using wordTrace_append hprefix tailTrace_3209021
  have hstable : (prefixWord ++ tailWord_3209021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209021).length < 2 ^ (prefixWord ++ tailWord_3209021).sum := by decide
  have hdescent : baseEnd_3209021 < baseStart_3209021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209043 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 6, 5]
def baseStart_3209043 : Nat := 118140960795 + 3209043 * 2 ^ 59
def prefixEnd_3209043 : Nat := 4983230072969 + 3 ^ 40 * 3209043 * 2
def baseEnd_3209043 : Nat := 1098520999964128892136257

theorem tailTrace_3209043 : CollatzResearch.WordTrace tailWord_3209043 prefixEnd_3209043 1098520999964128892136257 := by
  unfold tailWord_3209043
  simp only [CollatzResearch.WordTrace]
  refine ⟨117043413713192746756151783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78028942475461831170767855 117043413713192746756151783)
  ·
    refine ⟨175565120569789120134227675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117043413713192746756151783 175565120569789120134227675)
    ·
      refine ⟨263347680854683680201341513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175565120569789120134227675 263347680854683680201341513)
      ·
        refine ⟨197510760641012760151006135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263347680854683680201341513 197510760641012760151006135)
        ·
          refine ⟨296266140961519140226509203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197510760641012760151006135 296266140961519140226509203)
          ·
            refine ⟨444399211442278710339763805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296266140961519140226509203 444399211442278710339763805)
            ·
              refine ⟨166649704290854516377411427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 444399211442278710339763805 166649704290854516377411427)
              ·
                refine ⟨249974556436281774566117141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166649704290854516377411427 249974556436281774566117141)
                ·
                  refine ⟨11717557332950708182786741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 249974556436281774566117141 11717557332950708182786741)
                  ·
                    refine ⟨1098520999964128892136257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11717557332950708182786741 1098520999964128892136257)
                    ·
                      rfl

theorem cell22_3209043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 5].length) (baseStart_3209043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3209043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3209043 prefixEnd_3209043 := by exact prefixLift 3209043
  have htrace : WordTrace (prefixWord ++ tailWord_3209043) baseStart_3209043 baseEnd_3209043 := by
    simpa [prefixWord, tailWord_3209043, baseEnd_3209043] using wordTrace_append hprefix tailTrace_3209043
  have hstable : (prefixWord ++ tailWord_3209043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209043).length < 2 ^ (prefixWord ++ tailWord_3209043).sum := by decide
  have hdescent : baseEnd_3209043 < baseStart_3209043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209105 : List Nat := [1, 2, 2, 1, 1, 1, 6, 2, 1, 5]
def baseStart_3209105 : Nat := 118140960795 + 3209105 * 2 ^ 59
def prefixEnd_3209105 : Nat := 4983230072969 + 3 ^ 40 * 3209105 * 2
def baseEnd_3209105 : Nat := 1098542223831181397086067

theorem tailTrace_3209105 : CollatzResearch.WordTrace tailWord_3209105 prefixEnd_3209105 1098542223831181397086067 := by
  unfold tailWord_3209105
  simp only [CollatzResearch.WordTrace]
  refine ⟨117045675038968131344908769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78030450025978754229939179 117045675038968131344908769)
  ·
    refine ⟨87784256279226098508681577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117045675038968131344908769 87784256279226098508681577)
    ·
      refine ⟨65838192209419573881511183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87784256279226098508681577 65838192209419573881511183)
      ·
        refine ⟨98757288314129360822266775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65838192209419573881511183 98757288314129360822266775)
        ·
          refine ⟨148135932471194041233400163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98757288314129360822266775 148135932471194041233400163)
          ·
            refine ⟨222203898706791061850100245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148135932471194041233400163 222203898706791061850100245)
            ·
              refine ⟨10415807751880831024223449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 222203898706791061850100245 10415807751880831024223449)
              ·
                refine ⟨7811855813910623268167587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10415807751880831024223449 7811855813910623268167587)
                ·
                  refine ⟨11717783720865934902251381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7811855813910623268167587 11717783720865934902251381)
                  ·
                    refine ⟨1098542223831181397086067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11717783720865934902251381 1098542223831181397086067)
                    ·
                      rfl

theorem cell22_3209105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_3209105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3209105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3209105 prefixEnd_3209105 := by exact prefixLift 3209105
  have htrace : WordTrace (prefixWord ++ tailWord_3209105) baseStart_3209105 baseEnd_3209105 := by
    simpa [prefixWord, tailWord_3209105, baseEnd_3209105] using wordTrace_append hprefix tailTrace_3209105
  have hstable : (prefixWord ++ tailWord_3209105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209105).length < 2 ^ (prefixWord ++ tailWord_3209105).sum := by decide
  have hdescent : baseEnd_3209105 < baseStart_3209105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209120 : List Nat := [2, 1, 1, 4, 1, 1, 1, 3, 4, 4]
def baseStart_3209120 : Nat := 118140960795 + 3209120 * 2 ^ 59
def prefixEnd_3209120 : Nat := 4983230072969 + 3 ^ 40 * 3209120 * 2
def baseEnd_3209120 : Nat := 1098547358637726357961021

theorem tailTrace_3209120 : CollatzResearch.WordTrace tailWord_3209120 prefixEnd_3209120 1098547358637726357961021 := by
  unfold tailWord_3209120
  simp only [CollatzResearch.WordTrace]
  refine ⟨58523111066956894453352407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78030814755942525937803209 58523111066956894453352407)
  ·
    refine ⟨87784666600435341680028611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58523111066956894453352407 87784666600435341680028611)
    ·
      refine ⟨131676999900653012520042917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87784666600435341680028611 131676999900653012520042917)
      ·
        refine ⟨24689437481372439847508047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131676999900653012520042917 24689437481372439847508047)
        ·
          refine ⟨37034156222058659771262071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24689437481372439847508047 37034156222058659771262071)
          ·
            refine ⟨55551234333087989656893107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37034156222058659771262071 55551234333087989656893107)
            ·
              refine ⟨83326851499631984485339661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55551234333087989656893107 83326851499631984485339661)
              ·
                refine ⟨31247569312361994182002373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83326851499631984485339661 31247569312361994182002373)
                ·
                  refine ⟨5858919246067873909125445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31247569312361994182002373 5858919246067873909125445)
                  ·
                    refine ⟨1098547358637726357961021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5858919246067873909125445 1098547358637726357961021)
                    ·
                      rfl

theorem cell22_3209120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 4, 4].length) (baseStart_3209120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3209120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3209120 prefixEnd_3209120 := by exact prefixLift 3209120
  have htrace : WordTrace (prefixWord ++ tailWord_3209120) baseStart_3209120 baseEnd_3209120 := by
    simpa [prefixWord, tailWord_3209120, baseEnd_3209120] using wordTrace_append hprefix tailTrace_3209120
  have hstable : (prefixWord ++ tailWord_3209120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209120).length < 2 ^ (prefixWord ++ tailWord_3209120).sum := by decide
  have hdescent : baseEnd_3209120 < baseStart_3209120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209139 : List Nat := [1, 1, 1, 2, 3, 1, 7, 1, 2, 3]
def baseStart_3209139 : Nat := 118140960795 + 3209139 * 2 ^ 59
def prefixEnd_3209139 : Nat := 4983230072969 + 3 ^ 40 * 3209139 * 2
def baseEnd_3209139 : Nat := 1098553862726016641735963

theorem tailTrace_3209139 : CollatzResearch.WordTrace tailWord_3209139 prefixEnd_3209139 1098553862726016641735963 := by
  unfold tailWord_3209139
  simp only [CollatzResearch.WordTrace]
  refine ⟨117046915120844955151646471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78031276747229970101097647 117046915120844955151646471)
  ·
    refine ⟨175570372681267432727469707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117046915120844955151646471 175570372681267432727469707)
    ·
      refine ⟨263355559021901149091204561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175570372681267432727469707 263355559021901149091204561)
      ·
        refine ⟨197516669266425861818403421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263355559021901149091204561 197516669266425861818403421)
        ·
          refine ⟨74068750974909698181901283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197516669266425861818403421 74068750974909698181901283)
          ·
            refine ⟨111103126462364547272851925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74068750974909698181901283 111103126462364547272851925)
            ·
              refine ⟨2603979526461669076707467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 111103126462364547272851925 2603979526461669076707467)
              ·
                refine ⟨3905969289692503615061201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2603979526461669076707467 3905969289692503615061201)
                ·
                  refine ⟨2929476967269377711295901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3905969289692503615061201 2929476967269377711295901)
                  ·
                    refine ⟨1098553862726016641735963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2929476967269377711295901 1098553862726016641735963)
                    ·
                      rfl

theorem cell22_3209139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 2, 3].length) (baseStart_3209139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3209139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3209139 prefixEnd_3209139 := by exact prefixLift 3209139
  have htrace : WordTrace (prefixWord ++ tailWord_3209139) baseStart_3209139 baseEnd_3209139 := by
    simpa [prefixWord, tailWord_3209139, baseEnd_3209139] using wordTrace_append hprefix tailTrace_3209139
  have hstable : (prefixWord ++ tailWord_3209139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209139).length < 2 ^ (prefixWord ++ tailWord_3209139).sum := by decide
  have hdescent : baseEnd_3209139 < baseStart_3209139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209184 : List Nat := [2, 1, 1, 3, 1, 1, 1, 8, 1, 3]
def baseStart_3209184 : Nat := 118140960795 + 3209184 * 2 ^ 59
def prefixEnd_3209184 : Nat := 4983230072969 + 3 ^ 40 * 3209184 * 2
def baseEnd_3209184 : Nat := 1098569267145651524360825

theorem tailTrace_3209184 : CollatzResearch.WordTrace tailWord_3209184 prefixEnd_3209184 1098569267145651524360825 := by
  unfold tailWord_3209184
  simp only [CollatzResearch.WordTrace]
  refine ⟨58524278202840963918517303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78032370937121285224689737 58524278202840963918517303)
  ·
    refine ⟨87786417304261445877775955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58524278202840963918517303 87786417304261445877775955)
    ·
      refine ⟨131679625956392168816663933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87786417304261445877775955 131679625956392168816663933)
      ·
        refine ⟨49379859733647063306248975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131679625956392168816663933 49379859733647063306248975)
        ·
          refine ⟨74069789600470594959373463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49379859733647063306248975 74069789600470594959373463)
          ·
            refine ⟨111104684400705892439060195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74069789600470594959373463 111104684400705892439060195)
            ·
              refine ⟨166657026601058838658590293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111104684400705892439060195 166657026601058838658590293)
              ·
                refine ⟨1953012030481158265530355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 166657026601058838658590293 1953012030481158265530355)
                ·
                  refine ⟨2929518045721737398295533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1953012030481158265530355 2929518045721737398295533)
                  ·
                    refine ⟨1098569267145651524360825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2929518045721737398295533 1098569267145651524360825)
                    ·
                      rfl

theorem cell22_3209184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 8, 1, 3].length) (baseStart_3209184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3209184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3209184 prefixEnd_3209184 := by exact prefixLift 3209184
  have htrace : WordTrace (prefixWord ++ tailWord_3209184) baseStart_3209184 baseEnd_3209184 := by
    simpa [prefixWord, tailWord_3209184, baseEnd_3209184] using wordTrace_append hprefix tailTrace_3209184
  have hstable : (prefixWord ++ tailWord_3209184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209184).length < 2 ^ (prefixWord ++ tailWord_3209184).sum := by decide
  have hdescent : baseEnd_3209184 < baseStart_3209184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209195 : List Nat := [1, 1, 1, 1, 2, 3, 1, 5, 2, 5]
def baseStart_3209195 : Nat := 118140960795 + 3209195 * 2 ^ 59
def prefixEnd_3209195 : Nat := 4983230072969 + 3 ^ 40 * 3209195 * 2
def baseEnd_3209195 : Nat := 1098573032670451162335791

theorem tailTrace_3209195 : CollatzResearch.WordTrace tailWord_3209195 prefixEnd_3209195 1098573032670451162335791 := by
  unfold tailWord_3209195
  simp only [CollatzResearch.WordTrace]
  refine ⟨117048957608642076715685039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78032638405761384477123359 117048957608642076715685039)
  ·
    refine ⟨175573436412963115073527559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117048957608642076715685039 175573436412963115073527559)
    ·
      refine ⟨263360154619444672610291339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175573436412963115073527559 263360154619444672610291339)
      ·
        refine ⟨395040231929167008915437009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263360154619444672610291339 395040231929167008915437009)
        ·
          refine ⟨296280173946875256686577757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 395040231929167008915437009 296280173946875256686577757)
          ·
            refine ⟨111105065230078221257466659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 296280173946875256686577757 111105065230078221257466659)
            ·
              refine ⟨166657597845117331886199989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111105065230078221257466659 166657597845117331886199989)
              ·
                refine ⟨15624149797979749864331249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 166657597845117331886199989 15624149797979749864331249)
                ·
                  refine ⟨11718112348484812398248437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15624149797979749864331249 11718112348484812398248437)
                  ·
                    refine ⟨1098573032670451162335791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11718112348484812398248437 1098573032670451162335791)
                    ·
                      rfl

theorem cell22_3209195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 5].length) (baseStart_3209195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3209195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3209195 prefixEnd_3209195 := by exact prefixLift 3209195
  have htrace : WordTrace (prefixWord ++ tailWord_3209195) baseStart_3209195 baseEnd_3209195 := by
    simpa [prefixWord, tailWord_3209195, baseEnd_3209195] using wordTrace_append hprefix tailTrace_3209195
  have hstable : (prefixWord ++ tailWord_3209195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209195).length < 2 ^ (prefixWord ++ tailWord_3209195).sum := by decide
  have hdescent : baseEnd_3209195 < baseStart_3209195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209308 : List Nat := [2, 2, 4, 1, 1, 3, 3, 1, 2, 3]
def baseStart_3209308 : Nat := 118140960795 + 3209308 * 2 ^ 59
def prefixEnd_3209308 : Nat := 4983230072969 + 3 ^ 40 * 3209308 * 2
def baseEnd_3209308 : Nat := 1098611714879756534260445

theorem tailTrace_3209308 : CollatzResearch.WordTrace tailWord_3209308 prefixEnd_3209308 1098611714879756534260445 := by
  unfold tailWord_3209308
  simp only [CollatzResearch.WordTrace]
  refine ⟨58526539528616348507274289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78035386038155131343032385 58526539528616348507274289)
  ·
    refine ⟨43894904646462261380455717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58526539528616348507274289 43894904646462261380455717)
    ·
      refine ⟨8230294621211674008835447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43894904646462261380455717 8230294621211674008835447)
      ·
        refine ⟨12345441931817511013253171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8230294621211674008835447 12345441931817511013253171)
        ·
          refine ⟨18518162897726266519879757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12345441931817511013253171 18518162897726266519879757)
          ·
            refine ⟨6944311086647349944954909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18518162897726266519879757 6944311086647349944954909)
            ·
              refine ⟨2604116657492756229358091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6944311086647349944954909 2604116657492756229358091)
              ·
                refine ⟨3906174986239134344037137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2604116657492756229358091 3906174986239134344037137)
                ·
                  refine ⟨2929631239679350758027853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3906174986239134344037137 2929631239679350758027853)
                  ·
                    refine ⟨1098611714879756534260445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2929631239679350758027853 1098611714879756534260445)
                    ·
                      rfl

theorem cell22_3209308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_3209308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3209308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3209308 prefixEnd_3209308 := by exact prefixLift 3209308
  have htrace : WordTrace (prefixWord ++ tailWord_3209308) baseStart_3209308 baseEnd_3209308 := by
    simpa [prefixWord, tailWord_3209308, baseEnd_3209308] using wordTrace_append hprefix tailTrace_3209308
  have hstable : (prefixWord ++ tailWord_3209308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209308).length < 2 ^ (prefixWord ++ tailWord_3209308).sum := by decide
  have hdescent : baseEnd_3209308 < baseStart_3209308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209319 : List Nat := [1, 1, 5, 1, 1, 2, 1, 4, 3, 3]
def baseStart_3209319 : Nat := 118140960795 + 3209319 * 2 ^ 59
def prefixEnd_3209319 : Nat := 4983230072969 + 3 ^ 40 * 3209319 * 2
def baseEnd_3209319 : Nat := 1098615480404556172235411

theorem tailTrace_3209319 : CollatzResearch.WordTrace tailWord_3209319 prefixEnd_3209319 1098615480404556172235411 := by
  unfold tailWord_3209319
  simp only [CollatzResearch.WordTrace]
  refine ⟨117053480260192845893199011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78035653506795230595466007 117053480260192845893199011)
  ·
    refine ⟨175580220390289268839798517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117053480260192845893199011 175580220390289268839798517)
    ·
      refine ⟨16460645661589618953731111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 175580220390289268839798517 16460645661589618953731111)
      ·
        refine ⟨24690968492384428430596667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16460645661589618953731111 24690968492384428430596667)
        ·
          refine ⟨37036452738576642645895001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24690968492384428430596667 37036452738576642645895001)
          ·
            refine ⟨27777339553932481984421251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37036452738576642645895001 27777339553932481984421251)
            ·
              refine ⟨41666009330898722976631877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27777339553932481984421251 41666009330898722976631877)
              ·
                refine ⟨7812376749543510558118477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41666009330898722976631877 7812376749543510558118477)
                ·
                  refine ⟨2929641281078816459294429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7812376749543510558118477 2929641281078816459294429)
                  ·
                    refine ⟨1098615480404556172235411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2929641281078816459294429 1098615480404556172235411)
                    ·
                      rfl

theorem cell22_3209319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_3209319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3209319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3209319 prefixEnd_3209319 := by exact prefixLift 3209319
  have htrace : WordTrace (prefixWord ++ tailWord_3209319) baseStart_3209319 baseEnd_3209319 := by
    simpa [prefixWord, tailWord_3209319, baseEnd_3209319] using wordTrace_append hprefix tailTrace_3209319
  have hstable : (prefixWord ++ tailWord_3209319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209319).length < 2 ^ (prefixWord ++ tailWord_3209319).sum := by decide
  have hdescent : baseEnd_3209319 < baseStart_3209319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209353 : List Nat := [1, 2, 1, 1, 4, 2, 5, 2, 1, 3]
def baseStart_3209353 : Nat := 118140960795 + 3209353 * 2 ^ 59
def prefixEnd_3209353 : Nat := 4983230072969 + 3 ^ 40 * 3209353 * 2
def baseEnd_3209353 : Nat := 1098627119299391416885307

theorem tailTrace_3209353 : CollatzResearch.WordTrace tailWord_3209353 prefixEnd_3209353 1098627119299391416885307 := by
  unfold tailWord_3209353
  simp only [CollatzResearch.WordTrace]
  refine ⟨117054720342069669699936713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78036480228046446466624475 117054720342069669699936713)
  ·
    refine ⟨87791040256552252274952535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117054720342069669699936713 87791040256552252274952535)
    ·
      refine ⟨131686560384828378412428803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87791040256552252274952535 131686560384828378412428803)
      ·
        refine ⟨197529840577242567618643205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131686560384828378412428803 197529840577242567618643205)
        ·
          refine ⟨37036845108232981428495601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197529840577242567618643205 37036845108232981428495601)
          ·
            refine ⟨27777633831174736071371701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37036845108232981428495601 27777633831174736071371701)
            ·
              refine ⟨2604153171672631506691097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27777633831174736071371701 2604153171672631506691097)
              ·
                refine ⟨1953114878754473630018323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2604153171672631506691097 1953114878754473630018323)
                ·
                  refine ⟨2929672318131710445027485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1953114878754473630018323 2929672318131710445027485)
                  ·
                    refine ⟨1098627119299391416885307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2929672318131710445027485 1098627119299391416885307)
                    ·
                      rfl

theorem cell22_3209353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 2, 1, 3].length) (baseStart_3209353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3209353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3209353 prefixEnd_3209353 := by exact prefixLift 3209353
  have htrace : WordTrace (prefixWord ++ tailWord_3209353) baseStart_3209353 baseEnd_3209353 := by
    simpa [prefixWord, tailWord_3209353, baseEnd_3209353] using wordTrace_append hprefix tailTrace_3209353
  have hstable : (prefixWord ++ tailWord_3209353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209353).length < 2 ^ (prefixWord ++ tailWord_3209353).sum := by decide
  have hdescent : baseEnd_3209353 < baseStart_3209353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209407 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 3, 6]
def baseStart_3209407 : Nat := 118140960795 + 3209407 * 2 ^ 59
def prefixEnd_3209407 : Nat := 4983230072969 + 3 ^ 40 * 3209407 * 2
def baseEnd_3209407 : Nat := 1098645604602953276035141

theorem tailTrace_3209407 : CollatzResearch.WordTrace tailWord_3209407 prefixEnd_3209407 1098645604602953276035141 := by
  unfold tailWord_3209407
  simp only [CollatzResearch.WordTrace]
  refine ⟨117056689883874036922402475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78037793255916024614934983 117056689883874036922402475)
  ·
    refine ⟨175585034825811055383603713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117056689883874036922402475 175585034825811055383603713)
    ·
      refine ⟨131688776119358291537702785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175585034825811055383603713 131688776119358291537702785)
      ·
        refine ⟨98766582089518718653277089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131688776119358291537702785 98766582089518718653277089)
        ·
          refine ⟨74074936567139038989957817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98766582089518718653277089 74074936567139038989957817)
          ·
            refine ⟨55556202425354279242468363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74074936567139038989957817 55556202425354279242468363)
            ·
              refine ⟨83334303638031418863702545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55556202425354279242468363 83334303638031418863702545)
              ·
                refine ⟨62500727728523564147776909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83334303638031418863702545 62500727728523564147776909)
                ·
                  refine ⟨23437772898196336555416341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62500727728523564147776909 23437772898196336555416341)
                  ·
                    refine ⟨1098645604602953276035141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23437772898196336555416341 1098645604602953276035141)
                    ·
                      rfl

theorem cell22_3209407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 6].length) (baseStart_3209407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3209407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3209407 prefixEnd_3209407 := by exact prefixLift 3209407
  have htrace : WordTrace (prefixWord ++ tailWord_3209407) baseStart_3209407 baseEnd_3209407 := by
    simpa [prefixWord, tailWord_3209407, baseEnd_3209407] using wordTrace_append hprefix tailTrace_3209407
  have hstable : (prefixWord ++ tailWord_3209407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209407).length < 2 ^ (prefixWord ++ tailWord_3209407).sum := by decide
  have hdescent : baseEnd_3209407 < baseStart_3209407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209426 : List Nat := [3, 2, 2, 2, 1, 3, 2, 1, 1, 5]
def baseStart_3209426 : Nat := 118140960795 + 3209426 * 2 ^ 59
def prefixEnd_3209426 : Nat := 4983230072969 + 3 ^ 40 * 3209426 * 2
def baseEnd_3209426 : Nat := 1098652108691243559810083

theorem tailTrace_3209426 : CollatzResearch.WordTrace tailWord_3209426 prefixEnd_3209426 1098652108691243559810083 := by
  unfold tailWord_3209426
  simp only [CollatzResearch.WordTrace]
  refine ⟨29264345717701300791836033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78038255247203468778229421 29264345717701300791836033)
  ·
    refine ⟨21948259288275975593877025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29264345717701300791836033 21948259288275975593877025)
    ·
      refine ⟨16461194466206981695407769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21948259288275975593877025 16461194466206981695407769)
      ·
        refine ⟨12345895849655236271555827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16461194466206981695407769 12345895849655236271555827)
        ·
          refine ⟨18518843774482854407333741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12345895849655236271555827 18518843774482854407333741)
          ·
            refine ⟨6944566415431070402750153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18518843774482854407333741 6944566415431070402750153)
            ·
              refine ⟨5208424811573302802062615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6944566415431070402750153 5208424811573302802062615)
              ·
                refine ⟨7812637217359954203093923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5208424811573302802062615 7812637217359954203093923)
                ·
                  refine ⟨11718955826039931304640885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7812637217359954203093923 11718955826039931304640885)
                  ·
                    refine ⟨1098652108691243559810083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11718955826039931304640885 1098652108691243559810083)
                    ·
                      rfl

theorem cell22_3209426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_3209426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3209426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3209426 prefixEnd_3209426 := by exact prefixLift 3209426
  have htrace : WordTrace (prefixWord ++ tailWord_3209426) baseStart_3209426 baseEnd_3209426 := by
    simpa [prefixWord, tailWord_3209426, baseEnd_3209426] using wordTrace_append hprefix tailTrace_3209426
  have hstable : (prefixWord ++ tailWord_3209426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209426).length < 2 ^ (prefixWord ++ tailWord_3209426).sum := by decide
  have hdescent : baseEnd_3209426 < baseStart_3209426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209471 : List Nat := [1, 1, 2, 2, 1, 4, 4, 1, 3, 3]
def baseStart_3209471 : Nat := 118140960795 + 3209471 * 2 ^ 59
def prefixEnd_3209471 : Nat := 4983230072969 + 3 ^ 40 * 3209471 * 2
def baseEnd_3209471 : Nat := 1098667513110878442434945

theorem tailTrace_3209471 : CollatzResearch.WordTrace tailWord_3209471 prefixEnd_3209471 1098667513110878442434945 := by
  unfold tailWord_3209471
  simp only [CollatzResearch.WordTrace]
  refine ⟨117059024155642175852732267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78039349437094783901821511 117059024155642175852732267)
  ·
    refine ⟨175588536233463263779098401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117059024155642175852732267 175588536233463263779098401)
    ·
      refine ⟨131691402175097447834323801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175588536233463263779098401 131691402175097447834323801)
      ·
        refine ⟨98768551631323085875742851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131691402175097447834323801 98768551631323085875742851)
        ·
          refine ⟨148152827446984628813614277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98768551631323085875742851 148152827446984628813614277)
          ·
            refine ⟨27778655146309617902552677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148152827446984628813614277 27778655146309617902552677)
            ·
              refine ⟨5208497839933053356728627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27778655146309617902552677 5208497839933053356728627)
              ·
                refine ⟨7812746759899580035092941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5208497839933053356728627 7812746759899580035092941)
                ·
                  refine ⟨2929780034962342513159853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7812746759899580035092941 2929780034962342513159853)
                  ·
                    refine ⟨1098667513110878442434945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2929780034962342513159853 1098667513110878442434945)
                    ·
                      rfl

theorem cell22_3209471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 3, 3].length) (baseStart_3209471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3209471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3209471 prefixEnd_3209471 := by exact prefixLift 3209471
  have htrace : WordTrace (prefixWord ++ tailWord_3209471) baseStart_3209471 baseEnd_3209471 := by
    simpa [prefixWord, tailWord_3209471, baseEnd_3209471] using wordTrace_append hprefix tailTrace_3209471
  have hstable : (prefixWord ++ tailWord_3209471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209471).length < 2 ^ (prefixWord ++ tailWord_3209471).sum := by decide
  have hdescent : baseEnd_3209471 < baseStart_3209471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209522 : List Nat := [3, 2, 1, 1, 5, 1, 3, 2, 1, 3]
def baseStart_3209522 : Nat := 118140960795 + 3209522 * 2 ^ 59
def prefixEnd_3209522 : Nat := 4983230072969 + 3 ^ 40 * 3209522 * 2
def baseEnd_3209522 : Nat := 1098684971453131309409789

theorem tailTrace_3209522 : CollatzResearch.WordTrace tailWord_3209522 prefixEnd_3209522 1098684971453131309409789 := by
  unfold tailWord_3209522
  simp only [CollatzResearch.WordTrace]
  refine ⟨29265221069614352890709705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78040589518971607708559213 29265221069614352890709705)
  ·
    refine ⟨21948915802210764668032279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29265221069614352890709705 21948915802210764668032279)
    ·
      refine ⟨32923373703316147002048419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21948915802210764668032279 32923373703316147002048419)
      ·
        refine ⟨49385060554974220503072629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32923373703316147002048419 49385060554974220503072629)
        ·
          refine ⟨4629849427028833172163059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49385060554974220503072629 4629849427028833172163059)
          ·
            refine ⟨6944774140543249758244589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4629849427028833172163059 6944774140543249758244589)
            ·
              refine ⟨2604290302703718659341721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6944774140543249758244589 2604290302703718659341721)
              ·
                refine ⟨1953217727027788994506291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2604290302703718659341721 1953217727027788994506291)
                ·
                  refine ⟨2929826590541683491759437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1953217727027788994506291 2929826590541683491759437)
                  ·
                    refine ⟨1098684971453131309409789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2929826590541683491759437 1098684971453131309409789)
                    ·
                      rfl

theorem cell22_3209522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 2, 1, 3].length) (baseStart_3209522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3209522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3209522 prefixEnd_3209522 := by exact prefixLift 3209522
  have htrace : WordTrace (prefixWord ++ tailWord_3209522) baseStart_3209522 baseEnd_3209522 := by
    simpa [prefixWord, tailWord_3209522, baseEnd_3209522] using wordTrace_append hprefix tailTrace_3209522
  have hstable : (prefixWord ++ tailWord_3209522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209522).length < 2 ^ (prefixWord ++ tailWord_3209522).sum := by decide
  have hdescent : baseEnd_3209522 < baseStart_3209522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209640 : List Nat := [2, 1, 6, 1, 1, 1, 1, 3, 3, 3]
def baseStart_3209640 : Nat := 118140960795 + 3209640 * 2 ^ 59
def prefixEnd_3209640 : Nat := 4983230072969 + 3 ^ 40 * 3209640 * 2
def baseEnd_3209640 : Nat := 1098725365264618334959427

theorem tailTrace_3209640 : CollatzResearch.WordTrace tailWord_3209640 prefixEnd_3209640 1098725365264618334959427 := by
  unfold tailWord_3209640
  simp only [CollatzResearch.WordTrace]
  refine ⟨58532594046014958857817187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78043458728019945143756249 58532594046014958857817187)
  ·
    refine ⟨87798891069022438286725781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58532594046014958857817187 87798891069022438286725781)
    ·
      refine ⟨4115573018860426794690271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 87798891069022438286725781 4115573018860426794690271)
      ·
        refine ⟨6173359528290640192035407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4115573018860426794690271 6173359528290640192035407)
        ·
          refine ⟨9260039292435960288053111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6173359528290640192035407 9260039292435960288053111)
          ·
            refine ⟨13890058938653940432079667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9260039292435960288053111 13890058938653940432079667)
            ·
              refine ⟨20835088407980910648119501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13890058938653940432079667 20835088407980910648119501)
              ·
                refine ⟨7813158152992841493044813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20835088407980910648119501 7813158152992841493044813)
                ·
                  refine ⟨2929934307372315559891805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7813158152992841493044813 2929934307372315559891805)
                  ·
                    refine ⟨1098725365264618334959427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2929934307372315559891805 1098725365264618334959427)
                    ·
                      rfl

theorem cell22_3209640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_3209640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3209640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3209640 prefixEnd_3209640 := by exact prefixLift 3209640
  have htrace : WordTrace (prefixWord ++ tailWord_3209640) baseStart_3209640 baseEnd_3209640 := by
    simpa [prefixWord, tailWord_3209640, baseEnd_3209640] using wordTrace_append hprefix tailTrace_3209640
  have hstable : (prefixWord ++ tailWord_3209640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209640).length < 2 ^ (prefixWord ++ tailWord_3209640).sum := by decide
  have hdescent : baseEnd_3209640 < baseStart_3209640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209711 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 6, 4]
def baseStart_3209711 : Nat := 118140960795 + 3209711 * 2 ^ 59
def prefixEnd_3209711 : Nat := 4983230072969 + 3 ^ 40 * 3209711 * 2
def baseEnd_3209711 : Nat := 1098749670015597816434209

theorem tailTrace_3209711 : CollatzResearch.WordTrace tailWord_3209711 prefixEnd_3209711 1098749670015597816434209 := by
  unfold tailWord_3209711
  simp only [CollatzResearch.WordTrace]
  refine ⟨117067777674772696841468987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78045185116515131227645991 117067777674772696841468987)
  ·
    refine ⟨175601666512159045262203481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117067777674772696841468987 175601666512159045262203481)
    ·
      refine ⟨131701249884119283946652611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175601666512159045262203481 131701249884119283946652611)
      ·
        refine ⟨197551874826178925919978917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131701249884119283946652611 197551874826178925919978917)
        ·
          refine ⟨37040976529908548609996047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197551874826178925919978917 37040976529908548609996047)
          ·
            refine ⟨55561464794862822914994071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37040976529908548609996047 55561464794862822914994071)
            ·
              refine ⟨83342197192294234372491107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55561464794862822914994071 83342197192294234372491107)
              ·
                refine ⟨125013295788441351558736661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83342197192294234372491107 125013295788441351558736661)
                ·
                  refine ⟨5859998240083188354315781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 125013295788441351558736661 5859998240083188354315781)
                  ·
                    refine ⟨1098749670015597816434209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5859998240083188354315781 1098749670015597816434209)
                    ·
                      rfl

theorem cell22_3209711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 4].length) (baseStart_3209711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3209711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3209711 prefixEnd_3209711 := by exact prefixLift 3209711
  have htrace : WordTrace (prefixWord ++ tailWord_3209711) baseStart_3209711 baseEnd_3209711 := by
    simpa [prefixWord, tailWord_3209711, baseEnd_3209711] using wordTrace_append hprefix tailTrace_3209711
  have hstable : (prefixWord ++ tailWord_3209711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209711).length < 2 ^ (prefixWord ++ tailWord_3209711).sum := by decide
  have hdescent : baseEnd_3209711 < baseStart_3209711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209760 : List Nat := [2, 1, 1, 6, 2, 2, 1, 7]
def baseStart_3209760 : Nat := 118140960795 + 3209760 * 2 ^ 59
def prefixEnd_3209760 : Nat := 4983230072969 + 3 ^ 40 * 3209760 * 2
def baseEnd_3209760 : Nat := 122085160412997557995451

theorem tailTrace_3209760 : CollatzResearch.WordTrace tailWord_3209760 prefixEnd_3209760 122085160412997557995451 := by
  unfold tailWord_3209760
  simp only [CollatzResearch.WordTrace]
  refine ⟨58534782425797589105001367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78046376567730118806668489 58534782425797589105001367)
  ·
    refine ⟨87802173638696383657502051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58534782425797589105001367 87802173638696383657502051)
    ·
      refine ⟨131703260458044575486253077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87802173638696383657502051 131703260458044575486253077)
      ·
        refine ⟨6173590333970839475918113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 131703260458044575486253077 6173590333970839475918113)
        ·
          refine ⟨4630192750478129606938585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6173590333970839475918113 4630192750478129606938585)
          ·
            refine ⟨3472644562858597205203939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4630192750478129606938585 3472644562858597205203939)
            ·
              refine ⟨5208966844287895807805909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3472644562858597205203939 5208966844287895807805909)
              ·
                refine ⟨122085160412997557995451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5208966844287895807805909 122085160412997557995451)
                ·
                  rfl

theorem cell22_3209760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 7].length) (baseStart_3209760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3209760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3209760 prefixEnd_3209760 := by exact prefixLift 3209760
  have htrace : WordTrace (prefixWord ++ tailWord_3209760) baseStart_3209760 baseEnd_3209760 := by
    simpa [prefixWord, tailWord_3209760, baseEnd_3209760] using wordTrace_append hprefix tailTrace_3209760
  have hstable : (prefixWord ++ tailWord_3209760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209760).length < 2 ^ (prefixWord ++ tailWord_3209760).sum := by decide
  have hdescent : baseEnd_3209760 < baseStart_3209760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209805 : List Nat := [1, 6, 1, 1, 2, 2, 1, 1, 7]
def baseStart_3209805 : Nat := 118140960795 + 3209805 * 2 ^ 59
def prefixEnd_3209805 : Nat := 4983230072969 + 3 ^ 40 * 3209805 * 2
def baseEnd_3209805 : Nat := 366260616045537634861307

theorem tailTrace_3209805 : CollatzResearch.WordTrace tailWord_3209805 prefixEnd_3209805 366260616045537634861307 := by
  unfold tailWord_3209805
  simp only [CollatzResearch.WordTrace]
  refine ⟨117071206136432150895390869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78047470757621433930260579 117071206136432150895390869)
  ·
    refine ⟨5487712787645257073221447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 117071206136432150895390869 5487712787645257073221447)
    ·
      refine ⟨8231569181467885609832171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5487712787645257073221447 8231569181467885609832171)
      ·
        refine ⟨12347353772201828414748257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8231569181467885609832171 12347353772201828414748257)
        ·
          refine ⟨9260515329151371311061193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12347353772201828414748257 9260515329151371311061193)
          ·
            refine ⟨6945386496863528483295895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9260515329151371311061193 6945386496863528483295895)
            ·
              refine ⟨10418079745295292724943843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6945386496863528483295895 10418079745295292724943843)
              ·
                refine ⟨15627119617942939087415765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10418079745295292724943843 15627119617942939087415765)
                ·
                  refine ⟨366260616045537634861307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15627119617942939087415765 366260616045537634861307)
                  ·
                    rfl

theorem cell22_3209805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_3209805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3209805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3209805 prefixEnd_3209805 := by exact prefixLift 3209805
  have htrace : WordTrace (prefixWord ++ tailWord_3209805) baseStart_3209805 baseEnd_3209805 := by
    simpa [prefixWord, tailWord_3209805, baseEnd_3209805] using wordTrace_append hprefix tailTrace_3209805
  have hstable : (prefixWord ++ tailWord_3209805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209805).length < 2 ^ (prefixWord ++ tailWord_3209805).sum := by decide
  have hdescent : baseEnd_3209805 < baseStart_3209805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209865 : List Nat := [1, 2, 1, 1, 4, 1, 1, 6, 2, 3]
def baseStart_3209865 : Nat := 118140960795 + 3209865 * 2 ^ 59
def prefixEnd_3209865 : Nat := 4983230072969 + 3 ^ 40 * 3209865 * 2
def baseEnd_3209865 : Nat := 1098802387362792748083737

theorem tailTrace_3209865 : CollatzResearch.WordTrace tailWord_3209865 prefixEnd_3209865 1098802387362792748083737 := by
  unfold tailWord_3209865
  simp only [CollatzResearch.WordTrace]
  refine ⟨117073394516214781142575049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78048929677476520761716699 117073394516214781142575049)
  ·
    refine ⟨87805045887161085856931287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117073394516214781142575049 87805045887161085856931287)
    ·
      refine ⟨131707568830741628785396931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87805045887161085856931287 131707568830741628785396931)
      ·
        refine ⟨197561353246112443178095397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131707568830741628785396931 197561353246112443178095397)
        ·
          refine ⟨37042753733646083095892887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197561353246112443178095397 37042753733646083095892887)
          ·
            refine ⟨55564130600469124643839331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37042753733646083095892887 55564130600469124643839331)
            ·
              refine ⟨83346195900703686965758997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55564130600469124643839331 83346195900703686965758997)
              ·
                refine ⟨3906852932845485326519953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83346195900703686965758997 3906852932845485326519953)
                ·
                  refine ⟨2930139699634113994889965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3906852932845485326519953 2930139699634113994889965)
                  ·
                    refine ⟨1098802387362792748083737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2930139699634113994889965 1098802387362792748083737)
                    ·
                      rfl

theorem cell22_3209865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 2, 3].length) (baseStart_3209865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3209865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3209865 prefixEnd_3209865 := by exact prefixLift 3209865
  have htrace : WordTrace (prefixWord ++ tailWord_3209865) baseStart_3209865 baseEnd_3209865 := by
    simpa [prefixWord, tailWord_3209865, baseEnd_3209865] using wordTrace_append hprefix tailTrace_3209865
  have hstable : (prefixWord ++ tailWord_3209865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209865).length < 2 ^ (prefixWord ++ tailWord_3209865).sum := by decide
  have hdescent : baseEnd_3209865 < baseStart_3209865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209968 : List Nat := [2, 1, 1, 1, 3, 1, 3, 2, 8]
def baseStart_3209968 : Nat := 118140960795 + 3209968 * 2 ^ 59
def prefixEnd_3209968 : Nat := 4983230072969 + 3 ^ 40 * 3209968 * 2
def baseEnd_3209968 : Nat := 366279215455911604252807

theorem tailTrace_3209968 : CollatzResearch.WordTrace tailWord_3209968 prefixEnd_3209968 366279215455911604252807 := by
  unfold tailWord_3209968
  simp only [CollatzResearch.WordTrace]
  refine ⟨58538575617420814866787279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78051434156561086489049705 58538575617420814866787279)
  ·
    refine ⟨87807863426131222300180919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58538575617420814866787279 87807863426131222300180919)
    ·
      refine ⟨131711795139196833450271379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87807863426131222300180919 131711795139196833450271379)
      ·
        refine ⟨197567692708795250175407069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131711795139196833450271379 197567692708795250175407069)
        ·
          refine ⟨74087884765798218815777651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197567692708795250175407069 74087884765798218815777651)
          ·
            refine ⟨111131827148697328223666477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74087884765798218815777651 111131827148697328223666477)
            ·
              refine ⟨41674435180761498083874929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111131827148697328223666477 41674435180761498083874929)
              ·
                refine ⟨31255826385571123562906197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41674435180761498083874929 31255826385571123562906197)
                ·
                  refine ⟨366279215455911604252807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31255826385571123562906197 366279215455911604252807)
                  ·
                    rfl

theorem cell22_3209968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 8].length) (baseStart_3209968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3209968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3209968 prefixEnd_3209968 := by exact prefixLift 3209968
  have htrace : WordTrace (prefixWord ++ tailWord_3209968) baseStart_3209968 baseEnd_3209968 := by
    simpa [prefixWord, tailWord_3209968, baseEnd_3209968] using wordTrace_append hprefix tailTrace_3209968
  have hstable : (prefixWord ++ tailWord_3209968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209968).length < 2 ^ (prefixWord ++ tailWord_3209968).sum := by decide
  have hdescent : baseEnd_3209968 < baseStart_3209968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210015 : List Nat := [1, 1, 2, 4, 2, 2, 2, 1, 1, 6]
def baseStart_3210015 : Nat := 118140960795 + 3210015 * 2 ^ 59
def prefixEnd_3210015 : Nat := 4983230072969 + 3 ^ 40 * 3210015 * 2
def baseEnd_3210015 : Nat := 1098853735428242356833277

theorem tailTrace_3210015 : CollatzResearch.WordTrace tailWord_3210015 prefixEnd_3210015 1098853735428242356833277 := by
  unfold tailWord_3210015
  simp only [CollatzResearch.WordTrace]
  refine ⟨117078865465671356760535499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78052576977114237840356999 117078865465671356760535499)
  ·
    refine ⟨175618298198507035140803249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117078865465671356760535499 175618298198507035140803249)
    ·
      refine ⟨131713723648880276355602437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175618298198507035140803249 131713723648880276355602437)
      ·
        refine ⟨24696323184165051816675457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131713723648880276355602437 24696323184165051816675457)
        ·
          refine ⟨18522242388123788862506593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24696323184165051816675457 18522242388123788862506593)
          ·
            refine ⟨13891681791092841646879945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18522242388123788862506593 13891681791092841646879945)
            ·
              refine ⟨10418761343319631235159959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13891681791092841646879945 10418761343319631235159959)
              ·
                refine ⟨15628142014979446852739939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10418761343319631235159959 15628142014979446852739939)
                ·
                  refine ⟨23442213022469170279109909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15628142014979446852739939 23442213022469170279109909)
                  ·
                    refine ⟨1098853735428242356833277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23442213022469170279109909 1098853735428242356833277)
                    ·
                      rfl

theorem cell22_3210015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 6].length) (baseStart_3210015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3210015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3210015 prefixEnd_3210015 := by exact prefixLift 3210015
  have htrace : WordTrace (prefixWord ++ tailWord_3210015) baseStart_3210015 baseEnd_3210015 := by
    simpa [prefixWord, tailWord_3210015, baseEnd_3210015] using wordTrace_append hprefix tailTrace_3210015
  have hstable : (prefixWord ++ tailWord_3210015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210015).length < 2 ^ (prefixWord ++ tailWord_3210015).sum := by decide
  have hdescent : baseEnd_3210015 < baseStart_3210015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210036 : List Nat := [2, 5, 1, 1, 4, 1, 1, 1, 6]
def baseStart_3210036 : Nat := 118140960795 + 3210036 * 2 ^ 59
def prefixEnd_3210036 : Nat := 4983230072969 + 3 ^ 40 * 3210036 * 2
def baseEnd_3210036 : Nat := 366286974719135100686071

theorem tailTrace_3210036 : CollatzResearch.WordTrace tailWord_3210036 prefixEnd_3210036 366286974719135100686071 := by
  unfold tailWord_3210036
  simp only [CollatzResearch.WordTrace]
  refine ⟨58539815699297638673524981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78053087599063518231366641 58539815699297638673524981)
  ·
    refine ⟨5488107721809153625642967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58539815699297638673524981 5488107721809153625642967)
    ·
      refine ⟨8232161582713730438464451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5488107721809153625642967 8232161582713730438464451)
      ·
        refine ⟨12348242374070595657696677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8232161582713730438464451 12348242374070595657696677)
        ·
          refine ⟨2315295445138236685818127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12348242374070595657696677 2315295445138236685818127)
          ·
            refine ⟨3472943167707355028727191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2315295445138236685818127 3472943167707355028727191)
            ·
              refine ⟨5209414751561032543090787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3472943167707355028727191 5209414751561032543090787)
              ·
                refine ⟨7814122127341548814636181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5209414751561032543090787 7814122127341548814636181)
                ·
                  refine ⟨366286974719135100686071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7814122127341548814636181 366286974719135100686071)
                  ·
                    rfl

theorem cell22_3210036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_3210036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3210036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3210036 prefixEnd_3210036 := by exact prefixLift 3210036
  have htrace : WordTrace (prefixWord ++ tailWord_3210036) baseStart_3210036 baseEnd_3210036 := by
    simpa [prefixWord, tailWord_3210036, baseEnd_3210036] using wordTrace_append hprefix tailTrace_3210036
  have hstable : (prefixWord ++ tailWord_3210036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210036).length < 2 ^ (prefixWord ++ tailWord_3210036).sum := by decide
  have hdescent : baseEnd_3210036 < baseStart_3210036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210062 : List Nat := [4, 1, 1, 1, 1, 1, 1, 6, 3, 3]
def baseStart_3210062 : Nat := 118140960795 + 3210062 * 2 ^ 59
def prefixEnd_3210062 : Nat := 4983230072969 + 3 ^ 40 * 3210062 * 2
def baseEnd_3210062 : Nat := 1098869824488749900908133

theorem tailTrace_3210062 : CollatzResearch.WordTrace tailWord_3210062 prefixEnd_3210062 1098869824488749900908133 := by
  unfold tailWord_3210062
  simp only [CollatzResearch.WordTrace]
  refine ⟨14635072462062635473437055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78053719797667389191664293 14635072462062635473437055)
  ·
    refine ⟨21952608693093953210155583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14635072462062635473437055 21952608693093953210155583)
    ·
      refine ⟨32928913039640929815233375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21952608693093953210155583 32928913039640929815233375)
      ·
        refine ⟨49393369559461394722850063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32928913039640929815233375 49393369559461394722850063)
        ·
          refine ⟨74090054339192092084275095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49393369559461394722850063 74090054339192092084275095)
          ·
            refine ⟨111135081508788138126412643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74090054339192092084275095 111135081508788138126412643)
            ·
              refine ⟨166702622263182207189618965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111135081508788138126412643 166702622263182207189618965)
              ·
                refine ⟨7814185418586665962013389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 166702622263182207189618965 7814185418586665962013389)
                ·
                  refine ⟨2930319531969999735755021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7814185418586665962013389 2930319531969999735755021)
                  ·
                    refine ⟨1098869824488749900908133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2930319531969999735755021 1098869824488749900908133)
                    ·
                      rfl

theorem cell22_3210062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_3210062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3210062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3210062 prefixEnd_3210062 := by exact prefixLift 3210062
  have htrace : WordTrace (prefixWord ++ tailWord_3210062) baseStart_3210062 baseEnd_3210062 := by
    simpa [prefixWord, tailWord_3210062, baseEnd_3210062] using wordTrace_append hprefix tailTrace_3210062
  have hstable : (prefixWord ++ tailWord_3210062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210062).length < 2 ^ (prefixWord ++ tailWord_3210062).sum := by decide
  have hdescent : baseEnd_3210062 < baseStart_3210062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210079 : List Nat := [1, 1, 2, 3, 1, 3, 2, 5, 1, 3]
def baseStart_3210079 : Nat := 118140960795 + 3210079 * 2 ^ 59
def prefixEnd_3210079 : Nat := 4983230072969 + 3 ^ 40 * 3210079 * 2
def baseEnd_3210079 : Nat := 1098875643936167523233081

theorem tailTrace_3210079 : CollatzResearch.WordTrace tailWord_3210079 prefixEnd_3210079 1098875643936167523233081 := by
  unfold tailWord_3210079
  simp only [CollatzResearch.WordTrace]
  refine ⟨117081199737439495690865291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78054133158292997127243527 117081199737439495690865291)
  ·
    refine ⟨175621799606159243536297937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117081199737439495690865291 175621799606159243536297937)
    ·
      refine ⟨131716349704619432652223453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175621799606159243536297937 131716349704619432652223453)
      ·
        refine ⟨49393631139232287244583795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131716349704619432652223453 49393631139232287244583795)
        ·
          refine ⟨74090446708848430866875693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49393631139232287244583795 74090446708848430866875693)
          ·
            refine ⟨27783917515818161575078385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74090446708848430866875693 27783917515818161575078385)
            ·
              refine ⟨20837938136863621181308789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27783917515818161575078385 20837938136863621181308789)
              ·
                refine ⟨1953556700330964485747699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20837938136863621181308789 1953556700330964485747699)
                ·
                  refine ⟨2930335050496446728621549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1953556700330964485747699 2930335050496446728621549)
                  ·
                    refine ⟨1098875643936167523233081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2930335050496446728621549 1098875643936167523233081)
                    ·
                      rfl

theorem cell22_3210079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 5, 1, 3].length) (baseStart_3210079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3210079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3210079 prefixEnd_3210079 := by exact prefixLift 3210079
  have htrace : WordTrace (prefixWord ++ tailWord_3210079) baseStart_3210079 baseEnd_3210079 := by
    simpa [prefixWord, tailWord_3210079, baseEnd_3210079] using wordTrace_append hprefix tailTrace_3210079
  have hstable : (prefixWord ++ tailWord_3210079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210079).length < 2 ^ (prefixWord ++ tailWord_3210079).sum := by decide
  have hdescent : baseEnd_3210079 < baseStart_3210079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210092 : List Nat := [2, 2, 1, 1, 4, 1, 4, 2, 5]
def baseStart_3210092 : Nat := 118140960795 + 3210092 * 2 ^ 59
def prefixEnd_3210092 : Nat := 4983230072969 + 3 ^ 40 * 3210092 * 2
def baseEnd_3210092 : Nat := 366293364700613274219347

theorem tailTrace_3210092 : CollatzResearch.WordTrace tailWord_3210092 prefixEnd_3210092 366293364700613274219347 := by
  unfold tailWord_3210092
  simp only [CollatzResearch.WordTrace]
  refine ⟨58540836943196199455544265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78054449257594932607392353 58540836943196199455544265)
  ·
    refine ⟨43905627707397149591658199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58540836943196199455544265 43905627707397149591658199)
    ·
      refine ⟨65858441561095724387487299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43905627707397149591658199 65858441561095724387487299)
      ·
        refine ⟨98787662341643586581230949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65858441561095724387487299 98787662341643586581230949)
        ·
          refine ⟨18522686689058172483980803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98787662341643586581230949 18522686689058172483980803)
          ·
            refine ⟨27784030033587258725971205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18522686689058172483980803 27784030033587258725971205)
            ·
              refine ⟨5209505631297611011119601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27784030033587258725971205 5209505631297611011119601)
              ·
                refine ⟨3907129223473208258339701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5209505631297611011119601 3907129223473208258339701)
                ·
                  refine ⟨366293364700613274219347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3907129223473208258339701 366293364700613274219347)
                  ·
                    rfl

theorem cell22_3210092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 5].length) (baseStart_3210092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3210092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3210092 prefixEnd_3210092 := by exact prefixLift 3210092
  have htrace : WordTrace (prefixWord ++ tailWord_3210092) baseStart_3210092 baseEnd_3210092 := by
    simpa [prefixWord, tailWord_3210092, baseEnd_3210092] using wordTrace_append hprefix tailTrace_3210092
  have hstable : (prefixWord ++ tailWord_3210092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210092).length < 2 ^ (prefixWord ++ tailWord_3210092).sum := by decide
  have hdescent : baseEnd_3210092 < baseStart_3210092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210096 : List Nat := [2, 1, 1, 1, 4, 1, 6, 2, 1, 3]
def baseStart_3210096 : Nat := 118140960795 + 3210096 * 2 ^ 59
def prefixEnd_3210096 : Nat := 4983230072969 + 3 ^ 40 * 3210096 * 2
def baseEnd_3210096 : Nat := 1098881463383585145558029

theorem tailTrace_3210096 : CollatzResearch.WordTrace tailWord_3210096 prefixEnd_3210096 1098881463383585145558029 := by
  unfold tailWord_3210096
  simp only [CollatzResearch.WordTrace]
  refine ⟨58540909889188953797117071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78054546518918605062822761 58540909889188953797117071)
  ·
    refine ⟨87811364833783430695675607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58540909889188953797117071 87811364833783430695675607)
    ·
      refine ⟨131717047250675146043513411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87811364833783430695675607 131717047250675146043513411)
      ·
        refine ⟨197575570876012719065270117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131717047250675146043513411 197575570876012719065270117)
        ·
          refine ⟨37045419539252384824738147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197575570876012719065270117 37045419539252384824738147)
          ·
            refine ⟨55568129308878577237107221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37045419539252384824738147 55568129308878577237107221)
            ·
              refine ⟨2604756061353683307989401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55568129308878577237107221 2604756061353683307989401)
              ·
                refine ⟨1953567046015262480992051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2604756061353683307989401 1953567046015262480992051)
                ·
                  refine ⟨2930350569022893721488077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1953567046015262480992051 2930350569022893721488077)
                  ·
                    refine ⟨1098881463383585145558029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2930350569022893721488077 1098881463383585145558029)
                    ·
                      rfl

theorem cell22_3210096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 2, 1, 3].length) (baseStart_3210096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3210096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3210096 prefixEnd_3210096 := by exact prefixLift 3210096
  have htrace : WordTrace (prefixWord ++ tailWord_3210096) baseStart_3210096 baseEnd_3210096 := by
    simpa [prefixWord, tailWord_3210096, baseEnd_3210096] using wordTrace_append hprefix tailTrace_3210096
  have hstable : (prefixWord ++ tailWord_3210096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210096).length < 2 ^ (prefixWord ++ tailWord_3210096).sum := by decide
  have hdescent : baseEnd_3210096 < baseStart_3210096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210169 : List Nat := [1, 2, 1, 4, 2, 4, 1, 1, 1, 5]
def baseStart_3210169 : Nat := 118140960795 + 3210169 * 2 ^ 59
def prefixEnd_3210169 : Nat := 4983230072969 + 3 ^ 40 * 3210169 * 2
def baseEnd_3210169 : Nat := 1098906452775437288482805

theorem tailTrace_3210169 : CollatzResearch.WordTrace tailWord_3210169 prefixEnd_3210169 1098906452775437288482805 := by
  unfold tailWord_3210169
  simp only [CollatzResearch.WordTrace]
  refine ⟨117084482307113441061641561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78056321538075627374427707 117084482307113441061641561)
  ·
    refine ⟨87813361730335080796231171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117084482307113441061641561 87813361730335080796231171)
    ·
      refine ⟨131720042595502621194346757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87813361730335080796231171 131720042595502621194346757)
      ·
        refine ⟨24697507986656741473940017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131720042595502621194346757 24697507986656741473940017)
        ·
          refine ⟨18523130989992556105455013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24697507986656741473940017 18523130989992556105455013)
          ·
            refine ⟨3473087060623604269772815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18523130989992556105455013 3473087060623604269772815)
            ·
              refine ⟨5209630590935406404659223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3473087060623604269772815 5209630590935406404659223)
              ·
                refine ⟨7814445886403109606988835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5209630590935406404659223 7814445886403109606988835)
                ·
                  refine ⟨11721668829604664410483253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7814445886403109606988835 11721668829604664410483253)
                  ·
                    refine ⟨1098906452775437288482805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11721668829604664410483253 1098906452775437288482805)
                    ·
                      rfl

theorem cell22_3210169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 5].length) (baseStart_3210169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3210169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3210169 prefixEnd_3210169 := by exact prefixLift 3210169
  have htrace : WordTrace (prefixWord ++ tailWord_3210169) baseStart_3210169 baseEnd_3210169 := by
    simpa [prefixWord, tailWord_3210169, baseEnd_3210169] using wordTrace_append hprefix tailTrace_3210169
  have hstable : (prefixWord ++ tailWord_3210169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210169).length < 2 ^ (prefixWord ++ tailWord_3210169).sum := by decide
  have hdescent : baseEnd_3210169 < baseStart_3210169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210274 : List Nat := [3, 3, 1, 1, 1, 3, 1, 2, 3, 4]
def baseStart_3210274 : Nat := 118140960795 + 3210274 * 2 ^ 59
def prefixEnd_3210274 : Nat := 4983230072969 + 3 ^ 40 * 3210274 * 2
def baseEnd_3210274 : Nat := 1098942396421252014607483

theorem tailTrace_3210274 : CollatzResearch.WordTrace tailWord_3210274 prefixEnd_3210274 1098942396421252014607483 := by
  unfold tailWord_3210274
  simp only [CollatzResearch.WordTrace]
  refine ⟨29272077992933260998553469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78058874647822029329475917 29272077992933260998553469)
  ·
    refine ⟨10977029247349972874457551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29272077992933260998553469 10977029247349972874457551)
    ·
      refine ⟨16465543871024959311686327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10977029247349972874457551 16465543871024959311686327)
      ·
        refine ⟨24698315806537438967529491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16465543871024959311686327 24698315806537438967529491)
        ·
          refine ⟨37047473709806158451294237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24698315806537438967529491 37047473709806158451294237)
          ·
            refine ⟨13892802641177309419235339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37047473709806158451294237 13892802641177309419235339)
            ·
              refine ⟨20839203961765964128853009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13892802641177309419235339 20839203961765964128853009)
              ·
                refine ⟨15629402971324473096639757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20839203961765964128853009 15629402971324473096639757)
                ·
                  refine ⟨5861026114246677411239909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15629402971324473096639757 5861026114246677411239909)
                  ·
                    refine ⟨1098942396421252014607483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5861026114246677411239909 1098942396421252014607483)
                    ·
                      rfl

theorem cell22_3210274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_3210274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3210274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3210274 prefixEnd_3210274 := by exact prefixLift 3210274
  have htrace : WordTrace (prefixWord ++ tailWord_3210274) baseStart_3210274 baseEnd_3210274 := by
    simpa [prefixWord, tailWord_3210274, baseEnd_3210274] using wordTrace_append hprefix tailTrace_3210274
  have hstable : (prefixWord ++ tailWord_3210274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210274).length < 2 ^ (prefixWord ++ tailWord_3210274).sum := by decide
  have hdescent : baseEnd_3210274 < baseStart_3210274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210304 : List Nat := [2, 1, 1, 2, 2, 3, 2, 2, 4, 3]
def baseStart_3210304 : Nat := 118140960795 + 3210304 * 2 ^ 59
def prefixEnd_3210304 : Nat := 4983230072969 + 3 ^ 40 * 3210304 * 2
def baseEnd_3210304 : Nat := 1098952666034341936357391

theorem tailTrace_3210304 : CollatzResearch.WordTrace tailWord_3210304 prefixEnd_3210304 1098952666034341936357391 := by
  unfold tailWord_3210304
  simp only [CollatzResearch.WordTrace]
  refine ⟨58544703080812179558902983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78059604107749572745203977 58544703080812179558902983)
  ·
    refine ⟨87817054621218269338354475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58544703080812179558902983 87817054621218269338354475)
    ·
      refine ⟨131725581931827404007531713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87817054621218269338354475 131725581931827404007531713)
      ·
        refine ⟨98794186448870553005648785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131725581931827404007531713 98794186448870553005648785)
        ·
          refine ⟨74095639836652914754236589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98794186448870553005648785 74095639836652914754236589)
          ·
            refine ⟨27785864938744843032838721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74095639836652914754236589 27785864938744843032838721)
            ·
              refine ⟨20839398704058632274629041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27785864938744843032838721 20839398704058632274629041)
              ·
                refine ⟨15629549028043974205971781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20839398704058632274629041 15629549028043974205971781)
                ·
                  refine ⟨2930540442758245163619709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15629549028043974205971781 2930540442758245163619709)
                  ·
                    refine ⟨1098952666034341936357391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2930540442758245163619709 1098952666034341936357391)
                    ·
                      rfl

theorem cell22_3210304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 4, 3].length) (baseStart_3210304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3210304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3210304 prefixEnd_3210304 := by exact prefixLift 3210304
  have htrace : WordTrace (prefixWord ++ tailWord_3210304) baseStart_3210304 baseEnd_3210304 := by
    simpa [prefixWord, tailWord_3210304, baseEnd_3210304] using wordTrace_append hprefix tailTrace_3210304
  have hstable : (prefixWord ++ tailWord_3210304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210304).length < 2 ^ (prefixWord ++ tailWord_3210304).sum := by decide
  have hdescent : baseEnd_3210304 < baseStart_3210304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210321 : List Nat := [1, 2, 2, 1, 3, 1, 5, 2, 2, 3]
def baseStart_3210321 : Nat := 118140960795 + 3210321 * 2 ^ 59
def prefixEnd_3210321 : Nat := 4983230072969 + 3 ^ 40 * 3210321 * 2
def baseEnd_3210321 : Nat := 1098958485481759558682339

theorem tailTrace_3210321 : CollatzResearch.WordTrace tailWord_3210321 prefixEnd_3210321 1098958485481759558682339 := by
  unfold tailWord_3210321
  simp only [CollatzResearch.WordTrace]
  refine ⟨117090026202562771021174817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78060017468375180680783211 117090026202562771021174817)
  ·
    refine ⟨87817519651922078265881113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117090026202562771021174817 87817519651922078265881113)
    ·
      refine ⟨65863139738941558699410835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87817519651922078265881113 65863139738941558699410835)
      ·
        refine ⟨98794709608412338049116253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65863139738941558699410835 98794709608412338049116253)
        ·
          refine ⟨37048016103154626768418595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98794709608412338049116253 37048016103154626768418595)
          ·
            refine ⟨55572024154731940152627893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37048016103154626768418595 55572024154731940152627893)
            ·
              refine ⟨5209877264506119389308865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55572024154731940152627893 5209877264506119389308865)
              ·
                refine ⟨3907407948379589541981649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5209877264506119389308865 3907407948379589541981649)
                ·
                  refine ⟨2930555961284692156486237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3907407948379589541981649 2930555961284692156486237)
                  ·
                    refine ⟨1098958485481759558682339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2930555961284692156486237 1098958485481759558682339)
                    ·
                      rfl

theorem cell22_3210321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 2, 3].length) (baseStart_3210321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3210321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3210321 prefixEnd_3210321 := by exact prefixLift 3210321
  have htrace : WordTrace (prefixWord ++ tailWord_3210321) baseStart_3210321 baseEnd_3210321 := by
    simpa [prefixWord, tailWord_3210321, baseEnd_3210321] using wordTrace_append hprefix tailTrace_3210321
  have hstable : (prefixWord ++ tailWord_3210321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210321).length < 2 ^ (prefixWord ++ tailWord_3210321).sum := by decide
  have hdescent : baseEnd_3210321 < baseStart_3210321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210338 : List Nat := [3, 3, 2, 2, 1, 3, 1, 1, 1, 5]
def baseStart_3210338 : Nat := 118140960795 + 3210338 * 2 ^ 59
def prefixEnd_3210338 : Nat := 4983230072969 + 3 ^ 40 * 3210338 * 2
def baseEnd_3210338 : Nat := 1098964304929177181007287

theorem tailTrace_3210338 : CollatzResearch.WordTrace tailWord_3210338 prefixEnd_3210338 1098964304929177181007287 := by
  unfold tailWord_3210338
  simp only [CollatzResearch.WordTrace]
  refine ⟨29272661560875295731135917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78060430829000788616362445 29272661560875295731135917)
  ·
    refine ⟨10977248085328235899175969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29272661560875295731135917 10977248085328235899175969)
    ·
      refine ⟨8232936063996176924381977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10977248085328235899175969 8232936063996176924381977)
      ·
        refine ⟨6174702047997132693286483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8232936063996176924381977 6174702047997132693286483)
        ·
          refine ⟨9262053071995699039929725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6174702047997132693286483 9262053071995699039929725)
          ·
            refine ⟨3473269901998387139973647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9262053071995699039929725 3473269901998387139973647)
            ·
              refine ⟨5209904852997580709960471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3473269901998387139973647 5209904852997580709960471)
              ·
                refine ⟨7814857279496371064940707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5209904852997580709960471 7814857279496371064940707)
                ·
                  refine ⟨11722285919244556597411061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7814857279496371064940707 11722285919244556597411061)
                  ·
                    refine ⟨1098964304929177181007287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11722285919244556597411061 1098964304929177181007287)
                    ·
                      rfl

theorem cell22_3210338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_3210338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3210338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3210338 prefixEnd_3210338 := by exact prefixLift 3210338
  have htrace : WordTrace (prefixWord ++ tailWord_3210338) baseStart_3210338 baseEnd_3210338 := by
    simpa [prefixWord, tailWord_3210338, baseEnd_3210338] using wordTrace_append hprefix tailTrace_3210338
  have hstable : (prefixWord ++ tailWord_3210338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210338).length < 2 ^ (prefixWord ++ tailWord_3210338).sum := by decide
  have hdescent : baseEnd_3210338 < baseStart_3210338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210357 : List Nat := [1, 3, 4, 3, 2, 1, 1, 3, 4]
def baseStart_3210357 : Nat := 118140960795 + 3210357 * 2 ^ 59
def prefixEnd_3210357 : Nat := 4983230072969 + 3 ^ 40 * 3210357 * 2
def baseEnd_3210357 : Nat := 366323603005822488260743

theorem tailTrace_3210357 : CollatzResearch.WordTrace tailWord_3210357 prefixEnd_3210357 366323603005822488260743 := by
  unfold tailWord_3210357
  simp only [CollatzResearch.WordTrace]
  refine ⟨117091339230432349169485325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78060892820288232779656883 117091339230432349169485325)
  ·
    refine ⟨43909252211412130938556997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117091339230432349169485325 43909252211412130938556997)
    ·
      refine ⟨8232984789639774550979437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43909252211412130938556997 8232984789639774550979437)
      ·
        refine ⟨3087369296114915456617289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8232984789639774550979437 3087369296114915456617289)
        ·
          refine ⟨2315526972086186592462967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3087369296114915456617289 2315526972086186592462967)
          ·
            refine ⟨3473290458129279888694451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2315526972086186592462967 3473290458129279888694451)
            ·
              refine ⟨5209935687193919833041677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3473290458129279888694451 5209935687193919833041677)
              ·
                refine ⟨1953725882697719937390629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5209935687193919833041677 1953725882697719937390629)
                ·
                  refine ⟨366323603005822488260743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1953725882697719937390629 366323603005822488260743)
                  ·
                    rfl

theorem cell22_3210357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 3, 4].length) (baseStart_3210357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3210357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3210357 prefixEnd_3210357 := by exact prefixLift 3210357
  have htrace : WordTrace (prefixWord ++ tailWord_3210357) baseStart_3210357 baseEnd_3210357 := by
    simpa [prefixWord, tailWord_3210357, baseEnd_3210357] using wordTrace_append hprefix tailTrace_3210357
  have hstable : (prefixWord ++ tailWord_3210357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210357).length < 2 ^ (prefixWord ++ tailWord_3210357).sum := by decide
  have hdescent : baseEnd_3210357 < baseStart_3210357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210396 : List Nat := [2, 2, 3, 2, 1, 3, 1, 3, 5]
def baseStart_3210396 : Nat := 118140960795 + 3210396 * 2 ^ 59
def prefixEnd_3210396 : Nat := 4983230072969 + 3 ^ 40 * 3210396 * 2
def baseEnd_3210396 : Nat := 366328053171494787685703

theorem tailTrace_3210396 : CollatzResearch.WordTrace tailWord_3210396 prefixEnd_3210396 366328053171494787685703 := by
  unfold tailWord_3210396
  simp only [CollatzResearch.WordTrace]
  refine ⟨58546380838645529415077521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78061841118194039220103361 58546380838645529415077521)
  ·
    refine ⟨43909785628984147061308141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58546380838645529415077521 43909785628984147061308141)
    ·
      refine ⟨16466169610869055147990553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43909785628984147061308141 16466169610869055147990553)
      ·
        refine ⟨12349627208151791360992915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16466169610869055147990553 12349627208151791360992915)
        ·
          refine ⟨18524440812227687041489373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12349627208151791360992915 18524440812227687041489373)
          ·
            refine ⟨6946665304585382640558515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18524440812227687041489373 6946665304585382640558515)
            ·
              refine ⟨10419997956878073960837773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6946665304585382640558515 10419997956878073960837773)
              ·
                refine ⟨3907499233829277735314165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10419997956878073960837773 3907499233829277735314165)
                ·
                  refine ⟨366328053171494787685703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3907499233829277735314165 366328053171494787685703)
                  ·
                    rfl

theorem cell22_3210396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 5].length) (baseStart_3210396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3210396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3210396 prefixEnd_3210396 := by exact prefixLift 3210396
  have htrace : WordTrace (prefixWord ++ tailWord_3210396) baseStart_3210396 baseEnd_3210396 := by
    simpa [prefixWord, tailWord_3210396, baseEnd_3210396] using wordTrace_append hprefix tailTrace_3210396
  have hstable : (prefixWord ++ tailWord_3210396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210396).length < 2 ^ (prefixWord ++ tailWord_3210396).sum := by decide
  have hdescent : baseEnd_3210396 < baseStart_3210396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210434 : List Nat := [3, 5, 1, 1, 2, 1, 1, 4, 1, 3]
def baseStart_3210434 : Nat := 118140960795 + 3210434 * 2 ^ 59
def prefixEnd_3210434 : Nat := 4983230072969 + 3 ^ 40 * 3210434 * 2
def baseEnd_3210434 : Nat := 1098997167691064930606993

theorem tailTrace_3210434 : CollatzResearch.WordTrace tailWord_3210434 prefixEnd_3210434 1098997167691064930606993 := by
  unfold tailWord_3210434
  simp only [CollatzResearch.WordTrace]
  refine ⟨29273536912788347830009589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78062765100768927546692237 29273536912788347830009589)
  ·
    refine ⟨2744394085573907609063399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29273536912788347830009589 2744394085573907609063399)
    ·
      refine ⟨4116591128360861413595099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2744394085573907609063399 4116591128360861413595099)
      ·
        refine ⟨6174886692541292120392649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4116591128360861413595099 6174886692541292120392649)
        ·
          refine ⟨4631165019405969090294487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6174886692541292120392649 4631165019405969090294487)
          ·
            refine ⟨6946747529108953635441731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4631165019405969090294487 6946747529108953635441731)
            ·
              refine ⟨10420121293663430453162597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6946747529108953635441731 10420121293663430453162597)
              ·
                refine ⟨1953772742561893209967987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10420121293663430453162597 1953772742561893209967987)
                ·
                  refine ⟨2930659113842839814951981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1953772742561893209967987 2930659113842839814951981)
                  ·
                    refine ⟨1098997167691064930606993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2930659113842839814951981 1098997167691064930606993)
                    ·
                      rfl

theorem cell22_3210434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_3210434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3210434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3210434 prefixEnd_3210434 := by exact prefixLift 3210434
  have htrace : WordTrace (prefixWord ++ tailWord_3210434) baseStart_3210434 baseEnd_3210434 := by
    simpa [prefixWord, tailWord_3210434, baseEnd_3210434] using wordTrace_append hprefix tailTrace_3210434
  have hstable : (prefixWord ++ tailWord_3210434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210434).length < 2 ^ (prefixWord ++ tailWord_3210434).sum := by decide
  have hdescent : baseEnd_3210434 < baseStart_3210434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210445 : List Nat := [1, 6, 2, 2, 1, 1, 1, 1, 2, 5]
def baseStart_3210445 : Nat := 118140960795 + 3210445 * 2 ^ 59
def prefixEnd_3210445 : Nat := 4983230072969 + 3 ^ 40 * 3210445 * 2
def baseEnd_3210445 : Nat := 1099000933215864568581959

theorem tailTrace_3210445 : CollatzResearch.WordTrace tailWord_3210445 prefixEnd_3210445 1099000933215864568581959 := by
  unfold tailWord_3210445
  simp only [CollatzResearch.WordTrace]
  refine ⟨117094548854113540198688789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78063032569409026799125859 117094548854113540198688789)
  ·
    refine ⟨5488806977536572196813537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 117094548854113540198688789 5488806977536572196813537)
    ·
      refine ⟨4116605233152429147610153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5488806977536572196813537 4116605233152429147610153)
      ·
        refine ⟨3087453924864321860707615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4116605233152429147610153 3087453924864321860707615)
        ·
          refine ⟨4631180887296482791061423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3087453924864321860707615 4631180887296482791061423)
          ·
            refine ⟨6946771330944724186592135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4631180887296482791061423 6946771330944724186592135)
            ·
              refine ⟨10420156996417086279888203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6946771330944724186592135 10420156996417086279888203)
              ·
                refine ⟨15630235494625629419832305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10420156996417086279888203 15630235494625629419832305)
                ·
                  refine ⟨11722676620969222064874229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15630235494625629419832305 11722676620969222064874229)
                  ·
                    refine ⟨1099000933215864568581959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11722676620969222064874229 1099000933215864568581959)
                    ·
                      rfl

theorem cell22_3210445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_3210445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3210445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3210445 prefixEnd_3210445 := by exact prefixLift 3210445
  have htrace : WordTrace (prefixWord ++ tailWord_3210445) baseStart_3210445 baseEnd_3210445 := by
    simpa [prefixWord, tailWord_3210445, baseEnd_3210445] using wordTrace_append hprefix tailTrace_3210445
  have hstable : (prefixWord ++ tailWord_3210445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210445).length < 2 ^ (prefixWord ++ tailWord_3210445).sum := by decide
  have hdescent : baseEnd_3210445 < baseStart_3210445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210548 : List Nat := [2, 5, 1, 1, 1, 1, 2, 4, 5]
def baseStart_3210548 : Nat := 118140960795 + 3210548 * 2 ^ 59
def prefixEnd_3210548 : Nat := 4983230072969 + 3 ^ 40 * 3210548 * 2
def baseEnd_3210548 : Nat := 366345397406935544418881

theorem tailTrace_3210548 : CollatzResearch.WordTrace tailWord_3210548 prefixEnd_3210548 366345397406935544418881 := by
  unfold tailWord_3210548
  simp only [CollatzResearch.WordTrace]
  refine ⟨58549152786370194394844149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78065537048493592526458865 58549152786370194394844149)
  ·
    refine ⟨5488983073722205724516639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58549152786370194394844149 5488983073722205724516639)
    ·
      refine ⟨8233474610583308586774959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5488983073722205724516639 8233474610583308586774959)
      ·
        refine ⟨12350211915874962880162439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8233474610583308586774959 12350211915874962880162439)
        ·
          refine ⟨18525317873812444320243659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12350211915874962880162439 18525317873812444320243659)
          ·
            refine ⟨27787976810718666480365489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18525317873812444320243659 27787976810718666480365489)
            ·
              refine ⟨20840982608038999860274117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27787976810718666480365489 20840982608038999860274117)
              ·
                refine ⟨3907684239007312473801397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20840982608038999860274117 3907684239007312473801397)
                ·
                  refine ⟨366345397406935544418881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3907684239007312473801397 366345397406935544418881)
                  ·
                    rfl

theorem cell22_3210548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_3210548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3210548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3210548 prefixEnd_3210548 := by exact prefixLift 3210548
  have htrace : WordTrace (prefixWord ++ tailWord_3210548) baseStart_3210548 baseEnd_3210548 := by
    simpa [prefixWord, tailWord_3210548, baseEnd_3210548] using wordTrace_append hprefix tailTrace_3210548
  have hstable : (prefixWord ++ tailWord_3210548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210548).length < 2 ^ (prefixWord ++ tailWord_3210548).sum := by decide
  have hdescent : baseEnd_3210548 < baseStart_3210548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210595 : List Nat := [1, 1, 1, 5, 2, 3, 3, 1, 1, 4]
def baseStart_3210595 : Nat := 118140960795 + 3210595 * 2 ^ 59
def prefixEnd_3210595 : Nat := 4983230072969 + 3 ^ 40 * 3210595 * 2
def baseEnd_3210595 : Nat := 1099052281281314177331499

theorem tailTrace_3210595 : CollatzResearch.WordTrace tailWord_3210595 prefixEnd_3210595 1099052281281314177331499 := by
  unfold tailWord_3210595
  simp only [CollatzResearch.WordTrace]
  refine ⟨117100019803570115816649239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78066679869046743877766159 117100019803570115816649239)
  ·
    refine ⟨175650029705355173724973859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117100019803570115816649239 175650029705355173724973859)
    ·
      refine ⟨263475044558032760587460789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175650029705355173724973859 263475044558032760587460789)
      ·
        refine ⟨24700785427315571305074449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 263475044558032760587460789 24700785427315571305074449)
        ·
          refine ⟨18525589070486678478805837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24700785427315571305074449 18525589070486678478805837)
          ·
            refine ⟨6947095901432504429552189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18525589070486678478805837 6947095901432504429552189)
            ·
              refine ⟨2605160963037189161082071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6947095901432504429552189 2605160963037189161082071)
              ·
                refine ⟨3907741444555783741623107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2605160963037189161082071 3907741444555783741623107)
                ·
                  refine ⟨5861612166833675612434661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3907741444555783741623107 5861612166833675612434661)
                  ·
                    refine ⟨1099052281281314177331499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5861612166833675612434661 1099052281281314177331499)
                    ·
                      rfl

theorem cell22_3210595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 1, 4].length) (baseStart_3210595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3210595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3210595 prefixEnd_3210595 := by exact prefixLift 3210595
  have htrace : WordTrace (prefixWord ++ tailWord_3210595) baseStart_3210595 baseEnd_3210595 := by
    simpa [prefixWord, tailWord_3210595, baseEnd_3210595] using wordTrace_append hprefix tailTrace_3210595
  have hstable : (prefixWord ++ tailWord_3210595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210595).length < 2 ^ (prefixWord ++ tailWord_3210595).sum := by decide
  have hdescent : baseEnd_3210595 < baseStart_3210595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210625 : List Nat := [1, 2, 4, 3, 2, 1, 2, 1, 1, 5]
def baseStart_3210625 : Nat := 118140960795 + 3210625 * 2 ^ 59
def prefixEnd_3210625 : Nat := 4983230072969 + 3 ^ 40 * 3210625 * 2
def baseEnd_3210625 : Nat := 1099062550894404099081407

theorem tailTrace_3210625 : CollatzResearch.WordTrace tailWord_3210625 prefixEnd_3210625 1099062550894404099081407 := by
  unfold tailWord_3210625
  simp only [CollatzResearch.WordTrace]
  refine ⟨117101113993461430940241329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78067409328974287293494219 117101113993461430940241329)
  ·
    refine ⟨87825835495096073205180997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117101113993461430940241329 87825835495096073205180997)
    ·
      refine ⟨16467344155330513725971437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87825835495096073205180997 16467344155330513725971437)
      ·
        refine ⟨6175254058248942647239289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16467344155330513725971437 6175254058248942647239289)
        ·
          refine ⟨4631440543686706985429467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6175254058248942647239289 4631440543686706985429467)
          ·
            refine ⟨6947160815530060478144201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4631440543686706985429467 6947160815530060478144201)
            ·
              refine ⟨5210370611647545358608151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6947160815530060478144201 5210370611647545358608151)
              ·
                refine ⟨7815555917471318037912227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5210370611647545358608151 7815555917471318037912227)
                ·
                  refine ⟨11723333876206977056868341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7815555917471318037912227 11723333876206977056868341)
                  ·
                    refine ⟨1099062550894404099081407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11723333876206977056868341 1099062550894404099081407)
                    ·
                      rfl

theorem cell22_3210625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_3210625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3210625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3210625 prefixEnd_3210625 := by exact prefixLift 3210625
  have htrace : WordTrace (prefixWord ++ tailWord_3210625) baseStart_3210625 baseEnd_3210625 := by
    simpa [prefixWord, tailWord_3210625, baseEnd_3210625] using wordTrace_append hprefix tailTrace_3210625
  have hstable : (prefixWord ++ tailWord_3210625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210625).length < 2 ^ (prefixWord ++ tailWord_3210625).sum := by decide
  have hdescent : baseEnd_3210625 < baseStart_3210625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210711 : List Nat := [1, 1, 3, 2, 1, 1, 1, 4, 8]
def baseStart_3210711 : Nat := 118140960795 + 3210711 * 2 ^ 59
def prefixEnd_3210711 : Nat := 4983230072969 + 3 ^ 40 * 3210711 * 2
def baseEnd_3210711 : Nat := 366363996817309513810381

theorem tailTrace_3210711 : CollatzResearch.WordTrace tailWord_3210711 prefixEnd_3210711 366363996817309513810381 := by
  unfold tailWord_3210711
  simp only [CollatzResearch.WordTrace]
  refine ⟨117104250671149867627871987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78069500447433245085247991 117104250671149867627871987)
  ·
    refine ⟨175656376006724801441807981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117104250671149867627871987 175656376006724801441807981)
    ·
      refine ⟨65871141002521800540677993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175656376006724801441807981 65871141002521800540677993)
      ·
        refine ⟨49403355751891350405508495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65871141002521800540677993 49403355751891350405508495)
        ·
          refine ⟨74105033627837025608262743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49403355751891350405508495 74105033627837025608262743)
          ·
            refine ⟨111157550441755538412394115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74105033627837025608262743 111157550441755538412394115)
            ·
              refine ⟨166736325662633307618591173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111157550441755538412394115 166736325662633307618591173)
              ·
                refine ⟨31263061061743745178485845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 166736325662633307618591173 31263061061743745178485845)
                ·
                  refine ⟨366363996817309513810381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31263061061743745178485845 366363996817309513810381)
                  ·
                    rfl

theorem cell22_3210711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 8].length) (baseStart_3210711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3210711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3210711 prefixEnd_3210711 := by exact prefixLift 3210711
  have htrace : WordTrace (prefixWord ++ tailWord_3210711) baseStart_3210711 baseEnd_3210711 := by
    simpa [prefixWord, tailWord_3210711, baseEnd_3210711] using wordTrace_append hprefix tailTrace_3210711
  have hstable : (prefixWord ++ tailWord_3210711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210711).length < 2 ^ (prefixWord ++ tailWord_3210711).sum := by decide
  have hdescent : baseEnd_3210711 < baseStart_3210711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210743 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 6, 3]
def baseStart_3210743 : Nat := 118140960795 + 3210743 * 2 ^ 59
def prefixEnd_3210743 : Nat := 4983230072969 + 3 ^ 40 * 3210743 * 2
def baseEnd_3210743 : Nat := 1099102944705891124631045

theorem tailTrace_3210743 : CollatzResearch.WordTrace tailWord_3210743 prefixEnd_3210743 1099102944705891124631045 := by
  unfold tailWord_3210743
  simp only [CollatzResearch.WordTrace]
  refine ⟨117105417807033937093036883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78070278538022624728691255 117105417807033937093036883)
  ·
    refine ⟨175658126710550905639555325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117105417807033937093036883 175658126710550905639555325)
    ·
      refine ⟨65871797516456589614833247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175658126710550905639555325 65871797516456589614833247)
      ·
        refine ⟨98807696274684884422249871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65871797516456589614833247 98807696274684884422249871)
        ·
          refine ⟨148211544412027326633374807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98807696274684884422249871 148211544412027326633374807)
          ·
            refine ⟨222317316618040989950062211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148211544412027326633374807 222317316618040989950062211)
            ·
              refine ⟨333475974927061484925093317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222317316618040989950062211 333475974927061484925093317)
              ·
                refine ⟨62526745298824028423454997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 333475974927061484925093317 62526745298824028423454997)
                ·
                  refine ⟨2930941185882376332349453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62526745298824028423454997 2930941185882376332349453)
                  ·
                    refine ⟨1099102944705891124631045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2930941185882376332349453 1099102944705891124631045)
                    ·
                      rfl

theorem cell22_3210743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 6, 3].length) (baseStart_3210743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3210743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3210743 prefixEnd_3210743 := by exact prefixLift 3210743
  have htrace : WordTrace (prefixWord ++ tailWord_3210743) baseStart_3210743 baseEnd_3210743 := by
    simpa [prefixWord, tailWord_3210743, baseEnd_3210743] using wordTrace_append hprefix tailTrace_3210743
  have hstable : (prefixWord ++ tailWord_3210743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210743).length < 2 ^ (prefixWord ++ tailWord_3210743).sum := by decide
  have hdescent : baseEnd_3210743 < baseStart_3210743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210805 : List Nat := [1, 3, 3, 1, 1, 3, 1, 1, 5, 3]
def baseStart_3210805 : Nat := 118140960795 + 3210805 * 2 ^ 59
def prefixEnd_3210805 : Nat := 4983230072969 + 3 ^ 40 * 3210805 * 2
def baseEnd_3210805 : Nat := 1099124168572943629580855

theorem tailTrace_3210805 : CollatzResearch.WordTrace tailWord_3210805 prefixEnd_3210805 1099124168572943629580855 := by
  unfold tailWord_3210805
  simp only [CollatzResearch.WordTrace]
  refine ⟨117107679132809321681793869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78071786088539547787862579 117107679132809321681793869)
  ·
    refine ⟨43915379674803495630672701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117107679132809321681793869 43915379674803495630672701)
    ·
      refine ⟨16468267378051310861502263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43915379674803495630672701 16468267378051310861502263)
      ·
        refine ⟨24702401067076966292253395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16468267378051310861502263 24702401067076966292253395)
        ·
          refine ⟨37053601600615449438380093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24702401067076966292253395 37053601600615449438380093)
          ·
            refine ⟨13895100600230793539392535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37053601600615449438380093 13895100600230793539392535)
            ·
              refine ⟨20842650900346190309088803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13895100600230793539392535 20842650900346190309088803)
              ·
                refine ⟨31263976350519285463633205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20842650900346190309088803 31263976350519285463633205)
                ·
                  refine ⟨2930997782861183012215613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31263976350519285463633205 2930997782861183012215613)
                  ·
                    refine ⟨1099124168572943629580855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2930997782861183012215613 1099124168572943629580855)
                    ·
                      rfl

theorem cell22_3210805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_3210805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3210805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3210805 prefixEnd_3210805 := by exact prefixLift 3210805
  have htrace : WordTrace (prefixWord ++ tailWord_3210805) baseStart_3210805 baseEnd_3210805 := by
    simpa [prefixWord, tailWord_3210805, baseEnd_3210805] using wordTrace_append hprefix tailTrace_3210805
  have hstable : (prefixWord ++ tailWord_3210805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210805).length < 2 ^ (prefixWord ++ tailWord_3210805).sum := by decide
  have hdescent : baseEnd_3210805 < baseStart_3210805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210833 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 4, 5]
def baseStart_3210833 : Nat := 118140960795 + 3210833 * 2 ^ 59
def prefixEnd_3210833 : Nat := 4983230072969 + 3 ^ 40 * 3210833 * 2
def baseEnd_3210833 : Nat := 1099133753545160889880769

theorem tailTrace_3210833 : CollatzResearch.WordTrace tailWord_3210833 prefixEnd_3210833 1099133753545160889880769 := by
  unfold tailWord_3210833
  simp only [CollatzResearch.WordTrace]
  refine ⟨117108700376707882463813153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78072466917805254975875435 117108700376707882463813153)
  ·
    refine ⟨87831525282530911847859865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117108700376707882463813153 87831525282530911847859865)
    ·
      refine ⟨65873643961898183885894899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87831525282530911847859865 65873643961898183885894899)
      ·
        refine ⟨98810465942847275828842349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65873643961898183885894899 98810465942847275828842349)
        ·
          refine ⟨37053924728567728435815881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98810465942847275828842349 37053924728567728435815881)
          ·
            refine ⟨27790443546425796326861911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37053924728567728435815881 27790443546425796326861911)
            ·
              refine ⟨41685665319638694490292867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27790443546425796326861911 41685665319638694490292867)
              ·
                refine ⟨62528497979458041735439301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41685665319638694490292867 62528497979458041735439301)
                ·
                  refine ⟨11724093371148382825394869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62528497979458041735439301 11724093371148382825394869)
                  ·
                    refine ⟨1099133753545160889880769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11724093371148382825394869 1099133753545160889880769)
                    ·
                      rfl

theorem cell22_3210833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_3210833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3210833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3210833 prefixEnd_3210833 := by exact prefixLift 3210833
  have htrace : WordTrace (prefixWord ++ tailWord_3210833) baseStart_3210833 baseEnd_3210833 := by
    simpa [prefixWord, tailWord_3210833, baseEnd_3210833] using wordTrace_append hprefix tailTrace_3210833
  have hstable : (prefixWord ++ tailWord_3210833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210833).length < 2 ^ (prefixWord ++ tailWord_3210833).sum := by decide
  have hdescent : baseEnd_3210833 < baseStart_3210833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210852 : List Nat := [2, 3, 1, 1, 2, 4, 3, 1, 5]
def baseStart_3210852 : Nat := 118140960795 + 3210852 * 2 ^ 59
def prefixEnd_3210852 : Nat := 4983230072969 + 3 ^ 40 * 3210852 * 2
def baseEnd_3210852 : Nat := 366380085877817057885237

theorem tailTrace_3210852 : CollatzResearch.WordTrace tailWord_3210852 prefixEnd_3210852 366380085877817057885237 := by
  unfold tailWord_3210852
  simp only [CollatzResearch.WordTrace]
  refine ⟨58554696681819524354377405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78072928909092699139169873 58554696681819524354377405)
  ·
    refine ⟨21958011255682321632891527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58554696681819524354377405 21958011255682321632891527)
    ·
      refine ⟨32937016883523482449337291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21958011255682321632891527 32937016883523482449337291)
      ·
        refine ⟨49405525325285223674005937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32937016883523482449337291 49405525325285223674005937)
        ·
          refine ⟨37054143993963917755504453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49405525325285223674005937 37054143993963917755504453)
          ·
            refine ⟨6947651998868234579157085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37054143993963917755504453 6947651998868234579157085)
            ·
              refine ⟨2605369499575587967183907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6947651998868234579157085 2605369499575587967183907)
              ·
                refine ⟨3908054249363381950775861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2605369499575587967183907 3908054249363381950775861)
                ·
                  refine ⟨366380085877817057885237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3908054249363381950775861 366380085877817057885237)
                  ·
                    rfl

theorem cell22_3210852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_3210852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3210852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3210852 prefixEnd_3210852 := by exact prefixLift 3210852
  have htrace : WordTrace (prefixWord ++ tailWord_3210852) baseStart_3210852 baseEnd_3210852 := by
    simpa [prefixWord, tailWord_3210852, baseEnd_3210852] using wordTrace_append hprefix tailTrace_3210852
  have hstable : (prefixWord ++ tailWord_3210852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210852).length < 2 ^ (prefixWord ++ tailWord_3210852).sum := by decide
  have hdescent : baseEnd_3210852 < baseStart_3210852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210925 : List Nat := [1, 5, 2, 1, 1, 1, 1, 10]
def baseStart_3210925 : Nat := 118140960795 + 3210925 * 2 ^ 59
def prefixEnd_3210925 : Nat := 4983230072969 + 3 ^ 40 * 3210925 * 2
def baseEnd_3210925 : Nat := 122129471891700368508943

theorem tailTrace_3210925 : CollatzResearch.WordTrace tailWord_3210925 prefixEnd_3210925 122129471891700368508943 := by
  unfold tailWord_3210925
  simp only [CollatzResearch.WordTrace]
  refine ⟨117112055892374582176162229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78074703928249721450774819 117112055892374582176162229)
  ·
    refine ⟨10979255239910117079015209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117112055892374582176162229 10979255239910117079015209)
    ·
      refine ⟨8234441429932587809261407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10979255239910117079015209 8234441429932587809261407)
      ·
        refine ⟨12351662144898881713892111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8234441429932587809261407 12351662144898881713892111)
        ·
          refine ⟨18527493217348322570838167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12351662144898881713892111 18527493217348322570838167)
          ·
            refine ⟨27791239826022483856257251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18527493217348322570838167 27791239826022483856257251)
            ·
              refine ⟨41686859739033725784385877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27791239826022483856257251 41686859739033725784385877)
              ·
                refine ⟨122129471891700368508943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 41686859739033725784385877 122129471891700368508943)
                ·
                  rfl

theorem cell22_3210925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 10].length) (baseStart_3210925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3210925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3210925 prefixEnd_3210925 := by exact prefixLift 3210925
  have htrace : WordTrace (prefixWord ++ tailWord_3210925) baseStart_3210925 baseEnd_3210925 := by
    simpa [prefixWord, tailWord_3210925, baseEnd_3210925] using wordTrace_append hprefix tailTrace_3210925
  have hstable : (prefixWord ++ tailWord_3210925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210925).length < 2 ^ (prefixWord ++ tailWord_3210925).sum := by decide
  have hdescent : baseEnd_3210925 < baseStart_3210925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211000 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 5, 4]
def baseStart_3211000 : Nat := 118140960795 + 3211000 * 2 ^ 59
def prefixEnd_3211000 : Nat := 4983230072969 + 3 ^ 40 * 3211000 * 2
def baseEnd_3211000 : Nat := 1099190921058028120955257

theorem tailTrace_3211000 : CollatzResearch.WordTrace tailWord_3211000 prefixEnd_3211000 1099190921058028120955257 := by
  unfold tailWord_3211000
  simp only [CollatzResearch.WordTrace]
  refine ⟨58557395683551434992571227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78076527578068579990094969 58557395683551434992571227)
  ·
    refine ⟨87836093525327152488856841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58557395683551434992571227 87836093525327152488856841)
    ·
      refine ⟨65877070143995364366642631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87836093525327152488856841 65877070143995364366642631)
      ·
        refine ⟨98815605215993046549963947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65877070143995364366642631 98815605215993046549963947)
        ·
          refine ⟨148223407823989569824945921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98815605215993046549963947 148223407823989569824945921)
          ·
            refine ⟨111167555867992177368709441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148223407823989569824945921 111167555867992177368709441)
            ·
              refine ⟨83375666900994133026532081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111167555867992177368709441 83375666900994133026532081)
              ·
                refine ⟨62531750175745599769899061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83375666900994133026532081 62531750175745599769899061)
                ·
                  refine ⟨5862351578976149978428037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62531750175745599769899061 5862351578976149978428037)
                  ·
                    refine ⟨1099190921058028120955257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5862351578976149978428037 1099190921058028120955257)
                    ·
                      rfl

theorem cell22_3211000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_3211000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3211000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3211000 prefixEnd_3211000 := by exact prefixLift 3211000
  have htrace : WordTrace (prefixWord ++ tailWord_3211000) baseStart_3211000 baseEnd_3211000 := by
    simpa [prefixWord, tailWord_3211000, baseEnd_3211000] using wordTrace_append hprefix tailTrace_3211000
  have hstable : (prefixWord ++ tailWord_3211000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211000).length < 2 ^ (prefixWord ++ tailWord_3211000).sum := by decide
  have hdescent : baseEnd_3211000 < baseStart_3211000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211014 : List Nat := [6, 2, 2, 1, 1, 1, 3, 1, 2, 3]
def baseStart_3211014 : Nat := 118140960795 + 3211014 * 2 ^ 59
def prefixEnd_3211014 : Nat := 4983230072969 + 3 ^ 40 * 3211014 * 2
def baseEnd_3211014 : Nat := 1099195713544136751105215

theorem tailTrace_3211014 : CollatzResearch.WordTrace tailWord_3211014 prefixEnd_3211014 1099195713544136751105215 := by
  unfold tailWord_3211014
  simp only [CollatzResearch.WordTrace]
  refine ⟨3659853187157879699254753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 78076867992701433584101397 3659853187157879699254753)
  ·
    refine ⟨2744889890368409774441065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3659853187157879699254753 2744889890368409774441065)
    ·
      refine ⟨2058667417776307330830799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2744889890368409774441065 2058667417776307330830799)
      ·
        refine ⟨3088001126664460996246199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2058667417776307330830799 3088001126664460996246199)
        ·
          refine ⟨4632001689996691494369299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3088001126664460996246199 4632001689996691494369299)
          ·
            refine ⟨6948002534995037241553949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4632001689996691494369299 6948002534995037241553949)
            ·
              refine ⟨2605500950623138965582731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6948002534995037241553949 2605500950623138965582731)
              ·
                refine ⟨3908251425934708448374097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2605500950623138965582731 3908251425934708448374097)
                ·
                  refine ⟨2931188569451031336280573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3908251425934708448374097 2931188569451031336280573)
                  ·
                    refine ⟨1099195713544136751105215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2931188569451031336280573 1099195713544136751105215)
                    ·
                      rfl

theorem cell22_3211014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_3211014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3211014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3211014 prefixEnd_3211014 := by exact prefixLift 3211014
  have htrace : WordTrace (prefixWord ++ tailWord_3211014) baseStart_3211014 baseEnd_3211014 := by
    simpa [prefixWord, tailWord_3211014, baseEnd_3211014] using wordTrace_append hprefix tailTrace_3211014
  have hstable : (prefixWord ++ tailWord_3211014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211014).length < 2 ^ (prefixWord ++ tailWord_3211014).sum := by decide
  have hdescent : baseEnd_3211014 < baseStart_3211014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211034 : List Nat := [3, 1, 1, 3, 2, 3, 2, 2, 1, 4]
def baseStart_3211034 : Nat := 118140960795 + 3211034 * 2 ^ 59
def prefixEnd_3211034 : Nat := 4983230072969 + 3 ^ 40 * 3211034 * 2
def baseEnd_3211034 : Nat := 1099202559952863365605153

theorem tailTrace_3211034 : CollatzResearch.WordTrace tailWord_3211034 prefixEnd_3211034 1099202559952863365605153 := by
  unfold tailWord_3211034
  simp only [CollatzResearch.WordTrace]
  refine ⟨29279007862244923447970039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78077354299319795861253437 29279007862244923447970039)
  ·
    refine ⟨43918511793367385171955059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29279007862244923447970039 43918511793367385171955059)
    ·
      refine ⟨65877767690051077757932589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43918511793367385171955059 65877767690051077757932589)
      ·
        refine ⟨24704162883769154159224721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65877767690051077757932589 24704162883769154159224721)
        ·
          refine ⟨18528122162826865619418541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24704162883769154159224721 18528122162826865619418541)
          ·
            refine ⟨6948045811060074607281953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18528122162826865619418541 6948045811060074607281953)
            ·
              refine ⟨5211034358295055955461465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6948045811060074607281953 5211034358295055955461465)
              ·
                refine ⟨3908275768721291966596099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5211034358295055955461465 3908275768721291966596099)
                ·
                  refine ⟨5862413653081937949894149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3908275768721291966596099 5862413653081937949894149)
                  ·
                    refine ⟨1099202559952863365605153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5862413653081937949894149 1099202559952863365605153)
                    ·
                      rfl

theorem cell22_3211034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 1, 4].length) (baseStart_3211034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3211034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3211034 prefixEnd_3211034 := by exact prefixLift 3211034
  have htrace : WordTrace (prefixWord ++ tailWord_3211034) baseStart_3211034 baseEnd_3211034 := by
    simpa [prefixWord, tailWord_3211034, baseEnd_3211034] using wordTrace_append hprefix tailTrace_3211034
  have hstable : (prefixWord ++ tailWord_3211034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211034).length < 2 ^ (prefixWord ++ tailWord_3211034).sum := by decide
  have hdescent : baseEnd_3211034 < baseStart_3211034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211066 : List Nat := [3, 1, 1, 1, 5, 2, 3, 2, 4]
def baseStart_3211066 : Nat := 118140960795 + 3211066 * 2 ^ 59
def prefixEnd_3211066 : Nat := 4983230072969 + 3 ^ 40 * 3211066 * 2
def baseEnd_3211066 : Nat := 366404504735608649601685

theorem tailTrace_3211066 : CollatzResearch.WordTrace tailWord_3211066 prefixEnd_3211066 366404504735608649601685 := by
  unfold tailWord_3211066
  simp only [CollatzResearch.WordTrace]
  refine ⟨29279299646215940814261263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78078132389909175504696701 29279299646215940814261263)
  ·
    refine ⟨43918949469323911221391895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29279299646215940814261263 43918949469323911221391895)
    ·
      refine ⟨65878424203985866832087843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43918949469323911221391895 65878424203985866832087843)
      ·
        refine ⟨98817636305978800248131765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65878424203985866832087843 98817636305978800248131765)
        ·
          refine ⟨9264153403685512523262353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98817636305978800248131765 9264153403685512523262353)
          ·
            refine ⟨6948115052764134392446765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9264153403685512523262353 6948115052764134392446765)
            ·
              refine ⟨2605543144786550397167537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6948115052764134392446765 2605543144786550397167537)
              ·
                refine ⟨1954157358589912797875653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2605543144786550397167537 1954157358589912797875653)
                ·
                  refine ⟨366404504735608649601685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1954157358589912797875653 366404504735608649601685)
                  ·
                    rfl

theorem cell22_3211066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 2, 4].length) (baseStart_3211066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3211066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3211066 prefixEnd_3211066 := by exact prefixLift 3211066
  have htrace : WordTrace (prefixWord ++ tailWord_3211066) baseStart_3211066 baseEnd_3211066 := by
    simpa [prefixWord, tailWord_3211066, baseEnd_3211066] using wordTrace_append hprefix tailTrace_3211066
  have hstable : (prefixWord ++ tailWord_3211066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211066).length < 2 ^ (prefixWord ++ tailWord_3211066).sum := by decide
  have hdescent : baseEnd_3211066 < baseStart_3211066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211160 : List Nat := [2, 1, 2, 6, 1, 1, 2, 3, 1, 3]
def baseStart_3211160 : Nat := 118140960795 + 3211160 * 2 ^ 59
def prefixEnd_3211160 : Nat := 4983230072969 + 3 ^ 40 * 3211160 * 2
def baseEnd_3211160 : Nat := 1099245692327841036954767

theorem tailTrace_3211160 : CollatzResearch.WordTrace tailWord_3211160 prefixEnd_3211160 1099245692327841036954767 := by
  unfold tailWord_3211160
  simp only [CollatzResearch.WordTrace]
  refine ⟨58560313523261608655483467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78080418031015478207311289 58560313523261608655483467)
  ·
    refine ⟨87840470284892412983225201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58560313523261608655483467 87840470284892412983225201)
    ·
      refine ⟨65880352713669309737418901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87840470284892412983225201 65880352713669309737418901)
      ·
        refine ⟨3088141533453248893941511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 65880352713669309737418901 3088141533453248893941511)
        ·
          refine ⟨4632212300179873340912267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3088141533453248893941511 4632212300179873340912267)
          ·
            refine ⟨6948318450269810011368401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4632212300179873340912267 6948318450269810011368401)
            ·
              refine ⟨5211238837702357508526301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6948318450269810011368401 5211238837702357508526301)
              ·
                refine ⟨1954214564138384065697363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5211238837702357508526301 1954214564138384065697363)
                ·
                  refine ⟨2931321846207576098546045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1954214564138384065697363 2931321846207576098546045)
                  ·
                    refine ⟨1099245692327841036954767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2931321846207576098546045 1099245692327841036954767)
                    ·
                      rfl

theorem cell22_3211160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 3, 1, 3].length) (baseStart_3211160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3211160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3211160 prefixEnd_3211160 := by exact prefixLift 3211160
  have htrace : WordTrace (prefixWord ++ tailWord_3211160) baseStart_3211160 baseEnd_3211160 := by
    simpa [prefixWord, tailWord_3211160, baseEnd_3211160] using wordTrace_append hprefix tailTrace_3211160
  have hstable : (prefixWord ++ tailWord_3211160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211160).length < 2 ^ (prefixWord ++ tailWord_3211160).sum := by decide
  have hdescent : baseEnd_3211160 < baseStart_3211160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211214 : List Nat := [4, 1, 1, 1, 2, 2, 2, 3, 2, 4]
def baseStart_3211214 : Nat := 118140960795 + 3211214 * 2 ^ 59
def prefixEnd_3211214 : Nat := 4983230072969 + 3 ^ 40 * 3211214 * 2
def baseEnd_3211214 : Nat := 1099264177631402896104601

theorem tailTrace_3211214 : CollatzResearch.WordTrace tailWord_3211214 prefixEnd_3211214 1099264177631402896104601 := by
  unfold tailWord_3211214
  simp only [CollatzResearch.WordTrace]
  refine ⟨14640324573540948066679087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78081731058885056355621797 14640324573540948066679087)
  ·
    refine ⟨21960486860311422100018631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14640324573540948066679087 21960486860311422100018631)
    ·
      refine ⟨32940730290467133150027947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21960486860311422100018631 32940730290467133150027947)
      ·
        refine ⟨49411095435700699725041921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32940730290467133150027947 49411095435700699725041921)
        ·
          refine ⟨37058321576775524793781441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49411095435700699725041921 37058321576775524793781441)
          ·
            refine ⟨27793741182581643595336081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37058321576775524793781441 27793741182581643595336081)
            ·
              refine ⟨20845305886936232696502061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27793741182581643595336081 20845305886936232696502061)
              ·
                refine ⟨7816989707601087261188273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20845305886936232696502061 7816989707601087261188273)
                ·
                  refine ⟨5862742280700815445891205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7816989707601087261188273 5862742280700815445891205)
                  ·
                    refine ⟨1099264177631402896104601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5862742280700815445891205 1099264177631402896104601)
                    ·
                      rfl

theorem cell22_3211214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_3211214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3211214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3211214 prefixEnd_3211214 := by exact prefixLift 3211214
  have htrace : WordTrace (prefixWord ++ tailWord_3211214) baseStart_3211214 baseEnd_3211214 := by
    simpa [prefixWord, tailWord_3211214, baseEnd_3211214] using wordTrace_append hprefix tailTrace_3211214
  have hstable : (prefixWord ++ tailWord_3211214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211214).length < 2 ^ (prefixWord ++ tailWord_3211214).sum := by decide
  have hdescent : baseEnd_3211214 < baseStart_3211214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211278 : List Nat := [4, 1, 1, 2, 2, 1, 2, 5, 1, 3]
def baseStart_3211278 : Nat := 118140960795 + 3211278 * 2 ^ 59
def prefixEnd_3211278 : Nat := 4983230072969 + 3 ^ 40 * 3211278 * 2
def baseEnd_3211278 : Nat := 1099286086139328062504405

theorem tailTrace_3211278 : CollatzResearch.WordTrace tailWord_3211278 prefixEnd_3211278 1099286086139328062504405 := by
  unfold tailWord_3211278
  simp only [CollatzResearch.WordTrace]
  refine ⟨14640616357511965432970311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78083287240063815642508325 14640616357511965432970311)
  ·
    refine ⟨21960924536267948149455467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14640616357511965432970311 21960924536267948149455467)
    ·
      refine ⟨32941386804401922224183201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21960924536267948149455467 32941386804401922224183201)
      ·
        refine ⟨24706040103301441668137401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32941386804401922224183201 24706040103301441668137401)
        ·
          refine ⟨18529530077476081251103051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24706040103301441668137401 18529530077476081251103051)
          ·
            refine ⟨27794295116214121876654577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18529530077476081251103051 27794295116214121876654577)
            ·
              refine ⟨20845721337160591407490933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27794295116214121876654577 20845721337160591407490933)
              ·
                refine ⟨1954286375358805444452275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20845721337160591407490933 1954286375358805444452275)
                ·
                  refine ⟨2931429563038208166678413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1954286375358805444452275 2931429563038208166678413)
                  ·
                    refine ⟨1099286086139328062504405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2931429563038208166678413 1099286086139328062504405)
                    ·
                      rfl

theorem cell22_3211278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 5, 1, 3].length) (baseStart_3211278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3211278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3211278 prefixEnd_3211278 := by exact prefixLift 3211278
  have htrace : WordTrace (prefixWord ++ tailWord_3211278) baseStart_3211278 baseEnd_3211278 := by
    simpa [prefixWord, tailWord_3211278, baseEnd_3211278] using wordTrace_append hprefix tailTrace_3211278
  have hstable : (prefixWord ++ tailWord_3211278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211278).length < 2 ^ (prefixWord ++ tailWord_3211278).sum := by decide
  have hdescent : baseEnd_3211278 < baseStart_3211278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211306 : List Nat := [3, 1, 4, 1, 2, 2, 1, 1, 2, 5]
def baseStart_3211306 : Nat := 118140960795 + 3211306 * 2 ^ 59
def prefixEnd_3211306 : Nat := 4983230072969 + 3 ^ 40 * 3211306 * 2
def baseEnd_3211306 : Nat := 1099295671111545322804319

theorem tailTrace_3211306 : CollatzResearch.WordTrace tailWord_3211306 prefixEnd_3211306 1099295671111545322804319 := by
  unfold tailWord_3211306
  simp only [CollatzResearch.WordTrace]
  refine ⟨29281488025998571061445443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78083968069329522830521181 29281488025998571061445443)
  ·
    refine ⟨43922232038997856592168165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29281488025998571061445443 43922232038997856592168165)
    ·
      refine ⟨8235418507312098111031531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43922232038997856592168165 8235418507312098111031531)
      ·
        refine ⟨12353127760968147166547297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8235418507312098111031531 12353127760968147166547297)
        ·
          refine ⟨9264845820726110374910473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12353127760968147166547297 9264845820726110374910473)
          ·
            refine ⟨6948634365544582781182855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9264845820726110374910473 6948634365544582781182855)
            ·
              refine ⟨10422951548316874171774283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6948634365544582781182855 10422951548316874171774283)
              ·
                refine ⟨15634427322475311257661425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10422951548316874171774283 15634427322475311257661425)
                ·
                  refine ⟨11725820491856483443246069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15634427322475311257661425 11725820491856483443246069)
                  ·
                    refine ⟨1099295671111545322804319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11725820491856483443246069 1099295671111545322804319)
                    ·
                      rfl

theorem cell22_3211306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_3211306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3211306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3211306 prefixEnd_3211306 := by exact prefixLift 3211306
  have htrace : WordTrace (prefixWord ++ tailWord_3211306) baseStart_3211306 baseEnd_3211306 := by
    simpa [prefixWord, tailWord_3211306, baseEnd_3211306] using wordTrace_append hprefix tailTrace_3211306
  have hstable : (prefixWord ++ tailWord_3211306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211306).length < 2 ^ (prefixWord ++ tailWord_3211306).sum := by decide
  have hdescent : baseEnd_3211306 < baseStart_3211306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211516 : List Nat := [2, 2, 2, 1, 4, 2, 9]
def baseStart_3211516 : Nat := 118140960795 + 3211516 * 2 ^ 59
def prefixEnd_3211516 : Nat := 4983230072969 + 3 ^ 40 * 3211516 * 2
def baseEnd_3211516 : Nat := 40717316977895362039025

theorem tailTrace_3211516 : CollatzResearch.WordTrace tailWord_3211516 prefixEnd_3211516 40717316977895362039025 := by
  unfold tailWord_3211516
  simp only [CollatzResearch.WordTrace]
  refine ⟨58566805716616745055463201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78089074288822326740617601 58566805716616745055463201)
  ·
    refine ⟨43925104287462558791597401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58566805716616745055463201 43925104287462558791597401)
    ·
      refine ⟨32943828215596919093698051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43925104287462558791597401 32943828215596919093698051)
      ·
        refine ⟨49415742323395378640547077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32943828215596919093698051 49415742323395378640547077)
        ·
          refine ⟨9265451685636633495102577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49415742323395378640547077 9265451685636633495102577)
          ·
            refine ⟨6949088764227475121326933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9265451685636633495102577 6949088764227475121326933)
            ·
              refine ⟨40717316977895362039025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6949088764227475121326933 40717316977895362039025)
              ·
                rfl

theorem cell22_3211516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 9].length) (baseStart_3211516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3211516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3211516 prefixEnd_3211516 := by exact prefixLift 3211516
  have htrace : WordTrace (prefixWord ++ tailWord_3211516) baseStart_3211516 baseEnd_3211516 := by
    simpa [prefixWord, tailWord_3211516, baseEnd_3211516] using wordTrace_append hprefix tailTrace_3211516
  have hstable : (prefixWord ++ tailWord_3211516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211516).length < 2 ^ (prefixWord ++ tailWord_3211516).sum := by decide
  have hdescent : baseEnd_3211516 < baseStart_3211516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211518 : List Nat := [4, 2, 2, 1, 1, 1, 2, 1, 4, 4]
def baseStart_3211518 : Nat := 118140960795 + 3211518 * 2 ^ 59
def prefixEnd_3211518 : Nat := 4983230072969 + 3 ^ 40 * 3211518 * 2
def baseEnd_3211518 : Nat := 1099368243044047436503669

theorem tailTrace_3211518 : CollatzResearch.WordTrace tailWord_3211518 prefixEnd_3211518 1099368243044047436503669 := by
  unfold tailWord_3211518
  simp only [CollatzResearch.WordTrace]
  refine ⟨14641710547403280556562401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78089122919484162968332805 14641710547403280556562401)
  ·
    refine ⟨10981282910552460417421801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14641710547403280556562401 10981282910552460417421801)
    ·
      refine ⟨8235962182914345313066351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10981282910552460417421801 8235962182914345313066351)
      ·
        refine ⟨12353943274371517969599527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8235962182914345313066351 12353943274371517969599527)
        ·
          refine ⟨18530914911557276954399291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12353943274371517969599527 18530914911557276954399291)
          ·
            refine ⟨27796372367335915431598937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18530914911557276954399291 27796372367335915431598937)
            ·
              refine ⟨20847279275501936573699203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27796372367335915431598937 20847279275501936573699203)
              ·
                refine ⟨31270918913252904860548805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20847279275501936573699203 31270918913252904860548805)
                ·
                  refine ⟨5863297296234919661352901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31270918913252904860548805 5863297296234919661352901)
                  ·
                    refine ⟨1099368243044047436503669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5863297296234919661352901 1099368243044047436503669)
                    ·
                      rfl

theorem cell22_3211518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_3211518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3211518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3211518 prefixEnd_3211518 := by exact prefixLift 3211518
  have htrace : WordTrace (prefixWord ++ tailWord_3211518) baseStart_3211518 baseEnd_3211518 := by
    simpa [prefixWord, tailWord_3211518, baseEnd_3211518] using wordTrace_append hprefix tailTrace_3211518
  have hstable : (prefixWord ++ tailWord_3211518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211518).length < 2 ^ (prefixWord ++ tailWord_3211518).sum := by decide
  have hdescent : baseEnd_3211518 < baseStart_3211518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211550 : List Nat := [4, 3, 2, 1, 1, 2, 1, 8]
def baseStart_3211550 : Nat := 118140960795 + 3211550 * 2 ^ 59
def prefixEnd_3211550 : Nat := 4983230072969 + 3 ^ 40 * 3211550 * 2
def baseEnd_3211550 : Nat := 122153244144223335522619

theorem tailTrace_3211550 : CollatzResearch.WordTrace tailWord_3211550 prefixEnd_3211550 122153244144223335522619 := by
  unfold tailWord_3211550
  simp only [CollatzResearch.WordTrace]
  refine ⟨14641856439388789239708013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78089901010073542611776069 14641856439388789239708013)
  ·
    refine ⟨5490696164770795964890505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14641856439388789239708013 5490696164770795964890505)
    ·
      refine ⟨4118022123578096973667879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5490696164770795964890505 4118022123578096973667879)
      ·
        refine ⟨6177033185367145460501819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4118022123578096973667879 6177033185367145460501819)
        ·
          refine ⟨9265549778050718190752729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6177033185367145460501819 9265549778050718190752729)
          ·
            refine ⟨6949162333538038643064547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9265549778050718190752729 6949162333538038643064547)
            ·
              refine ⟨10423743500307057964596821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6949162333538038643064547 10423743500307057964596821)
              ·
                refine ⟨122153244144223335522619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10423743500307057964596821 122153244144223335522619)
                ·
                  rfl

theorem cell22_3211550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 8].length) (baseStart_3211550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3211550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3211550 prefixEnd_3211550 := by exact prefixLift 3211550
  have htrace : WordTrace (prefixWord ++ tailWord_3211550) baseStart_3211550 baseEnd_3211550 := by
    simpa [prefixWord, tailWord_3211550, baseEnd_3211550] using wordTrace_append hprefix tailTrace_3211550
  have hstable : (prefixWord ++ tailWord_3211550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211550).length < 2 ^ (prefixWord ++ tailWord_3211550).sum := by decide
  have hdescent : baseEnd_3211550 < baseStart_3211550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211576 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 4, 5]
def baseStart_3211576 : Nat := 118140960795 + 3211576 * 2 ^ 59
def prefixEnd_3211576 : Nat := 4983230072969 + 3 ^ 40 * 3211576 * 2
def baseEnd_3211576 : Nat := 1099388097629354618553491

theorem tailTrace_3211576 : CollatzResearch.WordTrace tailWord_3211576 prefixEnd_3211576 1099388097629354618553491 := by
  unfold tailWord_3211576
  simp only [CollatzResearch.WordTrace]
  refine ⟨58567899906508060179055291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78090533208677413572073721 58567899906508060179055291)
  ·
    refine ⟨87851849859762090268582937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58567899906508060179055291 87851849859762090268582937)
    ·
      refine ⟨65888887394821567701437203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87851849859762090268582937 65888887394821567701437203)
      ·
        refine ⟨98833331092232351552155805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65888887394821567701437203 98833331092232351552155805)
        ·
          refine ⟨37062499159587131832058427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98833331092232351552155805 37062499159587131832058427)
          ·
            refine ⟨55593748739380697748087641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37062499159587131832058427 55593748739380697748087641)
            ·
              refine ⟨41695311554535523311065731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55593748739380697748087641 41695311554535523311065731)
              ·
                refine ⟨62542967331803284966598597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41695311554535523311065731 62542967331803284966598597)
                ·
                  refine ⟨11726806374713115931237237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62542967331803284966598597 11726806374713115931237237)
                  ·
                    refine ⟨1099388097629354618553491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11726806374713115931237237 1099388097629354618553491)
                    ·
                      rfl

theorem cell22_3211576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_3211576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3211576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3211576 prefixEnd_3211576 := by exact prefixLift 3211576
  have htrace : WordTrace (prefixWord ++ tailWord_3211576) baseStart_3211576 baseEnd_3211576 := by
    simpa [prefixWord, tailWord_3211576, baseEnd_3211576] using wordTrace_append hprefix tailTrace_3211576
  have hstable : (prefixWord ++ tailWord_3211576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211576).length < 2 ^ (prefixWord ++ tailWord_3211576).sum := by decide
  have hdescent : baseEnd_3211576 < baseStart_3211576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211582 : List Nat := [4, 2, 1, 2, 1, 4, 1, 1, 3, 3]
def baseStart_3211582 : Nat := 118140960795 + 3211582 * 2 ^ 59
def prefixEnd_3211582 : Nat := 4983230072969 + 3 ^ 40 * 3211582 * 2
def baseEnd_3211582 : Nat := 1099390151551972602903473

theorem tailTrace_3211582 : CollatzResearch.WordTrace tailWord_3211582 prefixEnd_3211582 1099390151551972602903473 := by
  unfold tailWord_3211582
  simp only [CollatzResearch.WordTrace]
  refine ⟨14642002331374297922853625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78090679100662922255219333 14642002331374297922853625)
  ·
    refine ⟨10981501748530723442140219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14642002331374297922853625 10981501748530723442140219)
    ·
      refine ⟨16472252622796085163210329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10981501748530723442140219 16472252622796085163210329)
      ·
        refine ⟨12354189467097063872407747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16472252622796085163210329 12354189467097063872407747)
        ·
          refine ⟨18531284200645595808611621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12354189467097063872407747 18531284200645595808611621)
          ·
            refine ⟨3474615787621049214114679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18531284200645595808611621 3474615787621049214114679)
            ·
              refine ⟨5211923681431573821172019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3474615787621049214114679 5211923681431573821172019)
              ·
                refine ⟨7817885522147360731758029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5211923681431573821172019 7817885522147360731758029)
                ·
                  refine ⟨2931707070805260274409261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7817885522147360731758029 2931707070805260274409261)
                  ·
                    refine ⟨1099390151551972602903473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2931707070805260274409261 1099390151551972602903473)
                    ·
                      rfl

theorem cell22_3211582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_3211582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3211582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3211582 prefixEnd_3211582 := by exact prefixLift 3211582
  have htrace : WordTrace (prefixWord ++ tailWord_3211582) baseStart_3211582 baseEnd_3211582 := by
    simpa [prefixWord, tailWord_3211582, baseEnd_3211582] using wordTrace_append hprefix tailTrace_3211582
  have hstable : (prefixWord ++ tailWord_3211582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211582).length < 2 ^ (prefixWord ++ tailWord_3211582).sum := by decide
  have hdescent : baseEnd_3211582 < baseStart_3211582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211608 : List Nat := [2, 1, 2, 2, 1, 1, 2, 6, 1, 4]
def baseStart_3211608 : Nat := 118140960795 + 3211608 * 2 ^ 59
def prefixEnd_3211608 : Nat := 4983230072969 + 3 ^ 40 * 3211608 * 2
def baseEnd_3211608 : Nat := 1099399051883317201753393

theorem tailTrace_3211608 : CollatzResearch.WordTrace tailWord_3211608 prefixEnd_3211608 1099399051883317201753393 := by
  unfold tailWord_3211608
  simp only [CollatzResearch.WordTrace]
  refine ⟨58568483474450094911637739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78091311299266793215516985 58568483474450094911637739)
  ·
    refine ⟨87852725211675142367456609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58568483474450094911637739 87852725211675142367456609)
    ·
      refine ⟨65889543908756356775592457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87852725211675142367456609 65889543908756356775592457)
      ·
        refine ⟨49417157931567267581694343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65889543908756356775592457 49417157931567267581694343)
        ·
          refine ⟨74125736897350901372541515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49417157931567267581694343 74125736897350901372541515)
          ·
            refine ⟨111188605346026352058812273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74125736897350901372541515 111188605346026352058812273)
            ·
              refine ⟨83391454009519764044109205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111188605346026352058812273 83391454009519764044109205)
              ·
                refine ⟨3908974406696238939567619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83391454009519764044109205 3908974406696238939567619)
                ·
                  refine ⟨5863461610044358409351429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3908974406696238939567619 5863461610044358409351429)
                  ·
                    refine ⟨1099399051883317201753393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5863461610044358409351429 1099399051883317201753393)
                    ·
                      rfl

theorem cell22_3211608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 1, 4].length) (baseStart_3211608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3211608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3211608 prefixEnd_3211608 := by exact prefixLift 3211608
  have htrace : WordTrace (prefixWord ++ tailWord_3211608) baseStart_3211608 baseEnd_3211608 := by
    simpa [prefixWord, tailWord_3211608, baseEnd_3211608] using wordTrace_append hprefix tailTrace_3211608
  have hstable : (prefixWord ++ tailWord_3211608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211608).length < 2 ^ (prefixWord ++ tailWord_3211608).sum := by decide
  have hdescent : baseEnd_3211608 < baseStart_3211608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211625 : List Nat := [1, 2, 1, 1, 1, 3, 7, 1, 1, 4]
def baseStart_3211625 : Nat := 118140960795 + 3211625 * 2 ^ 59
def prefixEnd_3211625 : Nat := 4983230072969 + 3 ^ 40 * 3211625 * 2
def baseEnd_3211625 : Nat := 1099404871330734824078341

theorem tailTrace_3211625 : CollatzResearch.WordTrace tailWord_3211625 prefixEnd_3211625 1099404871330734824078341 := by
  unfold tailWord_3211625
  simp only [CollatzResearch.WordTrace]
  refine ⟨117137586989838601726644329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78091724659892401151096219 117137586989838601726644329)
  ·
    refine ⟨87853190242378951294983247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117137586989838601726644329 87853190242378951294983247)
    ·
      refine ⟨131779785363568426942474871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87853190242378951294983247 131779785363568426942474871)
      ·
        refine ⟨197669678045352640413712307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131779785363568426942474871 197669678045352640413712307)
        ·
          refine ⟨296504517068028960620568461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197669678045352640413712307 296504517068028960620568461)
          ·
            refine ⟨111189193900510860232713173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 296504517068028960620568461 111189193900510860232713173)
            ·
              refine ⟨2605996732043223286704215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 111189193900510860232713173 2605996732043223286704215)
              ·
                refine ⟨3908995098064834930056323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2605996732043223286704215 3908995098064834930056323)
                ·
                  refine ⟨5863492647097252395084485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3908995098064834930056323 5863492647097252395084485)
                  ·
                    refine ⟨1099404871330734824078341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5863492647097252395084485 1099404871330734824078341)
                    ·
                      rfl

theorem cell22_3211625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 1, 4].length) (baseStart_3211625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3211625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3211625 prefixEnd_3211625 := by exact prefixLift 3211625
  have htrace : WordTrace (prefixWord ++ tailWord_3211625) baseStart_3211625 baseEnd_3211625 := by
    simpa [prefixWord, tailWord_3211625, baseEnd_3211625] using wordTrace_append hprefix tailTrace_3211625
  have hstable : (prefixWord ++ tailWord_3211625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211625).length < 2 ^ (prefixWord ++ tailWord_3211625).sum := by decide
  have hdescent : baseEnd_3211625 < baseStart_3211625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211655 : List Nat := [1, 1, 4, 2, 2, 1, 1, 5, 2, 3]
def baseStart_3211655 : Nat := 118140960795 + 3211655 * 2 ^ 59
def prefixEnd_3211655 : Nat := 4983230072969 + 3 ^ 40 * 3211655 * 2
def baseEnd_3211655 : Nat := 1099415140943824745828249

theorem tailTrace_3211655 : CollatzResearch.WordTrace tailWord_3211655 prefixEnd_3211655 1099415140943824745828249 := by
  unfold tailWord_3211655
  simp only [CollatzResearch.WordTrace]
  refine ⟨117138681179729916850236419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78092454119819944566824279 117138681179729916850236419)
  ·
    refine ⟨175708021769594875275354629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117138681179729916850236419 175708021769594875275354629)
    ·
      refine ⟨32945254081799039114128993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175708021769594875275354629 32945254081799039114128993)
      ·
        refine ⟨24708940561349279335596745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32945254081799039114128993 24708940561349279335596745)
        ·
          refine ⟨18531705421011959501697559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24708940561349279335596745 18531705421011959501697559)
          ·
            refine ⟨27797558131517939252546339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18531705421011959501697559 27797558131517939252546339)
            ·
              refine ⟨41696337197276908878819509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27797558131517939252546339 41696337197276908878819509)
              ·
                refine ⟨3909031612244710207389329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41696337197276908878819509 3909031612244710207389329)
                ·
                  refine ⟨2931773709183532655541997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3909031612244710207389329 2931773709183532655541997)
                  ·
                    refine ⟨1099415140943824745828249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2931773709183532655541997 1099415140943824745828249)
                    ·
                      rfl

theorem cell22_3211655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_3211655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3211655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3211655 prefixEnd_3211655 := by exact prefixLift 3211655
  have htrace : WordTrace (prefixWord ++ tailWord_3211655) baseStart_3211655 baseEnd_3211655 := by
    simpa [prefixWord, tailWord_3211655, baseEnd_3211655] using wordTrace_append hprefix tailTrace_3211655
  have hstable : (prefixWord ++ tailWord_3211655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211655).length < 2 ^ (prefixWord ++ tailWord_3211655).sum := by decide
  have hdescent : baseEnd_3211655 < baseStart_3211655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211777 : List Nat := [1, 2, 4, 1, 3, 1, 3, 2, 1, 4]
def baseStart_3211777 : Nat := 118140960795 + 3211777 * 2 ^ 59
def prefixEnd_3211777 : Nat := 4983230072969 + 3 ^ 40 * 3211777 * 2
def baseEnd_3211777 : Nat := 1099456904037057094277875

theorem tailTrace_3211777 : CollatzResearch.WordTrace tailWord_3211777 prefixEnd_3211777 1099456904037057094277875 := by
  unfold tailWord_3211777
  simp only [CollatzResearch.WordTrace]
  refine ⟨117143130885287931686177585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78095420590191954457451723 117143130885287931686177585)
  ·
    refine ⟨87857348163965948764633189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117143130885287931686177585 87857348163965948764633189)
    ·
      refine ⟨16473252780743615393368723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87857348163965948764633189 16473252780743615393368723)
      ·
        refine ⟨24709879171115423090053085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16473252780743615393368723 24709879171115423090053085)
        ·
          refine ⟨9266204689168283658769907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24709879171115423090053085 9266204689168283658769907)
          ·
            refine ⟨13899307033752425488154861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9266204689168283658769907 13899307033752425488154861)
            ·
              refine ⟨5212240137657159558058073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13899307033752425488154861 5212240137657159558058073)
              ·
                refine ⟨3909180103242869668543555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5212240137657159558058073 3909180103242869668543555)
                ·
                  refine ⟨5863770154864304502815333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3909180103242869668543555 5863770154864304502815333)
                  ·
                    refine ⟨1099456904037057094277875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5863770154864304502815333 1099456904037057094277875)
                    ·
                      rfl

theorem cell22_3211777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_3211777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3211777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3211777 prefixEnd_3211777 := by exact prefixLift 3211777
  have htrace : WordTrace (prefixWord ++ tailWord_3211777) baseStart_3211777 baseEnd_3211777 := by
    simpa [prefixWord, tailWord_3211777, baseEnd_3211777] using wordTrace_append hprefix tailTrace_3211777
  have hstable : (prefixWord ++ tailWord_3211777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211777).length < 2 ^ (prefixWord ++ tailWord_3211777).sum := by decide
  have hdescent : baseEnd_3211777 < baseStart_3211777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211790 : List Nat := [4, 1, 1, 2, 3, 1, 1, 1, 3, 5]
def baseStart_3211790 : Nat := 118140960795 + 3211790 * 2 ^ 59
def prefixEnd_3211790 : Nat := 4983230072969 + 3 ^ 40 * 3211790 * 2
def baseEnd_3211790 : Nat := 1099461354202729393702835

theorem tailTrace_3211790 : CollatzResearch.WordTrace tailWord_3211790 prefixEnd_3211790 1099461354202729393702835 := by
  unfold tailWord_3211790
  simp only [CollatzResearch.WordTrace]
  refine ⟨14642950629280104363300103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78095736689493889937600549 14642950629280104363300103)
  ·
    refine ⟨21964425943920156544950155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14642950629280104363300103 21964425943920156544950155)
    ·
      refine ⟨32946638915880234817425233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21964425943920156544950155 32946638915880234817425233)
      ·
        refine ⟨24709979186910176113068925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32946638915880234817425233 24709979186910176113068925)
        ·
          refine ⟨9266242195091316042400847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24709979186910176113068925 9266242195091316042400847)
          ·
            refine ⟨13899363292636974063601271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9266242195091316042400847 13899363292636974063601271)
            ·
              refine ⟨20849044938955461095401907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13899363292636974063601271 20849044938955461095401907)
              ·
                refine ⟨31273567408433191643102861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20849044938955461095401907 31273567408433191643102861)
                ·
                  refine ⟨11727587778162446866163573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31273567408433191643102861 11727587778162446866163573)
                  ·
                    refine ⟨1099461354202729393702835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11727587778162446866163573 1099461354202729393702835)
                    ·
                      rfl

theorem cell22_3211790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_3211790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3211790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3211790 prefixEnd_3211790 := by exact prefixLift 3211790
  have htrace : WordTrace (prefixWord ++ tailWord_3211790) baseStart_3211790 baseEnd_3211790 := by
    simpa [prefixWord, tailWord_3211790, baseEnd_3211790] using wordTrace_append hprefix tailTrace_3211790
  have hstable : (prefixWord ++ tailWord_3211790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211790).length < 2 ^ (prefixWord ++ tailWord_3211790).sum := by decide
  have hdescent : baseEnd_3211790 < baseStart_3211790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211837 : List Nat := [1, 4, 1, 3, 2, 2, 3, 6]
def baseStart_3211837 : Nat := 118140960795 + 3211837 * 2 ^ 59
def prefixEnd_3211837 : Nat := 4983230072969 + 3 ^ 40 * 3211837 * 2
def baseEnd_3211837 : Nat := 122164160362581881975299

theorem tailTrace_3211837 : CollatzResearch.WordTrace tailWord_3211837 prefixEnd_3211837 122164160362581881975299 := by
  unfold tailWord_3211837
  simp only [CollatzResearch.WordTrace]
  refine ⟨117145319265070561933361765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78096879510047041288907843 117145319265070561933361765)
  ·
    refine ⟨21964747362200730362505331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117145319265070561933361765 21964747362200730362505331)
    ·
      refine ⟨32947121043301095543757997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21964747362200730362505331 32947121043301095543757997)
      ·
        refine ⟨12355170391237910828909249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32947121043301095543757997 12355170391237910828909249)
        ·
          refine ⟨9266377793428433121681937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12355170391237910828909249 9266377793428433121681937)
          ·
            refine ⟨6949783345071324841261453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9266377793428433121681937 6949783345071324841261453)
            ·
              refine ⟨2606168754401746815473045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6949783345071324841261453 2606168754401746815473045)
              ·
                refine ⟨122164160362581881975299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2606168754401746815473045 122164160362581881975299)
                ·
                  rfl

theorem cell22_3211837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 6].length) (baseStart_3211837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3211837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3211837 prefixEnd_3211837 := by exact prefixLift 3211837
  have htrace : WordTrace (prefixWord ++ tailWord_3211837) baseStart_3211837 baseEnd_3211837 := by
    simpa [prefixWord, tailWord_3211837, baseEnd_3211837] using wordTrace_append hprefix tailTrace_3211837
  have hstable : (prefixWord ++ tailWord_3211837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211837).length < 2 ^ (prefixWord ++ tailWord_3211837).sum := by decide
  have hdescent : baseEnd_3211837 < baseStart_3211837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
