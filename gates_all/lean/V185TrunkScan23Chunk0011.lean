import V185TrunkScan23Chunk0010

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_64228 : List Nat := [2, 3, 1, 1, 1, 4, 3, 1, 2, 3, 2]
def baseStart_64228 : Nat := 118140960795 + 64228 * 2 ^ 59
def prefixEnd_64228 : Nat := 4983230072969 + 3 ^ 40 * 64228 * 2
def baseEnd_64228 : Nat := 32979835477079941354627

theorem tailTrace_64228 : CollatzResearch.WordTrace tailWord_64228 prefixEnd_64228 32979835477079941354627 := by
  unfold tailWord_64228
  simp only [CollatzResearch.WordTrace]
  refine ⟨1171293805660200057100669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1561725074213600076134225 1171293805660200057100669)
  ·
    refine ⟨439235177122575021412751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1171293805660200057100669 439235177122575021412751)
    ·
      refine ⟨658852765683862532119127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439235177122575021412751 658852765683862532119127)
      ·
        refine ⟨988279148525793798178691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658852765683862532119127 988279148525793798178691)
        ·
          refine ⟨1482418722788690697268037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 988279148525793798178691 1482418722788690697268037)
          ·
            refine ⟨277953510522879505737757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1482418722788690697268037 277953510522879505737757)
            ·
              refine ⟨104232566446079814651659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277953510522879505737757 104232566446079814651659)
              ·
                refine ⟨156348849669119721977489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104232566446079814651659 156348849669119721977489)
                ·
                  refine ⟨117261637251839791483117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156348849669119721977489 117261637251839791483117)
                  ·
                    refine ⟨43973113969439921806169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117261637251839791483117 43973113969439921806169)
                    ·
                      refine ⟨32979835477079941354627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 43973113969439921806169 32979835477079941354627)
                      ·
                        rfl

theorem cell23_64228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 2, 3, 2].length) (baseStart_64228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64228 prefixEnd_64228 := by exact prefixLift 64228
  have htrace : WordTrace (prefixWord ++ tailWord_64228) baseStart_64228 baseEnd_64228 := by
    simpa [prefixWord, tailWord_64228, baseEnd_64228] using wordTrace_append hprefix tailTrace_64228
  have hstable : (prefixWord ++ tailWord_64228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64228).length < 2 ^ (prefixWord ++ tailWord_64228).sum := by decide
  have hdescent : baseEnd_64228 < baseStart_64228 := by decide
  rcases family_descends (prefixWord ++ tailWord_64228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64238 : List Nat := [4, 1, 2, 1, 1, 3, 4, 1, 1, 5]
def baseStart_64238 : Nat := 118140960795 + 64238 * 2 ^ 59
def prefixEnd_64238 : Nat := 4983230072969 + 3 ^ 40 * 64238 * 2
def baseEnd_64238 : Nat := 10994990094541634076527

theorem tailTrace_64238 : CollatzResearch.WordTrace tailWord_64238 prefixEnd_64238 10994990094541634076527 := by
  unfold tailWord_64238
  simp only [CollatzResearch.WordTrace]
  refine ⟨292869042660521477758171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1561968227522781214710245 292869042660521477758171)
  ·
    refine ⟨439303563990782216637257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292869042660521477758171 439303563990782216637257)
    ·
      refine ⟨329477672993086662477943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439303563990782216637257 329477672993086662477943)
      ·
        refine ⟨494216509489629993716915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329477672993086662477943 494216509489629993716915)
        ·
          refine ⟨741324764234444990575373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494216509489629993716915 741324764234444990575373)
          ·
            refine ⟨277996786587916871465765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 741324764234444990575373 277996786587916871465765)
            ·
              refine ⟨52124397485234413399831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 277996786587916871465765 52124397485234413399831)
              ·
                refine ⟨78186596227851620099747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52124397485234413399831 78186596227851620099747)
                ·
                  refine ⟨117279894341777430149621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78186596227851620099747 117279894341777430149621)
                  ·
                    refine ⟨10994990094541634076527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117279894341777430149621 10994990094541634076527)
                    ·
                      rfl

theorem cell23_64238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_64238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64238 prefixEnd_64238 := by exact prefixLift 64238
  have htrace : WordTrace (prefixWord ++ tailWord_64238) baseStart_64238 baseEnd_64238 := by
    simpa [prefixWord, tailWord_64238, baseEnd_64238] using wordTrace_append hprefix tailTrace_64238
  have hstable : (prefixWord ++ tailWord_64238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64238).length < 2 ^ (prefixWord ++ tailWord_64238).sum := by decide
  have hdescent : baseEnd_64238 < baseStart_64238 := by decide
  rcases family_descends (prefixWord ++ tailWord_64238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64241 : List Nat := [1, 2, 2, 2, 2, 2, 3, 3, 1, 1, 4]
def baseStart_64241 : Nat := 118140960795 + 64241 * 2 ^ 59
def prefixEnd_64241 : Nat := 4983230072969 + 3 ^ 40 * 64241 * 2
def baseEnd_64241 : Nat := 32986510725588390492067

theorem tailTrace_64241 : CollatzResearch.WordTrace tailWord_64241 prefixEnd_64241 32986510725588390492067 := by
  unfold tailWord_64241
  simp only [CollatzResearch.WordTrace]
  refine ⟨2343061760273303334424577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1562041173515535556283051 2343061760273303334424577)
  ·
    refine ⟨1757296320204977500818433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2343061760273303334424577 1757296320204977500818433)
    ·
      refine ⟨1317972240153733125613825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1757296320204977500818433 1317972240153733125613825)
      ·
        refine ⟨988479180115299844210369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1317972240153733125613825 988479180115299844210369)
        ·
          refine ⟨741359385086474883157777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 988479180115299844210369 741359385086474883157777)
          ·
            refine ⟨556019538814856162368333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 741359385086474883157777 556019538814856162368333)
            ·
              refine ⟨208507327055571060888125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 556019538814856162368333 208507327055571060888125)
              ·
                refine ⟨78190247645839147833047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208507327055571060888125 78190247645839147833047)
                ·
                  refine ⟨117285371468758721749571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78190247645839147833047 117285371468758721749571)
                  ·
                    refine ⟨175928057203138082624357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117285371468758721749571 175928057203138082624357)
                    ·
                      refine ⟨32986510725588390492067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 175928057203138082624357 32986510725588390492067)
                      ·
                        rfl

theorem cell23_64241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 1, 4].length) (baseStart_64241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64241 prefixEnd_64241 := by exact prefixLift 64241
  have htrace : WordTrace (prefixWord ++ tailWord_64241) baseStart_64241 baseEnd_64241 := by
    simpa [prefixWord, tailWord_64241, baseEnd_64241] using wordTrace_append hprefix tailTrace_64241
  have hstable : (prefixWord ++ tailWord_64241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64241).length < 2 ^ (prefixWord ++ tailWord_64241).sum := by decide
  have hdescent : baseEnd_64241 < baseStart_64241 := by decide
  rcases family_descends (prefixWord ++ tailWord_64241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64298 : List Nat := [3, 1, 4, 3, 1, 2, 9]
def baseStart_64298 : Nat := 118140960795 + 64298 * 2 ^ 59
def prefixEnd_64298 : Nat := 4983230072969 + 3 ^ 40 * 64298 * 2
def baseEnd_64298 : Nat := 407602211393761326905

theorem tailTrace_64298 : CollatzResearch.WordTrace tailWord_64298 prefixEnd_64298 407602211393761326905 := by
  unfold tailWord_64298
  simp only [CollatzResearch.WordTrace]
  refine ⟨586285180266700517312387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1563427147377868046166365 586285180266700517312387)
  ·
    refine ⟨879427770400050775968581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 586285180266700517312387 879427770400050775968581)
    ·
      refine ⟨164892706950009520494109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 879427770400050775968581 164892706950009520494109)
      ·
        refine ⟨61834765106253570185291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164892706950009520494109 61834765106253570185291)
        ·
          refine ⟨92752147659380355277937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61834765106253570185291 92752147659380355277937)
          ·
            refine ⟨69564110744535266458453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92752147659380355277937 69564110744535266458453)
            ·
              refine ⟨407602211393761326905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 69564110744535266458453 407602211393761326905)
              ·
                rfl

theorem cell23_64298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 9].length) (baseStart_64298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64298 prefixEnd_64298 := by exact prefixLift 64298
  have htrace : WordTrace (prefixWord ++ tailWord_64298) baseStart_64298 baseEnd_64298 := by
    simpa [prefixWord, tailWord_64298, baseEnd_64298] using wordTrace_append hprefix tailTrace_64298
  have hstable : (prefixWord ++ tailWord_64298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64298).length < 2 ^ (prefixWord ++ tailWord_64298).sum := by decide
  have hdescent : baseEnd_64298 < baseStart_64298 := by decide
  rcases family_descends (prefixWord ++ tailWord_64298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64309 : List Nat := [1, 3, 3, 1, 3, 2, 3, 2, 1, 2, 2]
def baseStart_64309 : Nat := 118140960795 + 64309 * 2 ^ 59
def prefixEnd_64309 : Nat := 4983230072969 + 3 ^ 40 * 64309 * 2
def baseEnd_64309 : Nat := 33021427410094124441755

theorem tailTrace_64309 : CollatzResearch.WordTrace tailWord_64309 prefixEnd_64309 33021427410094124441755 := by
  unfold tailWord_64309
  simp only [CollatzResearch.WordTrace]
  refine ⟨2345541924026950947899981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1563694616017967298599987 2345541924026950947899981)
  ·
    refine ⟨879578221510106605462493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2345541924026950947899981 879578221510106605462493)
    ·
      refine ⟨329841833066289977048435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 879578221510106605462493 329841833066289977048435)
      ·
        refine ⟨494762749599434965572653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329841833066289977048435 494762749599434965572653)
        ·
          refine ⟨185536031099788112089745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 494762749599434965572653 185536031099788112089745)
          ·
            refine ⟨139152023324841084067309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185536031099788112089745 139152023324841084067309)
            ·
              refine ⟨52182008746815406525241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139152023324841084067309 52182008746815406525241)
              ·
                refine ⟨39136506560111554893931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52182008746815406525241 39136506560111554893931)
                ·
                  refine ⟨58704759840167332340897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39136506560111554893931 58704759840167332340897)
                  ·
                    refine ⟨44028569880125499255673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58704759840167332340897 44028569880125499255673)
                    ·
                      refine ⟨33021427410094124441755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 44028569880125499255673 33021427410094124441755)
                      ·
                        rfl

theorem cell23_64309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_64309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64309 prefixEnd_64309 := by exact prefixLift 64309
  have htrace : WordTrace (prefixWord ++ tailWord_64309) baseStart_64309 baseEnd_64309 := by
    simpa [prefixWord, tailWord_64309, baseEnd_64309] using wordTrace_append hprefix tailTrace_64309
  have hstable : (prefixWord ++ tailWord_64309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64309).length < 2 ^ (prefixWord ++ tailWord_64309).sum := by decide
  have hdescent : baseEnd_64309 < baseStart_64309 := by decide
  rcases family_descends (prefixWord ++ tailWord_64309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64331 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 7, 4, 2]
def baseStart_64331 : Nat := 118140960795 + 64331 * 2 ^ 59
def prefixEnd_64331 : Nat := 4983230072969 + 3 ^ 40 * 64331 * 2
def baseEnd_64331 : Nat := 33032723984493038366653

theorem tailTrace_64331 : CollatzResearch.WordTrace tailWord_64331 prefixEnd_64331 33032723984493038366653 := by
  unfold tailWord_64331
  simp only [CollatzResearch.WordTrace]
  refine ⟨2346344329947248705200847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1564229553298165803467231 2346344329947248705200847)
  ·
    refine ⟨3519516494920873057801271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2346344329947248705200847 3519516494920873057801271)
    ·
      refine ⟨5279274742381309586701907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3519516494920873057801271 5279274742381309586701907)
      ·
        refine ⟨7918912113571964380052861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5279274742381309586701907 7918912113571964380052861)
        ·
          refine ⟨2969592042589486642519823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7918912113571964380052861 2969592042589486642519823)
          ·
            refine ⟨4454388063884229963779735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2969592042589486642519823 4454388063884229963779735)
            ·
              refine ⟨6681582095826344945669603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4454388063884229963779735 6681582095826344945669603)
              ·
                refine ⟨10022373143739517418504405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6681582095826344945669603 10022373143739517418504405)
                ·
                  refine ⟨234899370556394939496197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10022373143739517418504405 234899370556394939496197)
                  ·
                    refine ⟨44043631979324051155537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 234899370556394939496197 44043631979324051155537)
                    ·
                      refine ⟨33032723984493038366653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 44043631979324051155537 33032723984493038366653)
                      ·
                        rfl

theorem cell23_64331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 4, 2].length) (baseStart_64331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64331 prefixEnd_64331 := by exact prefixLift 64331
  have htrace : WordTrace (prefixWord ++ tailWord_64331) baseStart_64331 baseEnd_64331 := by
    simpa [prefixWord, tailWord_64331, baseEnd_64331] using wordTrace_append hprefix tailTrace_64331
  have hstable : (prefixWord ++ tailWord_64331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64331).length < 2 ^ (prefixWord ++ tailWord_64331).sum := by decide
  have hdescent : baseEnd_64331 < baseStart_64331 := by decide
  rcases family_descends (prefixWord ++ tailWord_64331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64381 : List Nat := [1, 4, 1, 1, 2, 1, 3, 1, 1, 5, 3]
def baseStart_64381 : Nat := 118140960795 + 64381 * 2 ^ 59
def prefixEnd_64381 : Nat := 4983230072969 + 3 ^ 40 * 64381 * 2
def baseEnd_64381 : Nat := 33058398017217842741423

theorem tailTrace_64381 : CollatzResearch.WordTrace tailWord_64381 prefixEnd_64381 33058398017217842741423 := by
  unfold tailWord_64381
  simp only [CollatzResearch.WordTrace]
  refine ⟨2348167979766107244520997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1565445319844071496347331 2348167979766107244520997)
  ·
    refine ⟨440281496206145108347687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2348167979766107244520997 440281496206145108347687)
    ·
      refine ⟨660422244309217662521531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440281496206145108347687 660422244309217662521531)
      ·
        refine ⟨990633366463826493782297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660422244309217662521531 990633366463826493782297)
        ·
          refine ⟨742975024847869870336723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 990633366463826493782297 742975024847869870336723)
          ·
            refine ⟨1114462537271804805505085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 742975024847869870336723 1114462537271804805505085)
            ·
              refine ⟨417923451476926802064407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1114462537271804805505085 417923451476926802064407)
              ·
                refine ⟨626885177215390203096611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 417923451476926802064407 626885177215390203096611)
                ·
                  refine ⟨940327765823085304644917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 626885177215390203096611 940327765823085304644917)
                  ·
                    refine ⟨88155728045914247310461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 940327765823085304644917 88155728045914247310461)
                    ·
                      refine ⟨33058398017217842741423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 88155728045914247310461 33058398017217842741423)
                      ·
                        rfl

theorem cell23_64381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_64381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64381 prefixEnd_64381 := by exact prefixLift 64381
  have htrace : WordTrace (prefixWord ++ tailWord_64381) baseStart_64381 baseEnd_64381 := by
    simpa [prefixWord, tailWord_64381, baseEnd_64381] using wordTrace_append hprefix tailTrace_64381
  have hstable : (prefixWord ++ tailWord_64381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64381).length < 2 ^ (prefixWord ++ tailWord_64381).sum := by decide
  have hdescent : baseEnd_64381 < baseStart_64381 := by decide
  rcases family_descends (prefixWord ++ tailWord_64381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64448 : List Nat := [2, 1, 1, 2, 3, 3, 2, 2, 3, 4]
def baseStart_64448 : Nat := 118140960795 + 64448 * 2 ^ 59
def prefixEnd_64448 : Nat := 4983230072969 + 3 ^ 40 * 64448 * 2
def baseEnd_64448 : Nat := 11030933740356360201205

theorem tailTrace_64448 : CollatzResearch.WordTrace tailWord_64448 prefixEnd_64448 11030933740356360201205 := by
  unfold tailWord_64448
  simp only [CollatzResearch.WordTrace]
  refine ⟨1175305835261688843604999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1567074447015585124806665 1175305835261688843604999)
  ·
    refine ⟨1762958752892533265407499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1175305835261688843604999 1762958752892533265407499)
    ·
      refine ⟨2644438129338799898111249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1762958752892533265407499 2644438129338799898111249)
      ·
        refine ⟨1983328597004099923583437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2644438129338799898111249 1983328597004099923583437)
        ·
          refine ⟨743748223876537471343789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1983328597004099923583437 743748223876537471343789)
          ·
            refine ⟨278905583953701551753921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 743748223876537471343789 278905583953701551753921)
            ·
              refine ⟨209179187965276163815441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278905583953701551753921 209179187965276163815441)
              ·
                refine ⟨156884390973957122861581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209179187965276163815441 156884390973957122861581)
                ·
                  refine ⟨58831646615233921073093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156884390973957122861581 58831646615233921073093)
                  ·
                    refine ⟨11030933740356360201205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58831646615233921073093 11030933740356360201205)
                    ·
                      rfl

theorem cell23_64448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 3, 4].length) (baseStart_64448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64448 prefixEnd_64448 := by exact prefixLift 64448
  have htrace : WordTrace (prefixWord ++ tailWord_64448) baseStart_64448 baseEnd_64448 := by
    simpa [prefixWord, tailWord_64448, baseEnd_64448] using wordTrace_append hprefix tailTrace_64448
  have hstable : (prefixWord ++ tailWord_64448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64448).length < 2 ^ (prefixWord ++ tailWord_64448).sum := by decide
  have hdescent : baseEnd_64448 < baseStart_64448 := by decide
  rcases family_descends (prefixWord ++ tailWord_64448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64458 : List Nat := [3, 1, 2, 1, 2, 1, 1, 5, 2, 2, 3]
def baseStart_64458 : Nat := 118140960795 + 64458 * 2 ^ 59
def prefixEnd_64458 : Nat := 4983230072969 + 3 ^ 40 * 64458 * 2
def baseEnd_64458 : Nat := 33097936027614041478569

theorem tailTrace_64458 : CollatzResearch.WordTrace tailWord_64458 prefixEnd_64458 33097936027614041478569 := by
  unfold tailWord_64458
  simp only [CollatzResearch.WordTrace]
  refine ⟨587744100121787348768507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1567317600324766263382685 587744100121787348768507)
  ·
    refine ⟨881616150182681023152761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 587744100121787348768507 881616150182681023152761)
    ·
      refine ⟨661212112637010767364571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 881616150182681023152761 661212112637010767364571)
      ·
        refine ⟨991818168955516151046857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661212112637010767364571 991818168955516151046857)
        ·
          refine ⟨743863626716637113285143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 991818168955516151046857 743863626716637113285143)
          ·
            refine ⟨1115795440074955669927715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 743863626716637113285143 1115795440074955669927715)
            ·
              refine ⟨1673693160112433504891573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1115795440074955669927715 1673693160112433504891573)
              ·
                refine ⟨156908733760540641083585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1673693160112433504891573 156908733760540641083585)
                ·
                  refine ⟨117681550320405480812689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156908733760540641083585 117681550320405480812689)
                  ·
                    refine ⟨88261162740304110609517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117681550320405480812689 88261162740304110609517)
                    ·
                      refine ⟨33097936027614041478569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 88261162740304110609517 33097936027614041478569)
                      ·
                        rfl

theorem cell23_64458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_64458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64458 prefixEnd_64458 := by exact prefixLift 64458
  have htrace : WordTrace (prefixWord ++ tailWord_64458) baseStart_64458 baseEnd_64458 := by
    simpa [prefixWord, tailWord_64458, baseEnd_64458] using wordTrace_append hprefix tailTrace_64458
  have hstable : (prefixWord ++ tailWord_64458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64458).length < 2 ^ (prefixWord ++ tailWord_64458).sum := by decide
  have hdescent : baseEnd_64458 < baseStart_64458 := by decide
  rcases family_descends (prefixWord ++ tailWord_64458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64482 : List Nat := [3, 3, 3, 1, 1, 1, 3, 1, 3, 4]
def baseStart_64482 : Nat := 118140960795 + 64482 * 2 ^ 59
def prefixEnd_64482 : Nat := 4983230072969 + 3 ^ 40 * 64482 * 2
def baseEnd_64482 : Nat := 11036753187773982526153

theorem tailTrace_64482 : CollatzResearch.WordTrace tailWord_64482 prefixEnd_64482 11036753187773982526153 := by
  unfold tailWord_64482
  simp only [CollatzResearch.WordTrace]
  refine ⟨587962938100050373486925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1567901168266800995965133 587962938100050373486925)
  ·
    refine ⟨220486101787518890057597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 587962938100050373486925 220486101787518890057597)
    ·
      refine ⟨82682288170319583771599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220486101787518890057597 82682288170319583771599)
      ·
        refine ⟨124023432255479375657399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82682288170319583771599 124023432255479375657399)
        ·
          refine ⟨186035148383219063486099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124023432255479375657399 186035148383219063486099)
          ·
            refine ⟨279052722574828595229149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186035148383219063486099 279052722574828595229149)
            ·
              refine ⟨104644770965560723210931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279052722574828595229149 104644770965560723210931)
              ·
                refine ⟨156967156448341084816397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104644770965560723210931 156967156448341084816397)
                ·
                  refine ⟨58862683668127906806149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156967156448341084816397 58862683668127906806149)
                  ·
                    refine ⟨11036753187773982526153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58862683668127906806149 11036753187773982526153)
                    ·
                      rfl

theorem cell23_64482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_64482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64482 prefixEnd_64482 := by exact prefixLift 64482
  have htrace : WordTrace (prefixWord ++ tailWord_64482) baseStart_64482 baseEnd_64482 := by
    simpa [prefixWord, tailWord_64482, baseEnd_64482] using wordTrace_append hprefix tailTrace_64482
  have hstable : (prefixWord ++ tailWord_64482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64482).length < 2 ^ (prefixWord ++ tailWord_64482).sum := by decide
  have hdescent : baseEnd_64482 < baseStart_64482 := by decide
  rcases family_descends (prefixWord ++ tailWord_64482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64495 : List Nat := [1, 1, 2, 1, 4, 5, 2, 1, 6]
def baseStart_64495 : Nat := 118140960795 + 64495 * 2 ^ 59
def prefixEnd_64495 : Nat := 4983230072969 + 3 ^ 40 * 64495 * 2
def baseEnd_64495 : Nat := 3679659423536710746211

theorem tailTrace_64495 : CollatzResearch.WordTrace tailWord_64495 prefixEnd_64495 3679659423536710746211 := by
  unfold tailWord_64495
  simp only [CollatzResearch.WordTrace]
  refine ⟨2352325901353104714170939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1568217267568736476113959 2352325901353104714170939)
  ·
    refine ⟨3528488852029657071256409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2352325901353104714170939 3528488852029657071256409)
    ·
      refine ⟨2646366639022242803442307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3528488852029657071256409 2646366639022242803442307)
      ·
        refine ⟨3969549958533364205163461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2646366639022242803442307 3969549958533364205163461)
        ·
          refine ⟨744290617225005788468149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3969549958533364205163461 744290617225005788468149)
          ·
            refine ⟨69777245364844292668889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 744290617225005788468149 69777245364844292668889)
            ·
              refine ⟨52332934023633219501667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69777245364844292668889 52332934023633219501667)
              ·
                refine ⟨78499401035449829252501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52332934023633219501667 78499401035449829252501)
                ·
                  refine ⟨3679659423536710746211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 78499401035449829252501 3679659423536710746211)
                  ·
                    rfl

theorem cell23_64495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 6].length) (baseStart_64495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64495 prefixEnd_64495 := by exact prefixLift 64495
  have htrace : WordTrace (prefixWord ++ tailWord_64495) baseStart_64495 baseEnd_64495 := by
    simpa [prefixWord, tailWord_64495, baseEnd_64495] using wordTrace_append hprefix tailTrace_64495
  have hstable : (prefixWord ++ tailWord_64495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64495).length < 2 ^ (prefixWord ++ tailWord_64495).sum := by decide
  have hdescent : baseEnd_64495 < baseStart_64495 := by decide
  rcases family_descends (prefixWord ++ tailWord_64495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64508 : List Nat := [2, 2, 2, 1, 2, 4, 1, 1, 3, 5]
def baseStart_64508 : Nat := 118140960795 + 64508 * 2 ^ 59
def prefixEnd_64508 : Nat := 4983230072969 + 3 ^ 40 * 64508 * 2
def baseEnd_64508 : Nat := 11041203353446281951113

theorem tailTrace_64508 : CollatzResearch.WordTrace tailWord_64508 prefixEnd_64508 11041203353446281951113 := by
  unfold tailWord_64508
  simp only [CollatzResearch.WordTrace]
  refine ⟨1176400025153003967197089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1568533366870671956262785 1176400025153003967197089)
  ·
    refine ⟨882300018864752975397817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1176400025153003967197089 882300018864752975397817)
    ·
      refine ⟨661725014148564731548363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 882300018864752975397817 661725014148564731548363)
      ·
        refine ⟨992587521222847097322545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661725014148564731548363 992587521222847097322545)
        ·
          refine ⟨744440640917135322991909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 992587521222847097322545 744440640917135322991909)
          ·
            refine ⟨139582620171962873060983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 744440640917135322991909 139582620171962873060983)
            ·
              refine ⟨209373930257944309591475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139582620171962873060983 209373930257944309591475)
              ·
                refine ⟨314060895386916464387213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209373930257944309591475 314060895386916464387213)
                ·
                  refine ⟨117772835770093674145205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 314060895386916464387213 117772835770093674145205)
                  ·
                    refine ⟨11041203353446281951113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117772835770093674145205 11041203353446281951113)
                    ·
                      rfl

theorem cell23_64508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_64508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64508 prefixEnd_64508 := by exact prefixLift 64508
  have htrace : WordTrace (prefixWord ++ tailWord_64508) baseStart_64508 baseEnd_64508 := by
    simpa [prefixWord, tailWord_64508, baseEnd_64508] using wordTrace_append hprefix tailTrace_64508
  have hstable : (prefixWord ++ tailWord_64508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64508).length < 2 ^ (prefixWord ++ tailWord_64508).sum := by decide
  have hdescent : baseEnd_64508 < baseStart_64508 := by decide
  rcases family_descends (prefixWord ++ tailWord_64508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64562 : List Nat := [3, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2]
def baseStart_64562 : Nat := 118140960795 + 64562 * 2 ^ 59
def prefixEnd_64562 : Nat := 4983230072969 + 3 ^ 40 * 64562 * 2
def baseEnd_64562 : Nat := 33151338015681634578091

theorem tailTrace_64562 : CollatzResearch.WordTrace tailWord_64562 prefixEnd_64562 33151338015681634578091 := by
  unfold tailWord_64562
  simp only [CollatzResearch.WordTrace]
  refine ⟨588692398027593789214985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1569846394740250104573293 588692398027593789214985)
  ·
    refine ⟨441519298520695341911239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 588692398027593789214985 441519298520695341911239)
    ·
      refine ⟨662278947781043012866859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441519298520695341911239 662278947781043012866859)
      ·
        refine ⟨993418421671564519300289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662278947781043012866859 993418421671564519300289)
        ·
          refine ⟨745063816253673389475217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 993418421671564519300289 745063816253673389475217)
          ·
            refine ⟨558797862190255042106413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 745063816253673389475217 558797862190255042106413)
            ·
              refine ⟨209549198321345640789905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 558797862190255042106413 209549198321345640789905)
              ·
                refine ⟨157161898741009230592429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209549198321345640789905 157161898741009230592429)
                ·
                  refine ⟨58935712027878461472161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157161898741009230592429 58935712027878461472161)
                  ·
                    refine ⟨44201784020908846104121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58935712027878461472161 44201784020908846104121)
                    ·
                      refine ⟨33151338015681634578091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 44201784020908846104121 33151338015681634578091)
                      ·
                        rfl

theorem cell23_64562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2].length) (baseStart_64562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64562 prefixEnd_64562 := by exact prefixLift 64562
  have htrace : WordTrace (prefixWord ++ tailWord_64562) baseStart_64562 baseEnd_64562 := by
    simpa [prefixWord, tailWord_64562, baseEnd_64562] using wordTrace_append hprefix tailTrace_64562
  have hstable : (prefixWord ++ tailWord_64562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64562).length < 2 ^ (prefixWord ++ tailWord_64562).sum := by decide
  have hdescent : baseEnd_64562 < baseStart_64562 := by decide
  rcases family_descends (prefixWord ++ tailWord_64562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64565 : List Nat := [1, 3, 3, 1, 1, 1, 1, 6, 1, 2, 3]
def baseStart_64565 : Nat := 118140960795 + 64565 * 2 ^ 59
def prefixEnd_64565 : Nat := 4983230072969 + 3 ^ 40 * 64565 * 2
def baseEnd_64565 : Nat := 33152878457645122840577

theorem tailTrace_64565 : CollatzResearch.WordTrace tailWord_64565 prefixEnd_64565 33152878457645122840577 := by
  unfold tailWord_64565
  simp only [CollatzResearch.WordTrace]
  refine ⟨2354879011099506669219149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1569919340733004446146099 2354879011099506669219149)
  ·
    refine ⟨883079629162315000957181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2354879011099506669219149 883079629162315000957181)
    ·
      refine ⟨331154860935868125358943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 883079629162315000957181 331154860935868125358943)
      ·
        refine ⟨496732291403802188038415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331154860935868125358943 496732291403802188038415)
        ·
          refine ⟨745098437105703282057623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496732291403802188038415 745098437105703282057623)
          ·
            refine ⟨1117647655658554923086435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 745098437105703282057623 1117647655658554923086435)
            ·
              refine ⟨1676471483487832384629653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1117647655658554923086435 1676471483487832384629653)
              ·
                refine ⟨78584600788492143029515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1676471483487832384629653 78584600788492143029515)
                ·
                  refine ⟨117876901182738214544273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78584600788492143029515 117876901182738214544273)
                  ·
                    refine ⟨88407675887053660908205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117876901182738214544273 88407675887053660908205)
                    ·
                      refine ⟨33152878457645122840577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 88407675887053660908205 33152878457645122840577)
                      ·
                        rfl

theorem cell23_64565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_64565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64565 prefixEnd_64565 := by exact prefixLift 64565
  have htrace : WordTrace (prefixWord ++ tailWord_64565) baseStart_64565 baseEnd_64565 := by
    simpa [prefixWord, tailWord_64565, baseEnd_64565] using wordTrace_append hprefix tailTrace_64565
  have hstable : (prefixWord ++ tailWord_64565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64565).length < 2 ^ (prefixWord ++ tailWord_64565).sum := by decide
  have hdescent : baseEnd_64565 < baseStart_64565 := by decide
  rcases family_descends (prefixWord ++ tailWord_64565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64579 : List Nat := [1, 1, 1, 3, 1, 2, 6, 3, 1, 2, 2]
def baseStart_64579 : Nat := 118140960795 + 64579 * 2 ^ 59
def prefixEnd_64579 : Nat := 4983230072969 + 3 ^ 40 * 64579 * 2
def baseEnd_64579 : Nat := 33160067186808068065513

theorem tailTrace_64579 : CollatzResearch.WordTrace tailWord_64579 prefixEnd_64579 33160067186808068065513 := by
  unfold tailWord_64579
  simp only [CollatzResearch.WordTrace]
  refine ⟨2355389633048787060228791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1570259755365858040152527 2355389633048787060228791)
  ·
    refine ⟨3533084449573180590343187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2355389633048787060228791 3533084449573180590343187)
    ·
      refine ⟨5299626674359770885514781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3533084449573180590343187 5299626674359770885514781)
      ·
        refine ⟨1987360002884914082068043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5299626674359770885514781 1987360002884914082068043)
        ·
          refine ⟨2981040004327371123102065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1987360002884914082068043 2981040004327371123102065)
          ·
            refine ⟨2235780003245528342326549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2981040004327371123102065 2235780003245528342326549)
            ·
              refine ⟨104802187652134141046557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2235780003245528342326549 104802187652134141046557)
              ·
                refine ⟨39300820369550302892459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104802187652134141046557 39300820369550302892459)
                ·
                  refine ⟨58951230554325454338689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39300820369550302892459 58951230554325454338689)
                  ·
                    refine ⟨44213422915744090754017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58951230554325454338689 44213422915744090754017)
                    ·
                      refine ⟨33160067186808068065513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 44213422915744090754017 33160067186808068065513)
                      ·
                        rfl

theorem cell23_64579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 3, 1, 2, 2].length) (baseStart_64579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64579 prefixEnd_64579 := by exact prefixLift 64579
  have htrace : WordTrace (prefixWord ++ tailWord_64579) baseStart_64579 baseEnd_64579 := by
    simpa [prefixWord, tailWord_64579, baseEnd_64579] using wordTrace_append hprefix tailTrace_64579
  have hstable : (prefixWord ++ tailWord_64579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64579).length < 2 ^ (prefixWord ++ tailWord_64579).sum := by decide
  have hdescent : baseEnd_64579 < baseStart_64579 := by decide
  rcases family_descends (prefixWord ++ tailWord_64579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64589 : List Nat := [1, 6, 1, 1, 1, 4, 1, 2, 2, 4]
def baseStart_64589 : Nat := 118140960795 + 64589 * 2 ^ 59
def prefixEnd_64589 : Nat := 4983230072969 + 3 ^ 40 * 64589 * 2
def baseEnd_64589 : Nat := 11055067331117676313489

theorem tailTrace_64589 : CollatzResearch.WordTrace tailWord_64589 prefixEnd_64589 11055067331117676313489 := by
  unfold tailWord_64589
  simp only [CollatzResearch.WordTrace]
  refine ⟨2355754363012558768092821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1570502908675039178728547 2355754363012558768092821)
  ·
    refine ⟨110425985766213692254351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2355754363012558768092821 110425985766213692254351)
    ·
      refine ⟨165638978649320538381527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110425985766213692254351 165638978649320538381527)
      ·
        refine ⟨248458467973980807572291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165638978649320538381527 248458467973980807572291)
        ·
          refine ⟨372687701960971211358437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248458467973980807572291 372687701960971211358437)
          ·
            refine ⟨69878944117682102129707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 372687701960971211358437 69878944117682102129707)
            ·
              refine ⟨104818416176523153194561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69878944117682102129707 104818416176523153194561)
              ·
                refine ⟨78613812132392364895921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104818416176523153194561 78613812132392364895921)
                ·
                  refine ⟨58960359099294273671941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78613812132392364895921 58960359099294273671941)
                  ·
                    refine ⟨11055067331117676313489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58960359099294273671941 11055067331117676313489)
                    ·
                      rfl

theorem cell23_64589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_64589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64589 prefixEnd_64589 := by exact prefixLift 64589
  have htrace : WordTrace (prefixWord ++ tailWord_64589) baseStart_64589 baseEnd_64589 := by
    simpa [prefixWord, tailWord_64589, baseEnd_64589] using wordTrace_append hprefix tailTrace_64589
  have hstable : (prefixWord ++ tailWord_64589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64589).length < 2 ^ (prefixWord ++ tailWord_64589).sum := by decide
  have hdescent : baseEnd_64589 < baseStart_64589 := by decide
  rcases family_descends (prefixWord ++ tailWord_64589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64591 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 7]
def baseStart_64591 : Nat := 118140960795 + 64591 * 2 ^ 59
def prefixEnd_64591 : Nat := 4983230072969 + 3 ^ 40 * 64591 * 2
def baseEnd_64591 : Nat := 33166228954662021115457

theorem tailTrace_64591 : CollatzResearch.WordTrace tailWord_64591 prefixEnd_64591 33166228954662021115457 := by
  unfold tailWord_64591
  simp only [CollatzResearch.WordTrace]
  refine ⟨2355827309005313109665627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1570551539336875406443751 2355827309005313109665627)
  ·
    refine ⟨3533740963507969664498441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2355827309005313109665627 3533740963507969664498441)
    ·
      refine ⟨2650305722630977248373831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3533740963507969664498441 2650305722630977248373831)
      ·
        refine ⟨3975458583946465872560747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2650305722630977248373831 3975458583946465872560747)
        ·
          refine ⟨5963187875919698808841121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3975458583946465872560747 5963187875919698808841121)
          ·
            refine ⟨4472390906939774106630841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5963187875919698808841121 4472390906939774106630841)
            ·
              refine ⟨3354293180204830579973131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4472390906939774106630841 3354293180204830579973131)
              ·
                refine ⟨5031439770307245869959697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3354293180204830579973131 5031439770307245869959697)
                ·
                  refine ⟨3773579827730434402469773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5031439770307245869959697 3773579827730434402469773)
                  ·
                    refine ⟨1415092435398912900926165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3773579827730434402469773 1415092435398912900926165)
                    ·
                      refine ⟨33166228954662021115457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 1415092435398912900926165 33166228954662021115457)
                      ·
                        rfl

theorem cell23_64591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 7].length) (baseStart_64591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64591 prefixEnd_64591 := by exact prefixLift 64591
  have htrace : WordTrace (prefixWord ++ tailWord_64591) baseStart_64591 baseEnd_64591 := by
    simpa [prefixWord, tailWord_64591, baseEnd_64591] using wordTrace_append hprefix tailTrace_64591
  have hstable : (prefixWord ++ tailWord_64591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64591).length < 2 ^ (prefixWord ++ tailWord_64591).sum := by decide
  have hdescent : baseEnd_64591 < baseStart_64591 := by decide
  rcases family_descends (prefixWord ++ tailWord_64591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64635 : List Nat := [1, 1, 1, 1, 1, 4, 1, 6, 1, 4, 2]
def baseStart_64635 : Nat := 118140960795 + 64635 * 2 ^ 59
def prefixEnd_64635 : Nat := 4983230072969 + 3 ^ 40 * 64635 * 2
def baseEnd_64635 : Nat := 33188822103459848965255

theorem tailTrace_64635 : CollatzResearch.WordTrace tailWord_64635 prefixEnd_64635 33188822103459848965255 := by
  unfold tailWord_64635
  simp only [CollatzResearch.WordTrace]
  refine ⟨2357432120845908624267359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1571621413897272416178239 2357432120845908624267359)
  ·
    refine ⟨3536148181268862936401039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2357432120845908624267359 3536148181268862936401039)
    ·
      refine ⟨5304222271903294404601559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3536148181268862936401039 5304222271903294404601559)
      ·
        refine ⟨7956333407854941606902339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5304222271903294404601559 7956333407854941606902339)
        ·
          refine ⟨11934500111782412410353509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7956333407854941606902339 11934500111782412410353509)
          ·
            refine ⟨2237718770959202326941283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11934500111782412410353509 2237718770959202326941283)
            ·
              refine ⟨3356578156438803490411925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2237718770959202326941283 3356578156438803490411925)
              ·
                refine ⟨157339601083068913613059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3356578156438803490411925 157339601083068913613059)
                ·
                  refine ⟨236009401624603370419589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157339601083068913613059 236009401624603370419589)
                  ·
                    refine ⟨44251762804613131953673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 236009401624603370419589 44251762804613131953673)
                    ·
                      refine ⟨33188822103459848965255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 44251762804613131953673 33188822103459848965255)
                      ·
                        rfl

theorem cell23_64635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 4, 2].length) (baseStart_64635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64635 prefixEnd_64635 := by exact prefixLift 64635
  have htrace : WordTrace (prefixWord ++ tailWord_64635) baseStart_64635 baseEnd_64635 := by
    simpa [prefixWord, tailWord_64635, baseEnd_64635] using wordTrace_append hprefix tailTrace_64635
  have hstable : (prefixWord ++ tailWord_64635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64635).length < 2 ^ (prefixWord ++ tailWord_64635).sum := by decide
  have hdescent : baseEnd_64635 < baseStart_64635 := by decide
  rcases family_descends (prefixWord ++ tailWord_64635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64669 : List Nat := [1, 4, 2, 1, 1, 2, 3, 3, 2, 2, 2]
def baseStart_64669 : Nat := 118140960795 + 64669 * 2 ^ 59
def prefixEnd_64669 : Nat := 4983230072969 + 3 ^ 40 * 64669 * 2
def baseEnd_64669 : Nat := 33206280445712715940099

theorem tailTrace_64669 : CollatzResearch.WordTrace tailWord_64669 prefixEnd_64669 33206280445712715940099 := by
  unfold tailWord_64669
  simp only [CollatzResearch.WordTrace]
  refine ⟨2358672202722732431005061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1572448135148488287336707 2358672202722732431005061)
  ·
    refine ⟨442251038010512330813449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2358672202722732431005061 442251038010512330813449)
    ·
      refine ⟨331688278507884248110087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442251038010512330813449 331688278507884248110087)
      ·
        refine ⟨497532417761826372165131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331688278507884248110087 497532417761826372165131)
        ·
          refine ⟨746298626642739558247697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497532417761826372165131 746298626642739558247697)
          ·
            refine ⟨559723969982054668685773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 746298626642739558247697 559723969982054668685773)
            ·
              refine ⟨209896488743270500757165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 559723969982054668685773 209896488743270500757165)
              ·
                refine ⟨78711183278726437783937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209896488743270500757165 78711183278726437783937)
                ·
                  refine ⟨59033387459044828337953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78711183278726437783937 59033387459044828337953)
                  ·
                    refine ⟨44275040594283621253465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59033387459044828337953 44275040594283621253465)
                    ·
                      refine ⟨33206280445712715940099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 44275040594283621253465 33206280445712715940099)
                      ·
                        rfl

theorem cell23_64669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_64669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64669 prefixEnd_64669 := by exact prefixLift 64669
  have htrace : WordTrace (prefixWord ++ tailWord_64669) baseStart_64669 baseEnd_64669 := by
    simpa [prefixWord, tailWord_64669, baseEnd_64669] using wordTrace_append hprefix tailTrace_64669
  have hstable : (prefixWord ++ tailWord_64669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64669).length < 2 ^ (prefixWord ++ tailWord_64669).sum := by decide
  have hdescent : baseEnd_64669 < baseStart_64669 := by decide
  rcases family_descends (prefixWord ++ tailWord_64669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64688 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 6, 5]
def baseStart_64688 : Nat := 118140960795 + 64688 * 2 ^ 59
def prefixEnd_64688 : Nat := 4983230072969 + 3 ^ 40 * 64688 * 2
def baseEnd_64688 : Nat := 11072012192716047200837

theorem tailTrace_64688 : CollatzResearch.WordTrace tailWord_64688 prefixEnd_64688 11072012192716047200837 := by
  unfold tailWord_64688
  simp only [CollatzResearch.WordTrace]
  refine ⟨1179682594826949337973359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1572910126435932450631145 1179682594826949337973359)
  ·
    refine ⟨1769523892240424006960039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1179682594826949337973359 1769523892240424006960039)
    ·
      refine ⟨2654285838360636010440059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1769523892240424006960039 2654285838360636010440059)
      ·
        refine ⟨3981428757540954015660089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2654285838360636010440059 3981428757540954015660089)
        ·
          refine ⟨2986071568155715511745067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3981428757540954015660089 2986071568155715511745067)
          ·
            refine ⟨4479107352233573267617601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2986071568155715511745067 4479107352233573267617601)
            ·
              refine ⟨3359330514175179950713201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4479107352233573267617601 3359330514175179950713201)
              ·
                refine ⟨2519497885631384963034901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3359330514175179950713201 2519497885631384963034901)
                ·
                  refine ⟨118101463388971170142261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2519497885631384963034901 118101463388971170142261)
                  ·
                    refine ⟨11072012192716047200837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 118101463388971170142261 11072012192716047200837)
                    ·
                      rfl

theorem cell23_64688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 6, 5].length) (baseStart_64688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64688 prefixEnd_64688 := by exact prefixLift 64688
  have htrace : WordTrace (prefixWord ++ tailWord_64688) baseStart_64688 baseEnd_64688 := by
    simpa [prefixWord, tailWord_64688, baseEnd_64688] using wordTrace_append hprefix tailTrace_64688
  have hstable : (prefixWord ++ tailWord_64688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64688).length < 2 ^ (prefixWord ++ tailWord_64688).sum := by decide
  have hdescent : baseEnd_64688 < baseStart_64688 := by decide
  rcases family_descends (prefixWord ++ tailWord_64688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64735 : List Nat := [1, 1, 2, 3, 2, 1, 3, 1, 5, 4]
def baseStart_64735 : Nat := 118140960795 + 64735 * 2 ^ 59
def prefixEnd_64735 : Nat := 4983230072969 + 3 ^ 40 * 64735 * 2
def baseEnd_64735 : Nat := 11080056722969819238265

theorem tailTrace_64735 : CollatzResearch.WordTrace tailWord_64735 prefixEnd_64735 11080056722969819238265 := by
  unfold tailWord_64735
  simp only [CollatzResearch.WordTrace]
  refine ⟨2361079420483625702907659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1574052946989083801938439 2361079420483625702907659)
  ·
    refine ⟨3541619130725438554361489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2361079420483625702907659 3541619130725438554361489)
    ·
      refine ⟨2656214348044078915771117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3541619130725438554361489 2656214348044078915771117)
      ·
        refine ⟨996080380516529593414169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2656214348044078915771117 996080380516529593414169)
        ·
          refine ⟨747060285387397195060627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 996080380516529593414169 747060285387397195060627)
          ·
            refine ⟨1120590428081095792590941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747060285387397195060627 1120590428081095792590941)
            ·
              refine ⟨420221410530410922221603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1120590428081095792590941 420221410530410922221603)
              ·
                refine ⟨630332115795616383332405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420221410530410922221603 630332115795616383332405)
                ·
                  refine ⟨59093635855839035937413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 630332115795616383332405 59093635855839035937413)
                  ·
                    refine ⟨11080056722969819238265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59093635855839035937413 11080056722969819238265)
                    ·
                      rfl

theorem cell23_64735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 5, 4].length) (baseStart_64735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64735 prefixEnd_64735 := by exact prefixLift 64735
  have htrace : WordTrace (prefixWord ++ tailWord_64735) baseStart_64735 baseEnd_64735 := by
    simpa [prefixWord, tailWord_64735, baseEnd_64735] using wordTrace_append hprefix tailTrace_64735
  have hstable : (prefixWord ++ tailWord_64735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64735).length < 2 ^ (prefixWord ++ tailWord_64735).sum := by decide
  have hdescent : baseEnd_64735 < baseStart_64735 := by decide
  rcases family_descends (prefixWord ++ tailWord_64735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64769 : List Nat := [1, 2, 4, 1, 1, 3, 2, 4, 1, 4]
def baseStart_64769 : Nat := 118140960795 + 64769 * 2 ^ 59
def prefixEnd_64769 : Nat := 4983230072969 + 3 ^ 40 * 64769 * 2
def baseEnd_64769 : Nat := 11085876170387441563213

theorem tailTrace_64769 : CollatzResearch.WordTrace tailWord_64769 prefixEnd_64769 11085876170387441563213 := by
  unfold tailWord_64769
  simp only [CollatzResearch.WordTrace]
  refine ⟨2362319502360449509645361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1574879668240299673096907 2362319502360449509645361)
  ·
    refine ⟨1771739626770337132234021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2362319502360449509645361 1771739626770337132234021)
    ·
      refine ⟨332201180019438212293879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1771739626770337132234021 332201180019438212293879)
      ·
        refine ⟨498301770029157318440819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332201180019438212293879 498301770029157318440819)
        ·
          refine ⟨747452655043735977661229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498301770029157318440819 747452655043735977661229)
          ·
            refine ⟨280294745641400991622961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 747452655043735977661229 280294745641400991622961)
            ·
              refine ⟨210221059231050743717221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280294745641400991622961 210221059231050743717221)
              ·
                refine ⟨39416448605822014446979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210221059231050743717221 39416448605822014446979)
                ·
                  refine ⟨59124672908733021670469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39416448605822014446979 59124672908733021670469)
                  ·
                    refine ⟨11085876170387441563213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59124672908733021670469 11085876170387441563213)
                    ·
                      rfl

theorem cell23_64769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_64769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64769 prefixEnd_64769 := by exact prefixLift 64769
  have htrace : WordTrace (prefixWord ++ tailWord_64769) baseStart_64769 baseEnd_64769 := by
    simpa [prefixWord, tailWord_64769, baseEnd_64769] using wordTrace_append hprefix tailTrace_64769
  have hstable : (prefixWord ++ tailWord_64769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64769).length < 2 ^ (prefixWord ++ tailWord_64769).sum := by decide
  have hdescent : baseEnd_64769 < baseStart_64769 := by decide
  rcases family_descends (prefixWord ++ tailWord_64769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64815 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 4]
def baseStart_64815 : Nat := 118140960795 + 64815 * 2 ^ 59
def prefixEnd_64815 : Nat := 4983230072969 + 3 ^ 40 * 64815 * 2
def baseEnd_64815 : Nat := 33281248621269144714427

theorem tailTrace_64815 : CollatzResearch.WordTrace tailWord_64815 prefixEnd_64815 33281248621269144714427 := by
  unfold tailWord_64815
  simp only [CollatzResearch.WordTrace]
  refine ⟨2363997260193799365819899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1575998173462532910546599 2363997260193799365819899)
  ·
    refine ⟨3545995890290699048729849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2363997260193799365819899 3545995890290699048729849)
    ·
      refine ⟨2659496917718024286547387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3545995890290699048729849 2659496917718024286547387)
      ·
        refine ⟨3989245376577036429821081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2659496917718024286547387 3989245376577036429821081)
        ·
          refine ⟨2991934032432777322365811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3989245376577036429821081 2991934032432777322365811)
          ·
            refine ⟨4487901048649165983548717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2991934032432777322365811 4487901048649165983548717)
            ·
              refine ⟨1682962893243437243830769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4487901048649165983548717 1682962893243437243830769)
              ·
                refine ⟨1262222169932577932873077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1682962893243437243830769 1262222169932577932873077)
                ·
                  refine ⟨118333328431179181206851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1262222169932577932873077 118333328431179181206851)
                  ·
                    refine ⟨177499992646768771810277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118333328431179181206851 177499992646768771810277)
                    ·
                      refine ⟨33281248621269144714427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 177499992646768771810277 33281248621269144714427)
                      ·
                        rfl

theorem cell23_64815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 4].length) (baseStart_64815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64815 prefixEnd_64815 := by exact prefixLift 64815
  have htrace : WordTrace (prefixWord ++ tailWord_64815) baseStart_64815 baseEnd_64815 := by
    simpa [prefixWord, tailWord_64815, baseEnd_64815] using wordTrace_append hprefix tailTrace_64815
  have hstable : (prefixWord ++ tailWord_64815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64815).length < 2 ^ (prefixWord ++ tailWord_64815).sum := by decide
  have hdescent : baseEnd_64815 < baseStart_64815 := by decide
  rcases family_descends (prefixWord ++ tailWord_64815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64819 : List Nat := [1, 1, 1, 2, 5, 3, 1, 2, 2, 3, 2]
def baseStart_64819 : Nat := 118140960795 + 64819 * 2 ^ 59
def prefixEnd_64819 : Nat := 4983230072969 + 3 ^ 40 * 64819 * 2
def baseEnd_64819 : Nat := 33283302543887129064409

theorem tailTrace_64819 : CollatzResearch.WordTrace tailWord_64819 prefixEnd_64819 33283302543887129064409 := by
  unfold tailWord_64819
  simp only [CollatzResearch.WordTrace]
  refine ⟨2364143152179308048965511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1576095434786205365977007 2364143152179308048965511)
  ·
    refine ⟨3546214728268962073448267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2364143152179308048965511 3546214728268962073448267)
    ·
      refine ⟨5319322092403443110172401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3546214728268962073448267 5319322092403443110172401)
      ·
        refine ⟨3989491569302582332629301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5319322092403443110172401 3989491569302582332629301)
        ·
          refine ⟨374014834622117093683997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3989491569302582332629301 374014834622117093683997)
          ·
            refine ⟨140255562983293910131499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 374014834622117093683997 140255562983293910131499)
            ·
              refine ⟨210383344474940865197249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140255562983293910131499 210383344474940865197249)
              ·
                refine ⟨157787508356205648897937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210383344474940865197249 157787508356205648897937)
                ·
                  refine ⟨118340631267154236673453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157787508356205648897937 118340631267154236673453)
                  ·
                    refine ⟨44377736725182838752545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118340631267154236673453 44377736725182838752545)
                    ·
                      refine ⟨33283302543887129064409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 44377736725182838752545 33283302543887129064409)
                      ·
                        rfl

theorem cell23_64819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 3, 2].length) (baseStart_64819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64819 prefixEnd_64819 := by exact prefixLift 64819
  have htrace : WordTrace (prefixWord ++ tailWord_64819) baseStart_64819 baseEnd_64819 := by
    simpa [prefixWord, tailWord_64819, baseEnd_64819] using wordTrace_append hprefix tailTrace_64819
  have hstable : (prefixWord ++ tailWord_64819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64819).length < 2 ^ (prefixWord ++ tailWord_64819).sum := by decide
  have hdescent : baseEnd_64819 < baseStart_64819 := by decide
  rcases family_descends (prefixWord ++ tailWord_64819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64835 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 2, 6, 3]
def baseStart_64835 : Nat := 118140960795 + 64835 * 2 ^ 59
def prefixEnd_64835 : Nat := 4983230072969 + 3 ^ 40 * 64835 * 2
def baseEnd_64835 : Nat := 33291518234359066464335

theorem tailTrace_64835 : CollatzResearch.WordTrace tailWord_64835 prefixEnd_64835 33291518234359066464335 := by
  unfold tailWord_64835
  simp only [CollatzResearch.WordTrace]
  refine ⟨2364726720121342781547959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1576484480080895187698639 2364726720121342781547959)
  ·
    refine ⟨3547090080182014172321939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2364726720121342781547959 3547090080182014172321939)
    ·
      refine ⟨5320635120273021258482909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3547090080182014172321939 5320635120273021258482909)
      ·
        refine ⟨1995238170102382971931091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5320635120273021258482909 1995238170102382971931091)
        ·
          refine ⟨2992857255153574457896637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1995238170102382971931091 2992857255153574457896637)
          ·
            refine ⟨1122321470682590421711239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2992857255153574457896637 1122321470682590421711239)
            ·
              refine ⟨1683482206023885632566859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1122321470682590421711239 1683482206023885632566859)
              ·
                refine ⟨2525223309035828448850289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1683482206023885632566859 2525223309035828448850289)
                ·
                  refine ⟨1893917481776871336637717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2525223309035828448850289 1893917481776871336637717)
                  ·
                    refine ⟨88777381958290843904893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1893917481776871336637717 88777381958290843904893)
                    ·
                      refine ⟨33291518234359066464335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 88777381958290843904893 33291518234359066464335)
                      ·
                        rfl

theorem cell23_64835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 6, 3].length) (baseStart_64835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64835 prefixEnd_64835 := by exact prefixLift 64835
  have htrace : WordTrace (prefixWord ++ tailWord_64835) baseStart_64835 baseEnd_64835 := by
    simpa [prefixWord, tailWord_64835, baseEnd_64835] using wordTrace_append hprefix tailTrace_64835
  have hstable : (prefixWord ++ tailWord_64835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64835).length < 2 ^ (prefixWord ++ tailWord_64835).sum := by decide
  have hdescent : baseEnd_64835 < baseStart_64835 := by decide
  rcases family_descends (prefixWord ++ tailWord_64835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64849 : List Nat := [1, 2, 2, 1, 4, 1, 2, 1, 5, 2, 2]
def baseStart_64849 : Nat := 118140960795 + 64849 * 2 ^ 59
def prefixEnd_64849 : Nat := 4983230072969 + 3 ^ 40 * 64849 * 2
def baseEnd_64849 : Nat := 33298706963522011689271

theorem tailTrace_64849 : CollatzResearch.WordTrace tailWord_64849 prefixEnd_64849 33298706963522011689271 := by
  unfold tailWord_64849
  simp only [CollatzResearch.WordTrace]
  refine ⟨2365237342070623172557601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1576824894713748781705067 2365237342070623172557601)
  ·
    refine ⟨1773928006552967379418201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2365237342070623172557601 1773928006552967379418201)
    ·
      refine ⟨1330446004914725534563651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1773928006552967379418201 1330446004914725534563651)
      ·
        refine ⟨1995669007372088301845477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1330446004914725534563651 1995669007372088301845477)
        ·
          refine ⟨374187938882266556596027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1995669007372088301845477 374187938882266556596027)
          ·
            refine ⟨561281908323399834894041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374187938882266556596027 561281908323399834894041)
            ·
              refine ⟨420961431242549876170531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 561281908323399834894041 420961431242549876170531)
              ·
                refine ⟨631442146863824814255797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420961431242549876170531 631442146863824814255797)
                ·
                  refine ⟨59197701268483576336481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 631442146863824814255797 59197701268483576336481)
                  ·
                    refine ⟨44398275951362682252361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59197701268483576336481 44398275951362682252361)
                    ·
                      refine ⟨33298706963522011689271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 44398275951362682252361 33298706963522011689271)
                      ·
                        rfl

theorem cell23_64849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 5, 2, 2].length) (baseStart_64849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64849 prefixEnd_64849 := by exact prefixLift 64849
  have htrace : WordTrace (prefixWord ++ tailWord_64849) baseStart_64849 baseEnd_64849 := by
    simpa [prefixWord, tailWord_64849, baseEnd_64849] using wordTrace_append hprefix tailTrace_64849
  have hstable : (prefixWord ++ tailWord_64849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64849).length < 2 ^ (prefixWord ++ tailWord_64849).sum := by decide
  have hdescent : baseEnd_64849 < baseStart_64849 := by decide
  rcases family_descends (prefixWord ++ tailWord_64849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64855 : List Nat := [1, 1, 3, 2, 3, 2, 2, 9]
def baseStart_64855 : Nat := 118140960795 + 64855 * 2 ^ 59
def prefixEnd_64855 : Nat := 4983230072969 + 3 ^ 40 * 64855 * 2
def baseEnd_64855 : Nat := 1233399549905518082009

theorem tailTrace_64855 : CollatzResearch.WordTrace tailWord_64855 prefixEnd_64855 1233399549905518082009 := by
  unfold tailWord_64855
  simp only [CollatzResearch.WordTrace]
  refine ⟨2365456180048886197276019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1576970786699257464850679 2365456180048886197276019)
  ·
    refine ⟨3548184270073329295914029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2365456180048886197276019 3548184270073329295914029)
    ·
      refine ⟨1330569101277498485967761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3548184270073329295914029 1330569101277498485967761)
      ·
        refine ⟨997926825958123864475821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1330569101277498485967761 997926825958123864475821)
        ·
          refine ⟨374222559734296449178433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 997926825958123864475821 374222559734296449178433)
          ·
            refine ⟨280666919800722336883825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374222559734296449178433 280666919800722336883825)
            ·
              refine ⟨210500189850541752662869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280666919800722336883825 210500189850541752662869)
              ·
                refine ⟨1233399549905518082009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 210500189850541752662869 1233399549905518082009)
                ·
                  rfl

theorem cell23_64855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 9].length) (baseStart_64855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64855 prefixEnd_64855 := by exact prefixLift 64855
  have htrace : WordTrace (prefixWord ++ tailWord_64855) baseStart_64855 baseEnd_64855 := by
    simpa [prefixWord, tailWord_64855, baseEnd_64855] using wordTrace_append hprefix tailTrace_64855
  have hstable : (prefixWord ++ tailWord_64855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64855).length < 2 ^ (prefixWord ++ tailWord_64855).sum := by decide
  have hdescent : baseEnd_64855 < baseStart_64855 := by decide
  rcases family_descends (prefixWord ++ tailWord_64855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64866 : List Nat := [3, 3, 2, 1, 1, 1, 5, 1, 1, 1, 4]
def baseStart_64866 : Nat := 118140960795 + 64866 * 2 ^ 59
def prefixEnd_64866 : Nat := 4983230072969 + 3 ^ 40 * 64866 * 2
def baseEnd_64866 : Nat := 33307436134648445176693

theorem tailTrace_64866 : CollatzResearch.WordTrace tailWord_64866 prefixEnd_64866 33307436134648445176693 := by
  unfold tailWord_64866
  simp only [CollatzResearch.WordTrace]
  refine ⟨591464345752258768981613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1577238255339356717284301 591464345752258768981613)
  ·
    refine ⟨221799129657097038368105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 591464345752258768981613 221799129657097038368105)
    ·
      refine ⟨166349347242822778776079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221799129657097038368105 166349347242822778776079)
      ·
        refine ⟨249524020864234168164119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166349347242822778776079 249524020864234168164119)
        ·
          refine ⟨374286031296351252246179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249524020864234168164119 374286031296351252246179)
          ·
            refine ⟨561429046944526878369269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374286031296351252246179 561429046944526878369269)
            ·
              refine ⟨52633973151049394847119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 561429046944526878369269 52633973151049394847119)
              ·
                refine ⟨78950959726574092270679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52633973151049394847119 78950959726574092270679)
                ·
                  refine ⟨118426439589861138406019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78950959726574092270679 118426439589861138406019)
                  ·
                    refine ⟨177639659384791707609029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118426439589861138406019 177639659384791707609029)
                    ·
                      refine ⟨33307436134648445176693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 177639659384791707609029 33307436134648445176693)
                      ·
                        rfl

theorem cell23_64866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_64866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64866 prefixEnd_64866 := by exact prefixLift 64866
  have htrace : WordTrace (prefixWord ++ tailWord_64866) baseStart_64866 baseEnd_64866 := by
    simpa [prefixWord, tailWord_64866, baseEnd_64866] using wordTrace_append hprefix tailTrace_64866
  have hstable : (prefixWord ++ tailWord_64866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64866).length < 2 ^ (prefixWord ++ tailWord_64866).sum := by decide
  have hdescent : baseEnd_64866 < baseStart_64866 := by decide
  rcases family_descends (prefixWord ++ tailWord_64866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64872 : List Nat := [2, 1, 4, 2, 4, 10]
def baseStart_64872 : Nat := 118140960795 + 64872 * 2 ^ 59
def prefixEnd_64872 : Nat := 4983230072969 + 3 ^ 40 * 64872 * 2
def baseEnd_64872 : Nat := 137080316948870048155

theorem tailTrace_64872 : CollatzResearch.WordTrace tailWord_64872 prefixEnd_64872 137080316948870048155 := by
  unfold tailWord_64872
  simp only [CollatzResearch.WordTrace]
  refine ⟨1183038110493649050322435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1577384147324865400429913 1183038110493649050322435)
  ·
    refine ⟨1774557165740473575483653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1183038110493649050322435 1774557165740473575483653)
    ·
      refine ⟨332729468576338795403185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1774557165740473575483653 332729468576338795403185)
      ·
        refine ⟨249547101432254096552389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332729468576338795403185 249547101432254096552389)
        ·
          refine ⟨46790081518547643103573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249547101432254096552389 46790081518547643103573)
          ·
            refine ⟨137080316948870048155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 46790081518547643103573 137080316948870048155)
            ·
              rfl

theorem cell23_64872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 10].length) (baseStart_64872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64872 prefixEnd_64872 := by exact prefixLift 64872
  have htrace : WordTrace (prefixWord ++ tailWord_64872) baseStart_64872 baseEnd_64872 := by
    simpa [prefixWord, tailWord_64872, baseEnd_64872] using wordTrace_append hprefix tailTrace_64872
  have hstable : (prefixWord ++ tailWord_64872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64872).length < 2 ^ (prefixWord ++ tailWord_64872).sum := by decide
  have hdescent : baseEnd_64872 < baseStart_64872 := by decide
  rcases family_descends (prefixWord ++ tailWord_64872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64882 : List Nat := [3, 2, 1, 2, 1, 2, 1, 2, 3, 3, 3]
def baseStart_64882 : Nat := 118140960795 + 64882 * 2 ^ 59
def prefixEnd_64882 : Nat := 4983230072969 + 3 ^ 40 * 64882 * 2
def baseEnd_64882 : Nat := 33315651825120382576619

theorem tailTrace_64882 : CollatzResearch.WordTrace tailWord_64882 prefixEnd_64882 33315651825120382576619 := by
  unfold tailWord_64882
  simp only [CollatzResearch.WordTrace]
  refine ⟨591610237737767452127225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1577627300634046539005933 591610237737767452127225)
  ·
    refine ⟨443707678303325589095419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 591610237737767452127225 443707678303325589095419)
    ·
      refine ⟨665561517454988383643129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443707678303325589095419 665561517454988383643129)
      ·
        refine ⟨499171138091241287732347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 665561517454988383643129 499171138091241287732347)
        ·
          refine ⟨748756707136861931598521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499171138091241287732347 748756707136861931598521)
          ·
            refine ⟨561567530352646448698891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 748756707136861931598521 561567530352646448698891)
            ·
              refine ⟨842351295528969673048337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561567530352646448698891 842351295528969673048337)
              ·
                refine ⟨631763471646727254786253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 842351295528969673048337 631763471646727254786253)
                ·
                  refine ⟨236911301867522720544845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 631763471646727254786253 236911301867522720544845)
                  ·
                    refine ⟨88841738200321020204317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 236911301867522720544845 88841738200321020204317)
                    ·
                      refine ⟨33315651825120382576619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 88841738200321020204317 33315651825120382576619)
                      ·
                        rfl

theorem cell23_64882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_64882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64882 prefixEnd_64882 := by exact prefixLift 64882
  have htrace : WordTrace (prefixWord ++ tailWord_64882) baseStart_64882 baseEnd_64882 := by
    simpa [prefixWord, tailWord_64882, baseEnd_64882] using wordTrace_append hprefix tailTrace_64882
  have hstable : (prefixWord ++ tailWord_64882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64882).length < 2 ^ (prefixWord ++ tailWord_64882).sum := by decide
  have hdescent : baseEnd_64882 < baseStart_64882 := by decide
  rcases family_descends (prefixWord ++ tailWord_64882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64899 : List Nat := [1, 1, 1, 3, 5, 2, 2, 1, 1, 3, 3]
def baseStart_64899 : Nat := 118140960795 + 64899 * 2 ^ 59
def prefixEnd_64899 : Nat := 4983230072969 + 3 ^ 40 * 64899 * 2
def baseEnd_64899 : Nat := 33324380996246816064041

theorem tailTrace_64899 : CollatzResearch.WordTrace tailWord_64899 prefixEnd_64899 33324380996246816064041 := by
  unfold tailWord_64899
  simp only [CollatzResearch.WordTrace]
  refine ⟨2367060991889481711877751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1578040661259654474585167 2367060991889481711877751)
  ·
    refine ⟨3550591487834222567816627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2367060991889481711877751 3550591487834222567816627)
    ·
      refine ⟨5325887231751333851724941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3550591487834222567816627 5325887231751333851724941)
      ·
        refine ⟨1997207711906750194396853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5325887231751333851724941 1997207711906750194396853)
        ·
          refine ⟨187238222991257830724705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1997207711906750194396853 187238222991257830724705)
          ·
            refine ⟨140428667243443373043529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187238222991257830724705 140428667243443373043529)
            ·
              refine ⟨105321500432582529782647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140428667243443373043529 105321500432582529782647)
              ·
                refine ⟨157982250648873794673971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105321500432582529782647 157982250648873794673971)
                ·
                  refine ⟨236973375973310692010957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157982250648873794673971 236973375973310692010957)
                  ·
                    refine ⟨88865015989991509504109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 236973375973310692010957 88865015989991509504109)
                    ·
                      refine ⟨33324380996246816064041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 88865015989991509504109 33324380996246816064041)
                      ·
                        rfl

theorem cell23_64899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 3, 3].length) (baseStart_64899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64899 prefixEnd_64899 := by exact prefixLift 64899
  have htrace : WordTrace (prefixWord ++ tailWord_64899) baseStart_64899 baseEnd_64899 := by
    simpa [prefixWord, tailWord_64899, baseEnd_64899] using wordTrace_append hprefix tailTrace_64899
  have hstable : (prefixWord ++ tailWord_64899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64899).length < 2 ^ (prefixWord ++ tailWord_64899).sum := by decide
  have hdescent : baseEnd_64899 < baseStart_64899 := by decide
  rcases family_descends (prefixWord ++ tailWord_64899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64920 : List Nat := [2, 1, 2, 5, 3, 1, 2, 1, 1, 2, 3]
def baseStart_64920 : Nat := 118140960795 + 64920 * 2 ^ 59
def prefixEnd_64920 : Nat := 4983230072969 + 3 ^ 40 * 64920 * 2
def baseEnd_64920 : Nat := 33335164089991233901445

theorem tailTrace_64920 : CollatzResearch.WordTrace tailWord_64920 prefixEnd_64920 33335164089991233901445 := by
  unfold tailWord_64920
  simp only [CollatzResearch.WordTrace]
  refine ⟨1183913462406701149196107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1578551283208934865594809 1183913462406701149196107)
  ·
    refine ⟨1775870193610051723794161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1183913462406701149196107 1775870193610051723794161)
    ·
      refine ⟨1331902645207538792845621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1775870193610051723794161 1331902645207538792845621)
      ·
        refine ⟨124865872988206761829277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1331902645207538792845621 124865872988206761829277)
        ·
          refine ⟨46824702370577535685979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124865872988206761829277 46824702370577535685979)
          ·
            refine ⟨70237053555866303528969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46824702370577535685979 70237053555866303528969)
            ·
              refine ⟨52677790166899727646727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70237053555866303528969 52677790166899727646727)
              ·
                refine ⟨79016685250349591470091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52677790166899727646727 79016685250349591470091)
                ·
                  refine ⟨118525027875524387205137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79016685250349591470091 118525027875524387205137)
                  ·
                    refine ⟨88893770906643290403853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118525027875524387205137 88893770906643290403853)
                    ·
                      refine ⟨33335164089991233901445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 88893770906643290403853 33335164089991233901445)
                      ·
                        rfl

theorem cell23_64920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_64920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64920 prefixEnd_64920 := by exact prefixLift 64920
  have htrace : WordTrace (prefixWord ++ tailWord_64920) baseStart_64920 baseEnd_64920 := by
    simpa [prefixWord, tailWord_64920, baseEnd_64920] using wordTrace_append hprefix tailTrace_64920
  have hstable : (prefixWord ++ tailWord_64920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64920).length < 2 ^ (prefixWord ++ tailWord_64920).sum := by decide
  have hdescent : baseEnd_64920 < baseStart_64920 := by decide
  rcases family_descends (prefixWord ++ tailWord_64920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64952 : List Nat := [2, 1, 2, 1, 2, 2, 4, 1, 2, 2, 4]
def baseStart_64952 : Nat := 118140960795 + 64952 * 2 ^ 59
def prefixEnd_64952 : Nat := 4983230072969 + 3 ^ 40 * 64952 * 2
def baseEnd_64952 : Nat := 33351595470935108701297

theorem tailTrace_64952 : CollatzResearch.WordTrace tailWord_64952 prefixEnd_64952 33351595470935108701297 := by
  unfold tailWord_64952
  simp only [CollatzResearch.WordTrace]
  refine ⟨1184497030348735881778555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1579329373798314509038073 1184497030348735881778555)
  ·
    refine ⟨1776745545523103822667833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1184497030348735881778555 1776745545523103822667833)
    ·
      refine ⟨1332559159142327867000875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1776745545523103822667833 1332559159142327867000875)
      ·
        refine ⟨1998838738713491800501313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1332559159142327867000875 1998838738713491800501313)
        ·
          refine ⟨1499129054035118850375985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1998838738713491800501313 1499129054035118850375985)
          ·
            refine ⟨1124346790526339137781989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1499129054035118850375985 1124346790526339137781989)
            ·
              refine ⟨210815023223688588334123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1124346790526339137781989 210815023223688588334123)
              ·
                refine ⟨316222534835532882501185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210815023223688588334123 316222534835532882501185)
                ·
                  refine ⟨237166901126649661875889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316222534835532882501185 237166901126649661875889)
                  ·
                    refine ⟨177875175844987246406917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 237166901126649661875889 177875175844987246406917)
                    ·
                      refine ⟨33351595470935108701297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 177875175844987246406917 33351595470935108701297)
                      ·
                        rfl

theorem cell23_64952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_64952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_64952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_64952 prefixEnd_64952 := by exact prefixLift 64952
  have htrace : WordTrace (prefixWord ++ tailWord_64952) baseStart_64952 baseEnd_64952 := by
    simpa [prefixWord, tailWord_64952, baseEnd_64952] using wordTrace_append hprefix tailTrace_64952
  have hstable : (prefixWord ++ tailWord_64952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64952).length < 2 ^ (prefixWord ++ tailWord_64952).sum := by decide
  have hdescent : baseEnd_64952 < baseStart_64952 := by decide
  rcases family_descends (prefixWord ++ tailWord_64952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65026 : List Nat := [3, 4, 1, 2, 1, 1, 1, 3, 2, 5]
def baseStart_65026 : Nat := 118140960795 + 65026 * 2 ^ 59
def prefixEnd_65026 : Nat := 4983230072969 + 3 ^ 40 * 65026 * 2
def baseEnd_65026 : Nat := 11129864346455939725319

theorem tailTrace_65026 : CollatzResearch.WordTrace tailWord_65026 prefixEnd_65026 11129864346455939725319 := by
  unfold tailWord_65026
  simp only [CollatzResearch.WordTrace]
  refine ⟨592923265607345600437733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1581128708286254934500621 592923265607345600437733)
  ·
    refine ⟨111173112301377300082075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 592923265607345600437733 111173112301377300082075)
    ·
      refine ⟨166759668452065950123113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111173112301377300082075 166759668452065950123113)
      ·
        refine ⟨125069751339049462592335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166759668452065950123113 125069751339049462592335)
        ·
          refine ⟨187604627008574193888503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125069751339049462592335 187604627008574193888503)
          ·
            refine ⟨281406940512861290832755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187604627008574193888503 281406940512861290832755)
            ·
              refine ⟨422110410769291936249133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281406940512861290832755 422110410769291936249133)
              ·
                refine ⟨158291404038484476093425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 422110410769291936249133 158291404038484476093425)
                ·
                  refine ⟨118718553028863357070069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158291404038484476093425 118718553028863357070069)
                  ·
                    refine ⟨11129864346455939725319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 118718553028863357070069 11129864346455939725319)
                    ·
                      rfl

theorem cell23_65026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_65026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65026 prefixEnd_65026 := by exact prefixLift 65026
  have htrace : WordTrace (prefixWord ++ tailWord_65026) baseStart_65026 baseEnd_65026 := by
    simpa [prefixWord, tailWord_65026, baseEnd_65026] using wordTrace_append hprefix tailTrace_65026
  have hstable : (prefixWord ++ tailWord_65026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65026).length < 2 ^ (prefixWord ++ tailWord_65026).sum := by decide
  have hdescent : baseEnd_65026 < baseStart_65026 := by decide
  rcases family_descends (prefixWord ++ tailWord_65026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65029 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 4, 4, 2]
def baseStart_65029 : Nat := 118140960795 + 65029 * 2 ^ 59
def prefixEnd_65029 : Nat := 4983230072969 + 3 ^ 40 * 65029 * 2
def baseEnd_65029 : Nat := 33391133481331307438443

theorem tailTrace_65029 : CollatzResearch.WordTrace tailWord_65029 prefixEnd_65029 33391133481331307438443 := by
  unfold tailWord_65029
  simp only [CollatzResearch.WordTrace]
  refine ⟨2371802481418513914110141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1581201654279009276073427 2371802481418513914110141)
  ·
    refine ⟨889425930531942717791303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2371802481418513914110141 889425930531942717791303)
    ·
      refine ⟨1334138895797914076686955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 889425930531942717791303 1334138895797914076686955)
      ·
        refine ⟨2001208343696871115030433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1334138895797914076686955 2001208343696871115030433)
        ·
          refine ⟨1500906257772653336272825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2001208343696871115030433 1500906257772653336272825)
          ·
            refine ⟨1125679693329490002204619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1500906257772653336272825 1125679693329490002204619)
            ·
              refine ⟨1688519539994235003306929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1125679693329490002204619 1688519539994235003306929)
              ·
                refine ⟨1266389654995676252480197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1688519539994235003306929 1266389654995676252480197)
                ·
                  refine ⟨237448060311689297340037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1266389654995676252480197 237448060311689297340037)
                  ·
                    refine ⟨44521511308441743251257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 237448060311689297340037 44521511308441743251257)
                    ·
                      refine ⟨33391133481331307438443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 44521511308441743251257 33391133481331307438443)
                      ·
                        rfl

theorem cell23_65029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 4, 2].length) (baseStart_65029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65029 prefixEnd_65029 := by exact prefixLift 65029
  have htrace : WordTrace (prefixWord ++ tailWord_65029) baseStart_65029 baseEnd_65029 := by
    simpa [prefixWord, tailWord_65029, baseEnd_65029] using wordTrace_append hprefix tailTrace_65029
  have hstable : (prefixWord ++ tailWord_65029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65029).length < 2 ^ (prefixWord ++ tailWord_65029).sum := by decide
  have hdescent : baseEnd_65029 < baseStart_65029 := by decide
  rcases family_descends (prefixWord ++ tailWord_65029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65129 : List Nat := [1, 2, 1, 1, 1, 4, 5, 1, 1, 6]
def baseStart_65129 : Nat := 118140960795 + 65129 * 2 ^ 59
def prefixEnd_65129 : Nat := 4983230072969 + 3 ^ 40 * 65129 * 2
def baseEnd_65129 : Nat := 11147493848926972062661

theorem tailTrace_65129 : CollatzResearch.WordTrace tailWord_65129 prefixEnd_65129 11147493848926972062661 := by
  unfold tailWord_65129
  simp only [CollatzResearch.WordTrace]
  refine ⟨2375449781056230992750441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1583633187370820661833627 2375449781056230992750441)
  ·
    refine ⟨1781587335792173244562831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2375449781056230992750441 1781587335792173244562831)
    ·
      refine ⟨2672381003688259866844247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1781587335792173244562831 2672381003688259866844247)
      ·
        refine ⟨4008571505532389800266371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2672381003688259866844247 4008571505532389800266371)
        ·
          refine ⟨6012857258298584700399557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4008571505532389800266371 6012857258298584700399557)
          ·
            refine ⟨1127410735930984631324917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6012857258298584700399557 1127410735930984631324917)
            ·
              refine ⟨105694756493529809186711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1127410735930984631324917 105694756493529809186711)
              ·
                refine ⟨158542134740294713780067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105694756493529809186711 158542134740294713780067)
                ·
                  refine ⟨237813202110442070670101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158542134740294713780067 237813202110442070670101)
                  ·
                    refine ⟨11147493848926972062661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 237813202110442070670101 11147493848926972062661)
                    ·
                      rfl

theorem cell23_65129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 6].length) (baseStart_65129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65129 prefixEnd_65129 := by exact prefixLift 65129
  have htrace : WordTrace (prefixWord ++ tailWord_65129) baseStart_65129 baseEnd_65129 := by
    simpa [prefixWord, tailWord_65129, baseEnd_65129] using wordTrace_append hprefix tailTrace_65129
  have hstable : (prefixWord ++ tailWord_65129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65129).length < 2 ^ (prefixWord ++ tailWord_65129).sum := by decide
  have hdescent : baseEnd_65129 < baseStart_65129 := by decide
  rcases family_descends (prefixWord ++ tailWord_65129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65133 : List Nat := [1, 5, 1, 1, 4, 1, 2, 2, 1, 5]
def baseStart_65133 : Nat := 118140960795 + 65133 * 2 ^ 59
def prefixEnd_65133 : Nat := 4983230072969 + 3 ^ 40 * 65133 * 2
def baseEnd_65133 : Nat := 11148178489799633512655

theorem tailTrace_65133 : CollatzResearch.WordTrace tailWord_65133 prefixEnd_65133 11148178489799633512655 := by
  unfold tailWord_65133
  simp only [CollatzResearch.WordTrace]
  refine ⟨2375595673041739675896053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1583730448694493117264035 2375595673041739675896053)
  ·
    refine ⟨222712094347663094615255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2375595673041739675896053 222712094347663094615255)
    ·
      refine ⟨334068141521494641922883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222712094347663094615255 334068141521494641922883)
      ·
        refine ⟨501102212282241962884325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334068141521494641922883 501102212282241962884325)
        ·
          refine ⟨93956664802920368040811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 501102212282241962884325 93956664802920368040811)
          ·
            refine ⟨140934997204380552061217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93956664802920368040811 140934997204380552061217)
            ·
              refine ⟨105701247903285414045913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140934997204380552061217 105701247903285414045913)
              ·
                refine ⟨79275935927464060534435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105701247903285414045913 79275935927464060534435)
                ·
                  refine ⟨118913903891196090801653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79275935927464060534435 118913903891196090801653)
                  ·
                    refine ⟨11148178489799633512655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 118913903891196090801653 11148178489799633512655)
                    ·
                      rfl

theorem cell23_65133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_65133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65133 prefixEnd_65133 := by exact prefixLift 65133
  have htrace : WordTrace (prefixWord ++ tailWord_65133) baseStart_65133 baseEnd_65133 := by
    simpa [prefixWord, tailWord_65133, baseEnd_65133] using wordTrace_append hprefix tailTrace_65133
  have hstable : (prefixWord ++ tailWord_65133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65133).length < 2 ^ (prefixWord ++ tailWord_65133).sum := by decide
  have hdescent : baseEnd_65133 < baseStart_65133 := by decide
  rcases family_descends (prefixWord ++ tailWord_65133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65136 : List Nat := [2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 4]
def baseStart_65136 : Nat := 118140960795 + 65136 * 2 ^ 59
def prefixEnd_65136 : Nat := 4983230072969 + 3 ^ 40 * 65136 * 2
def baseEnd_65136 : Nat := 33446075911362388800451

theorem tailTrace_65136 : CollatzResearch.WordTrace tailWord_65136 prefixEnd_65136 33446075911362388800451 := by
  unfold tailWord_65136
  simp only [CollatzResearch.WordTrace]
  refine ⟨1187852546015435594127631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1583803394687247458836841 1187852546015435594127631)
  ·
    refine ⟨1781778819023153391191447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1187852546015435594127631 1781778819023153391191447)
    ·
      refine ⟨2672668228534730086787171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1781778819023153391191447 2672668228534730086787171)
      ·
        refine ⟨4009002342802095130180757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2672668228534730086787171 4009002342802095130180757)
        ·
          refine ⟨187921984818848209227223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4009002342802095130180757 187921984818848209227223)
          ·
            refine ⟨281882977228272313840835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187921984818848209227223 281882977228272313840835)
            ·
              refine ⟨422824465842408470761253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281882977228272313840835 422824465842408470761253)
              ·
                refine ⟨79279587345451588267735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 422824465842408470761253 79279587345451588267735)
                ·
                  refine ⟨118919381018177382401603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79279587345451588267735 118919381018177382401603)
                  ·
                    refine ⟨178379071527266073602405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118919381018177382401603 178379071527266073602405)
                    ·
                      refine ⟨33446075911362388800451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 178379071527266073602405 33446075911362388800451)
                      ·
                        rfl

theorem cell23_65136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 4].length) (baseStart_65136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65136 prefixEnd_65136 := by exact prefixLift 65136
  have htrace : WordTrace (prefixWord ++ tailWord_65136) baseStart_65136 baseEnd_65136 := by
    simpa [prefixWord, tailWord_65136, baseEnd_65136] using wordTrace_append hprefix tailTrace_65136
  have hstable : (prefixWord ++ tailWord_65136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65136).length < 2 ^ (prefixWord ++ tailWord_65136).sum := by decide
  have hdescent : baseEnd_65136 < baseStart_65136 := by decide
  rcases family_descends (prefixWord ++ tailWord_65136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65139 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 7, 2, 3]
def baseStart_65139 : Nat := 118140960795 + 65139 * 2 ^ 59
def prefixEnd_65139 : Nat := 4983230072969 + 3 ^ 40 * 65139 * 2
def baseEnd_65139 : Nat := 33447616353325877062937

theorem tailTrace_65139 : CollatzResearch.WordTrace tailWord_65139 prefixEnd_65139 33447616353325877062937 := by
  unfold tailWord_65139
  simp only [CollatzResearch.WordTrace]
  refine ⟨2375814511020002700614471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1583876340680001800409647 2375814511020002700614471)
  ·
    refine ⟨3563721766530004050921707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2375814511020002700614471 3563721766530004050921707)
    ·
      refine ⟨5345582649795006076382561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3563721766530004050921707 5345582649795006076382561)
      ·
        refine ⟨4009186987346254557286921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5345582649795006076382561 4009186987346254557286921)
        ·
          refine ⟨3006890240509690917965191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4009186987346254557286921 3006890240509690917965191)
          ·
            refine ⟨4510335360764536376947787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3006890240509690917965191 4510335360764536376947787)
            ·
              refine ⟨6765503041146804565421681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4510335360764536376947787 6765503041146804565421681)
              ·
                refine ⟨5074127280860103424066261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6765503041146804565421681 5074127280860103424066261)
                ·
                  refine ⟨118924858145158674001553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5074127280860103424066261 118924858145158674001553)
                  ·
                    refine ⟨89193643608869005501165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118924858145158674001553 89193643608869005501165)
                    ·
                      refine ⟨33447616353325877062937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 89193643608869005501165 33447616353325877062937)
                      ·
                        rfl

theorem cell23_65139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 2, 3].length) (baseStart_65139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65139 prefixEnd_65139 := by exact prefixLift 65139
  have htrace : WordTrace (prefixWord ++ tailWord_65139) baseStart_65139 baseEnd_65139 := by
    simpa [prefixWord, tailWord_65139, baseEnd_65139] using wordTrace_append hprefix tailTrace_65139
  have hstable : (prefixWord ++ tailWord_65139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65139).length < 2 ^ (prefixWord ++ tailWord_65139).sum := by decide
  have hdescent : baseEnd_65139 < baseStart_65139 := by decide
  rcases family_descends (prefixWord ++ tailWord_65139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65159 : List Nat := [1, 1, 4, 2, 1, 5, 9]
def baseStart_65159 : Nat := 118140960795 + 65159 * 2 ^ 59
def prefixEnd_65159 : Nat := 4983230072969 + 3 ^ 40 * 65159 * 2
def baseEnd_65159 : Nat := 413060320573034553245

theorem tailTrace_65159 : CollatzResearch.WordTrace tailWord_65159 prefixEnd_65159 413060320573034553245 := by
  unfold tailWord_65159
  simp only [CollatzResearch.WordTrace]
  refine ⟨2376543970947546116342531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1584362647298364077561687 2376543970947546116342531)
  ·
    refine ⟨3564815956421319174513797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2376543970947546116342531 3564815956421319174513797)
    ·
      refine ⟨668402991828997345221337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3564815956421319174513797 668402991828997345221337)
      ·
        refine ⟨501302243871748008916003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 668402991828997345221337 501302243871748008916003)
        ·
          refine ⟨751953365807622013374005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501302243871748008916003 751953365807622013374005)
          ·
            refine ⟨70495628044464563753813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 751953365807622013374005 70495628044464563753813)
            ·
              refine ⟨413060320573034553245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 70495628044464563753813 413060320573034553245)
              ·
                rfl

theorem cell23_65159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 9].length) (baseStart_65159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65159 prefixEnd_65159 := by exact prefixLift 65159
  have htrace : WordTrace (prefixWord ++ tailWord_65159) baseStart_65159 baseEnd_65159 := by
    simpa [prefixWord, tailWord_65159, baseEnd_65159] using wordTrace_append hprefix tailTrace_65159
  have hstable : (prefixWord ++ tailWord_65159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65159).length < 2 ^ (prefixWord ++ tailWord_65159).sum := by decide
  have hdescent : baseEnd_65159 < baseStart_65159 := by decide
  rcases family_descends (prefixWord ++ tailWord_65159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65169 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 3]
def baseStart_65169 : Nat := 118140960795 + 65169 * 2 ^ 59
def prefixEnd_65169 : Nat := 4983230072969 + 3 ^ 40 * 65169 * 2
def baseEnd_65169 : Nat := 33463020772960759687799

theorem tailTrace_65169 : CollatzResearch.WordTrace tailWord_65169 prefixEnd_65169 33463020772960759687799 := by
  unfold tailWord_65169
  simp only [CollatzResearch.WordTrace]
  refine ⟨2376908700911317824206561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1584605800607545216137707 2376908700911317824206561)
  ·
    refine ⟨1782681525683488368154921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2376908700911317824206561 1782681525683488368154921)
    ·
      refine ⟨1337011144262616276116191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1782681525683488368154921 1337011144262616276116191)
      ·
        refine ⟨2005516716393924414174287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1337011144262616276116191 2005516716393924414174287)
        ·
          refine ⟨3008275074590886621261431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2005516716393924414174287 3008275074590886621261431)
          ·
            refine ⟨4512412611886329931892147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3008275074590886621261431 4512412611886329931892147)
            ·
              refine ⟨6768618917829494897838221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4512412611886329931892147 6768618917829494897838221)
              ·
                refine ⟨2538232094186060586689333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6768618917829494897838221 2538232094186060586689333)
                ·
                  refine ⟨237959258829943180002125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2538232094186060586689333 237959258829943180002125)
                  ·
                    refine ⟨89234722061228692500797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 237959258829943180002125 89234722061228692500797)
                    ·
                      refine ⟨33463020772960759687799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 89234722061228692500797 33463020772960759687799)
                      ·
                        rfl

theorem cell23_65169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 3].length) (baseStart_65169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65169 prefixEnd_65169 := by exact prefixLift 65169
  have htrace : WordTrace (prefixWord ++ tailWord_65169) baseStart_65169 baseEnd_65169 := by
    simpa [prefixWord, tailWord_65169, baseEnd_65169] using wordTrace_append hprefix tailTrace_65169
  have hstable : (prefixWord ++ tailWord_65169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65169).length < 2 ^ (prefixWord ++ tailWord_65169).sum := by decide
  have hdescent : baseEnd_65169 < baseStart_65169 := by decide
  rcases family_descends (prefixWord ++ tailWord_65169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65220 : List Nat := [2, 3, 3, 1, 1, 1, 4, 2, 2, 1, 3]
def baseStart_65220 : Nat := 118140960795 + 65220 * 2 ^ 59
def prefixEnd_65220 : Nat := 4983230072969 + 3 ^ 40 * 65220 * 2
def baseEnd_65220 : Nat := 33489208286340060150065

theorem tailTrace_65220 : CollatzResearch.WordTrace tailWord_65220 prefixEnd_65220 33489208286340060150065 := by
  unfold tailWord_65220
  simp only [CollatzResearch.WordTrace]
  refine ⟨1189384411863276767156557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1585845882484369022875409 1189384411863276767156557)
  ·
    refine ⟨446019154448728787683709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1189384411863276767156557 446019154448728787683709)
    ·
      refine ⟨167257182918273295381391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 446019154448728787683709 167257182918273295381391)
      ·
        refine ⟨250885774377409943072087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167257182918273295381391 250885774377409943072087)
        ·
          refine ⟨376328661566114914608131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250885774377409943072087 376328661566114914608131)
          ·
            refine ⟨564492992349172371912197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376328661566114914608131 564492992349172371912197)
            ·
              refine ⟨105842436065469819733537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 564492992349172371912197 105842436065469819733537)
              ·
                refine ⟨79381827049102364800153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105842436065469819733537 79381827049102364800153)
                ·
                  refine ⟨59536370286826773600115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79381827049102364800153 59536370286826773600115)
                  ·
                    refine ⟨89304555430240160400173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59536370286826773600115 89304555430240160400173)
                    ·
                      refine ⟨33489208286340060150065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 89304555430240160400173 33489208286340060150065)
                      ·
                        rfl

theorem cell23_65220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_65220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65220 prefixEnd_65220 := by exact prefixLift 65220
  have htrace : WordTrace (prefixWord ++ tailWord_65220) baseStart_65220 baseEnd_65220 := by
    simpa [prefixWord, tailWord_65220, baseEnd_65220] using wordTrace_append hprefix tailTrace_65220
  have hstable : (prefixWord ++ tailWord_65220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65220).length < 2 ^ (prefixWord ++ tailWord_65220).sum := by decide
  have hdescent : baseEnd_65220 < baseStart_65220 := by decide
  rcases family_descends (prefixWord ++ tailWord_65220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65236 : List Nat := [2, 4, 1, 3, 1, 1, 1, 1, 1, 8]
def baseStart_65236 : Nat := 118140960795 + 65236 * 2 ^ 59
def prefixEnd_65236 : Nat := 4983230072969 + 3 ^ 40 * 65236 * 2
def baseEnd_65236 : Nat := 11165807992270665849997

theorem tailTrace_65236 : CollatzResearch.WordTrace tailWord_65236 prefixEnd_65236 11165807992270665849997 := by
  unfold tailWord_65236
  simp only [CollatzResearch.WordTrace]
  refine ⟨1189676195834294133447781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1586234927779058844597041 1189676195834294133447781)
  ·
    refine ⟨223064286718930150021459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1189676195834294133447781 223064286718930150021459)
    ·
      refine ⟨334596430078395225032189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223064286718930150021459 334596430078395225032189)
      ·
        refine ⟨125473661279398209387071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334596430078395225032189 125473661279398209387071)
        ·
          refine ⟨188210491919097314080607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125473661279398209387071 188210491919097314080607)
          ·
            refine ⟨282315737878645971120911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188210491919097314080607 282315737878645971120911)
            ·
              refine ⟨423473606817968956681367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282315737878645971120911 423473606817968956681367)
              ·
                refine ⟨635210410226953435022051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423473606817968956681367 635210410226953435022051)
                ·
                  refine ⟨952815615340430152533077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 635210410226953435022051 952815615340430152533077)
                  ·
                    refine ⟨11165807992270665849997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 952815615340430152533077 11165807992270665849997)
                    ·
                      rfl

theorem cell23_65236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_65236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65236 prefixEnd_65236 := by exact prefixLift 65236
  have htrace : WordTrace (prefixWord ++ tailWord_65236) baseStart_65236 baseEnd_65236 := by
    simpa [prefixWord, tailWord_65236, baseEnd_65236] using wordTrace_append hprefix tailTrace_65236
  have hstable : (prefixWord ++ tailWord_65236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65236).length < 2 ^ (prefixWord ++ tailWord_65236).sum := by decide
  have hdescent : baseEnd_65236 < baseStart_65236 := by decide
  rcases family_descends (prefixWord ++ tailWord_65236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65276 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 4, 3, 3]
def baseStart_65276 : Nat := 118140960795 + 65276 * 2 ^ 59
def prefixEnd_65276 : Nat := 4983230072969 + 3 ^ 40 * 65276 * 2
def baseEnd_65276 : Nat := 33517963202991841049807

theorem tailTrace_65276 : CollatzResearch.WordTrace tailWord_65276 prefixEnd_65276 33517963202991841049807 := by
  unfold tailWord_65276
  simp only [CollatzResearch.WordTrace]
  refine ⟨1190405655761837549175841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1587207541015783398901121 1190405655761837549175841)
  ·
    refine ⟨892804241821378161881881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1190405655761837549175841 892804241821378161881881)
    ·
      refine ⟨669603181366033621411411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 892804241821378161881881 669603181366033621411411)
      ·
        refine ⟨1004404772049050432117117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669603181366033621411411 1004404772049050432117117)
        ·
          refine ⟨376651789518393912043919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1004404772049050432117117 376651789518393912043919)
          ·
            refine ⟨564977684277590868065879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376651789518393912043919 564977684277590868065879)
            ·
              refine ⟨847466526416386302098819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564977684277590868065879 847466526416386302098819)
              ·
                refine ⟨1271199789624579453148229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 847466526416386302098819 1271199789624579453148229)
                ·
                  refine ⟨238349960554608647465293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1271199789624579453148229 238349960554608647465293)
                  ·
                    refine ⟨89381235207978242799485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 238349960554608647465293 89381235207978242799485)
                    ·
                      refine ⟨33517963202991841049807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 89381235207978242799485 33517963202991841049807)
                      ·
                        rfl

theorem cell23_65276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_65276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65276 prefixEnd_65276 := by exact prefixLift 65276
  have htrace : WordTrace (prefixWord ++ tailWord_65276) baseStart_65276 baseEnd_65276 := by
    simpa [prefixWord, tailWord_65276, baseEnd_65276] using wordTrace_append hprefix tailTrace_65276
  have hstable : (prefixWord ++ tailWord_65276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65276).length < 2 ^ (prefixWord ++ tailWord_65276).sum := by decide
  have hdescent : baseEnd_65276 < baseStart_65276 := by decide
  rcases family_descends (prefixWord ++ tailWord_65276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65289 : List Nat := [1, 2, 1, 1, 3, 2, 1, 3, 1, 1, 7]
def baseStart_65289 : Nat := 118140960795 + 65289 * 2 ^ 59
def prefixEnd_65289 : Nat := 4983230072969 + 3 ^ 40 * 65289 * 2
def baseEnd_65289 : Nat := 33524638451500290187247

theorem tailTrace_65289 : CollatzResearch.WordTrace tailWord_65289 prefixEnd_65289 33524638451500290187247 := by
  unfold tailWord_65289
  simp only [CollatzResearch.WordTrace]
  refine ⟨2381285460476578318574921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1587523640317718879049947 2381285460476578318574921)
  ·
    refine ⟨1785964095357433738931191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2381285460476578318574921 1785964095357433738931191)
    ·
      refine ⟨2678946143036150608396787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1785964095357433738931191 2678946143036150608396787)
      ·
        refine ⟨4018419214554225912595181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2678946143036150608396787 4018419214554225912595181)
        ·
          refine ⟨1506907205457834717223193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4018419214554225912595181 1506907205457834717223193)
          ·
            refine ⟨1130180404093376037917395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1506907205457834717223193 1130180404093376037917395)
            ·
              refine ⟨1695270606140064056876093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1130180404093376037917395 1695270606140064056876093)
              ·
                refine ⟨635726477302524021328535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1695270606140064056876093 635726477302524021328535)
                ·
                  refine ⟨953589715953786031992803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 635726477302524021328535 953589715953786031992803)
                  ·
                    refine ⟨1430384573930679047989205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 953589715953786031992803 1430384573930679047989205)
                    ·
                      refine ⟨33524638451500290187247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 1430384573930679047989205 33524638451500290187247)
                      ·
                        rfl

theorem cell23_65289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 1, 7].length) (baseStart_65289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65289 prefixEnd_65289 := by exact prefixLift 65289
  have htrace : WordTrace (prefixWord ++ tailWord_65289) baseStart_65289 baseEnd_65289 := by
    simpa [prefixWord, tailWord_65289, baseEnd_65289] using wordTrace_append hprefix tailTrace_65289
  have hstable : (prefixWord ++ tailWord_65289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65289).length < 2 ^ (prefixWord ++ tailWord_65289).sum := by decide
  have hdescent : baseEnd_65289 < baseStart_65289 := by decide
  rcases family_descends (prefixWord ++ tailWord_65289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65390 : List Nat := [4, 1, 2, 3, 1, 2, 2, 2, 6]
def baseStart_65390 : Nat := 118140960795 + 65390 * 2 ^ 59
def prefixEnd_65390 : Nat := 4983230072969 + 3 ^ 40 * 65390 * 2
def baseEnd_65390 : Nat := 3730722221956043891587

theorem tailTrace_65390 : CollatzResearch.WordTrace tailWord_65390 prefixEnd_65390 3730722221956043891587 := by
  unfold tailWord_65390
  simp only [CollatzResearch.WordTrace]
  refine ⟨298121154138834071000203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1589979488740448378667749 298121154138834071000203)
  ·
    refine ⟨447181731208251106500305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298121154138834071000203 447181731208251106500305)
    ·
      refine ⟨335386298406188329875229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447181731208251106500305 335386298406188329875229)
      ·
        refine ⟨125769861902320623703211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335386298406188329875229 125769861902320623703211)
        ·
          refine ⟨188654792853480935554817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125769861902320623703211 188654792853480935554817)
          ·
            refine ⟨141491094640110701666113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188654792853480935554817 141491094640110701666113)
            ·
              refine ⟨106118320980083026249585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141491094640110701666113 106118320980083026249585)
              ·
                refine ⟨79588740735062269687189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106118320980083026249585 79588740735062269687189)
                ·
                  refine ⟨3730722221956043891587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79588740735062269687189 3730722221956043891587)
                  ·
                    rfl

theorem cell23_65390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 6].length) (baseStart_65390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65390 prefixEnd_65390 := by exact prefixLift 65390
  have htrace : WordTrace (prefixWord ++ tailWord_65390) baseStart_65390 baseEnd_65390 := by
    simpa [prefixWord, tailWord_65390, baseEnd_65390] using wordTrace_append hprefix tailTrace_65390
  have hstable : (prefixWord ++ tailWord_65390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65390).length < 2 ^ (prefixWord ++ tailWord_65390).sum := by decide
  have hdescent : baseEnd_65390 < baseStart_65390 := by decide
  rcases family_descends (prefixWord ++ tailWord_65390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65434 : List Nat := [3, 1, 1, 4, 2, 2, 2, 3, 1, 1, 3]
def baseStart_65434 : Nat := 118140960795 + 65434 * 2 ^ 59
def prefixEnd_65434 : Nat := 4983230072969 + 3 ^ 40 * 65434 * 2
def baseEnd_65434 : Nat := 33599093146402222874081

theorem tailTrace_65434 : CollatzResearch.WordTrace tailWord_65434 prefixEnd_65434 33599093146402222874081 := by
  unfold tailWord_65434
  simp only [CollatzResearch.WordTrace]
  refine ⟨596643511237817020650839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1591049363300845388402237 596643511237817020650839)
  ·
    refine ⟨894965266856725530976259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 596643511237817020650839 894965266856725530976259)
    ·
      refine ⟨1342447900285088296464389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 894965266856725530976259 1342447900285088296464389)
      ·
        refine ⟨251708981303454055587073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1342447900285088296464389 251708981303454055587073)
        ·
          refine ⟨188781735977590541690305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251708981303454055587073 188781735977590541690305)
          ·
            refine ⟨141586301983192906267729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188781735977590541690305 141586301983192906267729)
            ·
              refine ⟨106189726487394679700797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141586301983192906267729 106189726487394679700797)
              ·
                refine ⟨39821147432773004887799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106189726487394679700797 39821147432773004887799)
                ·
                  refine ⟨59731721149159507331699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39821147432773004887799 59731721149159507331699)
                  ·
                    refine ⟨89597581723739260997549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59731721149159507331699 89597581723739260997549)
                    ·
                      refine ⟨33599093146402222874081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 89597581723739260997549 33599093146402222874081)
                      ·
                        rfl

theorem cell23_65434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_65434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65434 prefixEnd_65434 := by exact prefixLift 65434
  have htrace : WordTrace (prefixWord ++ tailWord_65434) baseStart_65434 baseEnd_65434 := by
    simpa [prefixWord, tailWord_65434, baseEnd_65434] using wordTrace_append hprefix tailTrace_65434
  have hstable : (prefixWord ++ tailWord_65434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65434).length < 2 ^ (prefixWord ++ tailWord_65434).sum := by decide
  have hdescent : baseEnd_65434 < baseStart_65434 := by decide
  rcases family_descends (prefixWord ++ tailWord_65434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65437 : List Nat := [1, 4, 2, 1, 2, 4, 2, 1, 1, 5]
def baseStart_65437 : Nat := 118140960795 + 65437 * 2 ^ 59
def prefixEnd_65437 : Nat := 4983230072969 + 3 ^ 40 * 65437 * 2
def baseEnd_65437 : Nat := 11200211196121903712189

theorem tailTrace_65437 : CollatzResearch.WordTrace tailWord_65437 prefixEnd_65437 11200211196121903712189 := by
  unfold tailWord_65437
  simp only [CollatzResearch.WordTrace]
  refine ⟨2386683463940399594962565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1591122309293599729975043 2386683463940399594962565)
  ·
    refine ⟨447503149488824924055481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2386683463940399594962565 447503149488824924055481)
    ·
      refine ⟨335627362116618693041611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447503149488824924055481 335627362116618693041611)
      ·
        refine ⟨503441043174928039562417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335627362116618693041611 503441043174928039562417)
        ·
          refine ⟨377580782381196029671813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 503441043174928039562417 377580782381196029671813)
          ·
            refine ⟨70796396696474255563465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 377580782381196029671813 70796396696474255563465)
            ·
              refine ⟨53097297522355691672599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70796396696474255563465 53097297522355691672599)
              ·
                refine ⟨79645946283533537508899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53097297522355691672599 79645946283533537508899)
                ·
                  refine ⟨119468919425300306263349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79645946283533537508899 119468919425300306263349)
                  ·
                    refine ⟨11200211196121903712189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 119468919425300306263349 11200211196121903712189)
                    ·
                      rfl

theorem cell23_65437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_65437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65437 prefixEnd_65437 := by exact prefixLift 65437
  have htrace : WordTrace (prefixWord ++ tailWord_65437) baseStart_65437 baseEnd_65437 := by
    simpa [prefixWord, tailWord_65437, baseEnd_65437] using wordTrace_append hprefix tailTrace_65437
  have hstable : (prefixWord ++ tailWord_65437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65437).length < 2 ^ (prefixWord ++ tailWord_65437).sum := by decide
  have hdescent : baseEnd_65437 < baseStart_65437 := by decide
  rcases family_descends (prefixWord ++ tailWord_65437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65440 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 7, 2, 2]
def baseStart_65440 : Nat := 118140960795 + 65440 * 2 ^ 59
def prefixEnd_65440 : Nat := 4983230072969 + 3 ^ 40 * 65440 * 2
def baseEnd_65440 : Nat := 33602174030329199399053

theorem tailTrace_65440 : CollatzResearch.WordTrace tailWord_65440 prefixEnd_65440 33602174030329199399053 := by
  unfold tailWord_65440
  simp only [CollatzResearch.WordTrace]
  refine ⟨1193396441464765553660887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1591195255286354071547849 1193396441464765553660887)
  ·
    refine ⟨1790094662197148330491331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1193396441464765553660887 1790094662197148330491331)
    ·
      refine ⟨2685141993295722495736997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1790094662197148330491331 2685141993295722495736997)
      ·
        refine ⟨503464123742947967950687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2685141993295722495736997 503464123742947967950687)
        ·
          refine ⟨755196185614421951926031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503464123742947967950687 755196185614421951926031)
          ·
            refine ⟨1132794278421632927889047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755196185614421951926031 1132794278421632927889047)
            ·
              refine ⟨1699191417632449391833571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1132794278421632927889047 1699191417632449391833571)
              ·
                refine ⟨2548787126448674087750357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1699191417632449391833571 2548787126448674087750357)
                ·
                  refine ⟨59737198276140798931649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2548787126448674087750357 59737198276140798931649)
                  ·
                    refine ⟨44802898707105599198737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59737198276140798931649 44802898707105599198737)
                    ·
                      refine ⟨33602174030329199399053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 44802898707105599198737 33602174030329199399053)
                      ·
                        rfl

theorem cell23_65440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_65440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65440 prefixEnd_65440 := by exact prefixLift 65440
  have htrace : WordTrace (prefixWord ++ tailWord_65440) baseStart_65440 baseEnd_65440 := by
    simpa [prefixWord, tailWord_65440, baseEnd_65440] using wordTrace_append hprefix tailTrace_65440
  have hstable : (prefixWord ++ tailWord_65440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65440).length < 2 ^ (prefixWord ++ tailWord_65440).sum := by decide
  have hdescent : baseEnd_65440 < baseStart_65440 := by decide
  rcases family_descends (prefixWord ++ tailWord_65440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65457 : List Nat := [1, 2, 2, 4, 2, 1, 1, 3, 3, 2, 2]
def baseStart_65457 : Nat := 118140960795 + 65457 * 2 ^ 59
def prefixEnd_65457 : Nat := 4983230072969 + 3 ^ 40 * 65457 * 2
def baseEnd_65457 : Nat := 33610903201455632886475

theorem tailTrace_65457 : CollatzResearch.WordTrace tailWord_65457 prefixEnd_65457 33610903201455632886475 := by
  unfold tailWord_65457
  simp only [CollatzResearch.WordTrace]
  refine ⟨2387412923867943010690625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1591608615911962007127083 2387412923867943010690625)
  ·
    refine ⟨1790559692900957258017969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2387412923867943010690625 1790559692900957258017969)
    ·
      refine ⟨1342919769675717943513477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1790559692900957258017969 1342919769675717943513477)
      ·
        refine ⟨251797456814197114408777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1342919769675717943513477 251797456814197114408777)
        ·
          refine ⟨188848092610647835806583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251797456814197114408777 188848092610647835806583)
          ·
            refine ⟨283272138915971753709875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188848092610647835806583 283272138915971753709875)
            ·
              refine ⟨424908208373957630564813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283272138915971753709875 424908208373957630564813)
              ·
                refine ⟨159340578140234111461805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 424908208373957630564813 159340578140234111461805)
                ·
                  refine ⟨59752716802587791798177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159340578140234111461805 59752716802587791798177)
                  ·
                    refine ⟨44814537601940843848633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59752716802587791798177 44814537601940843848633)
                    ·
                      refine ⟨33610903201455632886475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 44814537601940843848633 33610903201455632886475)
                      ·
                        rfl

theorem cell23_65457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_65457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65457 prefixEnd_65457 := by exact prefixLift 65457
  have htrace : WordTrace (prefixWord ++ tailWord_65457) baseStart_65457 baseEnd_65457 := by
    simpa [prefixWord, tailWord_65457, baseEnd_65457] using wordTrace_append hprefix tailTrace_65457
  have hstable : (prefixWord ++ tailWord_65457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65457).length < 2 ^ (prefixWord ++ tailWord_65457).sum := by decide
  have hdescent : baseEnd_65457 < baseStart_65457 := by decide
  rcases family_descends (prefixWord ++ tailWord_65457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65466 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 1, 4, 6]
def baseStart_65466 : Nat := 118140960795 + 65466 * 2 ^ 59
def prefixEnd_65466 : Nat := 4983230072969 + 3 ^ 40 * 65466 * 2
def baseEnd_65466 : Nat := 33615524527346097673933

theorem tailTrace_65466 : CollatzResearch.WordTrace tailWord_65466 prefixEnd_65466 33615524527346097673933 := by
  unfold tailWord_65466
  simp only [CollatzResearch.WordTrace]
  refine ⟨596935295208834386942063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1591827453890225031845501 596935295208834386942063)
  ·
    refine ⟨895402942813251580413095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 596935295208834386942063 895402942813251580413095)
    ·
      refine ⟨1343104414219877370619643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 895402942813251580413095 1343104414219877370619643)
      ·
        refine ⟨2014656621329816055929465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1343104414219877370619643 2014656621329816055929465)
        ·
          refine ⟨1510992465997362041947099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2014656621329816055929465 1510992465997362041947099)
          ·
            refine ⟨2266488698996043062920649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1510992465997362041947099 2266488698996043062920649)
            ·
              refine ⟨1699866524247032297190487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2266488698996043062920649 1699866524247032297190487)
              ·
                refine ⟨2549799786370548445785731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1699866524247032297190487 2549799786370548445785731)
                ·
                  refine ⟨3824699679555822668678597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2549799786370548445785731 3824699679555822668678597)
                  ·
                    refine ⟨717131189916716750377237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3824699679555822668678597 717131189916716750377237)
                    ·
                      refine ⟨33615524527346097673933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 717131189916716750377237 33615524527346097673933)
                      ·
                        rfl

theorem cell23_65466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_65466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65466 prefixEnd_65466 := by exact prefixLift 65466
  have htrace : WordTrace (prefixWord ++ tailWord_65466) baseStart_65466 baseEnd_65466 := by
    simpa [prefixWord, tailWord_65466, baseEnd_65466] using wordTrace_append hprefix tailTrace_65466
  have hstable : (prefixWord ++ tailWord_65466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65466).length < 2 ^ (prefixWord ++ tailWord_65466).sum := by decide
  have hdescent : baseEnd_65466 < baseStart_65466 := by decide
  rcases family_descends (prefixWord ++ tailWord_65466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65470 : List Nat := [4, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4]
def baseStart_65470 : Nat := 118140960795 + 65470 * 2 ^ 59
def prefixEnd_65470 : Nat := 4983230072969 + 3 ^ 40 * 65470 * 2
def baseEnd_65470 : Nat := 33617578449964082023915

theorem tailTrace_65470 : CollatzResearch.WordTrace tailWord_65470 prefixEnd_65470 33617578449964082023915 := by
  unfold tailWord_65470
  simp only [CollatzResearch.WordTrace]
  refine ⟨298485884102605778864233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1591924715213897487275909 298485884102605778864233)
  ·
    refine ⟨223864413076954334148175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298485884102605778864233 223864413076954334148175)
    ·
      refine ⟨335796619615431501222263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223864413076954334148175 335796619615431501222263)
      ·
        refine ⟨503694929423147251833395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335796619615431501222263 503694929423147251833395)
        ·
          refine ⟨755542394134720877750093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503694929423147251833395 755542394134720877750093)
          ·
            refine ⟨283328397800520329156285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 755542394134720877750093 283328397800520329156285)
            ·
              refine ⟨106248149175195123433607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283328397800520329156285 106248149175195123433607)
              ·
                refine ⟨159372223762792685150411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106248149175195123433607 159372223762792685150411)
                ·
                  refine ⟨239058335644189027725617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159372223762792685150411 239058335644189027725617)
                  ·
                    refine ⟨179293751733141770794213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 239058335644189027725617 179293751733141770794213)
                    ·
                      refine ⟨33617578449964082023915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 179293751733141770794213 33617578449964082023915)
                      ·
                        rfl

theorem cell23_65470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_65470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65470 prefixEnd_65470 := by exact prefixLift 65470
  have htrace : WordTrace (prefixWord ++ tailWord_65470) baseStart_65470 baseEnd_65470 := by
    simpa [prefixWord, tailWord_65470, baseEnd_65470] using wordTrace_append hprefix tailTrace_65470
  have hstable : (prefixWord ++ tailWord_65470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65470).length < 2 ^ (prefixWord ++ tailWord_65470).sum := by decide
  have hdescent : baseEnd_65470 < baseStart_65470 := by decide
  rcases family_descends (prefixWord ++ tailWord_65470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65480 : List Nat := [2, 1, 3, 1, 4, 3, 2, 7]
def baseStart_65480 : Nat := 118140960795 + 65480 * 2 ^ 59
def prefixEnd_65480 : Nat := 4983230072969 + 3 ^ 40 * 65480 * 2
def baseEnd_65480 : Nat := 1245285676167001588847

theorem tailTrace_65480 : CollatzResearch.WordTrace tailWord_65480 prefixEnd_65480 1245285676167001588847 := by
  unfold tailWord_65480
  simp only [CollatzResearch.WordTrace]
  refine ⟨1194125901392308969388947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1592167868523078625851929 1194125901392308969388947)
  ·
    refine ⟨1791188852088463454083421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1194125901392308969388947 1791188852088463454083421)
    ·
      refine ⟨671695819533173795281283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1791188852088463454083421 671695819533173795281283)
      ·
        refine ⟨1007543729299760692921925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671695819533173795281283 1007543729299760692921925)
        ·
          refine ⟨188914449243705129922861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1007543729299760692921925 188914449243705129922861)
          ·
            refine ⟨70842918466389423721073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188914449243705129922861 70842918466389423721073)
            ·
              refine ⟨53132188849792067790805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70842918466389423721073 53132188849792067790805)
              ·
                refine ⟨1245285676167001588847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 53132188849792067790805 1245285676167001588847)
                ·
                  rfl

theorem cell23_65480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 7].length) (baseStart_65480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65480 prefixEnd_65480 := by exact prefixLift 65480
  have htrace : WordTrace (prefixWord ++ tailWord_65480) baseStart_65480 baseEnd_65480 := by
    simpa [prefixWord, tailWord_65480, baseEnd_65480] using wordTrace_append hprefix tailTrace_65480
  have hstable : (prefixWord ++ tailWord_65480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65480).length < 2 ^ (prefixWord ++ tailWord_65480).sum := by decide
  have hdescent : baseEnd_65480 < baseStart_65480 := by decide
  rcases family_descends (prefixWord ++ tailWord_65480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65533 : List Nat := [1, 4, 1, 1, 1, 2, 3, 2, 2, 1, 5]
def baseStart_65533 : Nat := 118140960795 + 65533 * 2 ^ 59
def prefixEnd_65533 : Nat := 4983230072969 + 3 ^ 40 * 65533 * 2
def baseEnd_65533 : Nat := 33649927731197335536125

theorem tailTrace_65533 : CollatzResearch.WordTrace tailWord_65533 prefixEnd_65533 33649927731197335536125 := by
  unfold tailWord_65533
  simp only [CollatzResearch.WordTrace]
  refine ⟨2390184871592607990457253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1593456581061738660304835 2390184871592607990457253)
  ·
    refine ⟨448159663423613998210735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2390184871592607990457253 448159663423613998210735)
    ·
      refine ⟨672239495135420997316103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448159663423613998210735 672239495135420997316103)
      ·
        refine ⟨1008359242703131495974155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672239495135420997316103 1008359242703131495974155)
        ·
          refine ⟨1512538864054697243961233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1008359242703131495974155 1512538864054697243961233)
          ·
            refine ⟨1134404148041022932970925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1512538864054697243961233 1134404148041022932970925)
            ·
              refine ⟨425401555515383599864097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1134404148041022932970925 425401555515383599864097)
              ·
                refine ⟨319051166636537699898073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 425401555515383599864097 319051166636537699898073)
                ·
                  refine ⟨239288374977403274923555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319051166636537699898073 239288374977403274923555)
                  ·
                    refine ⟨358932562466104912385333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 239288374977403274923555 358932562466104912385333)
                    ·
                      refine ⟨33649927731197335536125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 358932562466104912385333 33649927731197335536125)
                      ·
                        rfl

theorem cell23_65533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_65533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65533 prefixEnd_65533 := by exact prefixLift 65533
  have htrace : WordTrace (prefixWord ++ tailWord_65533) baseStart_65533 baseEnd_65533 := by
    simpa [prefixWord, tailWord_65533, baseEnd_65533] using wordTrace_append hprefix tailTrace_65533
  have hstable : (prefixWord ++ tailWord_65533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65533).length < 2 ^ (prefixWord ++ tailWord_65533).sum := by decide
  have hdescent : baseEnd_65533 < baseStart_65533 := by decide
  rcases family_descends (prefixWord ++ tailWord_65533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65534 : List Nat := [4, 2, 2, 2, 1, 2, 1, 1, 3, 3, 2]
def baseStart_65534 : Nat := 118140960795 + 65534 * 2 ^ 59
def prefixEnd_65534 : Nat := 4983230072969 + 3 ^ 40 * 65534 * 2
def baseEnd_65534 : Nat := 33650441211851831623621

theorem tailTrace_65534 : CollatzResearch.WordTrace tailWord_65534 prefixEnd_65534 33650441211851831623621 := by
  unfold tailWord_65534
  simp only [CollatzResearch.WordTrace]
  refine ⟨298777668073623145155457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1593480896392656774162437 298777668073623145155457)
  ·
    refine ⟨224083251055217358866593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298777668073623145155457 224083251055217358866593)
    ·
      refine ⟨168062438291413019149945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224083251055217358866593 168062438291413019149945)
      ·
        refine ⟨126046828718559764362459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168062438291413019149945 126046828718559764362459)
        ·
          refine ⟨189070243077839646543689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126046828718559764362459 189070243077839646543689)
          ·
            refine ⟨141802682308379734907767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189070243077839646543689 141802682308379734907767)
            ·
              refine ⟨212704023462569602361651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141802682308379734907767 212704023462569602361651)
              ·
                refine ⟨319056035193854403542477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212704023462569602361651 319056035193854403542477)
                ·
                  refine ⟨119646013197695401328429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 319056035193854403542477 119646013197695401328429)
                  ·
                    refine ⟨44867254949135775498161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119646013197695401328429 44867254949135775498161)
                    ·
                      refine ⟨33650441211851831623621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 44867254949135775498161 33650441211851831623621)
                      ·
                        rfl

theorem cell23_65534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_65534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65534 prefixEnd_65534 := by exact prefixLift 65534
  have htrace : WordTrace (prefixWord ++ tailWord_65534) baseStart_65534 baseEnd_65534 := by
    simpa [prefixWord, tailWord_65534, baseEnd_65534] using wordTrace_append hprefix tailTrace_65534
  have hstable : (prefixWord ++ tailWord_65534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65534).length < 2 ^ (prefixWord ++ tailWord_65534).sum := by decide
  have hdescent : baseEnd_65534 < baseStart_65534 := by decide
  rcases family_descends (prefixWord ++ tailWord_65534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65564 : List Nat := [2, 2, 3, 1, 3, 1, 1, 4, 2, 2, 2]
def baseStart_65564 : Nat := 118140960795 + 65564 * 2 ^ 59
def prefixEnd_65564 : Nat := 4983230072969 + 3 ^ 40 * 65564 * 2
def baseEnd_65564 : Nat := 33665845631486714248483

theorem tailTrace_65564 : CollatzResearch.WordTrace tailWord_65564 prefixEnd_65564 33665845631486714248483 := by
  unfold tailWord_65564
  simp only [CollatzResearch.WordTrace]
  refine ⟨1195657767240150142417873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1594210356320200189890497 1195657767240150142417873)
  ·
    refine ⟨896743325430112606813405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1195657767240150142417873 896743325430112606813405)
    ·
      refine ⟨336278747036292227555027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 896743325430112606813405 336278747036292227555027)
      ·
        refine ⟨504418120554438341332541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336278747036292227555027 504418120554438341332541)
        ·
          refine ⟨189156795207914377999703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 504418120554438341332541 189156795207914377999703)
          ·
            refine ⟨283735192811871566999555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189156795207914377999703 283735192811871566999555)
            ·
              refine ⟨425602789217807350499333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283735192811871566999555 425602789217807350499333)
              ·
                refine ⟨79800522978338878218625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 425602789217807350499333 79800522978338878218625)
                ·
                  refine ⟨59850392233754158663969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79800522978338878218625 59850392233754158663969)
                  ·
                    refine ⟨44887794175315618997977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59850392233754158663969 44887794175315618997977)
                    ·
                      refine ⟨33665845631486714248483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 44887794175315618997977 33665845631486714248483)
                      ·
                        rfl

theorem cell23_65564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_65564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65564 prefixEnd_65564 := by exact prefixLift 65564
  have htrace : WordTrace (prefixWord ++ tailWord_65564) baseStart_65564 baseEnd_65564 := by
    simpa [prefixWord, tailWord_65564, baseEnd_65564] using wordTrace_append hprefix tailTrace_65564
  have hstable : (prefixWord ++ tailWord_65564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65564).length < 2 ^ (prefixWord ++ tailWord_65564).sum := by decide
  have hdescent : baseEnd_65564 < baseStart_65564 := by decide
  rcases family_descends (prefixWord ++ tailWord_65564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65600 : List Nat := [2, 1, 1, 2, 2, 4, 3, 1, 2, 5]
def baseStart_65600 : Nat := 118140960795 + 65600 * 2 ^ 59
def prefixEnd_65600 : Nat := 4983230072969 + 3 ^ 40 * 65600 * 2
def baseEnd_65600 : Nat := 11228110311682857799439

theorem tailTrace_65600 : CollatzResearch.WordTrace tailWord_65600 prefixEnd_65600 11228110311682857799439 := by
  unfold tailWord_65600
  simp only [CollatzResearch.WordTrace]
  refine ⟨1196314281174939216573127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1595085708233252288764169 1196314281174939216573127)
  ·
    refine ⟨1794471421762408824859691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1196314281174939216573127 1794471421762408824859691)
    ·
      refine ⟨2691707132643613237289537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1794471421762408824859691 2691707132643613237289537)
      ·
        refine ⟨2018780349482709927967153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2691707132643613237289537 2018780349482709927967153)
        ·
          refine ⟨1514085262112032445975365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2018780349482709927967153 1514085262112032445975365)
          ·
            refine ⟨283890986646006083620381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1514085262112032445975365 283890986646006083620381)
            ·
              refine ⟨106459119992252281357643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283890986646006083620381 106459119992252281357643)
              ·
                refine ⟨159688679988378422036465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106459119992252281357643 159688679988378422036465)
                ·
                  refine ⟨119766509991283816527349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159688679988378422036465 119766509991283816527349)
                  ·
                    refine ⟨11228110311682857799439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 119766509991283816527349 11228110311682857799439)
                    ·
                      rfl

theorem cell23_65600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 2, 5].length) (baseStart_65600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65600 prefixEnd_65600 := by exact prefixLift 65600
  have htrace : WordTrace (prefixWord ++ tailWord_65600) baseStart_65600 baseEnd_65600 := by
    simpa [prefixWord, tailWord_65600, baseEnd_65600] using wordTrace_append hprefix tailTrace_65600
  have hstable : (prefixWord ++ tailWord_65600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65600).length < 2 ^ (prefixWord ++ tailWord_65600).sum := by decide
  have hdescent : baseEnd_65600 < baseStart_65600 := by decide
  rcases family_descends (prefixWord ++ tailWord_65600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65620 : List Nat := [2, 4, 1, 1, 1, 1, 1, 3, 4, 1, 4]
def baseStart_65620 : Nat := 118140960795 + 65620 * 2 ^ 59
def prefixEnd_65620 : Nat := 4983230072969 + 3 ^ 40 * 65620 * 2
def baseEnd_65620 : Nat := 33694600548138495148225

theorem tailTrace_65620 : CollatzResearch.WordTrace tailWord_65620 prefixEnd_65620 33694600548138495148225 := by
  unfold tailWord_65620
  simp only [CollatzResearch.WordTrace]
  refine ⟨1196679011138710924437157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1595572014851614565916209 1196679011138710924437157)
  ·
    refine ⟨224377314588508298331967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1196679011138710924437157 224377314588508298331967)
    ·
      refine ⟨336565971882762447497951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224377314588508298331967 336565971882762447497951)
      ·
        refine ⟨504848957824143671246927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336565971882762447497951 504848957824143671246927)
        ·
          refine ⟨757273436736215506870391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504848957824143671246927 757273436736215506870391)
          ·
            refine ⟨1135910155104323260305587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 757273436736215506870391 1135910155104323260305587)
            ·
              refine ⟨1703865232656484890458381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1135910155104323260305587 1703865232656484890458381)
              ·
                refine ⟨638949462246181833921893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1703865232656484890458381 638949462246181833921893)
                ·
                  refine ⟨119803024171159093860355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 638949462246181833921893 119803024171159093860355)
                  ·
                    refine ⟨179704536256738640790533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119803024171159093860355 179704536256738640790533)
                    ·
                      refine ⟨33694600548138495148225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 179704536256738640790533 33694600548138495148225)
                      ·
                        rfl

theorem cell23_65620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_65620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65620 prefixEnd_65620 := by exact prefixLift 65620
  have htrace : WordTrace (prefixWord ++ tailWord_65620) baseStart_65620 baseEnd_65620 := by
    simpa [prefixWord, tailWord_65620, baseEnd_65620] using wordTrace_append hprefix tailTrace_65620
  have hstable : (prefixWord ++ tailWord_65620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65620).length < 2 ^ (prefixWord ++ tailWord_65620).sum := by decide
  have hdescent : baseEnd_65620 < baseStart_65620 := by decide
  rcases family_descends (prefixWord ++ tailWord_65620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65623 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 5]
def baseStart_65623 : Nat := 118140960795 + 65623 * 2 ^ 59
def prefixEnd_65623 : Nat := 4983230072969 + 3 ^ 40 * 65623 * 2
def baseEnd_65623 : Nat := 33696140990101983410711

theorem tailTrace_65623 : CollatzResearch.WordTrace tailWord_65623 prefixEnd_65623 33696140990101983410711 := by
  unfold tailWord_65623
  simp only [CollatzResearch.WordTrace]
  refine ⟨2393467441266553361233523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1595644960844368907489015 2393467441266553361233523)
  ·
    refine ⟨3590201161899830041850285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2393467441266553361233523 3590201161899830041850285)
    ·
      refine ⟨1346325435712436265693857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3590201161899830041850285 1346325435712436265693857)
      ·
        refine ⟨1009744076784327199270393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1346325435712436265693857 1009744076784327199270393)
        ·
          refine ⟨757308057588245399452795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1009744076784327199270393 757308057588245399452795)
          ·
            refine ⟨1135962086382368099179193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 757308057588245399452795 1135962086382368099179193)
            ·
              refine ⟨851971564786776074384395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1135962086382368099179193 851971564786776074384395)
              ·
                refine ⟨1277957347180164111576593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 851971564786776074384395 1277957347180164111576593)
                ·
                  refine ⟨958468010385123083682445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1277957347180164111576593 958468010385123083682445)
                  ·
                    refine ⟨359425503894421156380917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 958468010385123083682445 359425503894421156380917)
                    ·
                      refine ⟨33696140990101983410711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 359425503894421156380917 33696140990101983410711)
                      ·
                        rfl

theorem cell23_65623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_65623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65623 prefixEnd_65623 := by exact prefixLift 65623
  have htrace : WordTrace (prefixWord ++ tailWord_65623) baseStart_65623 baseEnd_65623 := by
    simpa [prefixWord, tailWord_65623, baseEnd_65623] using wordTrace_append hprefix tailTrace_65623
  have hstable : (prefixWord ++ tailWord_65623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65623).length < 2 ^ (prefixWord ++ tailWord_65623).sum := by decide
  have hdescent : baseEnd_65623 < baseStart_65623 := by decide
  rcases family_descends (prefixWord ++ tailWord_65623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65633 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 4, 1, 6]
def baseStart_65633 : Nat := 118140960795 + 65633 * 2 ^ 59
def prefixEnd_65633 : Nat := 4983230072969 + 3 ^ 40 * 65633 * 2
def baseEnd_65633 : Nat := 33701275796646944285665

theorem tailTrace_65633 : CollatzResearch.WordTrace tailWord_65633 prefixEnd_65633 33701275796646944285665 := by
  unfold tailWord_65633
  simp only [CollatzResearch.WordTrace]
  refine ⟨2393832171230325069097553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1595888114153550046065035 2393832171230325069097553)
  ·
    refine ⟨1795374128422743801823165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2393832171230325069097553 1795374128422743801823165)
    ·
      refine ⟨673265298158528925683687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1795374128422743801823165 673265298158528925683687)
      ·
        refine ⟨1009897947237793388525531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 673265298158528925683687 1009897947237793388525531)
        ·
          refine ⟨1514846920856690082788297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1009897947237793388525531 1514846920856690082788297)
          ·
            refine ⟨1136135190642517562091223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1514846920856690082788297 1136135190642517562091223)
            ·
              refine ⟨1704202785963776343136835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1136135190642517562091223 1704202785963776343136835)
              ·
                refine ⟨2556304178945664514705253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1704202785963776343136835 2556304178945664514705253)
                ·
                  refine ⟨479307033552312096507235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2556304178945664514705253 479307033552312096507235)
                  ·
                    refine ⟨718960550328468144760853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 479307033552312096507235 718960550328468144760853)
                    ·
                      refine ⟨33701275796646944285665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 718960550328468144760853 33701275796646944285665)
                      ·
                        rfl

theorem cell23_65633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_65633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65633 prefixEnd_65633 := by exact prefixLift 65633
  have htrace : WordTrace (prefixWord ++ tailWord_65633) baseStart_65633 baseEnd_65633 := by
    simpa [prefixWord, tailWord_65633, baseEnd_65633] using wordTrace_append hprefix tailTrace_65633
  have hstable : (prefixWord ++ tailWord_65633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65633).length < 2 ^ (prefixWord ++ tailWord_65633).sum := by decide
  have hdescent : baseEnd_65633 < baseStart_65633 := by decide
  rcases family_descends (prefixWord ++ tailWord_65633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65637 : List Nat := [1, 3, 1, 3, 2, 2, 2, 1, 2, 4, 2]
def baseStart_65637 : Nat := 118140960795 + 65637 * 2 ^ 59
def prefixEnd_65637 : Nat := 4983230072969 + 3 ^ 40 * 65637 * 2
def baseEnd_65637 : Nat := 33703329719264928635647

theorem tailTrace_65637 : CollatzResearch.WordTrace tailWord_65637 prefixEnd_65637 33703329719264928635647 := by
  unfold tailWord_65637
  simp only [CollatzResearch.WordTrace]
  refine ⟨2393978063215833752243165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1595985375477222501495443 2393978063215833752243165)
  ·
    refine ⟨897741773705937657091187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2393978063215833752243165 897741773705937657091187)
    ·
      refine ⟨1346612660558906485636781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 897741773705937657091187 1346612660558906485636781)
      ·
        refine ⟨504979747709589932113793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1346612660558906485636781 504979747709589932113793)
        ·
          refine ⟨378734810782192449085345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504979747709589932113793 378734810782192449085345)
          ·
            refine ⟨284051108086644336814009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378734810782192449085345 284051108086644336814009)
            ·
              refine ⟨213038331064983252610507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284051108086644336814009 213038331064983252610507)
              ·
                refine ⟨319557496597474878915761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213038331064983252610507 319557496597474878915761)
                ·
                  refine ⟨239668122448106159186821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319557496597474878915761 239668122448106159186821)
                  ·
                    refine ⟨44937772959019904847529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 239668122448106159186821 44937772959019904847529)
                    ·
                      refine ⟨33703329719264928635647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 44937772959019904847529 33703329719264928635647)
                      ·
                        rfl

theorem cell23_65637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_65637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65637 prefixEnd_65637 := by exact prefixLift 65637
  have htrace : WordTrace (prefixWord ++ tailWord_65637) baseStart_65637 baseEnd_65637 := by
    simpa [prefixWord, tailWord_65637, baseEnd_65637] using wordTrace_append hprefix tailTrace_65637
  have hstable : (prefixWord ++ tailWord_65637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65637).length < 2 ^ (prefixWord ++ tailWord_65637).sum := by decide
  have hdescent : baseEnd_65637 < baseStart_65637 := by decide
  rcases family_descends (prefixWord ++ tailWord_65637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65683 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 7]
def baseStart_65683 : Nat := 118140960795 + 65683 * 2 ^ 59
def prefixEnd_65683 : Nat := 4983230072969 + 3 ^ 40 * 65683 * 2
def baseEnd_65683 : Nat := 33726949829371748660435

theorem tailTrace_65683 : CollatzResearch.WordTrace tailWord_65683 prefixEnd_65683 33726949829371748660435 := by
  unfold tailWord_65683
  simp only [CollatzResearch.WordTrace]
  refine ⟨2395655821049183608417703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1597103880699455738945135 2395655821049183608417703)
  ·
    refine ⟨3593483731573775412626555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2395655821049183608417703 3593483731573775412626555)
    ·
      refine ⟨5390225597360663118939833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3593483731573775412626555 5390225597360663118939833)
      ·
        refine ⟨4042669198020497339204875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5390225597360663118939833 4042669198020497339204875)
        ·
          refine ⟨6064003797030746008807313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4042669198020497339204875 6064003797030746008807313)
          ·
            refine ⟨4548002847773059506605485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6064003797030746008807313 4548002847773059506605485)
            ·
              refine ⟨1705501067914897314977057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4548002847773059506605485 1705501067914897314977057)
              ·
                refine ⟨1279125800936172986232793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1705501067914897314977057 1279125800936172986232793)
                ·
                  refine ⟨959344350702129739674595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1279125800936172986232793 959344350702129739674595)
                  ·
                    refine ⟨1439016526053194609511893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 959344350702129739674595 1439016526053194609511893)
                    ·
                      refine ⟨33726949829371748660435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 1439016526053194609511893 33726949829371748660435)
                      ·
                        rfl

theorem cell23_65683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 7].length) (baseStart_65683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65683 prefixEnd_65683 := by exact prefixLift 65683
  have htrace : WordTrace (prefixWord ++ tailWord_65683) baseStart_65683 baseEnd_65683 := by
    simpa [prefixWord, tailWord_65683, baseEnd_65683] using wordTrace_append hprefix tailTrace_65683
  have hstable : (prefixWord ++ tailWord_65683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65683).length < 2 ^ (prefixWord ++ tailWord_65683).sum := by decide
  have hdescent : baseEnd_65683 < baseStart_65683 := by decide
  rcases family_descends (prefixWord ++ tailWord_65683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65694 : List Nat := [4, 3, 1, 1, 3, 1, 1, 3, 6]
def baseStart_65694 : Nat := 118140960795 + 65694 * 2 ^ 59
def prefixEnd_65694 : Nat := 4983230072969 + 3 ^ 40 * 65694 * 2
def baseEnd_65694 : Nat := 3748066457396800624765

theorem tailTrace_65694 : CollatzResearch.WordTrace tailWord_65694 prefixEnd_65694 3748066457396800624765 := by
  unfold tailWord_65694
  simp only [CollatzResearch.WordTrace]
  refine ⟨299507128001166560883517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1597371349339554991378757 299507128001166560883517)
  ·
    refine ⟨112315173000437460331319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299507128001166560883517 112315173000437460331319)
    ·
      refine ⟨168472759500656190496979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112315173000437460331319 168472759500656190496979)
      ·
        refine ⟨252709139250984285745469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168472759500656190496979 252709139250984285745469)
        ·
          refine ⟨94765927219119107154551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252709139250984285745469 94765927219119107154551)
          ·
            refine ⟨142148890828678660731827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94765927219119107154551 142148890828678660731827)
            ·
              refine ⟨213223336243017991097741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142148890828678660731827 213223336243017991097741)
              ·
                refine ⟨79958751091131746661653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213223336243017991097741 79958751091131746661653)
                ·
                  refine ⟨3748066457396800624765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79958751091131746661653 3748066457396800624765)
                  ·
                    rfl

theorem cell23_65694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_65694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65694 prefixEnd_65694 := by exact prefixLift 65694
  have htrace : WordTrace (prefixWord ++ tailWord_65694) baseStart_65694 baseEnd_65694 := by
    simpa [prefixWord, tailWord_65694, baseEnd_65694] using wordTrace_append hprefix tailTrace_65694
  have hstable : (prefixWord ++ tailWord_65694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65694).length < 2 ^ (prefixWord ++ tailWord_65694).sum := by decide
  have hdescent : baseEnd_65694 < baseStart_65694 := by decide
  rcases family_descends (prefixWord ++ tailWord_65694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65714 : List Nat := [3, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2]
def baseStart_65714 : Nat := 118140960795 + 65714 * 2 ^ 59
def prefixEnd_65714 : Nat := 4983230072969 + 3 ^ 40 * 65714 * 2
def baseEnd_65714 : Nat := 33742867729661127372793

theorem tailTrace_65714 : CollatzResearch.WordTrace tailWord_65714 prefixEnd_65714 33742867729661127372793 := by
  unfold tailWord_65714
  simp only [CollatzResearch.WordTrace]
  refine ⟨599196620984218975699049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1597857655957917268530797 599196620984218975699049)
  ·
    refine ⟨449397465738164231774287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 599196620984218975699049 449397465738164231774287)
    ·
      refine ⟨674096198607246347661431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449397465738164231774287 674096198607246347661431)
      ·
        refine ⟨1011144297910869521492147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674096198607246347661431 1011144297910869521492147)
        ·
          refine ⟨1516716446866304282238221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1011144297910869521492147 1516716446866304282238221)
          ·
            refine ⟨568768667574864105839333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1516716446866304282238221 568768667574864105839333)
            ·
              refine ⟨106644125170287019844875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 568768667574864105839333 106644125170287019844875)
              ·
                refine ⟨159966187755430529767313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106644125170287019844875 159966187755430529767313)
                ·
                  refine ⟨119974640816572897325485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159966187755430529767313 119974640816572897325485)
                  ·
                    refine ⟨44990490306214836497057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119974640816572897325485 44990490306214836497057)
                    ·
                      refine ⟨33742867729661127372793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 44990490306214836497057 33742867729661127372793)
                      ·
                        rfl

theorem cell23_65714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2].length) (baseStart_65714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65714 prefixEnd_65714 := by exact prefixLift 65714
  have htrace : WordTrace (prefixWord ++ tailWord_65714) baseStart_65714 baseEnd_65714 := by
    simpa [prefixWord, tailWord_65714, baseEnd_65714] using wordTrace_append hprefix tailTrace_65714
  have hstable : (prefixWord ++ tailWord_65714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65714).length < 2 ^ (prefixWord ++ tailWord_65714).sum := by decide
  have hdescent : baseEnd_65714 < baseStart_65714 := by decide
  rcases family_descends (prefixWord ++ tailWord_65714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65720 : List Nat := [2, 1, 2, 1, 2, 1, 5, 2, 1, 6]
def baseStart_65720 : Nat := 118140960795 + 65720 * 2 ^ 59
def prefixEnd_65720 : Nat := 4983230072969 + 3 ^ 40 * 65720 * 2
def baseEnd_65720 : Nat := 11248649537862701299255

theorem tailTrace_65720 : CollatzResearch.WordTrace tailWord_65720 prefixEnd_65720 11248649537862701299255 := by
  unfold tailWord_65720
  simp only [CollatzResearch.WordTrace]
  refine ⟨1198502660957569463757307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1598003547943425951676409 1198502660957569463757307)
  ·
    refine ⟨1797753991436354195635961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1198502660957569463757307 1797753991436354195635961)
    ·
      refine ⟨1348315493577265646726971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1797753991436354195635961 1348315493577265646726971)
      ·
        refine ⟨2022473240365898470090457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1348315493577265646726971 2022473240365898470090457)
        ·
          refine ⟨1516854930274423852567843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2022473240365898470090457 1516854930274423852567843)
          ·
            refine ⟨2275282395411635778851765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1516854930274423852567843 2275282395411635778851765)
            ·
              refine ⟨213307724569840854267353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2275282395411635778851765 213307724569840854267353)
              ·
                refine ⟨159980793427380640700515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213307724569840854267353 159980793427380640700515)
                ·
                  refine ⟨239971190141070961050773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159980793427380640700515 239971190141070961050773)
                  ·
                    refine ⟨11248649537862701299255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 239971190141070961050773 11248649537862701299255)
                    ·
                      rfl

theorem cell23_65720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 1, 6].length) (baseStart_65720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65720 prefixEnd_65720 := by exact prefixLift 65720
  have htrace : WordTrace (prefixWord ++ tailWord_65720) baseStart_65720 baseEnd_65720 := by
    simpa [prefixWord, tailWord_65720, baseEnd_65720] using wordTrace_append hprefix tailTrace_65720
  have hstable : (prefixWord ++ tailWord_65720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65720).length < 2 ^ (prefixWord ++ tailWord_65720).sum := by decide
  have hdescent : baseEnd_65720 < baseStart_65720 := by decide
  rcases family_descends (prefixWord ++ tailWord_65720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65777 : List Nat := [1, 2, 2, 2, 2, 1, 4, 2, 1, 3, 3]
def baseStart_65777 : Nat := 118140960795 + 65777 * 2 ^ 59
def prefixEnd_65777 : Nat := 4983230072969 + 3 ^ 40 * 65777 * 2
def baseEnd_65777 : Nat := 33775217010894380885003

theorem tailTrace_65777 : CollatzResearch.WordTrace tailWord_65777 prefixEnd_65777 33775217010894380885003 := by
  unfold tailWord_65777
  simp only [CollatzResearch.WordTrace]
  refine ⟨2399084282708637662339585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1599389521805758441559723 2399084282708637662339585)
  ·
    refine ⟨1799313212031478246754689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2399084282708637662339585 1799313212031478246754689)
    ·
      refine ⟨1349484909023608685066017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1799313212031478246754689 1349484909023608685066017)
      ·
        refine ⟨1012113681767706513799513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1349484909023608685066017 1012113681767706513799513)
        ·
          refine ⟨759085261325779885349635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1012113681767706513799513 759085261325779885349635)
          ·
            refine ⟨1138627891988669828024453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759085261325779885349635 1138627891988669828024453)
            ·
              refine ⟨213492729747875592754585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1138627891988669828024453 213492729747875592754585)
              ·
                refine ⟨160119547310906694565939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213492729747875592754585 160119547310906694565939)
                ·
                  refine ⟨240179320966360041848909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160119547310906694565939 240179320966360041848909)
                  ·
                    refine ⟨90067245362385015693341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 240179320966360041848909 90067245362385015693341)
                    ·
                      refine ⟨33775217010894380885003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 90067245362385015693341 33775217010894380885003)
                      ·
                        rfl

theorem cell23_65777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_65777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65777 prefixEnd_65777 := by exact prefixLift 65777
  have htrace : WordTrace (prefixWord ++ tailWord_65777) baseStart_65777 baseEnd_65777 := by
    simpa [prefixWord, tailWord_65777, baseEnd_65777] using wordTrace_append hprefix tailTrace_65777
  have hstable : (prefixWord ++ tailWord_65777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65777).length < 2 ^ (prefixWord ++ tailWord_65777).sum := by decide
  have hdescent : baseEnd_65777 < baseStart_65777 := by decide
  rcases family_descends (prefixWord ++ tailWord_65777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65778 : List Nat := [3, 2, 1, 3, 2, 1, 1, 5, 1, 2, 2]
def baseStart_65778 : Nat := 118140960795 + 65778 * 2 ^ 59
def prefixEnd_65778 : Nat := 4983230072969 + 3 ^ 40 * 65778 * 2
def baseEnd_65778 : Nat := 33775730491548876972499

theorem tailTrace_65778 : CollatzResearch.WordTrace tailWord_65778 prefixEnd_65778 33775730491548876972499 := by
  unfold tailWord_65778
  simp only [CollatzResearch.WordTrace]
  refine ⟨599780188926253708281497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1599413837136676555417325 599780188926253708281497)
  ·
    refine ⟨449835141694690281211123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 599780188926253708281497 449835141694690281211123)
    ·
      refine ⟨674752712542035421816685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449835141694690281211123 674752712542035421816685)
      ·
        refine ⟨253032267203263283181257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 674752712542035421816685 253032267203263283181257)
        ·
          refine ⟨189774200402447462385943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253032267203263283181257 189774200402447462385943)
          ·
            refine ⟨284661300603671193578915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189774200402447462385943 284661300603671193578915)
            ·
              refine ⟨426991950905506790368373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284661300603671193578915 426991950905506790368373)
              ·
                refine ⟨40030495397391261597035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 426991950905506790368373 40030495397391261597035)
                ·
                  refine ⟨60045743096086892395553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40030495397391261597035 60045743096086892395553)
                  ·
                    refine ⟨45034307322065169296665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60045743096086892395553 45034307322065169296665)
                    ·
                      refine ⟨33775730491548876972499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 45034307322065169296665 33775730491548876972499)
                      ·
                        rfl

theorem cell23_65778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_65778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65778 prefixEnd_65778 := by exact prefixLift 65778
  have htrace : WordTrace (prefixWord ++ tailWord_65778) baseStart_65778 baseEnd_65778 := by
    simpa [prefixWord, tailWord_65778, baseEnd_65778] using wordTrace_append hprefix tailTrace_65778
  have hstable : (prefixWord ++ tailWord_65778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65778).length < 2 ^ (prefixWord ++ tailWord_65778).sum := by decide
  have hdescent : baseEnd_65778 < baseStart_65778 := by decide
  rcases family_descends (prefixWord ++ tailWord_65778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65887 : List Nat := [1, 1, 2, 3, 1, 2, 3, 3, 2, 5]
def baseStart_65887 : Nat := 118140960795 + 65887 * 2 ^ 59
def prefixEnd_65887 : Nat := 4983230072969 + 3 ^ 40 * 65887 * 2
def baseEnd_65887 : Nat := 11277233294296316836499

theorem tailTrace_65887 : CollatzResearch.WordTrace tailWord_65887 prefixEnd_65887 11277233294296316836499 := by
  unfold tailWord_65887
  simp only [CollatzResearch.WordTrace]
  refine ⟨2403096312310126448843915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1602064208206750965895943 2403096312310126448843915)
  ·
    refine ⟨3604644468465189673265873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2403096312310126448843915 3604644468465189673265873)
    ·
      refine ⟨2703483351348892254949405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3604644468465189673265873 2703483351348892254949405)
      ·
        refine ⟨1013806256755834595606027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2703483351348892254949405 1013806256755834595606027)
        ·
          refine ⟨1520709385133751893409041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1013806256755834595606027 1520709385133751893409041)
          ·
            refine ⟨1140532038850313920056781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1520709385133751893409041 1140532038850313920056781)
            ·
              refine ⟨427699514568867720021293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1140532038850313920056781 427699514568867720021293)
              ·
                refine ⟨160387317963325395007985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 427699514568867720021293 160387317963325395007985)
                ·
                  refine ⟨120290488472494046255989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160387317963325395007985 120290488472494046255989)
                  ·
                    refine ⟨11277233294296316836499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120290488472494046255989 11277233294296316836499)
                    ·
                      rfl

theorem cell23_65887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 5].length) (baseStart_65887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65887 prefixEnd_65887 := by exact prefixLift 65887
  have htrace : WordTrace (prefixWord ++ tailWord_65887) baseStart_65887 baseEnd_65887 := by
    simpa [prefixWord, tailWord_65887, baseEnd_65887] using wordTrace_append hprefix tailTrace_65887
  have hstable : (prefixWord ++ tailWord_65887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65887).length < 2 ^ (prefixWord ++ tailWord_65887).sum := by decide
  have hdescent : baseEnd_65887 < baseStart_65887 := by decide
  rcases family_descends (prefixWord ++ tailWord_65887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65942 : List Nat := [5, 3, 1, 2, 1, 1, 2, 3, 5]
def baseStart_65942 : Nat := 118140960795 + 65942 * 2 ^ 59
def prefixEnd_65942 : Nat := 4983230072969 + 3 ^ 40 * 65942 * 2
def baseEnd_65942 : Nat := 3762215702098470591305

theorem tailTrace_65942 : CollatzResearch.WordTrace tailWord_65942 prefixEnd_65942 3762215702098470591305 := by
  unfold tailWord_65942
  simp only [CollatzResearch.WordTrace]
  refine ⟨150318895444429427631005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1603401551407247228064053 150318895444429427631005)
  ·
    refine ⟨56369585791661035361627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150318895444429427631005 56369585791661035361627)
    ·
      refine ⟨84554378687491553042441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56369585791661035361627 84554378687491553042441)
      ·
        refine ⟨63415784015618664781831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84554378687491553042441 63415784015618664781831)
        ·
          refine ⟨95123676023427997172747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63415784015618664781831 95123676023427997172747)
          ·
            refine ⟨142685514035141995759121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95123676023427997172747 142685514035141995759121)
            ·
              refine ⟨107014135526356496819341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142685514035141995759121 107014135526356496819341)
              ·
                refine ⟨40130300822383686307253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107014135526356496819341 40130300822383686307253)
                ·
                  refine ⟨3762215702098470591305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40130300822383686307253 3762215702098470591305)
                  ·
                    rfl

theorem cell23_65942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_65942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65942 prefixEnd_65942 := by exact prefixLift 65942
  have htrace : WordTrace (prefixWord ++ tailWord_65942) baseStart_65942 baseEnd_65942 := by
    simpa [prefixWord, tailWord_65942, baseEnd_65942] using wordTrace_append hprefix tailTrace_65942
  have hstable : (prefixWord ++ tailWord_65942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65942).length < 2 ^ (prefixWord ++ tailWord_65942).sum := by decide
  have hdescent : baseEnd_65942 < baseStart_65942 := by decide
  rcases family_descends (prefixWord ++ tailWord_65942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65981 : List Nat := [1, 4, 1, 2, 2, 3, 3, 1, 6]
def baseStart_65981 : Nat := 118140960795 + 65981 * 2 ^ 59
def prefixEnd_65981 : Nat := 4983230072969 + 3 ^ 40 * 65981 * 2
def baseEnd_65981 : Nat := 3764440784934620303785

theorem tailTrace_65981 : CollatzResearch.WordTrace tailWord_65981 prefixEnd_65981 3764440784934620303785 := by
  unfold tailWord_65981
  simp only [CollatzResearch.WordTrace]
  refine ⟨2406524773969580502765797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1604349849313053668510531 2406524773969580502765797)
  ·
    refine ⟨451223395119296344268587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2406524773969580502765797 451223395119296344268587)
    ·
      refine ⟨676835092678944516402881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451223395119296344268587 676835092678944516402881)
      ·
        refine ⟨507626319509208387302161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 676835092678944516402881 507626319509208387302161)
        ·
          refine ⟨380719739631906290476621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 507626319509208387302161 380719739631906290476621)
          ·
            refine ⟨142769902361964858928733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 380719739631906290476621 142769902361964858928733)
            ·
              refine ⟨53538713385736822098275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142769902361964858928733 53538713385736822098275)
              ·
                refine ⟨80308070078605233147413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53538713385736822098275 80308070078605233147413)
                ·
                  refine ⟨3764440784934620303785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80308070078605233147413 3764440784934620303785)
                  ·
                    rfl

theorem cell23_65981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 6].length) (baseStart_65981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65981 prefixEnd_65981 := by exact prefixLift 65981
  have htrace : WordTrace (prefixWord ++ tailWord_65981) baseStart_65981 baseEnd_65981 := by
    simpa [prefixWord, tailWord_65981, baseEnd_65981] using wordTrace_append hprefix tailTrace_65981
  have hstable : (prefixWord ++ tailWord_65981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65981).length < 2 ^ (prefixWord ++ tailWord_65981).sum := by decide
  have hdescent : baseEnd_65981 < baseStart_65981 := by decide
  rcases family_descends (prefixWord ++ tailWord_65981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65991 : List Nat := [1, 1, 4, 1, 1, 4, 2, 2, 3, 1, 3]
def baseStart_65991 : Nat := 118140960795 + 65991 * 2 ^ 59
def prefixEnd_65991 : Nat := 4983230072969 + 3 ^ 40 * 65991 * 2
def baseEnd_65991 : Nat := 33885101870956543609019

theorem tailTrace_65991 : CollatzResearch.WordTrace tailWord_65991 prefixEnd_65991 33885101870956543609019 := by
  unfold tailWord_65991
  simp only [CollatzResearch.WordTrace]
  refine ⟨2406889503933352210629827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1604593002622234807086551 2406889503933352210629827)
  ·
    refine ⟨3610334255900028315944741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2406889503933352210629827 3610334255900028315944741)
    ·
      refine ⟨676937672981255309239639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3610334255900028315944741 676937672981255309239639)
      ·
        refine ⟨1015406509471882963859459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676937672981255309239639 1015406509471882963859459)
        ·
          refine ⟨1523109764207824445789189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1015406509471882963859459 1523109764207824445789189)
          ·
            refine ⟨285583080788967083585473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1523109764207824445789189 285583080788967083585473)
            ·
              refine ⟨214187310591725312689105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285583080788967083585473 214187310591725312689105)
              ·
                refine ⟨160640482943793984516829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214187310591725312689105 160640482943793984516829)
                ·
                  refine ⟨60240181103922744193811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160640482943793984516829 60240181103922744193811)
                  ·
                    refine ⟨90360271655884116290717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60240181103922744193811 90360271655884116290717)
                    ·
                      refine ⟨33885101870956543609019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 90360271655884116290717 33885101870956543609019)
                      ·
                        rfl

theorem cell23_65991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 3, 1, 3].length) (baseStart_65991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_65991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_65991 prefixEnd_65991 := by exact prefixLift 65991
  have htrace : WordTrace (prefixWord ++ tailWord_65991) baseStart_65991 baseEnd_65991 := by
    simpa [prefixWord, tailWord_65991, baseEnd_65991] using wordTrace_append hprefix tailTrace_65991
  have hstable : (prefixWord ++ tailWord_65991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65991).length < 2 ^ (prefixWord ++ tailWord_65991).sum := by decide
  have hdescent : baseEnd_65991 < baseStart_65991 := by decide
  rcases family_descends (prefixWord ++ tailWord_65991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66002 : List Nat := [3, 2, 2, 4, 1, 2, 1, 3, 1, 4]
def baseStart_66002 : Nat := 118140960795 + 66002 * 2 ^ 59
def prefixEnd_66002 : Nat := 4983230072969 + 3 ^ 40 * 66002 * 2
def baseEnd_66002 : Nat := 11296916719385333523823

theorem tailTrace_66002 : CollatzResearch.WordTrace tailWord_66002 prefixEnd_66002 11296916719385333523823 := by
  unfold tailWord_66002
  simp only [CollatzResearch.WordTrace]
  refine ⟨601822676723375272320065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1604860471262334059520173 601822676723375272320065)
  ·
    refine ⟨451367007542531454240049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 601822676723375272320065 451367007542531454240049)
    ·
      refine ⟨338525255656898590680037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451367007542531454240049 338525255656898590680037)
      ·
        refine ⟨63473485435668485752507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 338525255656898590680037 63473485435668485752507)
        ·
          refine ⟨95210228153502728628761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63473485435668485752507 95210228153502728628761)
          ·
            refine ⟨71407671115127046471571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95210228153502728628761 71407671115127046471571)
            ·
              refine ⟨107111506672690569707357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71407671115127046471571 107111506672690569707357)
              ·
                refine ⟨40166815002258963640259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107111506672690569707357 40166815002258963640259)
                ·
                  refine ⟨60250222503388445460389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40166815002258963640259 60250222503388445460389)
                  ·
                    refine ⟨11296916719385333523823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60250222503388445460389 11296916719385333523823)
                    ·
                      rfl

theorem cell23_66002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_66002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66002 prefixEnd_66002 := by exact prefixLift 66002
  have htrace : WordTrace (prefixWord ++ tailWord_66002) baseStart_66002 baseEnd_66002 := by
    simpa [prefixWord, tailWord_66002, baseEnd_66002] using wordTrace_append hprefix tailTrace_66002
  have hstable : (prefixWord ++ tailWord_66002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66002).length < 2 ^ (prefixWord ++ tailWord_66002).sum := by decide
  have hdescent : baseEnd_66002 < baseStart_66002 := by decide
  rcases family_descends (prefixWord ++ tailWord_66002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66027 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 6]
def baseStart_66027 : Nat := 118140960795 + 66027 * 2 ^ 59
def prefixEnd_66027 : Nat := 4983230072969 + 3 ^ 40 * 66027 * 2
def baseEnd_66027 : Nat := 33903587174518402758853

theorem tailTrace_66027 : CollatzResearch.WordTrace tailWord_66027 prefixEnd_66027 33903587174518402758853 := by
  unfold tailWord_66027
  simp only [CollatzResearch.WordTrace]
  refine ⟨2408202531802930358940335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1605468354535286905960223 2408202531802930358940335)
  ·
    refine ⟨3612303797704395538410503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2408202531802930358940335 3612303797704395538410503)
    ·
      refine ⟨5418455696556593307615755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3612303797704395538410503 5418455696556593307615755)
      ·
        refine ⟨8127683544834889961423633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5418455696556593307615755 8127683544834889961423633)
        ·
          refine ⟨6095762658626167471067725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8127683544834889961423633 6095762658626167471067725)
          ·
            refine ⟨2285910996984812801650397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6095762658626167471067725 2285910996984812801650397)
            ·
              refine ⟨857216623869304800618899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2285910996984812801650397 857216623869304800618899)
              ·
                refine ⟨1285824935803957200928349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 857216623869304800618899 1285824935803957200928349)
                ·
                  refine ⟨482184350926483950348131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1285824935803957200928349 482184350926483950348131)
                  ·
                    refine ⟨723276526389725925522197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 482184350926483950348131 723276526389725925522197)
                    ·
                      refine ⟨33903587174518402758853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 723276526389725925522197 33903587174518402758853)
                      ·
                        rfl

theorem cell23_66027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 6].length) (baseStart_66027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66027 prefixEnd_66027 := by exact prefixLift 66027
  have htrace : WordTrace (prefixWord ++ tailWord_66027) baseStart_66027 baseEnd_66027 := by
    simpa [prefixWord, tailWord_66027, baseEnd_66027] using wordTrace_append hprefix tailTrace_66027
  have hstable : (prefixWord ++ tailWord_66027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66027).length < 2 ^ (prefixWord ++ tailWord_66027).sum := by decide
  have hdescent : baseEnd_66027 < baseStart_66027 := by decide
  rcases family_descends (prefixWord ++ tailWord_66027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66044 : List Nat := [2, 2, 2, 1, 2, 1, 1, 5, 1, 2, 4]
def baseStart_66044 : Nat := 118140960795 + 66044 * 2 ^ 59
def prefixEnd_66044 : Nat := 4983230072969 + 3 ^ 40 * 66044 * 2
def baseEnd_66044 : Nat := 33912316345644836246275

theorem tailTrace_66044 : CollatzResearch.WordTrace tailWord_66044 prefixEnd_66044 33912316345644836246275 := by
  unfold tailWord_66044
  simp only [CollatzResearch.WordTrace]
  refine ⟨1204411286370671131154593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1605881715160894841539457 1204411286370671131154593)
  ·
    refine ⟨903308464778003348365945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1204411286370671131154593 903308464778003348365945)
    ·
      refine ⟨677481348583502511274459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 903308464778003348365945 677481348583502511274459)
      ·
        refine ⟨1016222022875253766911689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 677481348583502511274459 1016222022875253766911689)
        ·
          refine ⟨762166517156440325183767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1016222022875253766911689 762166517156440325183767)
          ·
            refine ⟨1143249775734660487775651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 762166517156440325183767 1143249775734660487775651)
            ·
              refine ⟨1714874663601990731663477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1143249775734660487775651 1714874663601990731663477)
              ·
                refine ⟨160769499712686631093451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1714874663601990731663477 160769499712686631093451)
                ·
                  refine ⟨241154249569029946640177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160769499712686631093451 241154249569029946640177)
                  ·
                    refine ⟨180865687176772459980133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 241154249569029946640177 180865687176772459980133)
                    ·
                      refine ⟨33912316345644836246275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 180865687176772459980133 33912316345644836246275)
                      ·
                        rfl

theorem cell23_66044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_66044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66044 prefixEnd_66044 := by exact prefixLift 66044
  have htrace : WordTrace (prefixWord ++ tailWord_66044) baseStart_66044 baseEnd_66044 := by
    simpa [prefixWord, tailWord_66044, baseEnd_66044] using wordTrace_append hprefix tailTrace_66044
  have hstable : (prefixWord ++ tailWord_66044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66044).length < 2 ^ (prefixWord ++ tailWord_66044).sum := by decide
  have hdescent : baseEnd_66044 < baseStart_66044 := by decide
  rcases family_descends (prefixWord ++ tailWord_66044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66068 : List Nat := [2, 4, 3, 1, 1, 1, 3, 1, 1, 1, 5]
def baseStart_66068 : Nat := 118140960795 + 66068 * 2 ^ 59
def prefixEnd_66068 : Nat := 4983230072969 + 3 ^ 40 * 66068 * 2
def baseEnd_66068 : Nat := 33924639881352742346165

theorem tailTrace_66068 : CollatzResearch.WordTrace tailWord_66068 prefixEnd_66068 33924639881352742346165 := by
  unfold tailWord_66068
  simp only [CollatzResearch.WordTrace]
  refine ⟨1204848962327197180591429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1606465283102929574121905 1204848962327197180591429)
  ·
    refine ⟨225909180436349471360893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1204848962327197180591429 225909180436349471360893)
    ·
      refine ⟨84715942663631051760335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 225909180436349471360893 84715942663631051760335)
      ·
        refine ⟨127073913995446577640503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84715942663631051760335 127073913995446577640503)
        ·
          refine ⟨190610870993169866460755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127073913995446577640503 190610870993169866460755)
          ·
            refine ⟨285916306489754799691133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190610870993169866460755 285916306489754799691133)
            ·
              refine ⟨107218614933658049884175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285916306489754799691133 107218614933658049884175)
              ·
                refine ⟨160827922400487074826263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107218614933658049884175 160827922400487074826263)
                ·
                  refine ⟨241241883600730612239395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 160827922400487074826263 241241883600730612239395)
                  ·
                    refine ⟨361862825401095918359093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 241241883600730612239395 361862825401095918359093)
                    ·
                      refine ⟨33924639881352742346165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 361862825401095918359093 33924639881352742346165)
                      ·
                        rfl

theorem cell23_66068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_66068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66068 prefixEnd_66068 := by exact prefixLift 66068
  have htrace : WordTrace (prefixWord ++ tailWord_66068) baseStart_66068 baseEnd_66068 := by
    simpa [prefixWord, tailWord_66068, baseEnd_66068] using wordTrace_append hprefix tailTrace_66068
  have hstable : (prefixWord ++ tailWord_66068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66068).length < 2 ^ (prefixWord ++ tailWord_66068).sum := by decide
  have hdescent : baseEnd_66068 < baseStart_66068 := by decide
  rcases family_descends (prefixWord ++ tailWord_66068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66071 : List Nat := [1, 1, 3, 6, 2, 10]
def baseStart_66071 : Nat := 118140960795 + 66071 * 2 ^ 59
def prefixEnd_66071 : Nat := 4983230072969 + 3 ^ 40 * 66071 * 2
def baseEnd_66071 : Nat := 139613910795540043657

theorem tailTrace_66071 : CollatzResearch.WordTrace tailWord_66071 prefixEnd_66071 139613910795540043657 := by
  unfold tailWord_66071
  simp only [CollatzResearch.WordTrace]
  refine ⟨2409807343643525873542067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1606538229095683915694711 2409807343643525873542067)
  ·
    refine ⟨3614711015465288810313101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2409807343643525873542067 3614711015465288810313101)
    ·
      refine ⟨1355516630799483303867413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3614711015465288810313101 1355516630799483303867413)
      ·
        refine ⟨63539842068725779868785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1355516630799483303867413 63539842068725779868785)
        ·
          refine ⟨47654881551544334901589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63539842068725779868785 47654881551544334901589)
          ·
            refine ⟨139613910795540043657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 47654881551544334901589 139613910795540043657)
            ·
              rfl

theorem cell23_66071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 10].length) (baseStart_66071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66071 prefixEnd_66071 := by exact prefixLift 66071
  have htrace : WordTrace (prefixWord ++ tailWord_66071) baseStart_66071 baseEnd_66071 := by
    simpa [prefixWord, tailWord_66071, baseEnd_66071] using wordTrace_append hprefix tailTrace_66071
  have hstable : (prefixWord ++ tailWord_66071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66071).length < 2 ^ (prefixWord ++ tailWord_66071).sum := by decide
  have hdescent : baseEnd_66071 < baseStart_66071 := by decide
  rcases family_descends (prefixWord ++ tailWord_66071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66098 : List Nat := [3, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3]
def baseStart_66098 : Nat := 118140960795 + 66098 * 2 ^ 59
def prefixEnd_66098 : Nat := 4983230072969 + 3 ^ 40 * 66098 * 2
def baseEnd_66098 : Nat := 33940044300987624971027

theorem tailTrace_66098 : CollatzResearch.WordTrace tailWord_66098 prefixEnd_66098 33940044300987624971027 := by
  unfold tailWord_66098
  simp only [CollatzResearch.WordTrace]
  refine ⟨602698028636427371193737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1607194743030472989849965 602698028636427371193737)
  ·
    refine ⟨452023521477320528395303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 602698028636427371193737 452023521477320528395303)
    ·
      refine ⟨678035282215980792592955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452023521477320528395303 678035282215980792592955)
      ·
        refine ⟨1017052923323971188889433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 678035282215980792592955 1017052923323971188889433)
        ·
          refine ⟨762789692492978391667075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1017052923323971188889433 762789692492978391667075)
          ·
            refine ⟨1144184538739467587500613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 762789692492978391667075 1144184538739467587500613)
            ·
              refine ⟨214534601013650172656365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1144184538739467587500613 214534601013650172656365)
              ·
                refine ⟨80450475380118814746137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 214534601013650172656365 80450475380118814746137)
                ·
                  refine ⟨60337856535089111059603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80450475380118814746137 60337856535089111059603)
                  ·
                    refine ⟨90506784802633666589405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60337856535089111059603 90506784802633666589405)
                    ·
                      refine ⟨33940044300987624971027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 90506784802633666589405 33940044300987624971027)
                      ·
                        rfl

theorem cell23_66098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3].length) (baseStart_66098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66098 prefixEnd_66098 := by exact prefixLift 66098
  have htrace : WordTrace (prefixWord ++ tailWord_66098) baseStart_66098 baseEnd_66098 := by
    simpa [prefixWord, tailWord_66098, baseEnd_66098] using wordTrace_append hprefix tailTrace_66098
  have hstable : (prefixWord ++ tailWord_66098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66098).length < 2 ^ (prefixWord ++ tailWord_66098).sum := by decide
  have hdescent : baseEnd_66098 < baseStart_66098 := by decide
  rcases family_descends (prefixWord ++ tailWord_66098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66104 : List Nat := [2, 1, 2, 1, 4, 1, 1, 2, 2, 3, 4]
def baseStart_66104 : Nat := 118140960795 + 66104 * 2 ^ 59
def prefixEnd_66104 : Nat := 4983230072969 + 3 ^ 40 * 66104 * 2
def baseEnd_66104 : Nat := 33943125184914601495999

theorem tailTrace_66104 : CollatzResearch.WordTrace tailWord_66104 prefixEnd_66104 33943125184914601495999 := by
  unfold tailWord_66104
  simp only [CollatzResearch.WordTrace]
  refine ⟨1205505476261986254746683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1607340635015981672995577 1205505476261986254746683)
  ·
    refine ⟨1808258214392979382120025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1205505476261986254746683 1808258214392979382120025)
    ·
      refine ⟨1356193660794734536590019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1808258214392979382120025 1356193660794734536590019)
      ·
        refine ⟨2034290491192101804885029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1356193660794734536590019 2034290491192101804885029)
        ·
          refine ⟨381429467098519088415943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2034290491192101804885029 381429467098519088415943)
          ·
            refine ⟨572144200647778632623915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381429467098519088415943 572144200647778632623915)
            ·
              refine ⟨858216300971667948935873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572144200647778632623915 858216300971667948935873)
              ·
                refine ⟨643662225728750961701905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 858216300971667948935873 643662225728750961701905)
                ·
                  refine ⟨482746669296563221276429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 643662225728750961701905 482746669296563221276429)
                  ·
                    refine ⟨181030000986211207978661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 482746669296563221276429 181030000986211207978661)
                    ·
                      refine ⟨33943125184914601495999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 181030000986211207978661 33943125184914601495999)
                      ·
                        rfl

theorem cell23_66104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_66104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66104 prefixEnd_66104 := by exact prefixLift 66104
  have htrace : WordTrace (prefixWord ++ tailWord_66104) baseStart_66104 baseEnd_66104 := by
    simpa [prefixWord, tailWord_66104, baseEnd_66104] using wordTrace_append hprefix tailTrace_66104
  have hstable : (prefixWord ++ tailWord_66104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66104).length < 2 ^ (prefixWord ++ tailWord_66104).sum := by decide
  have hdescent : baseEnd_66104 < baseStart_66104 := by decide
  rcases family_descends (prefixWord ++ tailWord_66104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66108 : List Nat := [2, 2, 2, 2, 3, 1, 2, 1, 3, 3, 2]
def baseStart_66108 : Nat := 118140960795 + 66108 * 2 ^ 59
def prefixEnd_66108 : Nat := 4983230072969 + 3 ^ 40 * 66108 * 2
def baseEnd_66108 : Nat := 33945179107532585845981

theorem tailTrace_66108 : CollatzResearch.WordTrace tailWord_66108 prefixEnd_66108 33945179107532585845981 := by
  unfold tailWord_66108
  simp only [CollatzResearch.WordTrace]
  refine ⟨1205578422254740596319489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1607437896339654128425985 1205578422254740596319489)
  ·
    refine ⟨904183816691055447239617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1205578422254740596319489 904183816691055447239617)
    ·
      refine ⟨678137862518291585429713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 904183816691055447239617 678137862518291585429713)
      ·
        refine ⟨508603396888718689072285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 678137862518291585429713 508603396888718689072285)
        ·
          refine ⟨190726273833269508402107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 508603396888718689072285 190726273833269508402107)
          ·
            refine ⟨286089410749904262603161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190726273833269508402107 286089410749904262603161)
            ·
              refine ⟨214567058062428196952371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286089410749904262603161 214567058062428196952371)
              ·
                refine ⟨321850587093642295428557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214567058062428196952371 321850587093642295428557)
                ·
                  refine ⟨120693970160115860785709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 321850587093642295428557 120693970160115860785709)
                  ·
                    refine ⟨45260238810043447794641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120693970160115860785709 45260238810043447794641)
                    ·
                      refine ⟨33945179107532585845981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 45260238810043447794641 33945179107532585845981)
                      ·
                        rfl

theorem cell23_66108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_66108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66108 prefixEnd_66108 := by exact prefixLift 66108
  have htrace : WordTrace (prefixWord ++ tailWord_66108) baseStart_66108 baseEnd_66108 := by
    simpa [prefixWord, tailWord_66108, baseEnd_66108] using wordTrace_append hprefix tailTrace_66108
  have hstable : (prefixWord ++ tailWord_66108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66108).length < 2 ^ (prefixWord ++ tailWord_66108).sum := by decide
  have hdescent : baseEnd_66108 < baseStart_66108 := by decide
  rcases family_descends (prefixWord ++ tailWord_66108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66116 : List Nat := [2, 3, 5, 1, 2, 1, 2, 1, 1, 1, 4]
def baseStart_66116 : Nat := 118140960795 + 66116 * 2 ^ 59
def prefixEnd_66116 : Nat := 4983230072969 + 3 ^ 40 * 66116 * 2
def baseEnd_66116 : Nat := 33949286952768554545945

theorem tailTrace_66116 : CollatzResearch.WordTrace tailWord_66116 prefixEnd_66116 33949286952768554545945 := by
  unfold tailWord_66116
  simp only [CollatzResearch.WordTrace]
  refine ⟨1205724314240249279465101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1607632418986999039286801 1205724314240249279465101)
  ·
    refine ⟨452146617840093479799413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1205724314240249279465101 452146617840093479799413)
    ·
      refine ⟨42388745422508763731195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 452146617840093479799413 42388745422508763731195)
      ·
        refine ⟨63583118133763145596793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42388745422508763731195 63583118133763145596793)
        ·
          refine ⟨47687338600322359197595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63583118133763145596793 47687338600322359197595)
          ·
            refine ⟨71531007900483538796393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47687338600322359197595 71531007900483538796393)
            ·
              refine ⟨53648255925362654097295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71531007900483538796393 53648255925362654097295)
              ·
                refine ⟨80472383888043981145943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53648255925362654097295 80472383888043981145943)
                ·
                  refine ⟨120708575832065971718915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80472383888043981145943 120708575832065971718915)
                  ·
                    refine ⟨181062863748098957578373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120708575832065971718915 181062863748098957578373)
                    ·
                      refine ⟨33949286952768554545945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 181062863748098957578373 33949286952768554545945)
                      ·
                        rfl

theorem cell23_66116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_66116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66116 prefixEnd_66116 := by exact prefixLift 66116
  have htrace : WordTrace (prefixWord ++ tailWord_66116) baseStart_66116 baseEnd_66116 := by
    simpa [prefixWord, tailWord_66116, baseEnd_66116] using wordTrace_append hprefix tailTrace_66116
  have hstable : (prefixWord ++ tailWord_66116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66116).length < 2 ^ (prefixWord ++ tailWord_66116).sum := by decide
  have hdescent : baseEnd_66116 < baseStart_66116 := by decide
  rcases family_descends (prefixWord ++ tailWord_66116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66124 : List Nat := [2, 2, 1, 3, 1, 2, 2, 1, 1, 3, 5]
def baseStart_66124 : Nat := 118140960795 + 66124 * 2 ^ 59
def prefixEnd_66124 : Nat := 4983230072969 + 3 ^ 40 * 66124 * 2
def baseEnd_66124 : Nat := 33953394798004523245907

theorem tailTrace_66124 : CollatzResearch.WordTrace tailWord_66124 prefixEnd_66124 33953394798004523245907 := by
  unfold tailWord_66124
  simp only [CollatzResearch.WordTrace]
  refine ⟨1205870206225757962610713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1607826941634343950147617 1205870206225757962610713)
  ·
    refine ⟨904402654669318471958035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1205870206225757962610713 904402654669318471958035)
    ·
      refine ⟨1356603982003977707937053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 904402654669318471958035 1356603982003977707937053)
      ·
        refine ⟨508726493251491640476395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1356603982003977707937053 508726493251491640476395)
        ·
          refine ⟨763089739877237460714593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508726493251491640476395 763089739877237460714593)
          ·
            refine ⟨572317304907928095535945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 763089739877237460714593 572317304907928095535945)
            ·
              refine ⟨429237978680946071651959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 572317304907928095535945 429237978680946071651959)
              ·
                refine ⟨643856968021419107477939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 429237978680946071651959 643856968021419107477939)
                ·
                  refine ⟨965785452032128661216909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 643856968021419107477939 965785452032128661216909)
                  ·
                    refine ⟨362169544512048247956341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 965785452032128661216909 362169544512048247956341)
                    ·
                      refine ⟨33953394798004523245907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 362169544512048247956341 33953394798004523245907)
                      ·
                        rfl

theorem cell23_66124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_66124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66124 prefixEnd_66124 := by exact prefixLift 66124
  have htrace : WordTrace (prefixWord ++ tailWord_66124) baseStart_66124 baseEnd_66124 := by
    simpa [prefixWord, tailWord_66124, baseEnd_66124] using wordTrace_append hprefix tailTrace_66124
  have hstable : (prefixWord ++ tailWord_66124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66124).length < 2 ^ (prefixWord ++ tailWord_66124).sum := by decide
  have hdescent : baseEnd_66124 < baseStart_66124 := by decide
  rcases family_descends (prefixWord ++ tailWord_66124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66144 : List Nat := [2, 1, 1, 3, 2, 1, 3, 3, 7]
def baseStart_66144 : Nat := 118140960795 + 66144 * 2 ^ 59
def prefixEnd_66144 : Nat := 4983230072969 + 3 ^ 40 * 66144 * 2
def baseEnd_66144 : Nat := 3773740490121604999535

theorem tailTrace_66144 : CollatzResearch.WordTrace tailWord_66144 prefixEnd_66144 3773740490121604999535 := by
  unfold tailWord_66144
  simp only [CollatzResearch.WordTrace]
  refine ⟨1206234936189529670474743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1608313248252706227299657 1206234936189529670474743)
  ·
    refine ⟨1809352404284294505712115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1206234936189529670474743 1809352404284294505712115)
    ·
      refine ⟨2714028606426441758568173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1809352404284294505712115 2714028606426441758568173)
      ·
        refine ⟨1017760727409915659463065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2714028606426441758568173 1017760727409915659463065)
        ·
          refine ⟨763320545557436744597299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1017760727409915659463065 763320545557436744597299)
          ·
            refine ⟨1144980818336155116895949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 763320545557436744597299 1144980818336155116895949)
            ·
              refine ⟨429367806876058168835981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1144980818336155116895949 429367806876058168835981)
              ·
                refine ⟨161012927578521813313493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 429367806876058168835981 161012927578521813313493)
                ·
                  refine ⟨3773740490121604999535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 161012927578521813313493 3773740490121604999535)
                  ·
                    rfl

theorem cell23_66144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 7].length) (baseStart_66144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66144 prefixEnd_66144 := by exact prefixLift 66144
  have htrace : WordTrace (prefixWord ++ tailWord_66144) baseStart_66144 baseEnd_66144 := by
    simpa [prefixWord, tailWord_66144, baseEnd_66144] using wordTrace_append hprefix tailTrace_66144
  have hstable : (prefixWord ++ tailWord_66144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66144).length < 2 ^ (prefixWord ++ tailWord_66144).sum := by decide
  have hdescent : baseEnd_66144 < baseStart_66144 := by decide
  rcases family_descends (prefixWord ++ tailWord_66144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66224 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 6]
def baseStart_66224 : Nat := 118140960795 + 66224 * 2 ^ 59
def prefixEnd_66224 : Nat := 4983230072969 + 3 ^ 40 * 66224 * 2
def baseEnd_66224 : Nat := 34004742863454131995447

theorem tailTrace_66224 : CollatzResearch.WordTrace tailWord_66224 prefixEnd_66224 34004742863454131995447 := by
  unfold tailWord_66224
  simp only [CollatzResearch.WordTrace]
  refine ⟨1207693856044616501930863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1610258474726155335907817 1207693856044616501930863)
  ·
    refine ⟨1811540784066924752896295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1207693856044616501930863 1811540784066924752896295)
    ·
      refine ⟨2717311176100387129344443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1811540784066924752896295 2717311176100387129344443)
      ·
        refine ⟨4075966764150580694016665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2717311176100387129344443 4075966764150580694016665)
        ·
          refine ⟨3056975073112935520512499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4075966764150580694016665 3056975073112935520512499)
          ·
            refine ⟨4585462609669403280768749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3056975073112935520512499 4585462609669403280768749)
            ·
              refine ⟨1719548478626026230288281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4585462609669403280768749 1719548478626026230288281)
              ·
                refine ⟨1289661358969519672716211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1719548478626026230288281 1289661358969519672716211)
                ·
                  refine ⟨1934492038454279509074317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1289661358969519672716211 1934492038454279509074317)
                  ·
                    refine ⟨725434514420354815902869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1934492038454279509074317 725434514420354815902869)
                    ·
                      refine ⟨34004742863454131995447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 725434514420354815902869 34004742863454131995447)
                      ·
                        rfl

theorem cell23_66224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 6].length) (baseStart_66224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66224 prefixEnd_66224 := by exact prefixLift 66224
  have htrace : WordTrace (prefixWord ++ tailWord_66224) baseStart_66224 baseEnd_66224 := by
    simpa [prefixWord, tailWord_66224, baseEnd_66224] using wordTrace_append hprefix tailTrace_66224
  have hstable : (prefixWord ++ tailWord_66224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66224).length < 2 ^ (prefixWord ++ tailWord_66224).sum := by decide
  have hdescent : baseEnd_66224 < baseStart_66224 := by decide
  rcases family_descends (prefixWord ++ tailWord_66224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66225 : List Nat := [1, 2, 2, 6, 1, 1, 2, 1, 2, 5]
def baseStart_66225 : Nat := 118140960795 + 66225 * 2 ^ 59
def prefixEnd_66225 : Nat := 4983230072969 + 3 ^ 40 * 66225 * 2
def baseEnd_66225 : Nat := 11335085448036209360981

theorem tailTrace_66225 : CollatzResearch.WordTrace tailWord_66225 prefixEnd_66225 11335085448036209360981 := by
  unfold tailWord_66225
  simp only [CollatzResearch.WordTrace]
  refine ⟨2415424185085610174648129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1610282790057073449765419 2415424185085610174648129)
  ·
    refine ⟨1811568138814207630986097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2415424185085610174648129 1811568138814207630986097)
    ·
      refine ⟨1358676104110655723239573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1811568138814207630986097 1358676104110655723239573)
      ·
        refine ⟨63687942380186987026855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1358676104110655723239573 63687942380186987026855)
        ·
          refine ⟨95531913570280480540283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63687942380186987026855 95531913570280480540283)
          ·
            refine ⟨143297870355420720810425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95531913570280480540283 143297870355420720810425)
            ·
              refine ⟨107473402766565540607819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143297870355420720810425 107473402766565540607819)
              ·
                refine ⟨161210104149848310911729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107473402766565540607819 161210104149848310911729)
                ·
                  refine ⟨120907578112386233183797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161210104149848310911729 120907578112386233183797)
                  ·
                    refine ⟨11335085448036209360981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120907578112386233183797 11335085448036209360981)
                    ·
                      rfl

theorem cell23_66225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 5].length) (baseStart_66225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66225 prefixEnd_66225 := by exact prefixLift 66225
  have htrace : WordTrace (prefixWord ++ tailWord_66225) baseStart_66225 baseEnd_66225 := by
    simpa [prefixWord, tailWord_66225, baseEnd_66225] using wordTrace_append hprefix tailTrace_66225
  have hstable : (prefixWord ++ tailWord_66225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66225).length < 2 ^ (prefixWord ++ tailWord_66225).sum := by decide
  have hdescent : baseEnd_66225 < baseStart_66225 := by decide
  rcases family_descends (prefixWord ++ tailWord_66225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66246 : List Nat := [6, 1, 2, 1, 2, 2, 2, 2, 5]
def baseStart_66246 : Nat := 118140960795 + 66246 * 2 ^ 59
def prefixEnd_66246 : Nat := 4983230072969 + 3 ^ 40 * 66246 * 2
def baseEnd_66246 : Nat := 3779559937539227324483

theorem tailTrace_66246 : CollatzResearch.WordTrace tailWord_66246 prefixEnd_66246 3779559937539227324483 := by
  unfold tailWord_66246
  simp only [CollatzResearch.WordTrace]
  refine ⟨75505941187797836286331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1610793412006353840775061 75505941187797836286331)
  ·
    refine ⟨113258911781696754429497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75505941187797836286331 113258911781696754429497)
    ·
      refine ⟨84944183836272565822123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113258911781696754429497 84944183836272565822123)
      ·
        refine ⟨127416275754408848733185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84944183836272565822123 127416275754408848733185)
        ·
          refine ⟨95562206815806636549889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127416275754408848733185 95562206815806636549889)
          ·
            refine ⟨71671655111854977412417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95562206815806636549889 71671655111854977412417)
            ·
              refine ⟨53753741333891233059313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71671655111854977412417 53753741333891233059313)
              ·
                refine ⟨40315306000418424794485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53753741333891233059313 40315306000418424794485)
                ·
                  refine ⟨3779559937539227324483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40315306000418424794485 3779559937539227324483)
                  ·
                    rfl

theorem cell23_66246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_66246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66246 prefixEnd_66246 := by exact prefixLift 66246
  have htrace : WordTrace (prefixWord ++ tailWord_66246) baseStart_66246 baseEnd_66246 := by
    simpa [prefixWord, tailWord_66246, baseEnd_66246] using wordTrace_append hprefix tailTrace_66246
  have hstable : (prefixWord ++ tailWord_66246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66246).length < 2 ^ (prefixWord ++ tailWord_66246).sum := by decide
  have hdescent : baseEnd_66246 < baseStart_66246 := by decide
  rcases family_descends (prefixWord ++ tailWord_66246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66248 : List Nat := [2, 1, 3, 1, 2, 3, 2, 2, 2, 2, 3]
def baseStart_66248 : Nat := 118140960795 + 66248 * 2 ^ 59
def prefixEnd_66248 : Nat := 4983230072969 + 3 ^ 40 * 66248 * 2
def baseEnd_66248 : Nat := 34017066399162038095337

theorem tailTrace_66248 : CollatzResearch.WordTrace tailWord_66248 prefixEnd_66248 34017066399162038095337 := by
  unfold tailWord_66248
  simp only [CollatzResearch.WordTrace]
  refine ⟨1208131532001142551367699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1610842042668190068490265 1208131532001142551367699)
  ·
    refine ⟨1812197298001713827051549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1208131532001142551367699 1812197298001713827051549)
    ·
      refine ⟨679573986750642685144331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1812197298001713827051549 679573986750642685144331)
      ·
        refine ⟨1019360980125964027716497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679573986750642685144331 1019360980125964027716497)
        ·
          refine ⟨764520735094473020787373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1019360980125964027716497 764520735094473020787373)
          ·
            refine ⟨286695275660427382795265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 764520735094473020787373 286695275660427382795265)
            ·
              refine ⟨215021456745320537096449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286695275660427382795265 215021456745320537096449)
              ·
                refine ⟨161266092558990402822337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215021456745320537096449 161266092558990402822337)
                ·
                  refine ⟨120949569419242802116753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161266092558990402822337 120949569419242802116753)
                  ·
                    refine ⟨90712177064432101587565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120949569419242802116753 90712177064432101587565)
                    ·
                      refine ⟨34017066399162038095337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 90712177064432101587565 34017066399162038095337)
                      ·
                        rfl

theorem cell23_66248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_66248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66248 prefixEnd_66248 := by exact prefixLift 66248
  have htrace : WordTrace (prefixWord ++ tailWord_66248) baseStart_66248 baseEnd_66248 := by
    simpa [prefixWord, tailWord_66248, baseEnd_66248] using wordTrace_append hprefix tailTrace_66248
  have hstable : (prefixWord ++ tailWord_66248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66248).length < 2 ^ (prefixWord ++ tailWord_66248).sum := by decide
  have hdescent : baseEnd_66248 < baseStart_66248 := by decide
  rcases family_descends (prefixWord ++ tailWord_66248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66281 : List Nat := [1, 2, 1, 1, 1, 2, 6, 1, 3, 5]
def baseStart_66281 : Nat := 118140960795 + 66281 * 2 ^ 59
def prefixEnd_66281 : Nat := 4983230072969 + 3 ^ 40 * 66281 * 2
def baseEnd_66281 : Nat := 11344670420253469660895

theorem tailTrace_66281 : CollatzResearch.WordTrace tailWord_66281 prefixEnd_66281 11344670420253469660895 := by
  unfold tailWord_66281
  simp only [CollatzResearch.WordTrace]
  refine ⟨2417466672882731738686697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1611644448588487825791131 2417466672882731738686697)
  ·
    refine ⟨1813100004662048804015023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2417466672882731738686697 1813100004662048804015023)
    ·
      refine ⟨2719650006993073206022535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1813100004662048804015023 2719650006993073206022535)
      ·
        refine ⟨4079475010489609809033803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2719650006993073206022535 4079475010489609809033803)
        ·
          refine ⟨6119212515734414713550705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4079475010489609809033803 6119212515734414713550705)
          ·
            refine ⟨4589409386800811035163029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6119212515734414713550705 4589409386800811035163029)
            ·
              refine ⟨215128565006288017273267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4589409386800811035163029 215128565006288017273267)
              ·
                refine ⟨322692847509432025909901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215128565006288017273267 322692847509432025909901)
                ·
                  refine ⟨121009817816037009716213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 322692847509432025909901 121009817816037009716213)
                  ·
                    refine ⟨11344670420253469660895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 121009817816037009716213 11344670420253469660895)
                    ·
                      rfl

theorem cell23_66281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 5].length) (baseStart_66281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66281 prefixEnd_66281 := by exact prefixLift 66281
  have htrace : WordTrace (prefixWord ++ tailWord_66281) baseStart_66281 baseEnd_66281 := by
    simpa [prefixWord, tailWord_66281, baseEnd_66281] using wordTrace_append hprefix tailTrace_66281
  have hstable : (prefixWord ++ tailWord_66281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66281).length < 2 ^ (prefixWord ++ tailWord_66281).sum := by decide
  have hdescent : baseEnd_66281 < baseStart_66281 := by decide
  rcases family_descends (prefixWord ++ tailWord_66281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66288 : List Nat := [2, 1, 1, 1, 3, 1, 5, 1, 1, 5, 2]
def baseStart_66288 : Nat := 118140960795 + 66288 * 2 ^ 59
def prefixEnd_66288 : Nat := 4983230072969 + 3 ^ 40 * 66288 * 2
def baseEnd_66288 : Nat := 34037605625341881595153

theorem tailTrace_66288 : CollatzResearch.WordTrace tailWord_66288 prefixEnd_66288 34037605625341881595153 := by
  unfold tailWord_66288
  simp only [CollatzResearch.WordTrace]
  refine ⟨1208860991928685967095759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1611814655904914622794345 1208860991928685967095759)
  ·
    refine ⟨1813291487893028950643639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1208860991928685967095759 1813291487893028950643639)
    ·
      refine ⟨2719937231839543425965459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1813291487893028950643639 2719937231839543425965459)
      ·
        refine ⟨4079905847759315138948189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2719937231839543425965459 4079905847759315138948189)
        ·
          refine ⟨1529964692909743177105571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4079905847759315138948189 1529964692909743177105571)
          ·
            refine ⟨2294947039364614765658357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1529964692909743177105571 2294947039364614765658357)
            ·
              refine ⟨215151284940432634280471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2294947039364614765658357 215151284940432634280471)
              ·
                refine ⟨322726927410648951420707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215151284940432634280471 322726927410648951420707)
                ·
                  refine ⟨484090391115973427131061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322726927410648951420707 484090391115973427131061)
                  ·
                    refine ⟨45383474167122508793537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 484090391115973427131061 45383474167122508793537)
                    ·
                      refine ⟨34037605625341881595153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 45383474167122508793537 34037605625341881595153)
                      ·
                        rfl

theorem cell23_66288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 1, 5, 2].length) (baseStart_66288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66288 prefixEnd_66288 := by exact prefixLift 66288
  have htrace : WordTrace (prefixWord ++ tailWord_66288) baseStart_66288 baseEnd_66288 := by
    simpa [prefixWord, tailWord_66288, baseEnd_66288] using wordTrace_append hprefix tailTrace_66288
  have hstable : (prefixWord ++ tailWord_66288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66288).length < 2 ^ (prefixWord ++ tailWord_66288).sum := by decide
  have hdescent : baseEnd_66288 < baseStart_66288 := by decide
  rcases family_descends (prefixWord ++ tailWord_66288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66312 : List Nat := [2, 1, 3, 2, 2, 2, 2, 4, 1, 1, 3]
def baseStart_66312 : Nat := 118140960795 + 66312 * 2 ^ 59
def prefixEnd_66312 : Nat := 4983230072969 + 3 ^ 40 * 66312 * 2
def baseEnd_66312 : Nat := 34049929161049787695043

theorem tailTrace_66312 : CollatzResearch.WordTrace tailWord_66312 prefixEnd_66312 34049929161049787695043 := by
  unfold tailWord_66312
  simp only [CollatzResearch.WordTrace]
  refine ⟨1209298667885212016532595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1612398223846949355376793 1209298667885212016532595)
  ·
    refine ⟨1813948001827818024798893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1209298667885212016532595 1813948001827818024798893)
    ·
      refine ⟨680230500685431759299585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1813948001827818024798893 680230500685431759299585)
      ·
        refine ⟨510172875514073819474689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 680230500685431759299585 510172875514073819474689)
        ·
          refine ⟨382629656635555364606017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 510172875514073819474689 382629656635555364606017)
          ·
            refine ⟨286972242476666523454513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382629656635555364606017 286972242476666523454513)
            ·
              refine ⟨215229181857499892590885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286972242476666523454513 215229181857499892590885)
              ·
                refine ⟨40355471598281229860791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215229181857499892590885 40355471598281229860791)
                ·
                  refine ⟨60533207397421844791187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40355471598281229860791 60533207397421844791187)
                  ·
                    refine ⟨90799811096132767186781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60533207397421844791187 90799811096132767186781)
                    ·
                      refine ⟨34049929161049787695043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 90799811096132767186781 34049929161049787695043)
                      ·
                        rfl

theorem cell23_66312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_66312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66312 prefixEnd_66312 := by exact prefixLift 66312
  have htrace : WordTrace (prefixWord ++ tailWord_66312) baseStart_66312 baseEnd_66312 := by
    simpa [prefixWord, tailWord_66312, baseEnd_66312] using wordTrace_append hprefix tailTrace_66312
  have hstable : (prefixWord ++ tailWord_66312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66312).length < 2 ^ (prefixWord ++ tailWord_66312).sum := by decide
  have hdescent : baseEnd_66312 < baseStart_66312 := by decide
  rcases family_descends (prefixWord ++ tailWord_66312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66321 : List Nat := [1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 5]
def baseStart_66321 : Nat := 118140960795 + 66321 * 2 ^ 59
def prefixEnd_66321 : Nat := 4983230072969 + 3 ^ 40 * 66321 * 2
def baseEnd_66321 : Nat := 34054550486940252482501

theorem tailTrace_66321 : CollatzResearch.WordTrace tailWord_66321 prefixEnd_66321 34054550486940252482501 := by
  unfold tailWord_66321
  simp only [CollatzResearch.WordTrace]
  refine ⟨2418925592737818570142817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1612617061825212380095211 2418925592737818570142817)
  ·
    refine ⟨1814194194553363927607113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2418925592737818570142817 1814194194553363927607113)
    ·
      refine ⟨1360645645915022945705335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1814194194553363927607113 1360645645915022945705335)
      ·
        refine ⟨2040968468872534418558003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1360645645915022945705335 2040968468872534418558003)
        ·
          refine ⟨3061452703308801627837005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2040968468872534418558003 3061452703308801627837005)
          ·
            refine ⟨1148044763740800610438877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3061452703308801627837005 1148044763740800610438877)
            ·
              refine ⟨430516786402800228914579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1148044763740800610438877 430516786402800228914579)
              ·
                refine ⟨645775179604200343371869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 430516786402800228914579 645775179604200343371869)
                ·
                  refine ⟨242165692351575128764451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 645775179604200343371869 242165692351575128764451)
                  ·
                    refine ⟨363248538527362693146677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 242165692351575128764451 363248538527362693146677)
                    ·
                      refine ⟨34054550486940252482501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 363248538527362693146677 34054550486940252482501)
                      ·
                        rfl

theorem cell23_66321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_66321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66321 prefixEnd_66321 := by exact prefixLift 66321
  have htrace : WordTrace (prefixWord ++ tailWord_66321) baseStart_66321 baseEnd_66321 := by
    simpa [prefixWord, tailWord_66321, baseEnd_66321] using wordTrace_append hprefix tailTrace_66321
  have hstable : (prefixWord ++ tailWord_66321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66321).length < 2 ^ (prefixWord ++ tailWord_66321).sum := by decide
  have hdescent : baseEnd_66321 < baseStart_66321 := by decide
  rcases family_descends (prefixWord ++ tailWord_66321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66335 : List Nat := [1, 1, 2, 4, 2, 3, 2, 2, 1, 1, 4]
def baseStart_66335 : Nat := 118140960795 + 66335 * 2 ^ 59
def prefixEnd_66335 : Nat := 4983230072969 + 3 ^ 40 * 66335 * 2
def baseEnd_66335 : Nat := 34061739216103197707437

theorem tailTrace_66335 : CollatzResearch.WordTrace tailWord_66335 prefixEnd_66335 34061739216103197707437 := by
  unfold tailWord_66335
  simp only [CollatzResearch.WordTrace]
  refine ⟨2419436214687098961152459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1612957476458065974101639 2419436214687098961152459)
  ·
    refine ⟨3629154322030648441728689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2419436214687098961152459 3629154322030648441728689)
    ·
      refine ⟨2721865741522986331296517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3629154322030648441728689 2721865741522986331296517)
      ·
        refine ⟨510349826535559937118097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2721865741522986331296517 510349826535559937118097)
        ·
          refine ⟨382762369901669952838573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 510349826535559937118097 382762369901669952838573)
          ·
            refine ⟨143535888713126232314465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 382762369901669952838573 143535888713126232314465)
            ·
              refine ⟨107651916534844674235849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143535888713126232314465 107651916534844674235849)
              ·
                refine ⟨80738937401133505676887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107651916534844674235849 80738937401133505676887)
                ·
                  refine ⟨121108406101700258515331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80738937401133505676887 121108406101700258515331)
                  ·
                    refine ⟨181662609152550387772997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 121108406101700258515331 181662609152550387772997)
                    ·
                      refine ⟨34061739216103197707437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 181662609152550387772997 34061739216103197707437)
                      ·
                        rfl

theorem cell23_66335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_66335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66335 prefixEnd_66335 := by exact prefixLift 66335
  have htrace : WordTrace (prefixWord ++ tailWord_66335) baseStart_66335 baseEnd_66335 := by
    simpa [prefixWord, tailWord_66335, baseEnd_66335] using wordTrace_append hprefix tailTrace_66335
  have hstable : (prefixWord ++ tailWord_66335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66335).length < 2 ^ (prefixWord ++ tailWord_66335).sum := by decide
  have hdescent : baseEnd_66335 < baseStart_66335 := by decide
  rcases family_descends (prefixWord ++ tailWord_66335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66341 : List Nat := [1, 3, 1, 2, 3, 1, 3, 9]
def baseStart_66341 : Nat := 118140960795 + 66341 * 2 ^ 59
def prefixEnd_66341 : Nat := 4983230072969 + 3 ^ 40 * 66341 * 2
def baseEnd_66341 : Nat := 1261660003704821267867

theorem tailTrace_66341 : CollatzResearch.WordTrace tailWord_66341 prefixEnd_66341 1261660003704821267867 := by
  unfold tailWord_66341
  simp only [CollatzResearch.WordTrace]
  refine ⟨2419655052665361985870877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1613103368443574657247251 2419655052665361985870877)
  ·
    refine ⟨907370644749510744701579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2419655052665361985870877 907370644749510744701579)
    ·
      refine ⟨1361055967124266117052369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 907370644749510744701579 1361055967124266117052369)
      ·
        refine ⟨1020791975343199587789277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1361055967124266117052369 1020791975343199587789277)
        ·
          refine ⟨382796990753699845420979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1020791975343199587789277 382796990753699845420979)
          ·
            refine ⟨574195486130549768131469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382796990753699845420979 574195486130549768131469)
            ·
              refine ⟨215323307298956163049301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 574195486130549768131469 215323307298956163049301)
              ·
                refine ⟨1261660003704821267867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 215323307298956163049301 1261660003704821267867)
                ·
                  rfl

theorem cell23_66341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 9].length) (baseStart_66341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66341 prefixEnd_66341 := by exact prefixLift 66341
  have htrace : WordTrace (prefixWord ++ tailWord_66341) baseStart_66341 baseEnd_66341 := by
    simpa [prefixWord, tailWord_66341, baseEnd_66341] using wordTrace_append hprefix tailTrace_66341
  have hstable : (prefixWord ++ tailWord_66341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66341).length < 2 ^ (prefixWord ++ tailWord_66341).sum := by decide
  have hdescent : baseEnd_66341 < baseStart_66341 := by decide
  rcases family_descends (prefixWord ++ tailWord_66341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66355 : List Nat := [1, 1, 1, 2, 6, 1, 2, 3, 1, 2, 3]
def baseStart_66355 : Nat := 118140960795 + 66355 * 2 ^ 59
def prefixEnd_66355 : Nat := 4983230072969 + 3 ^ 40 * 66355 * 2
def baseEnd_66355 : Nat := 34072008829193119457345

theorem tailTrace_66355 : CollatzResearch.WordTrace tailWord_66355 prefixEnd_66355 34072008829193119457345 := by
  unfold tailWord_66355
  simp only [CollatzResearch.WordTrace]
  refine ⟨2420165674614642376880519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1613443783076428251253679 2420165674614642376880519)
  ·
    refine ⟨3630248511921963565320779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2420165674614642376880519 3630248511921963565320779)
    ·
      refine ⟨5445372767882945347981169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3630248511921963565320779 5445372767882945347981169)
      ·
        refine ⟨4084029575912209010985877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5445372767882945347981169 4084029575912209010985877)
        ·
          refine ⟨191438886370884797389963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4084029575912209010985877 191438886370884797389963)
          ·
            refine ⟨287158329556327196084945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191438886370884797389963 287158329556327196084945)
            ·
              refine ⟨215368747167245397063709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287158329556327196084945 215368747167245397063709)
              ·
                refine ⟨80763280187717023898891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215368747167245397063709 80763280187717023898891)
                ·
                  refine ⟨121144920281575535848337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80763280187717023898891 121144920281575535848337)
                  ·
                    refine ⟨90858690211181651886253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121144920281575535848337 90858690211181651886253)
                    ·
                      refine ⟨34072008829193119457345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 90858690211181651886253 34072008829193119457345)
                      ·
                        rfl

theorem cell23_66355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 2, 3].length) (baseStart_66355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66355 prefixEnd_66355 := by exact prefixLift 66355
  have htrace : WordTrace (prefixWord ++ tailWord_66355) baseStart_66355 baseEnd_66355 := by
    simpa [prefixWord, tailWord_66355, baseEnd_66355] using wordTrace_append hprefix tailTrace_66355
  have hstable : (prefixWord ++ tailWord_66355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66355).length < 2 ^ (prefixWord ++ tailWord_66355).sum := by decide
  have hdescent : baseEnd_66355 < baseStart_66355 := by decide
  rcases family_descends (prefixWord ++ tailWord_66355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66371 : List Nat := [1, 1, 1, 3, 1, 4, 2, 1, 2, 7]
def baseStart_66371 : Nat := 118140960795 + 66371 * 2 ^ 59
def prefixEnd_66371 : Nat := 4983230072969 + 3 ^ 40 * 66371 * 2
def baseEnd_66371 : Nat := 11360074839888352285757

theorem tailTrace_66371 : CollatzResearch.WordTrace tailWord_66371 prefixEnd_66371 11360074839888352285757 := by
  unfold tailWord_66371
  simp only [CollatzResearch.WordTrace]
  refine ⟨2420749242556677109462967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1613832828371118072975311 2420749242556677109462967)
  ·
    refine ⟨3631123863835015664194451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2420749242556677109462967 3631123863835015664194451)
    ·
      refine ⟨5446685795752523496291677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3631123863835015664194451 5446685795752523496291677)
      ·
        refine ⟨2042507173407196311109379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5446685795752523496291677 2042507173407196311109379)
        ·
          refine ⟨3063760760110794466664069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2042507173407196311109379 3063760760110794466664069)
          ·
            refine ⟨574455142520773962499513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3063760760110794466664069 574455142520773962499513)
            ·
              refine ⟨430841356890580471874635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 574455142520773962499513 430841356890580471874635)
              ·
                refine ⟨646262035335870707811953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 430841356890580471874635 646262035335870707811953)
                ·
                  refine ⟨484696526501903030858965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 646262035335870707811953 484696526501903030858965)
                  ·
                    refine ⟨11360074839888352285757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 484696526501903030858965 11360074839888352285757)
                    ·
                      rfl

theorem cell23_66371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 7].length) (baseStart_66371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66371 prefixEnd_66371 := by exact prefixLift 66371
  have htrace : WordTrace (prefixWord ++ tailWord_66371) baseStart_66371 baseEnd_66371 := by
    simpa [prefixWord, tailWord_66371, baseEnd_66371] using wordTrace_append hprefix tailTrace_66371
  have hstable : (prefixWord ++ tailWord_66371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66371).length < 2 ^ (prefixWord ++ tailWord_66371).sum := by decide
  have hdescent : baseEnd_66371 < baseStart_66371 := by decide
  rcases family_descends (prefixWord ++ tailWord_66371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66401 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 3, 8]
def baseStart_66401 : Nat := 118140960795 + 66401 * 2 ^ 59
def prefixEnd_66401 : Nat := 4983230072969 + 3 ^ 40 * 66401 * 2
def baseEnd_66401 : Nat := 11365209646433313160711

theorem tailTrace_66401 : CollatzResearch.WordTrace tailWord_66401 prefixEnd_66401 11365209646433313160711 := by
  unfold tailWord_66401
  simp only [CollatzResearch.WordTrace]
  refine ⟨2421843432447992233055057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1614562288298661488703371 2421843432447992233055057)
  ·
    refine ⟨1816382574335994174791293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2421843432447992233055057 1816382574335994174791293)
    ·
      refine ⟨681143465375997815546735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1816382574335994174791293 681143465375997815546735)
      ·
        refine ⟨1021715198063996723320103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 681143465375997815546735 1021715198063996723320103)
        ·
          refine ⟨1532572797095995084980155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1021715198063996723320103 1532572797095995084980155)
          ·
            refine ⟨2298859195643992627470233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1532572797095995084980155 2298859195643992627470233)
            ·
              refine ⟨1724144396732994470602675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2298859195643992627470233 1724144396732994470602675)
              ·
                refine ⟨2586216595099491705904013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1724144396732994470602675 2586216595099491705904013)
                ·
                  refine ⟨969831223162309389714005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2586216595099491705904013 969831223162309389714005)
                  ·
                    refine ⟨11365209646433313160711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 969831223162309389714005 11365209646433313160711)
                    ·
                      rfl

theorem cell23_66401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_66401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66401 prefixEnd_66401 := by exact prefixLift 66401
  have htrace : WordTrace (prefixWord ++ tailWord_66401) baseStart_66401 baseEnd_66401 := by
    simpa [prefixWord, tailWord_66401, baseEnd_66401] using wordTrace_append hprefix tailTrace_66401
  have hstable : (prefixWord ++ tailWord_66401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66401).length < 2 ^ (prefixWord ++ tailWord_66401).sum := by decide
  have hdescent : baseEnd_66401 < baseStart_66401 := by decide
  rcases family_descends (prefixWord ++ tailWord_66401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66402 : List Nat := [3, 3, 2, 1, 3, 1, 1, 2, 1, 3, 3]
def baseStart_66402 : Nat := 118140960795 + 66402 * 2 ^ 59
def prefixEnd_66402 : Nat := 4983230072969 + 3 ^ 40 * 66402 * 2
def baseEnd_66402 : Nat := 34096142419954435569629

theorem tailTrace_66402 : CollatzResearch.WordTrace tailWord_66402 prefixEnd_66402 34096142419954435569629 := by
  unfold tailWord_66402
  simp only [CollatzResearch.WordTrace]
  refine ⟨605469976361092350960365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1614586603629579602560973 605469976361092350960365)
  ·
    refine ⟨227051241135409631610137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 605469976361092350960365 227051241135409631610137)
    ·
      refine ⟨170288430851557223707603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227051241135409631610137 170288430851557223707603)
      ·
        refine ⟨255432646277335835561405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170288430851557223707603 255432646277335835561405)
        ·
          refine ⟨95787242354000938335527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255432646277335835561405 95787242354000938335527)
          ·
            refine ⟨143680863531001407503291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95787242354000938335527 143680863531001407503291)
            ·
              refine ⟨215521295296502111254937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143680863531001407503291 215521295296502111254937)
              ·
                refine ⟨161640971472376583441203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215521295296502111254937 161640971472376583441203)
                ·
                  refine ⟨242461457208564875161805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161640971472376583441203 242461457208564875161805)
                  ·
                    refine ⟨90923046453211828185677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 242461457208564875161805 90923046453211828185677)
                    ·
                      refine ⟨34096142419954435569629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 90923046453211828185677 34096142419954435569629)
                      ·
                        rfl

theorem cell23_66402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_66402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66402 prefixEnd_66402 := by exact prefixLift 66402
  have htrace : WordTrace (prefixWord ++ tailWord_66402) baseStart_66402 baseEnd_66402 := by
    simpa [prefixWord, tailWord_66402, baseEnd_66402] using wordTrace_append hprefix tailTrace_66402
  have hstable : (prefixWord ++ tailWord_66402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66402).length < 2 ^ (prefixWord ++ tailWord_66402).sum := by decide
  have hdescent : baseEnd_66402 < baseStart_66402 := by decide
  rcases family_descends (prefixWord ++ tailWord_66402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66442 : List Nat := [3, 1, 2, 4, 1, 1, 1, 3, 1, 4, 2]
def baseStart_66442 : Nat := 118140960795 + 66442 * 2 ^ 59
def prefixEnd_66442 : Nat := 4983230072969 + 3 ^ 40 * 66442 * 2
def baseEnd_66442 : Nat := 34116681646134279069445

theorem tailTrace_66442 : CollatzResearch.WordTrace tailWord_66442 prefixEnd_66442 34116681646134279069445 := by
  unfold tailWord_66442
  simp only [CollatzResearch.WordTrace]
  refine ⟨605834706324864058824395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1615559216866304156865053 605834706324864058824395)
  ·
    refine ⟨908752059487296088236593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 605834706324864058824395 908752059487296088236593)
    ·
      refine ⟨681564044615472066177445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 908752059487296088236593 681564044615472066177445)
      ·
        refine ⟨127793258365401012408271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 681564044615472066177445 127793258365401012408271)
        ·
          refine ⟨191689887548101518612407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127793258365401012408271 191689887548101518612407)
          ·
            refine ⟨287534831322152277918611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191689887548101518612407 287534831322152277918611)
            ·
              refine ⟨431302246983228416877917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287534831322152277918611 431302246983228416877917)
              ·
                refine ⟨161738342618710656329219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 431302246983228416877917 161738342618710656329219)
                ·
                  refine ⟨242607513928065984493829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161738342618710656329219 242607513928065984493829)
                  ·
                    refine ⟨45488908861512372092593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 242607513928065984493829 45488908861512372092593)
                    ·
                      refine ⟨34116681646134279069445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 45488908861512372092593 34116681646134279069445)
                      ·
                        rfl

theorem cell23_66442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_66442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66442 prefixEnd_66442 := by exact prefixLift 66442
  have htrace : WordTrace (prefixWord ++ tailWord_66442) baseStart_66442 baseEnd_66442 := by
    simpa [prefixWord, tailWord_66442, baseEnd_66442] using wordTrace_append hprefix tailTrace_66442
  have hstable : (prefixWord ++ tailWord_66442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66442).length < 2 ^ (prefixWord ++ tailWord_66442).sum := by decide
  have hdescent : baseEnd_66442 < baseStart_66442 := by decide
  rcases family_descends (prefixWord ++ tailWord_66442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66508 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 2, 8]
def baseStart_66508 : Nat := 118140960795 + 66508 * 2 ^ 59
def prefixEnd_66508 : Nat := 4983230072969 + 3 ^ 40 * 66508 * 2
def baseEnd_66508 : Nat := 11383523789777006948047

theorem tailTrace_66508 : CollatzResearch.WordTrace tailWord_66508 prefixEnd_66508 11383523789777006948047 := by
  unfold tailWord_66508
  simp only [CollatzResearch.WordTrace]
  refine ⟨1212873021530174753600089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1617164028706899671466785 1212873021530174753600089)
  ·
    refine ⟨909654766147631065200067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1212873021530174753600089 909654766147631065200067)
    ·
      refine ⟨1364482149221446597800101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 909654766147631065200067 1364482149221446597800101)
      ·
        refine ⟨255840402979021237087519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1364482149221446597800101 255840402979021237087519)
        ·
          refine ⟨383760604468531855631279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255840402979021237087519 383760604468531855631279)
          ·
            refine ⟨575640906702797783446919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383760604468531855631279 575640906702797783446919)
            ·
              refine ⟨863461360054196675170379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 575640906702797783446919 863461360054196675170379)
              ·
                refine ⟨1295192040081295012755569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 863461360054196675170379 1295192040081295012755569)
                ·
                  refine ⟨971394030060971259566677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1295192040081295012755569 971394030060971259566677)
                  ·
                    refine ⟨11383523789777006948047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 971394030060971259566677 11383523789777006948047)
                    ·
                      rfl

theorem cell23_66508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 2, 8].length) (baseStart_66508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66508 prefixEnd_66508 := by exact prefixLift 66508
  have htrace : WordTrace (prefixWord ++ tailWord_66508) baseStart_66508 baseEnd_66508 := by
    simpa [prefixWord, tailWord_66508, baseEnd_66508] using wordTrace_append hprefix tailTrace_66508
  have hstable : (prefixWord ++ tailWord_66508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66508).length < 2 ^ (prefixWord ++ tailWord_66508).sum := by decide
  have hdescent : baseEnd_66508 < baseStart_66508 := by decide
  rcases family_descends (prefixWord ++ tailWord_66508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66585 : List Nat := [1, 2, 1, 2, 1, 1, 4, 5, 1, 5]
def baseStart_66585 : Nat := 118140960795 + 66585 * 2 ^ 59
def prefixEnd_66585 : Nat := 4983230072969 + 3 ^ 40 * 66585 * 2
def baseEnd_66585 : Nat := 11396703126575739860429

theorem tailTrace_66585 : CollatzResearch.WordTrace tailWord_66585 prefixEnd_66585 11396703126575739860429 := by
  unfold tailWord_66585
  simp only [CollatzResearch.WordTrace]
  refine ⟨2428554463781391657753209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1619036309187594438502139 2428554463781391657753209)
  ·
    refine ⟨1821415847836043743314907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2428554463781391657753209 1821415847836043743314907)
    ·
      refine ⟨2732123771754065614972361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1821415847836043743314907 2732123771754065614972361)
      ·
        refine ⟨2049092828815549211229271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2732123771754065614972361 2049092828815549211229271)
        ·
          refine ⟨3073639243223323816843907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2049092828815549211229271 3073639243223323816843907)
          ·
            refine ⟨4610458864834985725265861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3073639243223323816843907 4610458864834985725265861)
            ·
              refine ⟨864461037156559823487349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4610458864834985725265861 864461037156559823487349)
              ·
                refine ⟨81043222233427483451939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 864461037156559823487349 81043222233427483451939)
                ·
                  refine ⟨121564833350141225177909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81043222233427483451939 121564833350141225177909)
                  ·
                    refine ⟨11396703126575739860429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 121564833350141225177909 11396703126575739860429)
                    ·
                      rfl

theorem cell23_66585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 5].length) (baseStart_66585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66585 prefixEnd_66585 := by exact prefixLift 66585
  have htrace : WordTrace (prefixWord ++ tailWord_66585) baseStart_66585 baseEnd_66585 := by
    simpa [prefixWord, tailWord_66585, baseEnd_66585] using wordTrace_append hprefix tailTrace_66585
  have hstable : (prefixWord ++ tailWord_66585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66585).length < 2 ^ (prefixWord ++ tailWord_66585).sum := by decide
  have hdescent : baseEnd_66585 < baseStart_66585 := by decide
  rcases family_descends (prefixWord ++ tailWord_66585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66615 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 6, 4]
def baseStart_66615 : Nat := 118140960795 + 66615 * 2 ^ 59
def prefixEnd_66615 : Nat := 4983230072969 + 3 ^ 40 * 66615 * 2
def baseEnd_66615 : Nat := 11401837933120700735383

theorem tailTrace_66615 : CollatzResearch.WordTrace tailWord_66615 prefixEnd_66615 11401837933120700735383 := by
  unfold tailWord_66615
  simp only [CollatzResearch.WordTrace]
  refine ⟨2429648653672706781345299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1619765769115137854230199 2429648653672706781345299)
  ·
    refine ⟨3644472980509060172017949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2429648653672706781345299 3644472980509060172017949)
    ·
      refine ⟨1366677367690897564506731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3644472980509060172017949 1366677367690897564506731)
      ·
        refine ⟨2050016051536346346760097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1366677367690897564506731 2050016051536346346760097)
        ·
          refine ⟨1537512038652259760070073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2050016051536346346760097 1537512038652259760070073)
          ·
            refine ⟨1153134028989194820052555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1537512038652259760070073 1153134028989194820052555)
            ·
              refine ⟨1729701043483792230078833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1153134028989194820052555 1729701043483792230078833)
              ·
                refine ⟨1297275782612844172559125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1729701043483792230078833 1297275782612844172559125)
                ·
                  refine ⟨60809802309977070588709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1297275782612844172559125 60809802309977070588709)
                  ·
                    refine ⟨11401837933120700735383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60809802309977070588709 11401837933120700735383)
                    ·
                      rfl

theorem cell23_66615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 6, 4].length) (baseStart_66615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66615 prefixEnd_66615 := by exact prefixLift 66615
  have htrace : WordTrace (prefixWord ++ tailWord_66615) baseStart_66615 baseEnd_66615 := by
    simpa [prefixWord, tailWord_66615, baseEnd_66615] using wordTrace_append hprefix tailTrace_66615
  have hstable : (prefixWord ++ tailWord_66615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66615).length < 2 ^ (prefixWord ++ tailWord_66615).sum := by decide
  have hdescent : baseEnd_66615 < baseStart_66615 := by decide
  rcases family_descends (prefixWord ++ tailWord_66615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66656 : List Nat := [2, 1, 1, 3, 2, 2, 1, 6, 1, 2, 2]
def baseStart_66656 : Nat := 118140960795 + 66656 * 2 ^ 59
def prefixEnd_66656 : Nat := 4983230072969 + 3 ^ 40 * 66656 * 2
def baseEnd_66656 : Nat := 34226566506196441793461

theorem tailTrace_66656 : CollatzResearch.WordTrace tailWord_66656 prefixEnd_66656 34226566506196441793461 := by
  unfold tailWord_66656
  simp only [CollatzResearch.WordTrace]
  refine ⟨1215572023262085391793911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1620762697682780522391881 1215572023262085391793911)
  ·
    refine ⟨1823358034893128087690867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1215572023262085391793911 1823358034893128087690867)
    ·
      refine ⟨2735037052339692131536301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1823358034893128087690867 2735037052339692131536301)
      ·
        refine ⟨1025638894627384549326113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2735037052339692131536301 1025638894627384549326113)
        ·
          refine ⟨769229170970538411994585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1025638894627384549326113 769229170970538411994585)
          ·
            refine ⟨576921878227903808995939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 769229170970538411994585 576921878227903808995939)
            ·
              refine ⟨865382817341855713493909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 576921878227903808995939 865382817341855713493909)
              ·
                refine ⟨40564819562899486570027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 865382817341855713493909 40564819562899486570027)
                ·
                  refine ⟨60847229344349229855041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40564819562899486570027 60847229344349229855041)
                  ·
                    refine ⟨45635422008261922391281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60847229344349229855041 45635422008261922391281)
                    ·
                      refine ⟨34226566506196441793461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 45635422008261922391281 34226566506196441793461)
                      ·
                        rfl

theorem cell23_66656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 6, 1, 2, 2].length) (baseStart_66656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66656 prefixEnd_66656 := by exact prefixLift 66656
  have htrace : WordTrace (prefixWord ++ tailWord_66656) baseStart_66656 baseEnd_66656 := by
    simpa [prefixWord, tailWord_66656, baseEnd_66656] using wordTrace_append hprefix tailTrace_66656
  have hstable : (prefixWord ++ tailWord_66656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66656).length < 2 ^ (prefixWord ++ tailWord_66656).sum := by decide
  have hdescent : baseEnd_66656 < baseStart_66656 := by decide
  rcases family_descends (prefixWord ++ tailWord_66656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66666 : List Nat := [3, 1, 3, 2, 2, 2, 3, 1, 2, 4]
def baseStart_66666 : Nat := 118140960795 + 66666 * 2 ^ 59
def prefixEnd_66666 : Nat := 4983230072969 + 3 ^ 40 * 66666 * 2
def baseEnd_66666 : Nat := 11410567104247134222805

theorem tailTrace_66666 : CollatzResearch.WordTrace tailWord_66666 prefixEnd_66666 11410567104247134222805 := by
  unfold tailWord_66666
  simp only [CollatzResearch.WordTrace]
  refine ⟨607877194121985622862963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1621005850991961660967901 607877194121985622862963)
  ·
    refine ⟨911815791182978434294445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 607877194121985622862963 911815791182978434294445)
    ·
      refine ⟨341930921693616912860417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 911815791182978434294445 341930921693616912860417)
      ·
        refine ⟨256448191270212684645313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341930921693616912860417 256448191270212684645313)
        ·
          refine ⟨192336143452659513483985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256448191270212684645313 192336143452659513483985)
          ·
            refine ⟨144252107589494635112989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192336143452659513483985 144252107589494635112989)
            ·
              refine ⟨54094540346060488167371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144252107589494635112989 54094540346060488167371)
              ·
                refine ⟨81141810519090732251057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54094540346060488167371 81141810519090732251057)
                ·
                  refine ⟨60856357889318049188293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81141810519090732251057 60856357889318049188293)
                  ·
                    refine ⟨11410567104247134222805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60856357889318049188293 11410567104247134222805)
                    ·
                      rfl

theorem cell23_66666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_66666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66666 prefixEnd_66666 := by exact prefixLift 66666
  have htrace : WordTrace (prefixWord ++ tailWord_66666) baseStart_66666 baseEnd_66666 := by
    simpa [prefixWord, tailWord_66666, baseEnd_66666] using wordTrace_append hprefix tailTrace_66666
  have hstable : (prefixWord ++ tailWord_66666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66666).length < 2 ^ (prefixWord ++ tailWord_66666).sum := by decide
  have hdescent : baseEnd_66666 < baseStart_66666 := by decide
  rcases family_descends (prefixWord ++ tailWord_66666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66669 : List Nat := [1, 5, 1, 1, 2, 4, 1, 1, 1, 2, 4]
def baseStart_66669 : Nat := 118140960795 + 66669 * 2 ^ 59
def prefixEnd_66669 : Nat := 4983230072969 + 3 ^ 40 * 66669 * 2
def baseEnd_66669 : Nat := 34233241754704890930901

theorem tailTrace_66669 : CollatzResearch.WordTrace tailWord_66669 prefixEnd_66669 34233241754704890930901 := by
  unfold tailWord_66669
  simp only [CollatzResearch.WordTrace]
  refine ⟨2431618195477074003811061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1621078796984716002540707 2431618195477074003811061)
  ·
    refine ⟨227964205825975687857287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2431618195477074003811061 227964205825975687857287)
    ·
      refine ⟨341946308738963531785931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227964205825975687857287 341946308738963531785931)
      ·
        refine ⟨512919463108445297678897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341946308738963531785931 512919463108445297678897)
        ·
          refine ⟨384689597331333973259173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512919463108445297678897 384689597331333973259173)
          ·
            refine ⟨72129299499625119986095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 384689597331333973259173 72129299499625119986095)
            ·
              refine ⟨108193949249437679979143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72129299499625119986095 108193949249437679979143)
              ·
                refine ⟨162290923874156519968715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108193949249437679979143 162290923874156519968715)
                ·
                  refine ⟨243436385811234779953073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162290923874156519968715 243436385811234779953073)
                  ·
                    refine ⟨182577289358426084964805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 243436385811234779953073 182577289358426084964805)
                    ·
                      refine ⟨34233241754704890930901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 182577289358426084964805 34233241754704890930901)
                      ·
                        rfl

theorem cell23_66669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_66669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66669 prefixEnd_66669 := by exact prefixLift 66669
  have htrace : WordTrace (prefixWord ++ tailWord_66669) baseStart_66669 baseEnd_66669 := by
    simpa [prefixWord, tailWord_66669, baseEnd_66669] using wordTrace_append hprefix tailTrace_66669
  have hstable : (prefixWord ++ tailWord_66669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66669).length < 2 ^ (prefixWord ++ tailWord_66669).sum := by decide
  have hdescent : baseEnd_66669 < baseStart_66669 := by decide
  rcases family_descends (prefixWord ++ tailWord_66669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66685 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 1, 4, 5]
def baseStart_66685 : Nat := 118140960795 + 66685 * 2 ^ 59
def prefixEnd_66685 : Nat := 4983230072969 + 3 ^ 40 * 66685 * 2
def baseEnd_66685 : Nat := 34241457445176828330827

theorem tailTrace_66685 : CollatzResearch.WordTrace tailWord_66685 prefixEnd_66685 34241457445176828330827 := by
  unfold tailWord_66685
  simp only [CollatzResearch.WordTrace]
  refine ⟨2432201763419108736393509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1621467842279405824262339 2432201763419108736393509)
  ·
    refine ⟨456037830641082888073783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2432201763419108736393509 456037830641082888073783)
    ·
      refine ⟨684056745961624332110675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456037830641082888073783 684056745961624332110675)
      ·
        refine ⟨1026085118942436498166013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 684056745961624332110675 1026085118942436498166013)
        ·
          refine ⟨384781919603413686812255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1026085118942436498166013 384781919603413686812255)
          ·
            refine ⟨577172879405120530218383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384781919603413686812255 577172879405120530218383)
            ·
              refine ⟨865759319107680795327575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577172879405120530218383 865759319107680795327575)
              ·
                refine ⟨1298638978661521192991363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 865759319107680795327575 1298638978661521192991363)
                ·
                  refine ⟨1947958467992281789487045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1298638978661521192991363 1947958467992281789487045)
                  ·
                    refine ⟨365242212748552835528821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1947958467992281789487045 365242212748552835528821)
                    ·
                      refine ⟨34241457445176828330827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 365242212748552835528821 34241457445176828330827)
                      ·
                        rfl

theorem cell23_66685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_66685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66685 prefixEnd_66685 := by exact prefixLift 66685
  have htrace : WordTrace (prefixWord ++ tailWord_66685) baseStart_66685 baseEnd_66685 := by
    simpa [prefixWord, tailWord_66685, baseEnd_66685] using wordTrace_append hprefix tailTrace_66685
  have hstable : (prefixWord ++ tailWord_66685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66685).length < 2 ^ (prefixWord ++ tailWord_66685).sum := by decide
  have hdescent : baseEnd_66685 < baseStart_66685 := by decide
  rcases family_descends (prefixWord ++ tailWord_66685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66689 : List Nat := [1, 2, 4, 2, 2, 1, 1, 2, 4, 1, 3]
def baseStart_66689 : Nat := 118140960795 + 66689 * 2 ^ 59
def prefixEnd_66689 : Nat := 4983230072969 + 3 ^ 40 * 66689 * 2
def baseEnd_66689 : Nat := 34243511367794812680809

theorem tailTrace_66689 : CollatzResearch.WordTrace tailWord_66689 prefixEnd_66689 34243511367794812680809 := by
  unfold tailWord_66689
  simp only [CollatzResearch.WordTrace]
  refine ⟨2432347655404617419539121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1621565103603078279692747 2432347655404617419539121)
  ·
    refine ⟨1824260741553463064654341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2432347655404617419539121 1824260741553463064654341)
    ·
      refine ⟨342048889041274324622689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1824260741553463064654341 342048889041274324622689)
      ·
        refine ⟨256536666780955743467017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342048889041274324622689 256536666780955743467017)
        ·
          refine ⟨192402500085716807600263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256536666780955743467017 192402500085716807600263)
          ·
            refine ⟨288603750128575211400395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192402500085716807600263 288603750128575211400395)
            ·
              refine ⟨432905625192862817100593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288603750128575211400395 432905625192862817100593)
              ·
                refine ⟨324679218894647112825445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432905625192862817100593 324679218894647112825445)
                ·
                  refine ⟨60877353542746333654771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 324679218894647112825445 60877353542746333654771)
                  ·
                    refine ⟨91316030314119500482157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60877353542746333654771 91316030314119500482157)
                    ·
                      refine ⟨34243511367794812680809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 91316030314119500482157 34243511367794812680809)
                      ·
                        rfl

theorem cell23_66689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_66689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66689 prefixEnd_66689 := by exact prefixLift 66689
  have htrace : WordTrace (prefixWord ++ tailWord_66689) baseStart_66689 baseEnd_66689 := by
    simpa [prefixWord, tailWord_66689, baseEnd_66689] using wordTrace_append hprefix tailTrace_66689
  have hstable : (prefixWord ++ tailWord_66689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66689).length < 2 ^ (prefixWord ++ tailWord_66689).sum := by decide
  have hdescent : baseEnd_66689 < baseStart_66689 := by decide
  rcases family_descends (prefixWord ++ tailWord_66689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66695 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 4]
def baseStart_66695 : Nat := 118140960795 + 66695 * 2 ^ 59
def prefixEnd_66695 : Nat := 4983230072969 + 3 ^ 40 * 66695 * 2
def baseEnd_66695 : Nat := 34246592251721789205781

theorem tailTrace_66695 : CollatzResearch.WordTrace tailWord_66695 prefixEnd_66695 34246592251721789205781 := by
  unfold tailWord_66695
  simp only [CollatzResearch.WordTrace]
  refine ⟨2432566493382880444257539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1621710995588586962838359 2432566493382880444257539)
  ·
    refine ⟨3648849740074320666386309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2432566493382880444257539 3648849740074320666386309)
    ·
      refine ⟨684159326263935124947433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3648849740074320666386309 684159326263935124947433)
      ·
        refine ⟨513119494697951343710575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 684159326263935124947433 513119494697951343710575)
        ·
          refine ⟨769679242046927015565863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513119494697951343710575 769679242046927015565863)
          ·
            refine ⟨1154518863070390523348795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 769679242046927015565863 1154518863070390523348795)
            ·
              refine ⟨1731778294605585785023193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1154518863070390523348795 1731778294605585785023193)
              ·
                refine ⟨1298833720954189338767395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1731778294605585785023193 1298833720954189338767395)
                ·
                  refine ⟨1948250581431284008151093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1298833720954189338767395 1948250581431284008151093)
                  ·
                    refine ⟨182648492009182875764165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1948250581431284008151093 182648492009182875764165)
                    ·
                      refine ⟨34246592251721789205781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 182648492009182875764165 34246592251721789205781)
                      ·
                        rfl

theorem cell23_66695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_66695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66695 prefixEnd_66695 := by exact prefixLift 66695
  have htrace : WordTrace (prefixWord ++ tailWord_66695) baseStart_66695 baseEnd_66695 := by
    simpa [prefixWord, tailWord_66695, baseEnd_66695] using wordTrace_append hprefix tailTrace_66695
  have hstable : (prefixWord ++ tailWord_66695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66695).length < 2 ^ (prefixWord ++ tailWord_66695).sum := by decide
  have hdescent : baseEnd_66695 < baseStart_66695 := by decide
  rcases family_descends (prefixWord ++ tailWord_66695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66735 : List Nat := [1, 1, 2, 1, 2, 3, 2, 4, 7]
def baseStart_66735 : Nat := 118140960795 + 66735 * 2 ^ 59
def prefixEnd_66735 : Nat := 4983230072969 + 3 ^ 40 * 66735 * 2
def baseEnd_66735 : Nat := 3807459053100181411733

theorem tailTrace_66735 : CollatzResearch.WordTrace tailWord_66735 prefixEnd_66735 3807459053100181411733 := by
  unfold tailWord_66735
  simp only [CollatzResearch.WordTrace]
  refine ⟨2434025413237967275713659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1622683608825311517142439 2434025413237967275713659)
  ·
    refine ⟨3651038119856950913570489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2434025413237967275713659 3651038119856950913570489)
    ·
      refine ⟨2738278589892713185177867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3651038119856950913570489 2738278589892713185177867)
      ·
        refine ⟨4107417884839069777766801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2738278589892713185177867 4107417884839069777766801)
        ·
          refine ⟨3080563413629302333325101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4107417884839069777766801 3080563413629302333325101)
          ·
            refine ⟨1155211280110988374996913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3080563413629302333325101 1155211280110988374996913)
            ·
              refine ⟨866408460083241281247685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1155211280110988374996913 866408460083241281247685)
              ·
                refine ⟨162451586265607740233941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 866408460083241281247685 162451586265607740233941)
                ·
                  refine ⟨3807459053100181411733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 162451586265607740233941 3807459053100181411733)
                  ·
                    rfl

theorem cell23_66735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 7].length) (baseStart_66735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66735 prefixEnd_66735 := by exact prefixLift 66735
  have htrace : WordTrace (prefixWord ++ tailWord_66735) baseStart_66735 baseEnd_66735 := by
    simpa [prefixWord, tailWord_66735, baseEnd_66735] using wordTrace_append hprefix tailTrace_66735
  have hstable : (prefixWord ++ tailWord_66735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66735).length < 2 ^ (prefixWord ++ tailWord_66735).sum := by decide
  have hdescent : baseEnd_66735 < baseStart_66735 := by decide
  rcases family_descends (prefixWord ++ tailWord_66735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66758 : List Nat := [6, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2]
def baseStart_66758 : Nat := 118140960795 + 66758 * 2 ^ 59
def prefixEnd_66758 : Nat := 4983230072969 + 3 ^ 40 * 66758 * 2
def baseEnd_66758 : Nat := 34278941532955042717993

theorem tailTrace_66758 : CollatzResearch.WordTrace tailWord_66758 prefixEnd_66758 34278941532955042717993 := by
  unfold tailWord_66758
  simp only [CollatzResearch.WordTrace]
  refine ⟨76089509129832568868779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1623242861436428135867285 76089509129832568868779)
  ·
    refine ⟨114134263694748853303169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76089509129832568868779 114134263694748853303169)
    ·
      refine ⟨85600697771061639977377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114134263694748853303169 85600697771061639977377)
      ·
        refine ⟨64200523328296229983033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85600697771061639977377 64200523328296229983033)
        ·
          refine ⟨48150392496222172487275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64200523328296229983033 48150392496222172487275)
          ·
            refine ⟨72225588744333258730913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48150392496222172487275 72225588744333258730913)
            ·
              refine ⟨54169191558249944048185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72225588744333258730913 54169191558249944048185)
              ·
                refine ⟨40626893668687458036139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54169191558249944048185 40626893668687458036139)
                ·
                  refine ⟨60940340503031187054209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40626893668687458036139 60940340503031187054209)
                  ·
                    refine ⟨45705255377273390290657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60940340503031187054209 45705255377273390290657)
                    ·
                      refine ⟨34278941532955042717993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 45705255377273390290657 34278941532955042717993)
                      ·
                        rfl

theorem cell23_66758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_66758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66758 prefixEnd_66758 := by exact prefixLift 66758
  have htrace : WordTrace (prefixWord ++ tailWord_66758) baseStart_66758 baseEnd_66758 := by
    simpa [prefixWord, tailWord_66758, baseEnd_66758] using wordTrace_append hprefix tailTrace_66758
  have hstable : (prefixWord ++ tailWord_66758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66758).length < 2 ^ (prefixWord ++ tailWord_66758).sum := by decide
  have hdescent : baseEnd_66758 < baseStart_66758 := by decide
  rcases family_descends (prefixWord ++ tailWord_66758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66819 : List Nat := [1, 1, 1, 3, 2, 4, 1, 2, 2, 4, 2]
def baseStart_66819 : Nat := 118140960795 + 66819 * 2 ^ 59
def prefixEnd_66819 : Nat := 4983230072969 + 3 ^ 40 * 66819 * 2
def baseEnd_66819 : Nat := 34310263852879304055211

theorem tailTrace_66819 : CollatzResearch.WordTrace tailWord_66819 prefixEnd_66819 34310263852879304055211 := by
  unfold tailWord_66819
  simp only [CollatzResearch.WordTrace]
  refine ⟨2437089144933649621771511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1624726096622433081181007 2437089144933649621771511)
  ·
    refine ⟨3655633717400474432657267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2437089144933649621771511 3655633717400474432657267)
    ·
      refine ⟨5483450576100711648985901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3655633717400474432657267 5483450576100711648985901)
      ·
        refine ⟨2056293966037766868369713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5483450576100711648985901 2056293966037766868369713)
        ·
          refine ⟨1542220474528325151277285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2056293966037766868369713 1542220474528325151277285)
          ·
            refine ⟨289166338974060965864491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1542220474528325151277285 289166338974060965864491)
            ·
              refine ⟨433749508461091448796737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289166338974060965864491 433749508461091448796737)
              ·
                refine ⟨325312131345818586597553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433749508461091448796737 325312131345818586597553)
                ·
                  refine ⟨243984098509363939948165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 325312131345818586597553 243984098509363939948165)
                  ·
                    refine ⟨45747018470505738740281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 243984098509363939948165 45747018470505738740281)
                    ·
                      refine ⟨34310263852879304055211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 45747018470505738740281 34310263852879304055211)
                      ·
                        rfl

theorem cell23_66819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 4, 2].length) (baseStart_66819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66819 prefixEnd_66819 := by exact prefixLift 66819
  have htrace : WordTrace (prefixWord ++ tailWord_66819) baseStart_66819 baseEnd_66819 := by
    simpa [prefixWord, tailWord_66819, baseEnd_66819] using wordTrace_append hprefix tailTrace_66819
  have hstable : (prefixWord ++ tailWord_66819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66819).length < 2 ^ (prefixWord ++ tailWord_66819).sum := by decide
  have hdescent : baseEnd_66819 < baseStart_66819 := by decide
  rcases family_descends (prefixWord ++ tailWord_66819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66872 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 5, 5]
def baseStart_66872 : Nat := 118140960795 + 66872 * 2 ^ 59
def prefixEnd_66872 : Nat := 4983230072969 + 3 ^ 40 * 66872 * 2
def baseEnd_66872 : Nat := 11445826109189198897489

theorem tailTrace_66872 : CollatzResearch.WordTrace tailWord_66872 prefixEnd_66872 11445826109189198897489 := by
  unfold tailWord_66872
  simp only [CollatzResearch.WordTrace]
  refine ⟨1219511106870819836725435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1626014809161093115633913 1219511106870819836725435)
  ·
    refine ⟨1829266660306229755088153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1219511106870819836725435 1829266660306229755088153)
    ·
      refine ⟨1371949995229672316316115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1829266660306229755088153 1371949995229672316316115)
      ·
        refine ⟨2057924992844508474474173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1371949995229672316316115 2057924992844508474474173)
        ·
          refine ⟨771721872316690677927815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2057924992844508474474173 771721872316690677927815)
          ·
            refine ⟨1157582808475036016891723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 771721872316690677927815 1157582808475036016891723)
            ·
              refine ⟨1736374212712554025337585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1157582808475036016891723 1736374212712554025337585)
              ·
                refine ⟨1302280659534415519003189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1736374212712554025337585 1302280659534415519003189)
                ·
                  refine ⟨122088811831351454906549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1302280659534415519003189 122088811831351454906549)
                  ·
                    refine ⟨11445826109189198897489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 122088811831351454906549 11445826109189198897489)
                    ·
                      rfl

theorem cell23_66872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 5, 5].length) (baseStart_66872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66872 prefixEnd_66872 := by exact prefixLift 66872
  have htrace : WordTrace (prefixWord ++ tailWord_66872) baseStart_66872 baseEnd_66872 := by
    simpa [prefixWord, tailWord_66872, baseEnd_66872] using wordTrace_append hprefix tailTrace_66872
  have hstable : (prefixWord ++ tailWord_66872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66872).length < 2 ^ (prefixWord ++ tailWord_66872).sum := by decide
  have hdescent : baseEnd_66872 < baseStart_66872 := by decide
  rcases family_descends (prefixWord ++ tailWord_66872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66893 : List Nat := [1, 6, 1, 3, 1, 1, 1, 3, 6]
def baseStart_66893 : Nat := 118140960795 + 66893 * 2 ^ 59
def prefixEnd_66893 : Nat := 4983230072969 + 3 ^ 40 * 66893 * 2
def baseEnd_66893 : Nat := 3816473491256890503319

theorem tailTrace_66893 : CollatzResearch.WordTrace tailWord_66893 prefixEnd_66893 3816473491256890503319 := by
  unfold tailWord_66893
  simp only [CollatzResearch.WordTrace]
  refine ⟨2439788146665560259965333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1626525431110373506643555 2439788146665560259965333)
  ·
    refine ⟨114365069374948137185875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2439788146665560259965333 114365069374948137185875)
    ·
      refine ⟨171547604062422205778813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114365069374948137185875 171547604062422205778813)
      ·
        refine ⟨64330351523408327167055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171547604062422205778813 64330351523408327167055)
        ·
          refine ⟨96495527285112490750583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64330351523408327167055 96495527285112490750583)
          ·
            refine ⟨144743290927668736125875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96495527285112490750583 144743290927668736125875)
            ·
              refine ⟨217114936391503104188813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144743290927668736125875 217114936391503104188813)
              ·
                refine ⟨81418101146813664070805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217114936391503104188813 81418101146813664070805)
                ·
                  refine ⟨3816473491256890503319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 81418101146813664070805 3816473491256890503319)
                  ·
                    rfl

theorem cell23_66893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_66893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66893 prefixEnd_66893 := by exact prefixLift 66893
  have htrace : WordTrace (prefixWord ++ tailWord_66893) baseStart_66893 baseEnd_66893 := by
    simpa [prefixWord, tailWord_66893, baseEnd_66893] using wordTrace_append hprefix tailTrace_66893
  have hstable : (prefixWord ++ tailWord_66893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66893).length < 2 ^ (prefixWord ++ tailWord_66893).sum := by decide
  have hdescent : baseEnd_66893 < baseStart_66893 := by decide
  rcases family_descends (prefixWord ++ tailWord_66893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66929 : List Nat := [1, 2, 2, 2, 1, 2, 5, 1, 1, 1, 5]
def baseStart_66929 : Nat := 118140960795 + 66929 * 2 ^ 59
def prefixEnd_66929 : Nat := 4983230072969 + 3 ^ 40 * 66929 * 2
def baseEnd_66929 : Nat := 34366746724873873679705

theorem tailTrace_66929 : CollatzResearch.WordTrace tailWord_66929 prefixEnd_66929 34366746724873873679705 := by
  unfold tailWord_66929
  simp only [CollatzResearch.WordTrace]
  refine ⟨2441101174535138408275841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1627400783023425605517227 2441101174535138408275841)
  ·
    refine ⟨1830825880901353806206881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2441101174535138408275841 1830825880901353806206881)
    ·
      refine ⟨1373119410676015354655161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1830825880901353806206881 1373119410676015354655161)
      ·
        refine ⟨1029839558007011515991371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1373119410676015354655161 1029839558007011515991371)
        ·
          refine ⟨1544759337010517273987057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1029839558007011515991371 1544759337010517273987057)
          ·
            refine ⟨1158569502757887955490293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1544759337010517273987057 1158569502757887955490293)
            ·
              refine ⟨108615890883551995827215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1158569502757887955490293 108615890883551995827215)
              ·
                refine ⟨162923836325327993740823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108615890883551995827215 162923836325327993740823)
                ·
                  refine ⟨244385754487991990611235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162923836325327993740823 244385754487991990611235)
                  ·
                    refine ⟨366578631731987985916853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 244385754487991990611235 366578631731987985916853)
                    ·
                      refine ⟨34366746724873873679705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 366578631731987985916853 34366746724873873679705)
                      ·
                        rfl

theorem cell23_66929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_66929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66929 prefixEnd_66929 := by exact prefixLift 66929
  have htrace : WordTrace (prefixWord ++ tailWord_66929) baseStart_66929 baseEnd_66929 := by
    simpa [prefixWord, tailWord_66929, baseEnd_66929] using wordTrace_append hprefix tailTrace_66929
  have hstable : (prefixWord ++ tailWord_66929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66929).length < 2 ^ (prefixWord ++ tailWord_66929).sum := by decide
  have hdescent : baseEnd_66929 < baseStart_66929 := by decide
  rcases family_descends (prefixWord ++ tailWord_66929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66976 : List Nat := [2, 1, 1, 4, 1, 2, 2, 2, 4, 1, 3]
def baseStart_66976 : Nat := 118140960795 + 66976 * 2 ^ 59
def prefixEnd_66976 : Nat := 4983230072969 + 3 ^ 40 * 66976 * 2
def baseEnd_66976 : Nat := 34390880315635189791989

theorem tailTrace_66976 : CollatzResearch.WordTrace tailWord_66976 prefixEnd_66976 34390880315635189791989 := by
  unfold tailWord_66976
  simp only [CollatzResearch.WordTrace]
  refine ⟨1221407702682432717618391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1628543603576576956824521 1221407702682432717618391)
  ·
    refine ⟨1832111554023649076427587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1221407702682432717618391 1832111554023649076427587)
    ·
      refine ⟨2748167331035473614641381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1832111554023649076427587 2748167331035473614641381)
      ·
        refine ⟨515281374569151302745259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2748167331035473614641381 515281374569151302745259)
        ·
          refine ⟨772922061853726954117889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515281374569151302745259 772922061853726954117889)
          ·
            refine ⟨579691546390295215588417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 772922061853726954117889 579691546390295215588417)
            ·
              refine ⟨434768659792721411691313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 579691546390295215588417 434768659792721411691313)
              ·
                refine ⟨326076494844541058768485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 434768659792721411691313 326076494844541058768485)
                ·
                  refine ⟨61139342783351448519091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 326076494844541058768485 61139342783351448519091)
                  ·
                    refine ⟨91709014175027172778637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61139342783351448519091 91709014175027172778637)
                    ·
                      refine ⟨34390880315635189791989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 91709014175027172778637 34390880315635189791989)
                      ·
                        rfl

theorem cell23_66976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_66976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_66976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_66976 prefixEnd_66976 := by exact prefixLift 66976
  have htrace : WordTrace (prefixWord ++ tailWord_66976) baseStart_66976 baseEnd_66976 := by
    simpa [prefixWord, tailWord_66976, baseEnd_66976] using wordTrace_append hprefix tailTrace_66976
  have hstable : (prefixWord ++ tailWord_66976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66976).length < 2 ^ (prefixWord ++ tailWord_66976).sum := by decide
  have hdescent : baseEnd_66976 < baseStart_66976 := by decide
  rcases family_descends (prefixWord ++ tailWord_66976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67019 : List Nat := [1, 1, 1, 1, 3, 3, 2, 2, 2, 4, 3]
def baseStart_67019 : Nat := 118140960795 + 67019 * 2 ^ 59
def prefixEnd_67019 : Nat := 4983230072969 + 3 ^ 40 * 67019 * 2
def baseEnd_67019 : Nat := 34412959983778521554291

theorem tailTrace_67019 : CollatzResearch.WordTrace tailWord_67019 prefixEnd_67019 34412959983778521554291 := by
  unfold tailWord_67019
  simp only [CollatzResearch.WordTrace]
  refine ⟨2444383744209083779052111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1629589162806055852701407 2444383744209083779052111)
  ·
    refine ⟨3666575616313625668578167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2444383744209083779052111 3666575616313625668578167)
    ·
      refine ⟨5499863424470438502867251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3666575616313625668578167 5499863424470438502867251)
      ·
        refine ⟨8249795136705657754300877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5499863424470438502867251 8249795136705657754300877)
        ·
          refine ⟨3093673176264621657862829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8249795136705657754300877 3093673176264621657862829)
          ·
            refine ⟨1160127441099233121698561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3093673176264621657862829 1160127441099233121698561)
            ·
              refine ⟨870095580824424841273921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1160127441099233121698561 870095580824424841273921)
              ·
                refine ⟨652571685618318630955441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 870095580824424841273921 652571685618318630955441)
                ·
                  refine ⟨489428764213738973216581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 652571685618318630955441 489428764213738973216581)
                  ·
                    refine ⟨91767893290076057478109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 489428764213738973216581 91767893290076057478109)
                    ·
                      refine ⟨34412959983778521554291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 91767893290076057478109 34412959983778521554291)
                      ·
                        rfl

theorem cell23_67019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 4, 3].length) (baseStart_67019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67019 prefixEnd_67019 := by exact prefixLift 67019
  have htrace : WordTrace (prefixWord ++ tailWord_67019) baseStart_67019 baseEnd_67019 := by
    simpa [prefixWord, tailWord_67019, baseEnd_67019] using wordTrace_append hprefix tailTrace_67019
  have hstable : (prefixWord ++ tailWord_67019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67019).length < 2 ^ (prefixWord ++ tailWord_67019).sum := by decide
  have hdescent : baseEnd_67019 < baseStart_67019 := by decide
  rcases family_descends (prefixWord ++ tailWord_67019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67020 : List Nat := [2, 2, 1, 4, 2, 2, 2, 2, 1, 3, 2]
def baseStart_67020 : Nat := 118140960795 + 67020 * 2 ^ 59
def prefixEnd_67020 : Nat := 4983230072969 + 3 ^ 40 * 67020 * 2
def baseEnd_67020 : Nat := 34413473464433017641787

theorem tailTrace_67020 : CollatzResearch.WordTrace tailWord_67020 prefixEnd_67020 34413473464433017641787 := by
  unfold tailWord_67020
  simp only [CollatzResearch.WordTrace]
  refine ⟨1222210108602730474919257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1629613478136973966559009 1222210108602730474919257)
  ·
    refine ⟨916657581452047856189443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1222210108602730474919257 916657581452047856189443)
    ·
      refine ⟨1374986372178071784284165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 916657581452047856189443 1374986372178071784284165)
      ·
        refine ⟨257809944783388459553281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1374986372178071784284165 257809944783388459553281)
        ·
          refine ⟨193357458587541344664961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257809944783388459553281 193357458587541344664961)
          ·
            refine ⟨145018093940656008498721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193357458587541344664961 145018093940656008498721)
            ·
              refine ⟨108763570455492006374041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145018093940656008498721 108763570455492006374041)
              ·
                refine ⟨81572677841619004780531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108763570455492006374041 81572677841619004780531)
                ·
                  refine ⟨122359016762428507170797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81572677841619004780531 122359016762428507170797)
                  ·
                    refine ⟨45884631285910690189049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 122359016762428507170797 45884631285910690189049)
                    ·
                      refine ⟨34413473464433017641787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 45884631285910690189049 34413473464433017641787)
                      ·
                        rfl

theorem cell23_67020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_67020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67020 prefixEnd_67020 := by exact prefixLift 67020
  have htrace : WordTrace (prefixWord ++ tailWord_67020) baseStart_67020 baseEnd_67020 := by
    simpa [prefixWord, tailWord_67020, baseEnd_67020] using wordTrace_append hprefix tailTrace_67020
  have hstable : (prefixWord ++ tailWord_67020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67020).length < 2 ^ (prefixWord ++ tailWord_67020).sum := by decide
  have hdescent : baseEnd_67020 < baseStart_67020 := by decide
  rcases family_descends (prefixWord ++ tailWord_67020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67033 : List Nat := [1, 2, 1, 2, 4, 2, 1, 2, 4, 2, 2]
def baseStart_67033 : Nat := 118140960795 + 67033 * 2 ^ 59
def prefixEnd_67033 : Nat := 4983230072969 + 3 ^ 40 * 67033 * 2
def baseEnd_67033 : Nat := 34420148712941466779227

theorem tailTrace_67033 : CollatzResearch.WordTrace tailWord_67033 prefixEnd_67033 34420148712941466779227 := by
  unfold tailWord_67033
  simp only [CollatzResearch.WordTrace]
  refine ⟨2444894366158364170061753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1629929577438909446707835 2444894366158364170061753)
  ·
    refine ⟨1833670774618773127546315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2444894366158364170061753 1833670774618773127546315)
    ·
      refine ⟨2750506161928159691319473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1833670774618773127546315 2750506161928159691319473)
      ·
        refine ⟨2062879621446119768489605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2750506161928159691319473 2062879621446119768489605)
        ·
          refine ⟨386789929021147456591801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2062879621446119768489605 386789929021147456591801)
          ·
            refine ⟨290092446765860592443851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386789929021147456591801 290092446765860592443851)
            ·
              refine ⟨435138670148790888665777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290092446765860592443851 435138670148790888665777)
              ·
                refine ⟨326354002611593166499333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 435138670148790888665777 326354002611593166499333)
                ·
                  refine ⟨61191375489673718718625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 326354002611593166499333 61191375489673718718625)
                  ·
                    refine ⟨45893531617255289038969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61191375489673718718625 45893531617255289038969)
                    ·
                      refine ⟨34420148712941466779227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 45893531617255289038969 34420148712941466779227)
                      ·
                        rfl

theorem cell23_67033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 4, 2, 2].length) (baseStart_67033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67033 prefixEnd_67033 := by exact prefixLift 67033
  have htrace : WordTrace (prefixWord ++ tailWord_67033) baseStart_67033 baseEnd_67033 := by
    simpa [prefixWord, tailWord_67033, baseEnd_67033] using wordTrace_append hprefix tailTrace_67033
  have hstable : (prefixWord ++ tailWord_67033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67033).length < 2 ^ (prefixWord ++ tailWord_67033).sum := by decide
  have hdescent : baseEnd_67033 < baseStart_67033 := by decide
  rcases family_descends (prefixWord ++ tailWord_67033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67056 : List Nat := [2, 1, 1, 1, 3, 6, 1, 1, 7]
def baseStart_67056 : Nat := 118140960795 + 67056 * 2 ^ 59
def prefixEnd_67056 : Nat := 4983230072969 + 3 ^ 40 * 67056 * 2
def baseEnd_67056 : Nat := 3825773196443875199069

theorem tailTrace_67056 : CollatzResearch.WordTrace tailWord_67056 prefixEnd_67056 3825773196443875199069 := by
  unfold tailWord_67056
  simp only [CollatzResearch.WordTrace]
  refine ⟨1222866622537519549074511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1630488830050026065432681 1222866622537519549074511)
  ·
    refine ⟨1834299933806279323611767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1222866622537519549074511 1834299933806279323611767)
    ·
      refine ⟨2751449900709418985417651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1834299933806279323611767 2751449900709418985417651)
      ·
        refine ⟨4127174851064128478126477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2751449900709418985417651 4127174851064128478126477)
        ·
          refine ⟨1547690569149048179297429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4127174851064128478126477 1547690569149048179297429)
          ·
            refine ⟨72547995428861633404567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1547690569149048179297429 72547995428861633404567)
            ·
              refine ⟨108821993143292450106851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72547995428861633404567 108821993143292450106851)
              ·
                refine ⟨163232989714938675160277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108821993143292450106851 163232989714938675160277)
                ·
                  refine ⟨3825773196443875199069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 163232989714938675160277 3825773196443875199069)
                  ·
                    rfl

theorem cell23_67056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 7].length) (baseStart_67056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67056 prefixEnd_67056 := by exact prefixLift 67056
  have htrace : WordTrace (prefixWord ++ tailWord_67056) baseStart_67056 baseEnd_67056 := by
    simpa [prefixWord, tailWord_67056, baseEnd_67056] using wordTrace_append hprefix tailTrace_67056
  have hstable : (prefixWord ++ tailWord_67056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67056).length < 2 ^ (prefixWord ++ tailWord_67056).sum := by decide
  have hdescent : baseEnd_67056 < baseStart_67056 := by decide
  rcases family_descends (prefixWord ++ tailWord_67056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67107 : List Nat := [1, 1, 1, 4, 6, 1, 2, 2, 5]
def baseStart_67107 : Nat := 118140960795 + 67107 * 2 ^ 59
def prefixEnd_67107 : Nat := 4983230072969 + 3 ^ 40 * 67107 * 2
def baseEnd_67107 : Nat := 3828682920152686361543

theorem tailTrace_67107 : CollatzResearch.WordTrace tailWord_67107 prefixEnd_67107 3828682920152686361543 := by
  unfold tailWord_67107
  simp only [CollatzResearch.WordTrace]
  refine ⟨2447593367890274808255575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1631728911926849872170383 2447593367890274808255575)
  ·
    refine ⟨3671390051835412212383363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2447593367890274808255575 3671390051835412212383363)
    ·
      refine ⟨5507085077753118318575045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3671390051835412212383363 5507085077753118318575045)
      ·
        refine ⟨1032578452078709684732821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5507085077753118318575045 1032578452078709684732821)
        ·
          refine ⟨48402114941189516471851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1032578452078709684732821 48402114941189516471851)
          ·
            refine ⟨72603172411784274707777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48402114941189516471851 72603172411784274707777)
            ·
              refine ⟨54452379308838206030833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72603172411784274707777 54452379308838206030833)
              ·
                refine ⟨40839284481628654523125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54452379308838206030833 40839284481628654523125)
                ·
                  refine ⟨3828682920152686361543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40839284481628654523125 3828682920152686361543)
                  ·
                    rfl

theorem cell23_67107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 2, 5].length) (baseStart_67107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67107 prefixEnd_67107 := by exact prefixLift 67107
  have htrace : WordTrace (prefixWord ++ tailWord_67107) baseStart_67107 baseEnd_67107 := by
    simpa [prefixWord, tailWord_67107, baseEnd_67107] using wordTrace_append hprefix tailTrace_67107
  have hstable : (prefixWord ++ tailWord_67107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67107).length < 2 ^ (prefixWord ++ tailWord_67107).sum := by decide
  have hdescent : baseEnd_67107 < baseStart_67107 := by decide
  rcases family_descends (prefixWord ++ tailWord_67107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67109 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 1, 5, 5]
def baseStart_67109 : Nat := 118140960795 + 67109 * 2 ^ 59
def prefixEnd_67109 : Nat := 4983230072969 + 3 ^ 40 * 67109 * 2
def baseEnd_67109 : Nat := 34459173242683169428877

theorem tailTrace_67109 : CollatzResearch.WordTrace tailWord_67109 prefixEnd_67109 34459173242683169428877 := by
  unfold tailWord_67109
  simp only [CollatzResearch.WordTrace]
  refine ⟨2447666313883029149828381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1631777542588686099885587 2447666313883029149828381)
  ·
    refine ⟨917874867706135931185643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2447666313883029149828381 917874867706135931185643)
    ·
      refine ⟨1376812301559203896778465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 917874867706135931185643 1376812301559203896778465)
      ·
        refine ⟨1032609226169402922583849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1376812301559203896778465 1032609226169402922583849)
        ·
          refine ⟨774456919627052191937887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1032609226169402922583849 774456919627052191937887)
          ·
            refine ⟨1161685379440578287906831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 774456919627052191937887 1161685379440578287906831)
            ·
              refine ⟨1742528069160867431860247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1161685379440578287906831 1742528069160867431860247)
              ·
                refine ⟨2613792103741301147790371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1742528069160867431860247 2613792103741301147790371)
                ·
                  refine ⟨3920688155611951721685557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2613792103741301147790371 3920688155611951721685557)
                  ·
                    refine ⟨367564514588620473908021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3920688155611951721685557 367564514588620473908021)
                    ·
                      refine ⟨34459173242683169428877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 367564514588620473908021 34459173242683169428877)
                      ·
                        rfl

theorem cell23_67109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_67109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67109 prefixEnd_67109 := by exact prefixLift 67109
  have htrace : WordTrace (prefixWord ++ tailWord_67109) baseStart_67109 baseEnd_67109 := by
    simpa [prefixWord, tailWord_67109, baseEnd_67109] using wordTrace_append hprefix tailTrace_67109
  have hstable : (prefixWord ++ tailWord_67109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67109).length < 2 ^ (prefixWord ++ tailWord_67109).sum := by decide
  have hdescent : baseEnd_67109 < baseStart_67109 := by decide
  rcases family_descends (prefixWord ++ tailWord_67109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67123 : List Nat := [1, 1, 1, 2, 4, 4, 1, 1, 2, 4, 2]
def baseStart_67123 : Nat := 118140960795 + 67123 * 2 ^ 59
def prefixEnd_67123 : Nat := 4983230072969 + 3 ^ 40 * 67123 * 2
def baseEnd_67123 : Nat := 34466361971846114653813

theorem tailTrace_67123 : CollatzResearch.WordTrace tailWord_67123 prefixEnd_67123 34466361971846114653813 := by
  unfold tailWord_67123
  simp only [CollatzResearch.WordTrace]
  refine ⟨2448176935832309540838023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1632117957221539693892015 2448176935832309540838023)
  ·
    refine ⟨3672265403748464311257035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2448176935832309540838023 3672265403748464311257035)
    ·
      refine ⟨5508398105622696466885553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3672265403748464311257035 5508398105622696466885553)
      ·
        refine ⟨4131298579217022350164165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5508398105622696466885553 4131298579217022350164165)
        ·
          refine ⟨774618483603191690655781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4131298579217022350164165 774618483603191690655781)
          ·
            refine ⟨145240965675598441997959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 774618483603191690655781 145240965675598441997959)
            ·
              refine ⟨217861448513397662996939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145240965675598441997959 217861448513397662996939)
              ·
                refine ⟨326792172770096494495409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217861448513397662996939 326792172770096494495409)
                ·
                  refine ⟨245094129577572370871557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 326792172770096494495409 245094129577572370871557)
                  ·
                    refine ⟨45955149295794819538417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 245094129577572370871557 45955149295794819538417)
                    ·
                      refine ⟨34466361971846114653813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 45955149295794819538417 34466361971846114653813)
                      ·
                        rfl

theorem cell23_67123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 4, 2].length) (baseStart_67123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67123 prefixEnd_67123 := by exact prefixLift 67123
  have htrace : WordTrace (prefixWord ++ tailWord_67123) baseStart_67123 baseEnd_67123 := by
    simpa [prefixWord, tailWord_67123, baseEnd_67123] using wordTrace_append hprefix tailTrace_67123
  have hstable : (prefixWord ++ tailWord_67123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67123).length < 2 ^ (prefixWord ++ tailWord_67123).sum := by decide
  have hdescent : baseEnd_67123 < baseStart_67123 := by decide
  rcases family_descends (prefixWord ++ tailWord_67123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67143 : List Nat := [1, 1, 4, 1, 5, 1, 1, 1, 1, 4, 3]
def baseStart_67143 : Nat := 118140960795 + 67143 * 2 ^ 59
def prefixEnd_67143 : Nat := 4983230072969 + 3 ^ 40 * 67143 * 2
def baseEnd_67143 : Nat := 34476631584936036403721

theorem tailTrace_67143 : CollatzResearch.WordTrace tailWord_67143 prefixEnd_67143 34476631584936036403721 := by
  unfold tailWord_67143
  simp only [CollatzResearch.WordTrace]
  refine ⟨2448906395759852956566083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1632604263839901971044055 2448906395759852956566083)
  ·
    refine ⟨3673359593639779434849125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2448906395759852956566083 3673359593639779434849125)
    ·
      refine ⟨688754923807458644034211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3673359593639779434849125 688754923807458644034211)
      ·
        refine ⟨1033132385711187966051317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 688754923807458644034211 1033132385711187966051317)
        ·
          refine ⟨96856161160423871817311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1033132385711187966051317 96856161160423871817311)
          ·
            refine ⟨145284241740635807725967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96856161160423871817311 145284241740635807725967)
            ·
              refine ⟨217926362610953711588951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145284241740635807725967 217926362610953711588951)
              ·
                refine ⟨326889543916430567383427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217926362610953711588951 326889543916430567383427)
                ·
                  refine ⟨490334315874645851075141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 326889543916430567383427 490334315874645851075141)
                  ·
                    refine ⟨91937684226496097076589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 490334315874645851075141 91937684226496097076589)
                    ·
                      refine ⟨34476631584936036403721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 91937684226496097076589 34476631584936036403721)
                      ·
                        rfl

theorem cell23_67143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_67143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67143 prefixEnd_67143 := by exact prefixLift 67143
  have htrace : WordTrace (prefixWord ++ tailWord_67143) baseStart_67143 baseEnd_67143 := by
    simpa [prefixWord, tailWord_67143, baseEnd_67143] using wordTrace_append hprefix tailTrace_67143
  have hstable : (prefixWord ++ tailWord_67143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67143).length < 2 ^ (prefixWord ++ tailWord_67143).sum := by decide
  have hdescent : baseEnd_67143 < baseStart_67143 := by decide
  rcases family_descends (prefixWord ++ tailWord_67143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67193 : List Nat := [1, 2, 1, 3, 3, 1, 4, 2, 1, 5]
def baseStart_67193 : Nat := 118140960795 + 67193 * 2 ^ 59
def prefixEnd_67193 : Nat := 4983230072969 + 3 ^ 40 * 67193 * 2
def baseEnd_67193 : Nat := 11500768539220280259497

theorem tailTrace_67193 : CollatzResearch.WordTrace tailWord_67193 prefixEnd_67193 11500768539220280259497 := by
  unfold tailWord_67193
  simp only [CollatzResearch.WordTrace]
  refine ⟨2450730045578711495886233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1633820030385807663924155 2450730045578711495886233)
  ·
    refine ⟨1838047534184033621914675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2450730045578711495886233 1838047534184033621914675)
    ·
      refine ⟨2757071301276050432872013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1838047534184033621914675 2757071301276050432872013)
      ·
        refine ⟨1033901737978518912327005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2757071301276050432872013 1033901737978518912327005)
        ·
          refine ⟨387713151741944592122627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1033901737978518912327005 387713151741944592122627)
          ·
            refine ⟨581569727612916888183941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387713151741944592122627 581569727612916888183941)
            ·
              refine ⟨109044323927421916534489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 581569727612916888183941 109044323927421916534489)
              ·
                refine ⟨81783242945566437400867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109044323927421916534489 81783242945566437400867)
                ·
                  refine ⟨122674864418349656101301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81783242945566437400867 122674864418349656101301)
                  ·
                    refine ⟨11500768539220280259497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 122674864418349656101301 11500768539220280259497)
                    ·
                      rfl

theorem cell23_67193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 5].length) (baseStart_67193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67193 prefixEnd_67193 := by exact prefixLift 67193
  have htrace : WordTrace (prefixWord ++ tailWord_67193) baseStart_67193 baseEnd_67193 := by
    simpa [prefixWord, tailWord_67193, baseEnd_67193] using wordTrace_append hprefix tailTrace_67193
  have hstable : (prefixWord ++ tailWord_67193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67193).length < 2 ^ (prefixWord ++ tailWord_67193).sum := by decide
  have hdescent : baseEnd_67193 < baseStart_67193 := by decide
  rcases family_descends (prefixWord ++ tailWord_67193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67207 : List Nat := [1, 1, 4, 2, 1, 3, 3, 3, 1, 1, 3]
def baseStart_67207 : Nat := 118140960795 + 67207 * 2 ^ 59
def prefixEnd_67207 : Nat := 4983230072969 + 3 ^ 40 * 67207 * 2
def baseEnd_67207 : Nat := 34509494346823786003427

theorem tailTrace_67207 : CollatzResearch.WordTrace tailWord_67207 prefixEnd_67207 34509494346823786003427 := by
  unfold tailWord_67207
  simp only [CollatzResearch.WordTrace]
  refine ⟨2451240667527991886895875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1634160445018661257930583 2451240667527991886895875)
  ·
    refine ⟨3676861001291987830343813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2451240667527991886895875 3676861001291987830343813)
    ·
      refine ⟨689411437742247718189465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3676861001291987830343813 689411437742247718189465)
      ·
        refine ⟨517058578306685788642099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 689411437742247718189465 517058578306685788642099)
        ·
          refine ⟨775587867460028682963149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 517058578306685788642099 775587867460028682963149)
          ·
            refine ⟨290845450297510756111181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 775587867460028682963149 290845450297510756111181)
            ·
              refine ⟨109067043861566533541693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 290845450297510756111181 109067043861566533541693)
              ·
                refine ⟨40900141448087450078135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109067043861566533541693 40900141448087450078135)
                ·
                  refine ⟨61350212172131175117203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40900141448087450078135 61350212172131175117203)
                  ·
                    refine ⟨92025318258196762675805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61350212172131175117203 92025318258196762675805)
                    ·
                      refine ⟨34509494346823786003427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 92025318258196762675805 34509494346823786003427)
                      ·
                        rfl

theorem cell23_67207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_67207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67207 prefixEnd_67207 := by exact prefixLift 67207
  have htrace : WordTrace (prefixWord ++ tailWord_67207) baseStart_67207 baseEnd_67207 := by
    simpa [prefixWord, tailWord_67207, baseEnd_67207] using wordTrace_append hprefix tailTrace_67207
  have hstable : (prefixWord ++ tailWord_67207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67207).length < 2 ^ (prefixWord ++ tailWord_67207).sum := by decide
  have hdescent : baseEnd_67207 < baseStart_67207 := by decide
  rcases family_descends (prefixWord ++ tailWord_67207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67223 : List Nat := [1, 1, 3, 3, 2, 2, 2, 1, 4, 4]
def baseStart_67223 : Nat := 118140960795 + 67223 * 2 ^ 59
def prefixEnd_67223 : Nat := 4983230072969 + 3 ^ 40 * 67223 * 2
def baseEnd_67223 : Nat := 11505903345765241134451

theorem tailTrace_67223 : CollatzResearch.WordTrace tailWord_67223 prefixEnd_67223 11505903345765241134451 := by
  unfold tailWord_67223
  simp only [CollatzResearch.WordTrace]
  refine ⟨2451824235470026619478323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1634549490313351079652215 2451824235470026619478323)
  ·
    refine ⟨3677736353205039929217485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2451824235470026619478323 3677736353205039929217485)
    ·
      refine ⟨1379151132451889973456557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3677736353205039929217485 1379151132451889973456557)
      ·
        refine ⟨517181674669458740046209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1379151132451889973456557 517181674669458740046209)
        ·
          refine ⟨387886256002094055034657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 517181674669458740046209 387886256002094055034657)
          ·
            refine ⟨290914692001570541275993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 387886256002094055034657 290914692001570541275993)
            ·
              refine ⟨218186019001177905956995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290914692001570541275993 218186019001177905956995)
              ·
                refine ⟨327279028501766858935493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218186019001177905956995 327279028501766858935493)
                ·
                  refine ⟨61364817844081286050405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 327279028501766858935493 61364817844081286050405)
                  ·
                    refine ⟨11505903345765241134451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61364817844081286050405 11505903345765241134451)
                    ·
                      rfl

theorem cell23_67223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 4, 4].length) (baseStart_67223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67223 prefixEnd_67223 := by exact prefixLift 67223
  have htrace : WordTrace (prefixWord ++ tailWord_67223) baseStart_67223 baseEnd_67223 := by
    simpa [prefixWord, tailWord_67223, baseEnd_67223] using wordTrace_append hprefix tailTrace_67223
  have hstable : (prefixWord ++ tailWord_67223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67223).length < 2 ^ (prefixWord ++ tailWord_67223).sum := by decide
  have hdescent : baseEnd_67223 < baseStart_67223 := by decide
  rcases family_descends (prefixWord ++ tailWord_67223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67224 : List Nat := [2, 1, 2, 4, 1, 3, 3, 2, 1, 1, 3]
def baseStart_67224 : Nat := 118140960795 + 67224 * 2 ^ 59
def prefixEnd_67224 : Nat := 4983230072969 + 3 ^ 40 * 67224 * 2
def baseEnd_67224 : Nat := 34518223517950219490849

theorem tailTrace_67224 : CollatzResearch.WordTrace tailWord_67224 prefixEnd_67224 34518223517950219490849 := by
  unfold tailWord_67224
  simp only [CollatzResearch.WordTrace]
  refine ⟨1225930354233201895132363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1634573805644269193509817 1225930354233201895132363)
  ·
    refine ⟨1838895531349802842698545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1225930354233201895132363 1838895531349802842698545)
    ·
      refine ⟨1379171648512352132023909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1838895531349802842698545 1379171648512352132023909)
      ·
        refine ⟨258594684096066024754483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1379171648512352132023909 258594684096066024754483)
        ·
          refine ⟨387892026144099037131725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258594684096066024754483 387892026144099037131725)
          ·
            refine ⟨145459509804037138924397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 387892026144099037131725 145459509804037138924397)
            ·
              refine ⟨54547316176513927096649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145459509804037138924397 54547316176513927096649)
              ·
                refine ⟨40910487132385445322487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54547316176513927096649 40910487132385445322487)
                ·
                  refine ⟨61365730698578167983731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40910487132385445322487 61365730698578167983731)
                  ·
                    refine ⟨92048596047867251975597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61365730698578167983731 92048596047867251975597)
                    ·
                      refine ⟨34518223517950219490849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 92048596047867251975597 34518223517950219490849)
                      ·
                        rfl

theorem cell23_67224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_67224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67224 prefixEnd_67224 := by exact prefixLift 67224
  have htrace : WordTrace (prefixWord ++ tailWord_67224) baseStart_67224 baseEnd_67224 := by
    simpa [prefixWord, tailWord_67224, baseEnd_67224] using wordTrace_append hprefix tailTrace_67224
  have hstable : (prefixWord ++ tailWord_67224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67224).length < 2 ^ (prefixWord ++ tailWord_67224).sum := by decide
  have hdescent : baseEnd_67224 < baseStart_67224 := by decide
  rcases family_descends (prefixWord ++ tailWord_67224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67233 : List Nat := [1, 2, 3, 3, 2, 1, 2, 2, 1, 1, 5]
def baseStart_67233 : Nat := 118140960795 + 67233 * 2 ^ 59
def prefixEnd_67233 : Nat := 4983230072969 + 3 ^ 40 * 67233 * 2
def baseEnd_67233 : Nat := 34522844843840684278307

theorem tailTrace_67233 : CollatzResearch.WordTrace tailWord_67233 prefixEnd_67233 34522844843840684278307 := by
  unfold tailWord_67233
  simp only [CollatzResearch.WordTrace]
  refine ⟨2452188965433798327342353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1634792643622532218228235 2452188965433798327342353)
  ·
    refine ⟨1839141724075348745506765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2452188965433798327342353 1839141724075348745506765)
    ·
      refine ⟨689678146528255779565037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1839141724075348745506765 689678146528255779565037)
      ·
        refine ⟨258629304948095917336889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 689678146528255779565037 258629304948095917336889)
        ·
          refine ⟨193971978711071938002667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258629304948095917336889 193971978711071938002667)
          ·
            refine ⟨290957968066607907004001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193971978711071938002667 290957968066607907004001)
            ·
              refine ⟨218218476049955930253001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290957968066607907004001 218218476049955930253001)
              ·
                refine ⟨163663857037466947689751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 218218476049955930253001 163663857037466947689751)
                ·
                  refine ⟨245495785556200421534627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163663857037466947689751 245495785556200421534627)
                  ·
                    refine ⟨368243678334300632301941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 245495785556200421534627 368243678334300632301941)
                    ·
                      refine ⟨34522844843840684278307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 368243678334300632301941 34522844843840684278307)
                      ·
                        rfl

theorem cell23_67233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_67233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67233 prefixEnd_67233 := by exact prefixLift 67233
  have htrace : WordTrace (prefixWord ++ tailWord_67233) baseStart_67233 baseEnd_67233 := by
    simpa [prefixWord, tailWord_67233, baseEnd_67233] using wordTrace_append hprefix tailTrace_67233
  have hstable : (prefixWord ++ tailWord_67233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67233).length < 2 ^ (prefixWord ++ tailWord_67233).sum := by decide
  have hdescent : baseEnd_67233 < baseStart_67233 := by decide
  rcases family_descends (prefixWord ++ tailWord_67233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67236 : List Nat := [2, 3, 1, 2, 2, 2, 1, 10]
def baseStart_67236 : Nat := 118140960795 + 67236 * 2 ^ 59
def prefixEnd_67236 : Nat := 4983230072969 + 3 ^ 40 * 67236 * 2
def baseEnd_67236 : Nat := 1278680936511265649659

theorem tailTrace_67236 : CollatzResearch.WordTrace tailWord_67236 prefixEnd_67236 1278680936511265649659 := by
  unfold tailWord_67236
  simp only [CollatzResearch.WordTrace]
  refine ⟨1226149192211464919850781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1634865589615286559801041 1226149192211464919850781)
  ·
    refine ⟨459805947079299344944043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1226149192211464919850781 459805947079299344944043)
    ·
      refine ⟨689708920618949017416065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 459805947079299344944043 689708920618949017416065)
      ·
        refine ⟨517281690464211763062049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 689708920618949017416065 517281690464211763062049)
        ·
          refine ⟨387961267848158822296537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 517281690464211763062049 387961267848158822296537)
          ·
            refine ⟨290970950886119116722403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 387961267848158822296537 290970950886119116722403)
            ·
              refine ⟨436456426329178675083605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290970950886119116722403 436456426329178675083605)
              ·
                refine ⟨1278680936511265649659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 436456426329178675083605 1278680936511265649659)
                ·
                  rfl

theorem cell23_67236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 10].length) (baseStart_67236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67236 prefixEnd_67236 := by exact prefixLift 67236
  have htrace : WordTrace (prefixWord ++ tailWord_67236) baseStart_67236 baseEnd_67236 := by
    simpa [prefixWord, tailWord_67236, baseEnd_67236] using wordTrace_append hprefix tailTrace_67236
  have hstable : (prefixWord ++ tailWord_67236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67236).length < 2 ^ (prefixWord ++ tailWord_67236).sum := by decide
  have hdescent : baseEnd_67236 < baseStart_67236 := by decide
  rcases family_descends (prefixWord ++ tailWord_67236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67250 : List Nat := [3, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3]
def baseStart_67250 : Nat := 118140960795 + 67250 * 2 ^ 59
def prefixEnd_67250 : Nat := 4983230072969 + 3 ^ 40 * 67250 * 2
def baseEnd_67250 : Nat := 34531574014967117765729

theorem tailTrace_67250 : CollatzResearch.WordTrace tailWord_67250 prefixEnd_67250 34531574014967117765729 := by
  unfold tailWord_67250
  simp only [CollatzResearch.WordTrace]
  refine ⟨613202251593052557677801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1635206004248140153807469 613202251593052557677801)
  ·
    refine ⟨459901688694789418258351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 613202251593052557677801 459901688694789418258351)
    ·
      refine ⟨689852533042184127387527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 459901688694789418258351 689852533042184127387527)
      ·
        refine ⟨1034778799563276191081291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 689852533042184127387527 1034778799563276191081291)
        ·
          refine ⟨1552168199344914286621937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1034778799563276191081291 1552168199344914286621937)
          ·
            refine ⟨1164126149508685714966453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1552168199344914286621937 1164126149508685714966453)
            ·
              refine ⟨109136826516439285778105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1164126149508685714966453 109136826516439285778105)
              ·
                refine ⟨81852619887329464333579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109136826516439285778105 81852619887329464333579)
                ·
                  refine ⟨122778929830994196500369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81852619887329464333579 122778929830994196500369)
                  ·
                    refine ⟨92084197373245647375277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 122778929830994196500369 92084197373245647375277)
                    ·
                      refine ⟨34531574014967117765729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 92084197373245647375277 34531574014967117765729)
                      ·
                        rfl

theorem cell23_67250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3].length) (baseStart_67250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67250 prefixEnd_67250 := by exact prefixLift 67250
  have htrace : WordTrace (prefixWord ++ tailWord_67250) baseStart_67250 baseEnd_67250 := by
    simpa [prefixWord, tailWord_67250, baseEnd_67250] using wordTrace_append hprefix tailTrace_67250
  have hstable : (prefixWord ++ tailWord_67250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67250).length < 2 ^ (prefixWord ++ tailWord_67250).sum := by decide
  have hdescent : baseEnd_67250 < baseStart_67250 := by decide
  rcases family_descends (prefixWord ++ tailWord_67250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67263 : List Nat := [1, 1, 2, 2, 2, 3, 3, 2, 1, 3, 3]
def baseStart_67263 : Nat := 118140960795 + 67263 * 2 ^ 59
def prefixEnd_67263 : Nat := 4983230072969 + 3 ^ 40 * 67263 * 2
def baseEnd_67263 : Nat := 34538249263475566903169

theorem tailTrace_67263 : CollatzResearch.WordTrace tailWord_67263 prefixEnd_67263 34538249263475566903169 := by
  unfold tailWord_67263
  simp only [CollatzResearch.WordTrace]
  refine ⟨2453283155325113450934443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1635522103550075633956295 2453283155325113450934443)
  ·
    refine ⟨3679924732987670176401665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2453283155325113450934443 3679924732987670176401665)
    ·
      refine ⟨2759943549740752632301249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3679924732987670176401665 2759943549740752632301249)
      ·
        refine ⟨2069957662305564474225937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2759943549740752632301249 2069957662305564474225937)
        ·
          refine ⟨1552468246729173355669453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2069957662305564474225937 1552468246729173355669453)
          ·
            refine ⟨582175592523440008376045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1552468246729173355669453 582175592523440008376045)
            ·
              refine ⟨218315847196290003141017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 582175592523440008376045 218315847196290003141017)
              ·
                refine ⟨163736885397217502355763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 218315847196290003141017 163736885397217502355763)
                ·
                  refine ⟨245605328095826253533645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163736885397217502355763 245605328095826253533645)
                  ·
                    refine ⟨92101998035934845075117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 245605328095826253533645 92101998035934845075117)
                    ·
                      refine ⟨34538249263475566903169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 92101998035934845075117 34538249263475566903169)
                      ·
                        rfl

theorem cell23_67263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 3, 3].length) (baseStart_67263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67263 prefixEnd_67263 := by exact prefixLift 67263
  have htrace : WordTrace (prefixWord ++ tailWord_67263) baseStart_67263 baseEnd_67263 := by
    simpa [prefixWord, tailWord_67263, baseEnd_67263] using wordTrace_append hprefix tailTrace_67263
  have hstable : (prefixWord ++ tailWord_67263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67263).length < 2 ^ (prefixWord ++ tailWord_67263).sum := by decide
  have hdescent : baseEnd_67263 < baseStart_67263 := by decide
  rcases family_descends (prefixWord ++ tailWord_67263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67270 : List Nat := [6, 1, 2, 1, 1, 12]
def baseStart_67270 : Nat := 118140960795 + 67270 * 2 ^ 59
def prefixEnd_67270 : Nat := 4983230072969 + 3 ^ 40 * 67270 * 2
def baseEnd_67270 : Nat := 142147504642210039159

theorem tailTrace_67270 : CollatzResearch.WordTrace tailWord_67270 prefixEnd_67270 142147504642210039159 := by
  unfold tailWord_67270
  simp only [CollatzResearch.WordTrace]
  refine ⟨76673077071867301451227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1635692310866502430959509 76673077071867301451227)
  ·
    refine ⟨115009615607800952176841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76673077071867301451227 115009615607800952176841)
    ·
      refine ⟨86257211705850714132631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115009615607800952176841 86257211705850714132631)
      ·
        refine ⟨129385817558776071198947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86257211705850714132631 129385817558776071198947)
        ·
          refine ⟨194078726338164106798421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129385817558776071198947 194078726338164106798421)
          ·
            refine ⟨142147504642210039159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 194078726338164106798421 142147504642210039159)
            ·
              rfl

theorem cell23_67270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 12].length) (baseStart_67270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67270 prefixEnd_67270 := by exact prefixLift 67270
  have htrace : WordTrace (prefixWord ++ tailWord_67270) baseStart_67270 baseEnd_67270 := by
    simpa [prefixWord, tailWord_67270, baseEnd_67270] using wordTrace_append hprefix tailTrace_67270
  have hstable : (prefixWord ++ tailWord_67270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67270).length < 2 ^ (prefixWord ++ tailWord_67270).sum := by decide
  have hdescent : baseEnd_67270 < baseStart_67270 := by decide
  rcases family_descends (prefixWord ++ tailWord_67270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67281 : List Nat := [1, 2, 2, 1, 2, 6, 2, 2, 1, 2, 2]
def baseStart_67281 : Nat := 118140960795 + 67281 * 2 ^ 59
def prefixEnd_67281 : Nat := 4983230072969 + 3 ^ 40 * 67281 * 2
def baseEnd_67281 : Nat := 34547491915256496478087

theorem tailTrace_67281 : CollatzResearch.WordTrace tailWord_67281 prefixEnd_67281 34547491915256496478087 := by
  unfold tailWord_67281
  simp only [CollatzResearch.WordTrace]
  refine ⟨2453939669259902525089697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1635959779506601683393131 2453939669259902525089697)
  ·
    refine ⟨1840454751944926893817273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2453939669259902525089697 1840454751944926893817273)
    ·
      refine ⟨1380341063958695170362955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1840454751944926893817273 1380341063958695170362955)
      ·
        refine ⟨2070511595938042755544433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1380341063958695170362955 2070511595938042755544433)
        ·
          refine ⟨1552883696953532066658325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2070511595938042755544433 1552883696953532066658325)
          ·
            refine ⟨72791423294696815624609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1552883696953532066658325 72791423294696815624609)
            ·
              refine ⟨54593567471022611718457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72791423294696815624609 54593567471022611718457)
              ·
                refine ⟨40945175603266958788843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54593567471022611718457 40945175603266958788843)
                ·
                  refine ⟨61417763404900438183265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40945175603266958788843 61417763404900438183265)
                  ·
                    refine ⟨46063322553675328637449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61417763404900438183265 46063322553675328637449)
                    ·
                      refine ⟨34547491915256496478087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 46063322553675328637449 34547491915256496478087)
                      ·
                        rfl

theorem cell23_67281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 2, 1, 2, 2].length) (baseStart_67281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67281 prefixEnd_67281 := by exact prefixLift 67281
  have htrace : WordTrace (prefixWord ++ tailWord_67281) baseStart_67281 baseEnd_67281 := by
    simpa [prefixWord, tailWord_67281, baseEnd_67281] using wordTrace_append hprefix tailTrace_67281
  have hstable : (prefixWord ++ tailWord_67281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67281).length < 2 ^ (prefixWord ++ tailWord_67281).sum := by decide
  have hdescent : baseEnd_67281 < baseStart_67281 := by decide
  rcases family_descends (prefixWord ++ tailWord_67281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67290 : List Nat := [3, 1, 1, 2, 2, 3, 1, 2, 3, 3, 2]
def baseStart_67290 : Nat := 118140960795 + 67290 * 2 ^ 59
def prefixEnd_67290 : Nat := 4983230072969 + 3 ^ 40 * 67290 * 2
def baseEnd_67290 : Nat := 34552113241146961265545

theorem tailTrace_67290 : CollatzResearch.WordTrace tailWord_67290 prefixEnd_67290 34552113241146961265545 := by
  unfold tailWord_67290
  simp only [CollatzResearch.WordTrace]
  refine ⟨613566981556824265541831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1636178617484864708111549 613566981556824265541831)
  ·
    refine ⟨920350472335236398312747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 613566981556824265541831 920350472335236398312747)
    ·
      refine ⟨1380525708502854597469121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 920350472335236398312747 1380525708502854597469121)
      ·
        refine ⟨1035394281377140948101841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1380525708502854597469121 1035394281377140948101841)
        ·
          refine ⟨776545711032855711076381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1035394281377140948101841 776545711032855711076381)
          ·
            refine ⟨291204641637320891653643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 776545711032855711076381 291204641637320891653643)
            ·
              refine ⟨436806962455981337480465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291204641637320891653643 436806962455981337480465)
              ·
                refine ⟨327605221841986003110349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 436806962455981337480465 327605221841986003110349)
                ·
                  refine ⟨122851958190744751166381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 327605221841986003110349 122851958190744751166381)
                  ·
                    refine ⟨46069484321529281687393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 122851958190744751166381 46069484321529281687393)
                    ·
                      refine ⟨34552113241146961265545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 46069484321529281687393 34552113241146961265545)
                      ·
                        rfl

theorem cell23_67290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 3, 3, 2].length) (baseStart_67290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67290 prefixEnd_67290 := by exact prefixLift 67290
  have htrace : WordTrace (prefixWord ++ tailWord_67290) baseStart_67290 baseEnd_67290 := by
    simpa [prefixWord, tailWord_67290, baseEnd_67290] using wordTrace_append hprefix tailTrace_67290
  have hstable : (prefixWord ++ tailWord_67290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67290).length < 2 ^ (prefixWord ++ tailWord_67290).sum := by decide
  have hdescent : baseEnd_67290 < baseStart_67290 := by decide
  rcases family_descends (prefixWord ++ tailWord_67290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67296 : List Nat := [2, 1, 1, 3, 1, 2, 3, 1, 1, 8]
def baseStart_67296 : Nat := 118140960795 + 67296 * 2 ^ 59
def prefixEnd_67296 : Nat := 4983230072969 + 3 ^ 40 * 67296 * 2
def baseEnd_67296 : Nat := 11518398041691312596839

theorem tailTrace_67296 : CollatzResearch.WordTrace tailWord_67296 prefixEnd_67296 11518398041691312596839 := by
  unfold tailWord_67296
  simp only [CollatzResearch.WordTrace]
  refine ⟨1227243382102780043442871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1636324509470373391257161 1227243382102780043442871)
  ·
    refine ⟨1840865073154170065164307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1227243382102780043442871 1840865073154170065164307)
    ·
      refine ⟨2761297609731255097746461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1840865073154170065164307 2761297609731255097746461)
      ·
        refine ⟨1035486603649220661654923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2761297609731255097746461 1035486603649220661654923)
        ·
          refine ⟨1553229905473830992482385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1035486603649220661654923 1553229905473830992482385)
          ·
            refine ⟨1164922429105373244361789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1553229905473830992482385 1164922429105373244361789)
            ·
              refine ⟨436845910914514966635671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1164922429105373244361789 436845910914514966635671)
              ·
                refine ⟨655268866371772449953507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 436845910914514966635671 655268866371772449953507)
                ·
                  refine ⟨982903299557658674930261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 655268866371772449953507 982903299557658674930261)
                  ·
                    refine ⟨11518398041691312596839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 982903299557658674930261 11518398041691312596839)
                    ·
                      rfl

theorem cell23_67296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 1, 8].length) (baseStart_67296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67296 prefixEnd_67296 := by exact prefixLift 67296
  have htrace : WordTrace (prefixWord ++ tailWord_67296) baseStart_67296 baseEnd_67296 := by
    simpa [prefixWord, tailWord_67296, baseEnd_67296] using wordTrace_append hprefix tailTrace_67296
  have hstable : (prefixWord ++ tailWord_67296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67296).length < 2 ^ (prefixWord ++ tailWord_67296).sum := by decide
  have hdescent : baseEnd_67296 < baseStart_67296 := by decide
  rcases family_descends (prefixWord ++ tailWord_67296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67348 : List Nat := [2, 4, 4, 1, 2, 1, 1, 1, 1, 3, 3]
def baseStart_67348 : Nat := 118140960795 + 67348 * 2 ^ 59
def prefixEnd_67348 : Nat := 4983230072969 + 3 ^ 40 * 67348 * 2
def baseEnd_67348 : Nat := 34581895119107734340279

theorem tailTrace_67348 : CollatzResearch.WordTrace tailWord_67348 prefixEnd_67348 34581895119107734340279 := by
  unfold tailWord_67348
  simp only [CollatzResearch.WordTrace]
  refine ⟨1228191680008586483889349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1637588906678115311852465 1228191680008586483889349)
  ·
    refine ⟨230285940001609965729253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1228191680008586483889349 230285940001609965729253)
    ·
      refine ⟨43178613750301868574235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 230285940001609965729253 43178613750301868574235)
      ·
        refine ⟨64767920625452802861353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43178613750301868574235 64767920625452802861353)
        ·
          refine ⟨48575940469089602146015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64767920625452802861353 48575940469089602146015)
          ·
            refine ⟨72863910703634403219023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48575940469089602146015 72863910703634403219023)
            ·
              refine ⟨109295866055451604828535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72863910703634403219023 109295866055451604828535)
              ·
                refine ⟨163943799083177407242803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109295866055451604828535 163943799083177407242803)
                ·
                  refine ⟨245915698624766110864205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163943799083177407242803 245915698624766110864205)
                  ·
                    refine ⟨92218386984287291574077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 245915698624766110864205 92218386984287291574077)
                    ·
                      refine ⟨34581895119107734340279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 92218386984287291574077 34581895119107734340279)
                      ·
                        rfl

theorem cell23_67348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_67348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67348 prefixEnd_67348 := by exact prefixLift 67348
  have htrace : WordTrace (prefixWord ++ tailWord_67348) baseStart_67348 baseEnd_67348 := by
    simpa [prefixWord, tailWord_67348, baseEnd_67348] using wordTrace_append hprefix tailTrace_67348
  have hstable : (prefixWord ++ tailWord_67348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67348).length < 2 ^ (prefixWord ++ tailWord_67348).sum := by decide
  have hdescent : baseEnd_67348 < baseStart_67348 := by decide
  rcases family_descends (prefixWord ++ tailWord_67348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67358 : List Nat := [4, 3, 2, 2, 1, 1, 2, 2, 1, 3, 2]
def baseStart_67358 : Nat := 118140960795 + 67358 * 2 ^ 59
def prefixEnd_67358 : Nat := 4983230072969 + 3 ^ 40 * 67358 * 2
def baseEnd_67358 : Nat := 34587029925652695215233

theorem tailTrace_67358 : CollatzResearch.WordTrace tailWord_67358 prefixEnd_67358 34587029925652695215233 := by
  unfold tailWord_67358
  simp only [CollatzResearch.WordTrace]
  refine ⟨307093511247618084455341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1637832059987296450428485 307093511247618084455341)
  ·
    refine ⟨115160066717856781670753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 307093511247618084455341 115160066717856781670753)
    ·
      refine ⟨86370050038392586253065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115160066717856781670753 86370050038392586253065)
      ·
        refine ⟨64777537528794439689799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86370050038392586253065 64777537528794439689799)
        ·
          refine ⟨97166306293191659534699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64777537528794439689799 97166306293191659534699)
          ·
            refine ⟨145749459439787489302049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97166306293191659534699 145749459439787489302049)
            ·
              refine ⟨109312094579840616976537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145749459439787489302049 109312094579840616976537)
              ·
                refine ⟨81984070934880462732403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109312094579840616976537 81984070934880462732403)
                ·
                  refine ⟨122976106402320694098605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81984070934880462732403 122976106402320694098605)
                  ·
                    refine ⟨46116039900870260286977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 122976106402320694098605 46116039900870260286977)
                    ·
                      refine ⟨34587029925652695215233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 46116039900870260286977 34587029925652695215233)
                      ·
                        rfl

theorem cell23_67358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_67358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67358 prefixEnd_67358 := by exact prefixLift 67358
  have htrace : WordTrace (prefixWord ++ tailWord_67358) baseStart_67358 baseEnd_67358 := by
    simpa [prefixWord, tailWord_67358, baseEnd_67358] using wordTrace_append hprefix tailTrace_67358
  have hstable : (prefixWord ++ tailWord_67358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67358).length < 2 ^ (prefixWord ++ tailWord_67358).sum := by decide
  have hdescent : baseEnd_67358 < baseStart_67358 := by decide
  rcases family_descends (prefixWord ++ tailWord_67358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67377 : List Nat := [1, 2, 2, 3, 2, 4, 1, 3, 5]
def baseStart_67377 : Nat := 118140960795 + 67377 * 2 ^ 59
def prefixEnd_67377 : Nat := 4983230072969 + 3 ^ 40 * 67377 * 2
def baseEnd_67377 : Nat := 3844087339787568986405

theorem tailTrace_67377 : CollatzResearch.WordTrace tailWord_67377 prefixEnd_67377 3844087339787568986405 := by
  unfold tailWord_67377
  simp only [CollatzResearch.WordTrace]
  refine ⟨2457441076912110920584385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1638294051274740613722923 2457441076912110920584385)
  ·
    refine ⟨1843080807684083190438289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2457441076912110920584385 1843080807684083190438289)
    ·
      refine ⟨1382310605763062392828717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1843080807684083190438289 1382310605763062392828717)
      ·
        refine ⟨518366477161148397310769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1382310605763062392828717 518366477161148397310769)
        ·
          refine ⟨388774857870861297983077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 518366477161148397310769 388774857870861297983077)
          ·
            refine ⟨72895285850786493371827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 388774857870861297983077 72895285850786493371827)
            ·
              refine ⟨109342928776179740057741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72895285850786493371827 109342928776179740057741)
              ·
                refine ⟨41003598291067402521653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109342928776179740057741 41003598291067402521653)
                ·
                  refine ⟨3844087339787568986405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41003598291067402521653 3844087339787568986405)
                  ·
                    rfl

theorem cell23_67377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 3, 5].length) (baseStart_67377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67377 prefixEnd_67377 := by exact prefixLift 67377
  have htrace : WordTrace (prefixWord ++ tailWord_67377) baseStart_67377 baseEnd_67377 := by
    simpa [prefixWord, tailWord_67377, baseEnd_67377] using wordTrace_append hprefix tailTrace_67377
  have hstable : (prefixWord ++ tailWord_67377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67377).length < 2 ^ (prefixWord ++ tailWord_67377).sum := by decide
  have hdescent : baseEnd_67377 < baseStart_67377 := by decide
  rcases family_descends (prefixWord ++ tailWord_67377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67390 : List Nat := [4, 2, 1, 2, 2, 1, 1, 1, 4, 5]
def baseStart_67390 : Nat := 118140960795 + 67390 * 2 ^ 59
def prefixEnd_67390 : Nat := 4983230072969 + 3 ^ 40 * 67390 * 2
def baseEnd_67390 : Nat := 11534487102198856671695

theorem tailTrace_67390 : CollatzResearch.WordTrace tailWord_67390 prefixEnd_67390 11534487102198856671695 := by
  unfold tailWord_67390
  simp only [CollatzResearch.WordTrace]
  refine ⟨307239403233126767600953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1638610150576676093871749 307239403233126767600953)
  ·
    refine ⟨230429552424845075700715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 307239403233126767600953 230429552424845075700715)
    ·
      refine ⟨345644328637267613551073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230429552424845075700715 345644328637267613551073)
      ·
        refine ⟨259233246477950710163305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 345644328637267613551073 259233246477950710163305)
        ·
          refine ⟨194424934858463032622479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 259233246477950710163305 194424934858463032622479)
          ·
            refine ⟨291637402287694548933719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194424934858463032622479 291637402287694548933719)
            ·
              refine ⟨437456103431541823400579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291637402287694548933719 437456103431541823400579)
              ·
                refine ⟨656184155147312735100869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 437456103431541823400579 656184155147312735100869)
                ·
                  refine ⟨123034529090121137831413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 656184155147312735100869 123034529090121137831413)
                  ·
                    refine ⟨11534487102198856671695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 123034529090121137831413 11534487102198856671695)
                    ·
                      rfl

theorem cell23_67390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_67390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67390 prefixEnd_67390 := by exact prefixLift 67390
  have htrace : WordTrace (prefixWord ++ tailWord_67390) baseStart_67390 baseEnd_67390 := by
    simpa [prefixWord, tailWord_67390, baseEnd_67390] using wordTrace_append hprefix tailTrace_67390
  have hstable : (prefixWord ++ tailWord_67390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67390).length < 2 ^ (prefixWord ++ tailWord_67390).sum := by decide
  have hdescent : baseEnd_67390 < baseStart_67390 := by decide
  rcases family_descends (prefixWord ++ tailWord_67390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67427 : List Nat := [1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 4]
def baseStart_67427 : Nat := 118140960795 + 67427 * 2 ^ 59
def prefixEnd_67427 : Nat := 4983230072969 + 3 ^ 40 * 67427 * 2
def baseEnd_67427 : Nat := 34622460090812925252415

theorem tailTrace_67427 : CollatzResearch.WordTrace tailWord_67427 prefixEnd_67427 34622460090812925252415 := by
  unfold tailWord_67427
  simp only [CollatzResearch.WordTrace]
  refine ⟨2459264726730969459904535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1639509817820646306603023 2459264726730969459904535)
  ·
    refine ⟨3688897090096454189856803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2459264726730969459904535 3688897090096454189856803)
    ·
      refine ⟨5533345635144681284785205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3688897090096454189856803 5533345635144681284785205)
      ·
        refine ⟨518751153294813870448613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5533345635144681284785205 518751153294813870448613)
        ·
          refine ⟨97265841242777600709115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 518751153294813870448613 97265841242777600709115)
          ·
            refine ⟨145898761864166401063673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97265841242777600709115 145898761864166401063673)
            ·
              refine ⟨109424071398124800797755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145898761864166401063673 109424071398124800797755)
              ·
                refine ⟨164136107097187201196633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109424071398124800797755 164136107097187201196633)
                ·
                  refine ⟨123102080322890400897475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 164136107097187201196633 123102080322890400897475)
                  ·
                    refine ⟨184653120484335601346213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 123102080322890400897475 184653120484335601346213)
                    ·
                      refine ⟨34622460090812925252415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 184653120484335601346213 34622460090812925252415)
                      ·
                        rfl

theorem cell23_67427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_67427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67427 prefixEnd_67427 := by exact prefixLift 67427
  have htrace : WordTrace (prefixWord ++ tailWord_67427) baseStart_67427 baseEnd_67427 := by
    simpa [prefixWord, tailWord_67427, baseEnd_67427] using wordTrace_append hprefix tailTrace_67427
  have hstable : (prefixWord ++ tailWord_67427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67427).length < 2 ^ (prefixWord ++ tailWord_67427).sum := by decide
  have hdescent : baseEnd_67427 < baseStart_67427 := by decide
  rcases family_descends (prefixWord ++ tailWord_67427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67453 : List Nat := [1, 4, 1, 1, 2, 1, 1, 3, 1, 2, 6]
def baseStart_67453 : Nat := 118140960795 + 67453 * 2 ^ 59
def prefixEnd_67453 : Nat := 4983230072969 + 3 ^ 40 * 67453 * 2
def baseEnd_67453 : Nat := 34635810587829823527295

theorem tailTrace_67453 : CollatzResearch.WordTrace tailWord_67453 prefixEnd_67453 34635810587829823527295 := by
  unfold tailWord_67453
  simp only [CollatzResearch.WordTrace]
  refine ⟨2460213024636775900351013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1640142016424517266900675 2460213024636775900351013)
  ·
    refine ⟨461289942119395481315815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2460213024636775900351013 461289942119395481315815)
    ·
      refine ⟨691934913179093221973723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 461289942119395481315815 691934913179093221973723)
      ·
        refine ⟨1037902369768639832960585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 691934913179093221973723 1037902369768639832960585)
        ·
          refine ⟨778426777326479874720439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1037902369768639832960585 778426777326479874720439)
          ·
            refine ⟨1167640165989719812080659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 778426777326479874720439 1167640165989719812080659)
            ·
              refine ⟨1751460248984579718120989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1167640165989719812080659 1751460248984579718120989)
              ·
                refine ⟨656797593369217394295371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1751460248984579718120989 656797593369217394295371)
                ·
                  refine ⟨985196390053826091443057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 656797593369217394295371 985196390053826091443057)
                  ·
                    refine ⟨738897292540369568582293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 985196390053826091443057 738897292540369568582293)
                    ·
                      refine ⟨34635810587829823527295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 738897292540369568582293 34635810587829823527295)
                      ·
                        rfl

theorem cell23_67453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_67453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67453 prefixEnd_67453 := by exact prefixLift 67453
  have htrace : WordTrace (prefixWord ++ tailWord_67453) baseStart_67453 baseEnd_67453 := by
    simpa [prefixWord, tailWord_67453, baseEnd_67453] using wordTrace_append hprefix tailTrace_67453
  have hstable : (prefixWord ++ tailWord_67453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67453).length < 2 ^ (prefixWord ++ tailWord_67453).sum := by decide
  have hdescent : baseEnd_67453 < baseStart_67453 := by decide
  rcases family_descends (prefixWord ++ tailWord_67453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67477 : List Nat := [1, 3, 2, 1, 1, 3, 3, 2, 3, 1, 3]
def baseStart_67477 : Nat := 118140960795 + 67477 * 2 ^ 59
def prefixEnd_67477 : Nat := 4983230072969 + 3 ^ 40 * 67477 * 2
def baseEnd_67477 : Nat := 34648134123537729627185

theorem tailTrace_67477 : CollatzResearch.WordTrace tailWord_67477 prefixEnd_67477 34648134123537729627185 := by
  unfold tailWord_67477
  simp only [CollatzResearch.WordTrace]
  refine ⟨2461088376549827999224685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1640725584366551999483123 2461088376549827999224685)
  ·
    refine ⟨922908141206185499709257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2461088376549827999224685 922908141206185499709257)
    ·
      refine ⟨692181105904639124781943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 922908141206185499709257 692181105904639124781943)
      ·
        refine ⟨1038271658856958687172915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 692181105904639124781943 1038271658856958687172915)
        ·
          refine ⟨1557407488285438030759373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1038271658856958687172915 1557407488285438030759373)
          ·
            refine ⟨584027808107039261534765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1557407488285438030759373 584027808107039261534765)
            ·
              refine ⟨219010428040139723075537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 584027808107039261534765 219010428040139723075537)
              ·
                refine ⟨164257821030104792306653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 219010428040139723075537 164257821030104792306653)
                ·
                  refine ⟨61596682886289297114995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 164257821030104792306653 61596682886289297114995)
                  ·
                    refine ⟨92395024329433945672493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61596682886289297114995 92395024329433945672493)
                    ·
                      refine ⟨34648134123537729627185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 92395024329433945672493 34648134123537729627185)
                      ·
                        rfl

theorem cell23_67477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 3, 1, 3].length) (baseStart_67477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67477 prefixEnd_67477 := by exact prefixLift 67477
  have htrace : WordTrace (prefixWord ++ tailWord_67477) baseStart_67477 baseEnd_67477 := by
    simpa [prefixWord, tailWord_67477, baseEnd_67477] using wordTrace_append hprefix tailTrace_67477
  have hstable : (prefixWord ++ tailWord_67477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67477).length < 2 ^ (prefixWord ++ tailWord_67477).sum := by decide
  have hdescent : baseEnd_67477 < baseStart_67477 := by decide
  rcases family_descends (prefixWord ++ tailWord_67477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67478 : List Nat := [5, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4]
def baseStart_67478 : Nat := 118140960795 + 67478 * 2 ^ 59
def prefixEnd_67478 : Nat := 4983230072969 + 3 ^ 40 * 67478 * 2
def baseEnd_67478 : Nat := 34648647604192225714681

theorem tailTrace_67478 : CollatzResearch.WordTrace tailWord_67478 prefixEnd_67478 34648647604192225714681 := by
  unfold tailWord_67478
  simp only [CollatzResearch.WordTrace]
  refine ⟨153820303096637823125693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1640749899697470113340725 153820303096637823125693)
  ·
    refine ⟨57682613661239183672135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153820303096637823125693 57682613661239183672135)
    ·
      refine ⟨86523920491858775508203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57682613661239183672135 86523920491858775508203)
      ·
        refine ⟨129785880737788163262305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86523920491858775508203 129785880737788163262305)
        ·
          refine ⟨97339410553341122446729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129785880737788163262305 97339410553341122446729)
          ·
            refine ⟨73004557915005841835047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97339410553341122446729 73004557915005841835047)
            ·
              refine ⟨109506836872508762752571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73004557915005841835047 109506836872508762752571)
              ·
                refine ⟨164260255308763144128857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109506836872508762752571 164260255308763144128857)
                ·
                  refine ⟨123195191481572358096643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 164260255308763144128857 123195191481572358096643)
                  ·
                    refine ⟨184792787222358537144965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 123195191481572358096643 184792787222358537144965)
                    ·
                      refine ⟨34648647604192225714681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 184792787222358537144965 34648647604192225714681)
                      ·
                        rfl

theorem cell23_67478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_67478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67478 prefixEnd_67478 := by exact prefixLift 67478
  have htrace : WordTrace (prefixWord ++ tailWord_67478) baseStart_67478 baseEnd_67478 := by
    simpa [prefixWord, tailWord_67478, baseEnd_67478] using wordTrace_append hprefix tailTrace_67478
  have hstable : (prefixWord ++ tailWord_67478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67478).length < 2 ^ (prefixWord ++ tailWord_67478).sum := by decide
  have hdescent : baseEnd_67478 < baseStart_67478 := by decide
  rcases family_descends (prefixWord ++ tailWord_67478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67520 : List Nat := [2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 5]
def baseStart_67520 : Nat := 118140960795 + 67520 * 2 ^ 59
def prefixEnd_67520 : Nat := 4983230072969 + 3 ^ 40 * 67520 * 2
def baseEnd_67520 : Nat := 34670213791681061389487

theorem tailTrace_67520 : CollatzResearch.WordTrace tailWord_67520 prefixEnd_67520 34670213791681061389487 := by
  unfold tailWord_67520
  simp only [CollatzResearch.WordTrace]
  refine ⟨1231328357697023171520007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1641771143596030895360009 1231328357697023171520007)
  ·
    refine ⟨1846992536545534757280011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1231328357697023171520007 1846992536545534757280011)
    ·
      refine ⟨2770488804818302135920017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1846992536545534757280011 2770488804818302135920017)
      ·
        refine ⟨2077866603613726601940013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2770488804818302135920017 2077866603613726601940013)
        ·
          refine ⟨779199976355147475727505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2077866603613726601940013 779199976355147475727505)
          ·
            refine ⟨584399982266360606795629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 779199976355147475727505 584399982266360606795629)
            ·
              refine ⟨219149993349885227548361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 584399982266360606795629 219149993349885227548361)
              ·
                refine ⟨164362495012413920661271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 219149993349885227548361 164362495012413920661271)
                ·
                  refine ⟨246543742518620880991907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 164362495012413920661271 246543742518620880991907)
                  ·
                    refine ⟨369815613777931321487861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 246543742518620880991907 369815613777931321487861)
                    ·
                      refine ⟨34670213791681061389487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 369815613777931321487861 34670213791681061389487)
                      ·
                        rfl

theorem cell23_67520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 5].length) (baseStart_67520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67520 prefixEnd_67520 := by exact prefixLift 67520
  have htrace : WordTrace (prefixWord ++ tailWord_67520) baseStart_67520 baseEnd_67520 := by
    simpa [prefixWord, tailWord_67520, baseEnd_67520] using wordTrace_append hprefix tailTrace_67520
  have hstable : (prefixWord ++ tailWord_67520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67520).length < 2 ^ (prefixWord ++ tailWord_67520).sum := by decide
  have hdescent : baseEnd_67520 < baseStart_67520 := by decide
  rcases family_descends (prefixWord ++ tailWord_67520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67534 : List Nat := [4, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2]
def baseStart_67534 : Nat := 118140960795 + 67534 * 2 ^ 59
def prefixEnd_67534 : Nat := 4983230072969 + 3 ^ 40 * 67534 * 2
def baseEnd_67534 : Nat := 34677402520844006614423

theorem tailTrace_67534 : CollatzResearch.WordTrace tailWord_67534 prefixEnd_67534 34677402520844006614423 := by
  unfold tailWord_67534
  simp only [CollatzResearch.WordTrace]
  refine ⟨307895917167915841756207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1642111558228884489366437 307895917167915841756207)
  ·
    refine ⟨461843875751873762634311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 307895917167915841756207 461843875751873762634311)
    ·
      refine ⟨692765813627810643951467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 461843875751873762634311 692765813627810643951467)
      ·
        refine ⟨1039148720441715965927201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 692765813627810643951467 1039148720441715965927201)
        ·
          refine ⟨779361540331286974445401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1039148720441715965927201 779361540331286974445401)
          ·
            refine ⟨584521155248465230834051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 779361540331286974445401 584521155248465230834051)
            ·
              refine ⟨876781732872697846251077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 584521155248465230834051 876781732872697846251077)
              ·
                refine ⟨164396574913630846172077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 876781732872697846251077 164396574913630846172077)
                ·
                  refine ⟨61648715592611567314529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 164396574913630846172077 61648715592611567314529)
                  ·
                    refine ⟨46236536694458675485897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61648715592611567314529 46236536694458675485897)
                    ·
                      refine ⟨34677402520844006614423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 46236536694458675485897 34677402520844006614423)
                      ·
                        rfl

theorem cell23_67534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 3, 2, 2].length) (baseStart_67534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67534 prefixEnd_67534 := by exact prefixLift 67534
  have htrace : WordTrace (prefixWord ++ tailWord_67534) baseStart_67534 baseEnd_67534 := by
    simpa [prefixWord, tailWord_67534, baseEnd_67534] using wordTrace_append hprefix tailTrace_67534
  have hstable : (prefixWord ++ tailWord_67534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67534).length < 2 ^ (prefixWord ++ tailWord_67534).sum := by decide
  have hdescent : baseEnd_67534 < baseStart_67534 := by decide
  rcases family_descends (prefixWord ++ tailWord_67534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67540 : List Nat := [2, 4, 1, 2, 1, 1, 3, 9]
def baseStart_67540 : Nat := 118140960795 + 67540 * 2 ^ 59
def prefixEnd_67540 : Nat := 4983230072969 + 3 ^ 40 * 67540 * 2
def baseEnd_67540 : Nat := 1284462348324851227385

theorem tailTrace_67540 : CollatzResearch.WordTrace tailWord_67540 prefixEnd_67540 1284462348324851227385 := by
  unfold tailWord_67540
  simp only [CollatzResearch.WordTrace]
  refine ⟨1231693087660794879384037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1642257450214393172512049 1231693087660794879384037)
  ·
    refine ⟨230942453936399039884507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1231693087660794879384037 230942453936399039884507)
    ·
      refine ⟨346413680904598559826761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230942453936399039884507 346413680904598559826761)
      ·
        refine ⟨259810260678448919870071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 346413680904598559826761 259810260678448919870071)
        ·
          refine ⟨389715391017673379805107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259810260678448919870071 389715391017673379805107)
          ·
            refine ⟨584573086526510069707661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 389715391017673379805107 584573086526510069707661)
            ·
              refine ⟨219214907447441276140373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 584573086526510069707661 219214907447441276140373)
              ·
                refine ⟨1284462348324851227385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 219214907447441276140373 1284462348324851227385)
                ·
                  rfl

theorem cell23_67540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 9].length) (baseStart_67540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67540 prefixEnd_67540 := by exact prefixLift 67540
  have htrace : WordTrace (prefixWord ++ tailWord_67540) baseStart_67540 baseEnd_67540 := by
    simpa [prefixWord, tailWord_67540, baseEnd_67540] using wordTrace_append hprefix tailTrace_67540
  have hstable : (prefixWord ++ tailWord_67540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67540).length < 2 ^ (prefixWord ++ tailWord_67540).sum := by decide
  have hdescent : baseEnd_67540 < baseStart_67540 := by decide
  rcases family_descends (prefixWord ++ tailWord_67540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67567 : List Nat := [1, 1, 2, 1, 4, 2, 1, 3, 4, 1, 3]
def baseStart_67567 : Nat := 118140960795 + 67567 * 2 ^ 59
def prefixEnd_67567 : Nat := 4983230072969 + 3 ^ 40 * 67567 * 2
def baseEnd_67567 : Nat := 34694347382442377501771

theorem tailTrace_67567 : CollatzResearch.WordTrace tailWord_67567 prefixEnd_67567 34694347382442377501771 := by
  unfold tailWord_67567
  simp only [CollatzResearch.WordTrace]
  refine ⟨2464370946223773370000955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1642913964149182246667303 2464370946223773370000955)
  ·
    refine ⟨3696556419335660055001433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2464370946223773370000955 3696556419335660055001433)
    ·
      refine ⟨2772417314501745041251075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3696556419335660055001433 2772417314501745041251075)
      ·
        refine ⟨4158625971752617561876613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2772417314501745041251075 4158625971752617561876613)
        ·
          refine ⟨779742369703615792851865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4158625971752617561876613 779742369703615792851865)
          ·
            refine ⟨584806777277711844638899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 779742369703615792851865 584806777277711844638899)
            ·
              refine ⟨877210165916567766958349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 584806777277711844638899 877210165916567766958349)
              ·
                refine ⟨328953812218712912609381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 877210165916567766958349 328953812218712912609381)
                ·
                  refine ⟨61678839791008671114259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 328953812218712912609381 61678839791008671114259)
                  ·
                    refine ⟨92518259686513006671389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61678839791008671114259 92518259686513006671389)
                    ·
                      refine ⟨34694347382442377501771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 92518259686513006671389 34694347382442377501771)
                      ·
                        rfl

theorem cell23_67567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 4, 1, 3].length) (baseStart_67567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67567 prefixEnd_67567 := by exact prefixLift 67567
  have htrace : WordTrace (prefixWord ++ tailWord_67567) baseStart_67567 baseEnd_67567 := by
    simpa [prefixWord, tailWord_67567, baseEnd_67567] using wordTrace_append hprefix tailTrace_67567
  have hstable : (prefixWord ++ tailWord_67567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67567).length < 2 ^ (prefixWord ++ tailWord_67567).sum := by decide
  have hdescent : baseEnd_67567 < baseStart_67567 := by decide
  rcases family_descends (prefixWord ++ tailWord_67567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67588 : List Nat := [2, 3, 2, 4, 1, 2, 1, 2, 1, 2, 3]
def baseStart_67588 : Nat := 118140960795 + 67588 * 2 ^ 59
def prefixEnd_67588 : Nat := 4983230072969 + 3 ^ 40 * 67588 * 2
def baseEnd_67588 : Nat := 34705130476186795339175

theorem tailTrace_67588 : CollatzResearch.WordTrace tailWord_67588 prefixEnd_67588 34705130476186795339175 := by
  unfold tailWord_67588
  simp only [CollatzResearch.WordTrace]
  refine ⟨1232568439573846978257709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1643424586098462637676945 1232568439573846978257709)
  ·
    refine ⟨462213164840192616846641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1232568439573846978257709 462213164840192616846641)
    ·
      refine ⟨346659873630144462634981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 462213164840192616846641 346659873630144462634981)
      ·
        refine ⟨64998726305652086744059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 346659873630144462634981 64998726305652086744059)
        ·
          refine ⟨97498089458478130116089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64998726305652086744059 97498089458478130116089)
          ·
            refine ⟨73123567093858597587067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97498089458478130116089 73123567093858597587067)
            ·
              refine ⟨109685350640787896380601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73123567093858597587067 109685350640787896380601)
              ·
                refine ⟨82264012980590922285451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109685350640787896380601 82264012980590922285451)
                ·
                  refine ⟨123396019470886383428177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82264012980590922285451 123396019470886383428177)
                  ·
                    refine ⟨92547014603164787571133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 123396019470886383428177 92547014603164787571133)
                    ·
                      refine ⟨34705130476186795339175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 92547014603164787571133 34705130476186795339175)
                      ·
                        rfl

theorem cell23_67588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_67588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67588 prefixEnd_67588 := by exact prefixLift 67588
  have htrace : WordTrace (prefixWord ++ tailWord_67588) baseStart_67588 baseEnd_67588 := by
    simpa [prefixWord, tailWord_67588, baseEnd_67588] using wordTrace_append hprefix tailTrace_67588
  have hstable : (prefixWord ++ tailWord_67588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67588).length < 2 ^ (prefixWord ++ tailWord_67588).sum := by decide
  have hdescent : baseEnd_67588 < baseStart_67588 := by decide
  rcases family_descends (prefixWord ++ tailWord_67588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67641 : List Nat := [1, 2, 1, 5, 3, 1, 2, 1, 1, 4, 2]
def baseStart_67641 : Nat := 118140960795 + 67641 * 2 ^ 59
def prefixEnd_67641 : Nat := 4983230072969 + 3 ^ 40 * 67641 * 2
def baseEnd_67641 : Nat := 34732344950875087976431

theorem tailTrace_67641 : CollatzResearch.WordTrace tailWord_67641 prefixEnd_67641 34732344950875087976431 := by
  unfold tailWord_67641
  simp only [CollatzResearch.WordTrace]
  refine ⟨2467069947955684008194777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1644713298637122672129851 2467069947955684008194777)
  ·
    refine ⟨1850302460966763006146083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2467069947955684008194777 1850302460966763006146083)
    ·
      refine ⟨2775453691450144509219125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1850302460966763006146083 2775453691450144509219125)
      ·
        refine ⟨260198783573451047739293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2775453691450144509219125 260198783573451047739293)
        ·
          refine ⟨97574543840044142902235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 260198783573451047739293 97574543840044142902235)
          ·
            refine ⟨146361815760066214353353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97574543840044142902235 146361815760066214353353)
            ·
              refine ⟨109771361820049660765015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146361815760066214353353 109771361820049660765015)
              ·
                refine ⟨164657042730074491147523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109771361820049660765015 164657042730074491147523)
                ·
                  refine ⟨246985564095111736721285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 164657042730074491147523 246985564095111736721285)
                  ·
                    refine ⟨46309793267833450635241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 246985564095111736721285 46309793267833450635241)
                    ·
                      refine ⟨34732344950875087976431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 46309793267833450635241 34732344950875087976431)
                      ·
                        rfl

theorem cell23_67641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_67641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67641 prefixEnd_67641 := by exact prefixLift 67641
  have htrace : WordTrace (prefixWord ++ tailWord_67641) baseStart_67641 baseEnd_67641 := by
    simpa [prefixWord, tailWord_67641, baseEnd_67641] using wordTrace_append hprefix tailTrace_67641
  have hstable : (prefixWord ++ tailWord_67641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67641).length < 2 ^ (prefixWord ++ tailWord_67641).sum := by decide
  have hdescent : baseEnd_67641 < baseStart_67641 := by decide
  rcases family_descends (prefixWord ++ tailWord_67641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67654 : List Nat := [6, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_67654 : Nat := 118140960795 + 67654 * 2 ^ 59
def prefixEnd_67654 : Nat := 4983230072969 + 3 ^ 40 * 67654 * 2
def baseEnd_67654 : Nat := 34739020199383537113871

theorem tailTrace_67654 : CollatzResearch.WordTrace tailWord_67654 prefixEnd_67654 34739020199383537113871 := by
  unfold tailWord_67654
  simp only [CollatzResearch.WordTrace]
  refine ⟨77110753028393350888063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1645029397939058152278677 77110753028393350888063)
  ·
    refine ⟨115666129542590026332095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77110753028393350888063 115666129542590026332095)
    ·
      refine ⟨173499194313885039498143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115666129542590026332095 173499194313885039498143)
      ·
        refine ⟨260248791470827559247215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173499194313885039498143 260248791470827559247215)
        ·
          refine ⟨390373187206241338870823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260248791470827559247215 390373187206241338870823)
          ·
            refine ⟨585559780809362008306235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 390373187206241338870823 585559780809362008306235)
            ·
              refine ⟨878339671214043012459353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 585559780809362008306235 878339671214043012459353)
              ·
                refine ⟨658754753410532259344515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 878339671214043012459353 658754753410532259344515)
                ·
                  refine ⟨988132130115798389016773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 658754753410532259344515 988132130115798389016773)
                  ·
                    refine ⟨185274774396712197940645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 988132130115798389016773 185274774396712197940645)
                    ·
                      refine ⟨34739020199383537113871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 185274774396712197940645 34739020199383537113871)
                      ·
                        rfl

theorem cell23_67654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_67654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67654 prefixEnd_67654 := by exact prefixLift 67654
  have htrace : WordTrace (prefixWord ++ tailWord_67654) baseStart_67654 baseEnd_67654 := by
    simpa [prefixWord, tailWord_67654, baseEnd_67654] using wordTrace_append hprefix tailTrace_67654
  have hstable : (prefixWord ++ tailWord_67654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67654).length < 2 ^ (prefixWord ++ tailWord_67654).sum := by decide
  have hdescent : baseEnd_67654 < baseStart_67654 := by decide
  rcases family_descends (prefixWord ++ tailWord_67654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67741 : List Nat := [1, 4, 2, 1, 1, 5, 1, 1, 3, 4]
def baseStart_67741 : Nat := 118140960795 + 67741 * 2 ^ 59
def prefixEnd_67741 : Nat := 4983230072969 + 3 ^ 40 * 67741 * 2
def baseEnd_67741 : Nat := 11594564338774898908657

theorem tailTrace_67741 : CollatzResearch.WordTrace tailWord_67741 prefixEnd_67741 11594564338774898908657 := by
  unfold tailWord_67741
  simp only [CollatzResearch.WordTrace]
  refine ⟨2470717247593401086835077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1647144831728934057890051 2470717247593401086835077)
  ·
    refine ⟨463259483923762703781577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2470717247593401086835077 463259483923762703781577)
    ·
      refine ⟨347444612942822027836183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 463259483923762703781577 347444612942822027836183)
      ·
        refine ⟨521166919414233041754275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347444612942822027836183 521166919414233041754275)
        ·
          refine ⟨781750379121349562631413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 521166919414233041754275 781750379121349562631413)
          ·
            refine ⟨73289098042626521496695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 781750379121349562631413 73289098042626521496695)
            ·
              refine ⟨109933647063939782245043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73289098042626521496695 109933647063939782245043)
              ·
                refine ⟨164900470595909673367565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109933647063939782245043 164900470595909673367565)
                ·
                  refine ⟨61837676473466127512837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 164900470595909673367565 61837676473466127512837)
                  ·
                    refine ⟨11594564338774898908657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61837676473466127512837 11594564338774898908657)
                    ·
                      rfl

theorem cell23_67741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_67741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67741 prefixEnd_67741 := by exact prefixLift 67741
  have htrace : WordTrace (prefixWord ++ tailWord_67741) baseStart_67741 baseEnd_67741 := by
    simpa [prefixWord, tailWord_67741, baseEnd_67741] using wordTrace_append hprefix tailTrace_67741
  have hstable : (prefixWord ++ tailWord_67741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67741).length < 2 ^ (prefixWord ++ tailWord_67741).sum := by decide
  have hdescent : baseEnd_67741 < baseStart_67741 := by decide
  rcases family_descends (prefixWord ++ tailWord_67741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67807 : List Nat := [1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 5]
def baseStart_67807 : Nat := 118140960795 + 67807 * 2 ^ 59
def prefixEnd_67807 : Nat := 4983230072969 + 3 ^ 40 * 67807 * 2
def baseEnd_67807 : Nat := 34817582739521438500667

theorem tailTrace_67807 : CollatzResearch.WordTrace tailWord_67807 prefixEnd_67807 34817582739521438500667 := by
  unfold tailWord_67807
  simp only [CollatzResearch.WordTrace]
  refine ⟨2473124465354294358737675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1648749643569529572491783 2473124465354294358737675)
  ·
    refine ⟨3709686698031441538106513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2473124465354294358737675 3709686698031441538106513)
    ·
      refine ⟨2782265023523581153579885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3709686698031441538106513 2782265023523581153579885)
      ·
        refine ⟨1043349383821342932592457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2782265023523581153579885 1043349383821342932592457)
        ·
          refine ⟨782512037866007199444343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1043349383821342932592457 782512037866007199444343)
          ·
            refine ⟨1173768056799010799166515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 782512037866007199444343 1173768056799010799166515)
            ·
              refine ⟨1760652085198516198749773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1173768056799010799166515 1760652085198516198749773)
              ·
                refine ⟨660244531949443574531165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1760652085198516198749773 660244531949443574531165)
                ·
                  refine ⟨247591699481041340449187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 660244531949443574531165 247591699481041340449187)
                  ·
                    refine ⟨371387549221562010673781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 247591699481041340449187 371387549221562010673781)
                    ·
                      refine ⟨34817582739521438500667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 371387549221562010673781 34817582739521438500667)
                      ·
                        rfl

theorem cell23_67807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_67807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67807 prefixEnd_67807 := by exact prefixLift 67807
  have htrace : WordTrace (prefixWord ++ tailWord_67807) baseStart_67807 baseEnd_67807 := by
    simpa [prefixWord, tailWord_67807, baseEnd_67807] using wordTrace_append hprefix tailTrace_67807
  have hstable : (prefixWord ++ tailWord_67807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67807).length < 2 ^ (prefixWord ++ tailWord_67807).sum := by decide
  have hdescent : baseEnd_67807 < baseStart_67807 := by decide
  rcases family_descends (prefixWord ++ tailWord_67807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67817 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 5, 2, 4]
def baseStart_67817 : Nat := 118140960795 + 67817 * 2 ^ 59
def prefixEnd_67817 : Nat := 4983230072969 + 3 ^ 40 * 67817 * 2
def baseEnd_67817 : Nat := 34822717546066399375621

theorem tailTrace_67817 : CollatzResearch.WordTrace tailWord_67817 prefixEnd_67817 34822717546066399375621 := by
  unfold tailWord_67817
  simp only [CollatzResearch.WordTrace]
  refine ⟨2473489195318066066601705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1648992796878710711067803 2473489195318066066601705)
  ·
    refine ⟨1855116896488549549951279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2473489195318066066601705 1855116896488549549951279)
    ·
      refine ⟨2782675344732824324926919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1855116896488549549951279 2782675344732824324926919)
      ·
        refine ⟨4174013017099236487390379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2782675344732824324926919 4174013017099236487390379)
        ·
          refine ⟨6261019525648854731085569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4174013017099236487390379 6261019525648854731085569)
          ·
            refine ⟨4695764644236641048314177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6261019525648854731085569 4695764644236641048314177)
            ·
              refine ⟨3521823483177480786235633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4695764644236641048314177 3521823483177480786235633)
              ·
                refine ⟨2641367612383110589676725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3521823483177480786235633 2641367612383110589676725)
                ·
                  refine ⟨247628213660916617782193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2641367612383110589676725 247628213660916617782193)
                  ·
                    refine ⟨185721160245687463336645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 247628213660916617782193 185721160245687463336645)
                    ·
                      refine ⟨34822717546066399375621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 185721160245687463336645 34822717546066399375621)
                      ·
                        rfl

theorem cell23_67817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 2, 4].length) (baseStart_67817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67817 prefixEnd_67817 := by exact prefixLift 67817
  have htrace : WordTrace (prefixWord ++ tailWord_67817) baseStart_67817 baseEnd_67817 := by
    simpa [prefixWord, tailWord_67817, baseEnd_67817] using wordTrace_append hprefix tailTrace_67817
  have hstable : (prefixWord ++ tailWord_67817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67817).length < 2 ^ (prefixWord ++ tailWord_67817).sum := by decide
  have hdescent : baseEnd_67817 < baseStart_67817 := by decide
  rcases family_descends (prefixWord ++ tailWord_67817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67834 : List Nat := [3, 1, 1, 1, 1, 5, 2, 2, 1, 2, 4]
def baseStart_67834 : Nat := 118140960795 + 67834 * 2 ^ 59
def prefixEnd_67834 : Nat := 4983230072969 + 3 ^ 40 * 67834 * 2
def baseEnd_67834 : Nat := 34831446717192832863043

theorem tailTrace_67834 : CollatzResearch.WordTrace tailWord_67834 prefixEnd_67834 34831446717192832863043 := by
  unfold tailWord_67834
  simp only [CollatzResearch.WordTrace]
  refine ⟨618527309064119492492639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1649406157504318646647037 618527309064119492492639)
  ·
    refine ⟨927790963596179238738959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 618527309064119492492639 927790963596179238738959)
    ·
      refine ⟨1391686445394268858108439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 927790963596179238738959 1391686445394268858108439)
      ·
        refine ⟨2087529668091403287162659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1391686445394268858108439 2087529668091403287162659)
        ·
          refine ⟨3131294502137104930743989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2087529668091403287162659 3131294502137104930743989)
          ·
            refine ⟨293558859575353587257249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3131294502137104930743989 293558859575353587257249)
            ·
              refine ⟨220169144681515190442937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 293558859575353587257249 220169144681515190442937)
              ·
                refine ⟨165126858511136392832203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 220169144681515190442937 165126858511136392832203)
                ·
                  refine ⟨247690287766704589248305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 165126858511136392832203 247690287766704589248305)
                  ·
                    refine ⟨185767715825028441936229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 247690287766704589248305 185767715825028441936229)
                    ·
                      refine ⟨34831446717192832863043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 185767715825028441936229 34831446717192832863043)
                      ·
                        rfl

theorem cell23_67834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 1, 2, 4].length) (baseStart_67834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67834 prefixEnd_67834 := by exact prefixLift 67834
  have htrace : WordTrace (prefixWord ++ tailWord_67834) baseStart_67834 baseEnd_67834 := by
    simpa [prefixWord, tailWord_67834, baseEnd_67834] using wordTrace_append hprefix tailTrace_67834
  have hstable : (prefixWord ++ tailWord_67834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67834).length < 2 ^ (prefixWord ++ tailWord_67834).sum := by decide
  have hdescent : baseEnd_67834 < baseStart_67834 := by decide
  rcases family_descends (prefixWord ++ tailWord_67834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67838 : List Nat := [4, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2]
def baseStart_67838 : Nat := 118140960795 + 67838 * 2 ^ 59
def prefixEnd_67838 : Nat := 4983230072969 + 3 ^ 40 * 67838 * 2
def baseEnd_67838 : Nat := 34833500639810817213025

theorem tailTrace_67838 : CollatzResearch.WordTrace tailWord_67838 prefixEnd_67838 34833500639810817213025 := by
  unfold tailWord_67838
  simp only [CollatzResearch.WordTrace]
  refine ⟨309281891030248331639521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1649503418827991102077445 309281891030248331639521)
  ·
    refine ⟨231961418272686248729641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 309281891030248331639521 231961418272686248729641)
    ·
      refine ⟨173971063704514686547231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231961418272686248729641 173971063704514686547231)
      ·
        refine ⟨260956595556772029820847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173971063704514686547231 260956595556772029820847)
        ·
          refine ⟨391434893335158044731271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260956595556772029820847 391434893335158044731271)
          ·
            refine ⟨587152340002737067096907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391434893335158044731271 587152340002737067096907)
            ·
              refine ⟨880728510004105600645361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 587152340002737067096907 880728510004105600645361)
              ·
                refine ⟨660546382503079200484021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 880728510004105600645361 660546382503079200484021)
                ·
                  refine ⟨61926223359663675045377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 660546382503079200484021 61926223359663675045377)
                  ·
                    refine ⟨46444667519747756284033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61926223359663675045377 46444667519747756284033)
                    ·
                      refine ⟨34833500639810817213025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 46444667519747756284033 34833500639810817213025)
                      ·
                        rfl

theorem cell23_67838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_67838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67838 prefixEnd_67838 := by exact prefixLift 67838
  have htrace : WordTrace (prefixWord ++ tailWord_67838) baseStart_67838 baseEnd_67838 := by
    simpa [prefixWord, tailWord_67838, baseEnd_67838] using wordTrace_append hprefix tailTrace_67838
  have hstable : (prefixWord ++ tailWord_67838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67838).length < 2 ^ (prefixWord ++ tailWord_67838).sum := by decide
  have hdescent : baseEnd_67838 < baseStart_67838 := by decide
  rcases family_descends (prefixWord ++ tailWord_67838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67841 : List Nat := [1, 2, 4, 1, 1, 2, 3, 3, 1, 2, 3]
def baseStart_67841 : Nat := 118140960795 + 67841 * 2 ^ 59
def prefixEnd_67841 : Nat := 4983230072969 + 3 ^ 40 * 67841 * 2
def baseEnd_67841 : Nat := 34835041081774305475511

theorem tailTrace_67841 : CollatzResearch.WordTrace tailWord_67841 prefixEnd_67841 34835041081774305475511 := by
  unfold tailWord_67841
  simp only [CollatzResearch.WordTrace]
  refine ⟨2474364547231118165475377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1649576364820745443650251 2474364547231118165475377)
  ·
    refine ⟨1855773410423338624106533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2474364547231118165475377 1855773410423338624106533)
    ·
      refine ⟨347957514454375992019975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1855773410423338624106533 347957514454375992019975)
      ·
        refine ⟨521936271681563988029963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347957514454375992019975 521936271681563988029963)
        ·
          refine ⟨782904407522345982044945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 521936271681563988029963 782904407522345982044945)
          ·
            refine ⟨587178305641759486533709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 782904407522345982044945 587178305641759486533709)
            ·
              refine ⟨220191864615659807450141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 587178305641759486533709 220191864615659807450141)
              ·
                refine ⟨82571949230872427793803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 220191864615659807450141 82571949230872427793803)
                ·
                  refine ⟨123857923846308641690705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82571949230872427793803 123857923846308641690705)
                  ·
                    refine ⟨92893442884731481268029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 123857923846308641690705 92893442884731481268029)
                    ·
                      refine ⟨34835041081774305475511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 92893442884731481268029 34835041081774305475511)
                      ·
                        rfl

theorem cell23_67841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_67841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67841 prefixEnd_67841 := by exact prefixLift 67841
  have htrace : WordTrace (prefixWord ++ tailWord_67841) baseStart_67841 baseEnd_67841 := by
    simpa [prefixWord, tailWord_67841, baseEnd_67841] using wordTrace_append hprefix tailTrace_67841
  have hstable : (prefixWord ++ tailWord_67841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67841).length < 2 ^ (prefixWord ++ tailWord_67841).sum := by decide
  have hdescent : baseEnd_67841 < baseStart_67841 := by decide
  rcases family_descends (prefixWord ++ tailWord_67841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67844 : List Nat := [2, 3, 2, 2, 3, 1, 10]
def baseStart_67844 : Nat := 118140960795 + 67844 * 2 ^ 59
def prefixEnd_67844 : Nat := 4983230072969 + 3 ^ 40 * 67844 * 2
def baseEnd_67844 : Nat := 430081253379478935037

theorem tailTrace_67844 : CollatzResearch.WordTrace tailWord_67844 prefixEnd_67844 430081253379478935037 := by
  unfold tailWord_67844
  simp only [CollatzResearch.WordTrace]
  refine ⟨1237236983110124838917293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1649649310813499785223057 1237236983110124838917293)
  ·
    refine ⟨463963868666296814593985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1237236983110124838917293 463963868666296814593985)
    ·
      refine ⟨347972901499722610945489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 463963868666296814593985 347972901499722610945489)
      ·
        refine ⟨260979676124791958209117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 347972901499722610945489 260979676124791958209117)
        ·
          refine ⟨97867378546796984328419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 260979676124791958209117 97867378546796984328419)
          ·
            refine ⟨146801067820195476492629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97867378546796984328419 146801067820195476492629)
            ·
              refine ⟨430081253379478935037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 146801067820195476492629 430081253379478935037)
              ·
                rfl

theorem cell23_67844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 10].length) (baseStart_67844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67844 prefixEnd_67844 := by exact prefixLift 67844
  have htrace : WordTrace (prefixWord ++ tailWord_67844) baseStart_67844 baseEnd_67844 := by
    simpa [prefixWord, tailWord_67844, baseEnd_67844] using wordTrace_append hprefix tailTrace_67844
  have hstable : (prefixWord ++ tailWord_67844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67844).length < 2 ^ (prefixWord ++ tailWord_67844).sum := by decide
  have hdescent : baseEnd_67844 < baseStart_67844 := by decide
  rcases family_descends (prefixWord ++ tailWord_67844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67848 : List Nat := [2, 1, 3, 2, 3, 3, 1, 2, 2, 4]
def baseStart_67848 : Nat := 118140960795 + 67848 * 2 ^ 59
def prefixEnd_67848 : Nat := 4983230072969 + 3 ^ 40 * 67848 * 2
def baseEnd_67848 : Nat := 11612878482118592695993

theorem tailTrace_67848 : CollatzResearch.WordTrace tailWord_67848 prefixEnd_67848 11612878482118592695993 := by
  unfold tailWord_67848
  simp only [CollatzResearch.WordTrace]
  refine ⟨1237309929102879180490099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1649746572137172240653465 1237309929102879180490099)
  ·
    refine ⟨1855964893654318770735149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1237309929102879180490099 1855964893654318770735149)
    ·
      refine ⟨695986835120369539025681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1855964893654318770735149 695986835120369539025681)
      ·
        refine ⟨521990126340277154269261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 695986835120369539025681 521990126340277154269261)
        ·
          refine ⟨195746297377603932850973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 521990126340277154269261 195746297377603932850973)
          ·
            refine ⟨73404861516601474819115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 195746297377603932850973 73404861516601474819115)
            ·
              refine ⟨110107292274902212228673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73404861516601474819115 110107292274902212228673)
              ·
                refine ⟨82580469206176659171505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110107292274902212228673 82580469206176659171505)
                ·
                  refine ⟨61935351904632494378629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82580469206176659171505 61935351904632494378629)
                  ·
                    refine ⟨11612878482118592695993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61935351904632494378629 11612878482118592695993)
                    ·
                      rfl

theorem cell23_67848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_67848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67848 prefixEnd_67848 := by exact prefixLift 67848
  have htrace : WordTrace (prefixWord ++ tailWord_67848) baseStart_67848 baseEnd_67848 := by
    simpa [prefixWord, tailWord_67848, baseEnd_67848] using wordTrace_append hprefix tailTrace_67848
  have hstable : (prefixWord ++ tailWord_67848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67848).length < 2 ^ (prefixWord ++ tailWord_67848).sum := by decide
  have hdescent : baseEnd_67848 < baseStart_67848 := by decide
  rcases family_descends (prefixWord ++ tailWord_67848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67871 : List Nat := [1, 1, 2, 4, 3, 1, 3, 1, 1, 3, 3]
def baseStart_67871 : Nat := 118140960795 + 67871 * 2 ^ 59
def prefixEnd_67871 : Nat := 4983230072969 + 3 ^ 40 * 67871 * 2
def baseEnd_67871 : Nat := 34850445501409188100373

theorem tailTrace_67871 : CollatzResearch.WordTrace tailWord_67871 prefixEnd_67871 34850445501409188100373 := by
  unfold tailWord_67871
  simp only [CollatzResearch.WordTrace]
  refine ⟨2475458737122433289067467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1650305824748288859378311 2475458737122433289067467)
  ·
    refine ⟨3713188105683649933601201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2475458737122433289067467 3713188105683649933601201)
    ·
      refine ⟨2784891079262737450200901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3713188105683649933601201 2784891079262737450200901)
      ·
        refine ⟨522167077361763271912669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2784891079262737450200901 522167077361763271912669)
        ·
          refine ⟨195812654010661226967251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 522167077361763271912669 195812654010661226967251)
          ·
            refine ⟨293718981015991840450877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195812654010661226967251 293718981015991840450877)
            ·
              refine ⟨110144617880996940169079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 293718981015991840450877 110144617880996940169079)
              ·
                refine ⟨165216926821495410253619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110144617880996940169079 165216926821495410253619)
                ·
                  refine ⟨247825390232243115380429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 165216926821495410253619 247825390232243115380429)
                  ·
                    refine ⟨92934521337091168267661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 247825390232243115380429 92934521337091168267661)
                    ·
                      refine ⟨34850445501409188100373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 92934521337091168267661 34850445501409188100373)
                      ·
                        rfl

theorem cell23_67871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_67871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67871 prefixEnd_67871 := by exact prefixLift 67871
  have htrace : WordTrace (prefixWord ++ tailWord_67871) baseStart_67871 baseEnd_67871 := by
    simpa [prefixWord, tailWord_67871, baseEnd_67871] using wordTrace_append hprefix tailTrace_67871
  have hstable : (prefixWord ++ tailWord_67871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67871).length < 2 ^ (prefixWord ++ tailWord_67871).sum := by decide
  have hdescent : baseEnd_67871 < baseStart_67871 := by decide
  rcases family_descends (prefixWord ++ tailWord_67871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67887 : List Nat := [1, 1, 2, 1, 2, 1, 4, 2, 1, 8]
def baseStart_67887 : Nat := 118140960795 + 67887 * 2 ^ 59
def prefixEnd_67887 : Nat := 4983230072969 + 3 ^ 40 * 67887 * 2
def baseEnd_67887 : Nat := 11619553730627041833433

theorem tailTrace_67887 : CollatzResearch.WordTrace tailWord_67887 prefixEnd_67887 11619553730627041833433 := by
  unfold tailWord_67887
  simp only [CollatzResearch.WordTrace]
  refine ⟨2476042305064468021649915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1650694870042978681099943 2476042305064468021649915)
  ·
    refine ⟨3714063457596702032474873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2476042305064468021649915 3714063457596702032474873)
    ·
      refine ⟨2785547593197526524356155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3714063457596702032474873 2785547593197526524356155)
      ·
        refine ⟨4178321389796289786534233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2785547593197526524356155 4178321389796289786534233)
        ·
          refine ⟨3133741042347217339900675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4178321389796289786534233 3133741042347217339900675)
          ·
            refine ⟨4700611563520826009851013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3133741042347217339900675 4700611563520826009851013)
            ·
              refine ⟨881364668160154876847065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4700611563520826009851013 881364668160154876847065)
              ·
                refine ⟨661023501120116157635299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 881364668160154876847065 661023501120116157635299)
                ·
                  refine ⟨991535251680174236452949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 661023501120116157635299 991535251680174236452949)
                  ·
                    refine ⟨11619553730627041833433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 991535251680174236452949 11619553730627041833433)
                    ·
                      rfl

theorem cell23_67887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 8].length) (baseStart_67887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67887 prefixEnd_67887 := by exact prefixLift 67887
  have htrace : WordTrace (prefixWord ++ tailWord_67887) baseStart_67887 baseEnd_67887 := by
    simpa [prefixWord, tailWord_67887, baseEnd_67887] using wordTrace_append hprefix tailTrace_67887
  have hstable : (prefixWord ++ tailWord_67887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67887).length < 2 ^ (prefixWord ++ tailWord_67887).sum := by decide
  have hdescent : baseEnd_67887 < baseStart_67887 := by decide
  rcases family_descends (prefixWord ++ tailWord_67887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67889 : List Nat := [1, 2, 2, 3, 5, 1, 1, 3, 1, 2, 2]
def baseStart_67889 : Nat := 118140960795 + 67889 * 2 ^ 59
def prefixEnd_67889 : Nat := 4983230072969 + 3 ^ 40 * 67889 * 2
def baseEnd_67889 : Nat := 34859688153190117675291

theorem tailTrace_67889 : CollatzResearch.WordTrace tailWord_67889 prefixEnd_67889 34859688153190117675291 := by
  unfold tailWord_67889
  simp only [CollatzResearch.WordTrace]
  refine ⟨2476115251057222363222721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1650743500704814908815147 2476115251057222363222721)
  ·
    refine ⟨1857086438292916772417041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2476115251057222363222721 1857086438292916772417041)
    ·
      refine ⟨1392814828719687579312781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1857086438292916772417041 1392814828719687579312781)
      ·
        refine ⟨522305560769882842242293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1392814828719687579312781 522305560769882842242293)
        ·
          refine ⟨48966146322176516460215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 522305560769882842242293 48966146322176516460215)
          ·
            refine ⟨73449219483264774690323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48966146322176516460215 73449219483264774690323)
            ·
              refine ⟨110173829224897162035485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73449219483264774690323 110173829224897162035485)
              ·
                refine ⟨41315185959336435763307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110173829224897162035485 41315185959336435763307)
                ·
                  refine ⟨61972778939004653644961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41315185959336435763307 61972778939004653644961)
                  ·
                    refine ⟨46479584204253490233721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61972778939004653644961 46479584204253490233721)
                    ·
                      refine ⟨34859688153190117675291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 46479584204253490233721 34859688153190117675291)
                      ·
                        rfl

theorem cell23_67889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_67889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67889 prefixEnd_67889 := by exact prefixLift 67889
  have htrace : WordTrace (prefixWord ++ tailWord_67889) baseStart_67889 baseEnd_67889 := by
    simpa [prefixWord, tailWord_67889, baseEnd_67889] using wordTrace_append hprefix tailTrace_67889
  have hstable : (prefixWord ++ tailWord_67889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67889).length < 2 ^ (prefixWord ++ tailWord_67889).sum := by decide
  have hdescent : baseEnd_67889 < baseStart_67889 := by decide
  rcases family_descends (prefixWord ++ tailWord_67889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67898 : List Nat := [3, 1, 1, 1, 4, 2, 2, 3, 1, 3, 2]
def baseStart_67898 : Nat := 118140960795 + 67898 * 2 ^ 59
def prefixEnd_67898 : Nat := 4983230072969 + 3 ^ 40 * 67898 * 2
def baseEnd_67898 : Nat := 34864309479080582462749

theorem tailTrace_67898 : CollatzResearch.WordTrace tailWord_67898 prefixEnd_67898 34864309479080582462749 := by
  unfold tailWord_67898
  simp only [CollatzResearch.WordTrace]
  refine ⟨619110877006154225075087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1650962338683077933533565 619110877006154225075087)
  ·
    refine ⟨928666315509231337612631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 619110877006154225075087 928666315509231337612631)
    ·
      refine ⟨1392999473263847006418947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 928666315509231337612631 1392999473263847006418947)
      ·
        refine ⟨2089499209895770509628421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1392999473263847006418947 2089499209895770509628421)
        ·
          refine ⟨391781101855456970555329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2089499209895770509628421 391781101855456970555329)
          ·
            refine ⟨293835826391592727916497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 391781101855456970555329 293835826391592727916497)
            ·
              refine ⟨220376869793694545937373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 293835826391592727916497 220376869793694545937373)
              ·
                refine ⟨82641326172635454726515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 220376869793694545937373 82641326172635454726515)
                ·
                  refine ⟨123961989258953182089773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82641326172635454726515 123961989258953182089773)
                  ·
                    refine ⟨46485745972107443283665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 123961989258953182089773 46485745972107443283665)
                    ·
                      refine ⟨34864309479080582462749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 46485745972107443283665 34864309479080582462749)
                      ·
                        rfl

theorem cell23_67898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 1, 3, 2].length) (baseStart_67898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67898 prefixEnd_67898 := by exact prefixLift 67898
  have htrace : WordTrace (prefixWord ++ tailWord_67898) baseStart_67898 baseEnd_67898 := by
    simpa [prefixWord, tailWord_67898, baseEnd_67898] using wordTrace_append hprefix tailTrace_67898
  have hstable : (prefixWord ++ tailWord_67898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67898).length < 2 ^ (prefixWord ++ tailWord_67898).sum := by decide
  have hdescent : baseEnd_67898 < baseStart_67898 := by decide
  rcases family_descends (prefixWord ++ tailWord_67898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67964 : List Nat := [2, 2, 2, 1, 1, 1, 2, 3, 4, 5]
def baseStart_67964 : Nat := 118140960795 + 67964 * 2 ^ 59
def prefixEnd_67964 : Nat := 4983230072969 + 3 ^ 40 * 67964 * 2
def baseEnd_67964 : Nat := 11632733067425774745815

theorem tailTrace_67964 : CollatzResearch.WordTrace tailWord_67964 prefixEnd_67964 11632733067425774745815 := by
  unfold tailWord_67964
  simp only [CollatzResearch.WordTrace]
  refine ⟨1239425362892755086101473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1652567150523673448135297 1239425362892755086101473)
  ·
    refine ⟨929569022169566314576105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1239425362892755086101473 929569022169566314576105)
    ·
      refine ⟨697176766627174735932079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 929569022169566314576105 697176766627174735932079)
      ·
        refine ⟨1045765149940762103898119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 697176766627174735932079 1045765149940762103898119)
        ·
          refine ⟨1568647724911143155847179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1045765149940762103898119 1568647724911143155847179)
          ·
            refine ⟨2352971587366714733770769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1568647724911143155847179 2352971587366714733770769)
            ·
              refine ⟨1764728690525036050328077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2352971587366714733770769 1764728690525036050328077)
              ·
                refine ⟨661773258946888518873029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1764728690525036050328077 661773258946888518873029)
                ·
                  refine ⟨124082486052541597288693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 661773258946888518873029 124082486052541597288693)
                  ·
                    refine ⟨11632733067425774745815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 124082486052541597288693 11632733067425774745815)
                    ·
                      rfl

theorem cell23_67964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_67964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67964 prefixEnd_67964 := by exact prefixLift 67964
  have htrace : WordTrace (prefixWord ++ tailWord_67964) baseStart_67964 baseEnd_67964 := by
    simpa [prefixWord, tailWord_67964, baseEnd_67964] using wordTrace_append hprefix tailTrace_67964
  have hstable : (prefixWord ++ tailWord_67964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67964).length < 2 ^ (prefixWord ++ tailWord_67964).sum := by decide
  have hdescent : baseEnd_67964 < baseStart_67964 := by decide
  rcases family_descends (prefixWord ++ tailWord_67964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67998 : List Nat := [4, 3, 1, 2, 1, 2, 1, 1, 1, 7]
def baseStart_67998 : Nat := 118140960795 + 67998 * 2 ^ 59
def prefixEnd_67998 : Nat := 4983230072969 + 3 ^ 40 * 67998 * 2
def baseEnd_67998 : Nat := 11638552514843397070763

theorem tailTrace_67998 : CollatzResearch.WordTrace tailWord_67998 prefixEnd_67998 11638552514843397070763 := by
  unfold tailWord_67998
  simp only [CollatzResearch.WordTrace]
  refine ⟨310011350957791747367581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1653393871774889319293765 310011350957791747367581)
  ·
    refine ⟨116254256609171905262843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 310011350957791747367581 116254256609171905262843)
    ·
      refine ⟨174381384913757857894265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116254256609171905262843 174381384913757857894265)
      ·
        refine ⟨130786038685318393420699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174381384913757857894265 130786038685318393420699)
        ·
          refine ⟨196179058027977590131049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130786038685318393420699 196179058027977590131049)
          ·
            refine ⟨147134293520983192598287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196179058027977590131049 147134293520983192598287)
            ·
              refine ⟨220701440281474788897431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147134293520983192598287 220701440281474788897431)
              ·
                refine ⟨331052160422212183346147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220701440281474788897431 331052160422212183346147)
                ·
                  refine ⟨496578240633318275019221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 331052160422212183346147 496578240633318275019221)
                  ·
                    refine ⟨11638552514843397070763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 496578240633318275019221 11638552514843397070763)
                    ·
                      rfl

theorem cell23_67998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_67998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_67998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_67998 prefixEnd_67998 := by exact prefixLift 67998
  have htrace : WordTrace (prefixWord ++ tailWord_67998) baseStart_67998 baseEnd_67998 := by
    simpa [prefixWord, tailWord_67998, baseEnd_67998] using wordTrace_append hprefix tailTrace_67998
  have hstable : (prefixWord ++ tailWord_67998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67998).length < 2 ^ (prefixWord ++ tailWord_67998).sum := by decide
  have hdescent : baseEnd_67998 < baseStart_67998 := by decide
  rcases family_descends (prefixWord ++ tailWord_67998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68028 : List Nat := [2, 2, 2, 4, 1, 1, 1, 3, 3, 4]
def baseStart_68028 : Nat := 118140960795 + 68028 * 2 ^ 59
def prefixEnd_68028 : Nat := 4983230072969 + 3 ^ 40 * 68028 * 2
def baseEnd_68028 : Nat := 11643687321388357945717

theorem tailTrace_68028 : CollatzResearch.WordTrace tailWord_68028 prefixEnd_68028 11643687321388357945717 := by
  unfold tailWord_68028
  simp only [CollatzResearch.WordTrace]
  refine ⟨1240592498776824551266369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1654123331702432735021825 1240592498776824551266369)
  ·
    refine ⟨930444374082618413449777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1240592498776824551266369 930444374082618413449777)
    ·
      refine ⟨697833280561963810087333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 930444374082618413449777 697833280561963810087333)
      ·
        refine ⟨130843740105368214391375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 697833280561963810087333 130843740105368214391375)
        ·
          refine ⟨196265610158052321587063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130843740105368214391375 196265610158052321587063)
          ·
            refine ⟨294398415237078482380595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196265610158052321587063 294398415237078482380595)
            ·
              refine ⟨441597622855617723570893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294398415237078482380595 441597622855617723570893)
              ·
                refine ⟨165599108570856646339085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 441597622855617723570893 165599108570856646339085)
                ·
                  refine ⟨62099665714071242377157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 165599108570856646339085 62099665714071242377157)
                  ·
                    refine ⟨11643687321388357945717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62099665714071242377157 11643687321388357945717)
                    ·
                      rfl

theorem cell23_68028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_68028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68028 prefixEnd_68028 := by exact prefixLift 68028
  have htrace : WordTrace (prefixWord ++ tailWord_68028) baseStart_68028 baseEnd_68028 := by
    simpa [prefixWord, tailWord_68028, baseEnd_68028] using wordTrace_append hprefix tailTrace_68028
  have hstable : (prefixWord ++ tailWord_68028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68028).length < 2 ^ (prefixWord ++ tailWord_68028).sum := by decide
  have hdescent : baseEnd_68028 < baseStart_68028 := by decide
  rcases family_descends (prefixWord ++ tailWord_68028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68108 : List Nat := [2, 2, 1, 2, 4, 2, 1, 1, 3, 1, 4]
def baseStart_68108 : Nat := 118140960795 + 68108 * 2 ^ 59
def prefixEnd_68108 : Nat := 4983230072969 + 3 ^ 40 * 68108 * 2
def baseEnd_68108 : Nat := 34972140416524760836783

theorem tailTrace_68108 : CollatzResearch.WordTrace tailWord_68108 prefixEnd_68108 34972140416524760836783 := by
  unfold tailWord_68108
  simp only [CollatzResearch.WordTrace]
  refine ⟨1242051418631911382722489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1656068558175881843629985 1242051418631911382722489)
  ·
    refine ⟨931538563973933537041867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1242051418631911382722489 931538563973933537041867)
    ·
      refine ⟨1397307845960900305562801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 931538563973933537041867 1397307845960900305562801)
      ·
        refine ⟨1047980884470675229172101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1397307845960900305562801 1047980884470675229172101)
        ·
          refine ⟨196496415838251605469769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1047980884470675229172101 196496415838251605469769)
          ·
            refine ⟨147372311878688704102327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196496415838251605469769 147372311878688704102327)
            ·
              refine ⟨221058467818033056153491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147372311878688704102327 221058467818033056153491)
              ·
                refine ⟨331587701727049584230237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221058467818033056153491 331587701727049584230237)
                ·
                  refine ⟨124345388147643594086339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 331587701727049584230237 124345388147643594086339)
                  ·
                    refine ⟨186518082221465391129509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 124345388147643594086339 186518082221465391129509)
                    ·
                      refine ⟨34972140416524760836783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 186518082221465391129509 34972140416524760836783)
                      ·
                        rfl

theorem cell23_68108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_68108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68108 prefixEnd_68108 := by exact prefixLift 68108
  have htrace : WordTrace (prefixWord ++ tailWord_68108) baseStart_68108 baseEnd_68108 := by
    simpa [prefixWord, tailWord_68108, baseEnd_68108] using wordTrace_append hprefix tailTrace_68108
  have hstable : (prefixWord ++ tailWord_68108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68108).length < 2 ^ (prefixWord ++ tailWord_68108).sum := by decide
  have hdescent : baseEnd_68108 < baseStart_68108 := by decide
  rcases family_descends (prefixWord ++ tailWord_68108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68121 : List Nat := [1, 2, 1, 2, 1, 1, 2, 6, 1, 2, 4]
def baseStart_68121 : Nat := 118140960795 + 68121 * 2 ^ 59
def prefixEnd_68121 : Nat := 4983230072969 + 3 ^ 40 * 68121 * 2
def baseEnd_68121 : Nat := 34978815665033209974223

theorem tailTrace_68121 : CollatzResearch.WordTrace tailWord_68121 prefixEnd_68121 34978815665033209974223 := by
  unfold tailWord_68121
  simp only [CollatzResearch.WordTrace]
  refine ⟨2484576986216725985668217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1656384657477817323778811 2484576986216725985668217)
  ·
    refine ⟨1863432739662544489251163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2484576986216725985668217 1863432739662544489251163)
    ·
      refine ⟨2795149109493816733876745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1863432739662544489251163 2795149109493816733876745)
      ·
        refine ⟨2096361832120362550407559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2795149109493816733876745 2096361832120362550407559)
        ·
          refine ⟨3144542748180543825611339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2096361832120362550407559 3144542748180543825611339)
          ·
            refine ⟨4716814122270815738417009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3144542748180543825611339 4716814122270815738417009)
            ·
              refine ⟨3537610591703111803812757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4716814122270815738417009 3537610591703111803812757)
              ·
                refine ⟨165825496486083365803723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3537610591703111803812757 165825496486083365803723)
                ·
                  refine ⟨248738244729125048705585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 165825496486083365803723 248738244729125048705585)
                  ·
                    refine ⟨186553683546843786529189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 248738244729125048705585 186553683546843786529189)
                    ·
                      refine ⟨34978815665033209974223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 186553683546843786529189 34978815665033209974223)
                      ·
                        rfl

theorem cell23_68121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 2, 4].length) (baseStart_68121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68121 prefixEnd_68121 := by exact prefixLift 68121
  have htrace : WordTrace (prefixWord ++ tailWord_68121) baseStart_68121 baseEnd_68121 := by
    simpa [prefixWord, tailWord_68121, baseEnd_68121] using wordTrace_append hprefix tailTrace_68121
  have hstable : (prefixWord ++ tailWord_68121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68121).length < 2 ^ (prefixWord ++ tailWord_68121).sum := by decide
  have hdescent : baseEnd_68121 < baseStart_68121 := by decide
  rcases family_descends (prefixWord ++ tailWord_68121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68136 : List Nat := [2, 1, 5, 2, 1, 3, 2, 2, 1, 1, 3]
def baseStart_68136 : Nat := 118140960795 + 68136 * 2 ^ 59
def prefixEnd_68136 : Nat := 4983230072969 + 3 ^ 40 * 68136 * 2
def baseEnd_68136 : Nat := 34986517874850651286655

theorem tailTrace_68136 : CollatzResearch.WordTrace tailWord_68136 prefixEnd_68136 34986517874850651286655 := by
  unfold tailWord_68136
  simp only [CollatzResearch.WordTrace]
  refine ⟨1242562040581191773732131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1656749387441589031642841 1242562040581191773732131)
  ·
    refine ⟨1863843060871787660598197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1242562040581191773732131 1863843060871787660598197)
    ·
      refine ⟨174735286956730093181081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1863843060871787660598197 174735286956730093181081)
      ·
        refine ⟨131051465217547569885811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174735286956730093181081 131051465217547569885811)
        ·
          refine ⟨196577197826321354828717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131051465217547569885811 196577197826321354828717)
          ·
            refine ⟨73716449184870508060769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 196577197826321354828717 73716449184870508060769)
            ·
              refine ⟨55287336888652881045577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73716449184870508060769 55287336888652881045577)
              ·
                refine ⟨41465502666489660784183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55287336888652881045577 41465502666489660784183)
                ·
                  refine ⟨62198253999734491176275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41465502666489660784183 62198253999734491176275)
                  ·
                    refine ⟨93297380999601736764413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62198253999734491176275 93297380999601736764413)
                    ·
                      refine ⟨34986517874850651286655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 93297380999601736764413 34986517874850651286655)
                      ·
                        rfl

theorem cell23_68136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_68136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68136 prefixEnd_68136 := by exact prefixLift 68136
  have htrace : WordTrace (prefixWord ++ tailWord_68136) baseStart_68136 baseEnd_68136 := by
    simpa [prefixWord, tailWord_68136, baseEnd_68136] using wordTrace_append hprefix tailTrace_68136
  have hstable : (prefixWord ++ tailWord_68136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68136).length < 2 ^ (prefixWord ++ tailWord_68136).sum := by decide
  have hdescent : baseEnd_68136 < baseStart_68136 := by decide
  rcases family_descends (prefixWord ++ tailWord_68136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68201 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 4, 1, 5]
def baseStart_68201 : Nat := 118140960795 + 68201 * 2 ^ 59
def prefixEnd_68201 : Nat := 4983230072969 + 3 ^ 40 * 68201 * 2
def baseEnd_68201 : Nat := 35019894117392896973855

theorem tailTrace_68201 : CollatzResearch.WordTrace tailWord_68201 prefixEnd_68201 35019894117392896973855 := by
  unfold tailWord_68201
  simp only [CollatzResearch.WordTrace]
  refine ⟨2487494825926899648580457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1658329883951266432386971 2487494825926899648580457)
  ·
    refine ⟨1865621119445174736435343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2487494825926899648580457 1865621119445174736435343)
    ·
      refine ⟨2798431679167762104653015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1865621119445174736435343 2798431679167762104653015)
      ·
        refine ⟨4197647518751643156979523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2798431679167762104653015 4197647518751643156979523)
        ·
          refine ⟨6296471278127464735469285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4197647518751643156979523 6296471278127464735469285)
          ·
            refine ⟨1180588364648899637900491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6296471278127464735469285 1180588364648899637900491)
            ·
              refine ⟨1770882546973349456850737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1180588364648899637900491 1770882546973349456850737)
              ·
                refine ⟨1328161910230012092638053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1770882546973349456850737 1328161910230012092638053)
                ·
                  refine ⟨249030358168127267369635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1328161910230012092638053 249030358168127267369635)
                  ·
                    refine ⟨373545537252190901054453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 249030358168127267369635 373545537252190901054453)
                    ·
                      refine ⟨35019894117392896973855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 373545537252190901054453 35019894117392896973855)
                      ·
                        rfl

theorem cell23_68201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 1, 5].length) (baseStart_68201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68201 prefixEnd_68201 := by exact prefixLift 68201
  have htrace : WordTrace (prefixWord ++ tailWord_68201) baseStart_68201 baseEnd_68201 := by
    simpa [prefixWord, tailWord_68201, baseEnd_68201] using wordTrace_append hprefix tailTrace_68201
  have hstable : (prefixWord ++ tailWord_68201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68201).length < 2 ^ (prefixWord ++ tailWord_68201).sum := by decide
  have hdescent : baseEnd_68201 < baseStart_68201 := by decide
  rcases family_descends (prefixWord ++ tailWord_68201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68211 : List Nat := [1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 4]
def baseStart_68211 : Nat := 118140960795 + 68211 * 2 ^ 59
def prefixEnd_68211 : Nat := 4983230072969 + 3 ^ 40 * 68211 * 2
def baseEnd_68211 : Nat := 35025028923937857848809

theorem tailTrace_68211 : CollatzResearch.WordTrace tailWord_68211 prefixEnd_68211 35025028923937857848809 := by
  unfold tailWord_68211
  simp only [CollatzResearch.WordTrace]
  refine ⟨2487859555890671356444487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1658573037260447570962991 2487859555890671356444487)
  ·
    refine ⟨3731789333836007034666731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2487859555890671356444487 3731789333836007034666731)
    ·
      refine ⟨5597684000754010552000097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3731789333836007034666731 5597684000754010552000097)
      ·
        refine ⟨4198263000565507914000073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5597684000754010552000097 4198263000565507914000073)
        ·
          refine ⟨3148697250424130935500055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4198263000565507914000073 3148697250424130935500055)
          ·
            refine ⟨4723045875636196403250083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3148697250424130935500055 4723045875636196403250083)
            ·
              refine ⟨7084568813454294604875125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4723045875636196403250083 7084568813454294604875125)
              ·
                refine ⟨664178326261340119207043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7084568813454294604875125 664178326261340119207043)
                ·
                  refine ⟨996267489392010178810565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 664178326261340119207043 996267489392010178810565)
                  ·
                    refine ⟨186800154261001908526981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 996267489392010178810565 186800154261001908526981)
                    ·
                      refine ⟨35025028923937857848809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 186800154261001908526981 35025028923937857848809)
                      ·
                        rfl

theorem cell23_68211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 4].length) (baseStart_68211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68211 prefixEnd_68211 := by exact prefixLift 68211
  have htrace : WordTrace (prefixWord ++ tailWord_68211) baseStart_68211 baseEnd_68211 := by
    simpa [prefixWord, tailWord_68211, baseEnd_68211] using wordTrace_append hprefix tailTrace_68211
  have hstable : (prefixWord ++ tailWord_68211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68211).length < 2 ^ (prefixWord ++ tailWord_68211).sum := by decide
  have hdescent : baseEnd_68211 < baseStart_68211 := by decide
  rcases family_descends (prefixWord ++ tailWord_68211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68215 : List Nat := [1, 1, 3, 1, 1, 3, 5, 1, 1, 4, 2]
def baseStart_68215 : Nat := 118140960795 + 68215 * 2 ^ 59
def prefixEnd_68215 : Nat := 4983230072969 + 3 ^ 40 * 68215 * 2
def baseEnd_68215 : Nat := 35027082846555842198791

theorem tailTrace_68215 : CollatzResearch.WordTrace tailWord_68215 prefixEnd_68215 35027082846555842198791 := by
  unfold tailWord_68215
  simp only [CollatzResearch.WordTrace]
  refine ⟨2488005447876180039590099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1658670298584120026393399 2488005447876180039590099)
  ·
    refine ⟨3732008171814270059385149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2488005447876180039590099 3732008171814270059385149)
    ·
      refine ⟨1399503064430351272269431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3732008171814270059385149 1399503064430351272269431)
      ·
        refine ⟨2099254596645526908404147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1399503064430351272269431 2099254596645526908404147)
        ·
          refine ⟨3148881894968290362606221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2099254596645526908404147 3148881894968290362606221)
          ·
            refine ⟨1180830710613108885977333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3148881894968290362606221 1180830710613108885977333)
            ·
              refine ⟨110702879119978958060375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1180830710613108885977333 110702879119978958060375)
              ·
                refine ⟨166054318679968437090563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110702879119978958060375 166054318679968437090563)
                ·
                  refine ⟨249081478019952655635845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 166054318679968437090563 249081478019952655635845)
                  ·
                    refine ⟨46702777128741122931721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 249081478019952655635845 46702777128741122931721)
                    ·
                      refine ⟨35027082846555842198791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 46702777128741122931721 35027082846555842198791)
                      ·
                        rfl

theorem cell23_68215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 4, 2].length) (baseStart_68215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68215 prefixEnd_68215 := by exact prefixLift 68215
  have htrace : WordTrace (prefixWord ++ tailWord_68215) baseStart_68215 baseEnd_68215 := by
    simpa [prefixWord, tailWord_68215, baseEnd_68215] using wordTrace_append hprefix tailTrace_68215
  have hstable : (prefixWord ++ tailWord_68215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68215).length < 2 ^ (prefixWord ++ tailWord_68215).sum := by decide
  have hdescent : baseEnd_68215 < baseStart_68215 := by decide
  rcases family_descends (prefixWord ++ tailWord_68215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68285 : List Nat := [1, 4, 1, 2, 1, 4, 2, 1, 2, 5]
def baseStart_68285 : Nat := 118140960795 + 68285 * 2 ^ 59
def prefixEnd_68285 : Nat := 4983230072969 + 3 ^ 40 * 68285 * 2
def baseEnd_68285 : Nat := 11687675497456856107823

theorem tailTrace_68285 : CollatzResearch.WordTrace tailWord_68285 prefixEnd_68285 11687675497456856107823 := by
  unfold tailWord_68285
  simp only [CollatzResearch.WordTrace]
  refine ⟨2490558557622581994638309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1660372371748387996425539 2490558557622581994638309)
  ·
    refine ⟨466979729554234123994683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2490558557622581994638309 466979729554234123994683)
    ·
      refine ⟨700469594331351185992025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 466979729554234123994683 700469594331351185992025)
      ·
        refine ⟨525352195748513389494019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 700469594331351185992025 525352195748513389494019)
        ·
          refine ⟨788028293622770084241029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 525352195748513389494019 788028293622770084241029)
          ·
            refine ⟨147755305054269390795193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 788028293622770084241029 147755305054269390795193)
            ·
              refine ⟨110816478790702043096395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147755305054269390795193 110816478790702043096395)
              ·
                refine ⟨166224718186053064644593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110816478790702043096395 166224718186053064644593)
                ·
                  refine ⟨124668538639539798483445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 166224718186053064644593 124668538639539798483445)
                  ·
                    refine ⟨11687675497456856107823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 124668538639539798483445 11687675497456856107823)
                    ·
                      rfl

theorem cell23_68285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_68285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68285 prefixEnd_68285 := by exact prefixLift 68285
  have htrace : WordTrace (prefixWord ++ tailWord_68285) baseStart_68285 baseEnd_68285 := by
    simpa [prefixWord, tailWord_68285, baseEnd_68285] using wordTrace_append hprefix tailTrace_68285
  have hstable : (prefixWord ++ tailWord_68285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68285).length < 2 ^ (prefixWord ++ tailWord_68285).sum := by decide
  have hdescent : baseEnd_68285 < baseStart_68285 := by decide
  rcases family_descends (prefixWord ++ tailWord_68285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68291 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 11]
def baseStart_68291 : Nat := 118140960795 + 68291 * 2 ^ 59
def prefixEnd_68291 : Nat := 4983230072969 + 3 ^ 40 * 68291 * 2
def baseEnd_68291 : Nat := 35066107376297544848441

theorem tailTrace_68291 : CollatzResearch.WordTrace tailWord_68291 prefixEnd_68291 35066107376297544848441 := by
  unfold tailWord_68291
  simp only [CollatzResearch.WordTrace]
  refine ⟨2490777395600845019356727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1660518263733896679571151 2490777395600845019356727)
  ·
    refine ⟨3736166093401267529035091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2490777395600845019356727 3736166093401267529035091)
    ·
      refine ⟨5604249140101901293552637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3736166093401267529035091 5604249140101901293552637)
      ·
        refine ⟨2101593427538212985082239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5604249140101901293552637 2101593427538212985082239)
        ·
          refine ⟨3152390141307319477623359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2101593427538212985082239 3152390141307319477623359)
          ·
            refine ⟨4728585211960979216435039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3152390141307319477623359 4728585211960979216435039)
            ·
              refine ⟨7092877817941468824652559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4728585211960979216435039 7092877817941468824652559)
              ·
                refine ⟨10639316726912203236978839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7092877817941468824652559 10639316726912203236978839)
                ·
                  refine ⟨15958975090368304855468259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10639316726912203236978839 15958975090368304855468259)
                  ·
                    refine ⟨23938462635552457283202389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15958975090368304855468259 23938462635552457283202389)
                    ·
                      refine ⟨35066107376297544848441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 23938462635552457283202389 35066107376297544848441)
                      ·
                        rfl

theorem cell23_68291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_68291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68291 prefixEnd_68291 := by exact prefixLift 68291
  have htrace : WordTrace (prefixWord ++ tailWord_68291) baseStart_68291 baseEnd_68291 := by
    simpa [prefixWord, tailWord_68291, baseEnd_68291] using wordTrace_append hprefix tailTrace_68291
  have hstable : (prefixWord ++ tailWord_68291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68291).length < 2 ^ (prefixWord ++ tailWord_68291).sum := by decide
  have hdescent : baseEnd_68291 < baseStart_68291 := by decide
  rcases family_descends (prefixWord ++ tailWord_68291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68305 : List Nat := [1, 2, 2, 1, 2, 3, 2, 2, 2, 4, 2]
def baseStart_68305 : Nat := 118140960795 + 68305 * 2 ^ 59
def prefixEnd_68305 : Nat := 4983230072969 + 3 ^ 40 * 68305 * 2
def baseEnd_68305 : Nat := 35073296105460490073377

theorem tailTrace_68305 : CollatzResearch.WordTrace tailWord_68305 prefixEnd_68305 35073296105460490073377 := by
  unfold tailWord_68305
  simp only [CollatzResearch.WordTrace]
  refine ⟨2491288017550125410366369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1660858678366750273577579 2491288017550125410366369)
  ·
    refine ⟨1868466013162594057774777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2491288017550125410366369 1868466013162594057774777)
    ·
      refine ⟨1401349509871945543331083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1868466013162594057774777 1401349509871945543331083)
      ·
        refine ⟨2102024264807918314996625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1401349509871945543331083 2102024264807918314996625)
        ·
          refine ⟨1576518198605938736247469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2102024264807918314996625 1576518198605938736247469)
          ·
            refine ⟨591194324477227026092801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1576518198605938736247469 591194324477227026092801)
            ·
              refine ⟨443395743357920269569601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 591194324477227026092801 443395743357920269569601)
              ·
                refine ⟨332546807518440202177201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 443395743357920269569601 332546807518440202177201)
                ·
                  refine ⟨249410105638830151632901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 332546807518440202177201 249410105638830151632901)
                  ·
                    refine ⟨46764394807280653431169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 249410105638830151632901 46764394807280653431169)
                    ·
                      refine ⟨35073296105460490073377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 46764394807280653431169 35073296105460490073377)
                      ·
                        rfl

theorem cell23_68305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 4, 2].length) (baseStart_68305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68305 prefixEnd_68305 := by exact prefixLift 68305
  have htrace : WordTrace (prefixWord ++ tailWord_68305) baseStart_68305 baseEnd_68305 := by
    simpa [prefixWord, tailWord_68305, baseEnd_68305] using wordTrace_append hprefix tailTrace_68305
  have hstable : (prefixWord ++ tailWord_68305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68305).length < 2 ^ (prefixWord ++ tailWord_68305).sum := by decide
  have hdescent : baseEnd_68305 < baseStart_68305 := by decide
  rcases family_descends (prefixWord ++ tailWord_68305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68306 : List Nat := [3, 2, 2, 2, 4, 1, 2, 2, 5]
def baseStart_68306 : Nat := 118140960795 + 68306 * 2 ^ 59
def prefixEnd_68306 : Nat := 4983230072969 + 3 ^ 40 * 68306 * 2
def baseEnd_68306 : Nat := 3897089954012776240097

theorem tailTrace_68306 : CollatzResearch.WordTrace tailWord_68306 prefixEnd_68306 3897089954012776240097 := by
  unfold tailWord_68306
  simp only [CollatzResearch.WordTrace]
  refine ⟨622831122636625645288193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1660882993697668387435181 622831122636625645288193)
  ·
    refine ⟨467123341977469233966145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 622831122636625645288193 467123341977469233966145)
    ·
      refine ⟨350342506483101925474609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 467123341977469233966145 350342506483101925474609)
      ·
        refine ⟨262756879862326444105957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 350342506483101925474609 262756879862326444105957)
        ·
          refine ⟨49266914974186208269867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 262756879862326444105957 49266914974186208269867)
          ·
            refine ⟨73900372461279312404801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49266914974186208269867 73900372461279312404801)
            ·
              refine ⟨55425279345959484303601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73900372461279312404801 55425279345959484303601)
              ·
                refine ⟨41568959509469613227701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55425279345959484303601 41568959509469613227701)
                ·
                  refine ⟨3897089954012776240097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41568959509469613227701 3897089954012776240097)
                  ·
                    rfl

theorem cell23_68306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 2, 5].length) (baseStart_68306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68306 prefixEnd_68306 := by exact prefixLift 68306
  have htrace : WordTrace (prefixWord ++ tailWord_68306) baseStart_68306 baseEnd_68306 := by
    simpa [prefixWord, tailWord_68306, baseEnd_68306] using wordTrace_append hprefix tailTrace_68306
  have hstable : (prefixWord ++ tailWord_68306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68306).length < 2 ^ (prefixWord ++ tailWord_68306).sum := by decide
  have hdescent : baseEnd_68306 < baseStart_68306 := by decide
  rcases family_descends (prefixWord ++ tailWord_68306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68355 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 7, 1, 3]
def baseStart_68355 : Nat := 118140960795 + 68355 * 2 ^ 59
def prefixEnd_68355 : Nat := 4983230072969 + 3 ^ 40 * 68355 * 2
def baseEnd_68355 : Nat := 35098970138185294448147

theorem tailTrace_68355 : CollatzResearch.WordTrace tailWord_68355 prefixEnd_68355 35098970138185294448147 := by
  unfold tailWord_68355
  simp only [CollatzResearch.WordTrace]
  refine ⟨2493111667368983949686519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1662074444912655966457679 2493111667368983949686519)
  ·
    refine ⟨3739667501053475924529779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2493111667368983949686519 3739667501053475924529779)
    ·
      refine ⟨5609501251580213886794669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3739667501053475924529779 5609501251580213886794669)
      ·
        refine ⟨2103562969342580207548001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5609501251580213886794669 2103562969342580207548001)
        ·
          refine ⟨1577672227006935155661001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2103562969342580207548001 1577672227006935155661001)
          ·
            refine ⟨1183254170255201366745751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1577672227006935155661001 1183254170255201366745751)
            ·
              refine ⟨1774881255382802050118627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1183254170255201366745751 1774881255382802050118627)
              ·
                refine ⟨2662321883074203075177941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1774881255382802050118627 2662321883074203075177941)
                ·
                  refine ⟨62398169134551634574483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2662321883074203075177941 62398169134551634574483)
                  ·
                    refine ⟨93597253701827451861725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62398169134551634574483 93597253701827451861725)
                    ·
                      refine ⟨35098970138185294448147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 93597253701827451861725 35098970138185294448147)
                      ·
                        rfl

theorem cell23_68355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 7, 1, 3].length) (baseStart_68355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68355 prefixEnd_68355 := by exact prefixLift 68355
  have htrace : WordTrace (prefixWord ++ tailWord_68355) baseStart_68355 baseEnd_68355 := by
    simpa [prefixWord, tailWord_68355, baseEnd_68355] using wordTrace_append hprefix tailTrace_68355
  have hstable : (prefixWord ++ tailWord_68355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68355).length < 2 ^ (prefixWord ++ tailWord_68355).sum := by decide
  have hdescent : baseEnd_68355 < baseStart_68355 := by decide
  rcases family_descends (prefixWord ++ tailWord_68355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68392 : List Nat := [2, 1, 5, 1, 1, 1, 4, 2, 1, 5]
def baseStart_68392 : Nat := 118140960795 + 68392 * 2 ^ 59
def prefixEnd_68392 : Nat := 4983230072969 + 3 ^ 40 * 68392 * 2
def baseEnd_68392 : Nat := 11705989640800549895159

theorem tailTrace_68392 : CollatzResearch.WordTrace tailWord_68392 prefixEnd_68392 11705989640800549895159 := by
  unfold tailWord_68392
  simp only [CollatzResearch.WordTrace]
  refine ⟨1247230584117469634391715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1662974112156626179188953 1247230584117469634391715)
  ·
    refine ⟨1870845876176204451587573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1247230584117469634391715 1870845876176204451587573)
    ·
      refine ⟨175391800891519167336335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1870845876176204451587573 175391800891519167336335)
      ·
        refine ⟨263087701337278751004503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175391800891519167336335 263087701337278751004503)
        ·
          refine ⟨394631552005918126506755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263087701337278751004503 394631552005918126506755)
          ·
            refine ⟨591947328008877189760133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394631552005918126506755 591947328008877189760133)
            ·
              refine ⟨110990124001664473080025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 591947328008877189760133 110990124001664473080025)
              ·
                refine ⟨83242593001248354810019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110990124001664473080025 83242593001248354810019)
                ·
                  refine ⟨124863889501872532215029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83242593001248354810019 124863889501872532215029)
                  ·
                    refine ⟨11705989640800549895159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 124863889501872532215029 11705989640800549895159)
                    ·
                      rfl

theorem cell23_68392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_68392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68392 prefixEnd_68392 := by exact prefixLift 68392
  have htrace : WordTrace (prefixWord ++ tailWord_68392) baseStart_68392 baseEnd_68392 := by
    simpa [prefixWord, tailWord_68392, baseEnd_68392] using wordTrace_append hprefix tailTrace_68392
  have hstable : (prefixWord ++ tailWord_68392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68392).length < 2 ^ (prefixWord ++ tailWord_68392).sum := by decide
  have hdescent : baseEnd_68392 < baseStart_68392 := by decide
  rcases family_descends (prefixWord ++ tailWord_68392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68395 : List Nat := [1, 1, 1, 1, 2, 1, 2, 8, 1, 1, 4]
def baseStart_68395 : Nat := 118140960795 + 68395 * 2 ^ 59
def prefixEnd_68395 : Nat := 4983230072969 + 3 ^ 40 * 68395 * 2
def baseEnd_68395 : Nat := 35119509364365137947963

theorem tailTrace_68395 : CollatzResearch.WordTrace tailWord_68395 prefixEnd_68395 35119509364365137947963 := by
  unfold tailWord_68395
  simp only [CollatzResearch.WordTrace]
  refine ⟨2494570587224070781142639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1663047058149380520761759 2494570587224070781142639)
  ·
    refine ⟨3741855880836106171713959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2494570587224070781142639 3741855880836106171713959)
    ·
      refine ⟨5612783821254159257570939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3741855880836106171713959 5612783821254159257570939)
      ·
        refine ⟨8419175731881238886356409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5612783821254159257570939 8419175731881238886356409)
        ·
          refine ⟨6314381798910929164767307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8419175731881238886356409 6314381798910929164767307)
          ·
            refine ⟨9471572698366393747150961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6314381798910929164767307 9471572698366393747150961)
            ·
              refine ⟨7103679523774795310363221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9471572698366393747150961 7103679523774795310363221)
              ·
                refine ⟨83246244419235882543319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7103679523774795310363221 83246244419235882543319)
                ·
                  refine ⟨124869366628853823814979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83246244419235882543319 124869366628853823814979)
                  ·
                    refine ⟨187304049943280735722469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 124869366628853823814979 187304049943280735722469)
                    ·
                      refine ⟨35119509364365137947963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 187304049943280735722469 35119509364365137947963)
                      ·
                        rfl

theorem cell23_68395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 1, 4].length) (baseStart_68395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68395 prefixEnd_68395 := by exact prefixLift 68395
  have htrace : WordTrace (prefixWord ++ tailWord_68395) baseStart_68395 baseEnd_68395 := by
    simpa [prefixWord, tailWord_68395, baseEnd_68395] using wordTrace_append hprefix tailTrace_68395
  have hstable : (prefixWord ++ tailWord_68395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68395).length < 2 ^ (prefixWord ++ tailWord_68395).sum := by decide
  have hdescent : baseEnd_68395 < baseStart_68395 := by decide
  rcases family_descends (prefixWord ++ tailWord_68395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68415 : List Nat := [1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 5]
def baseStart_68415 : Nat := 118140960795 + 68415 * 2 ^ 59
def prefixEnd_68415 : Nat := 4983230072969 + 3 ^ 40 * 68415 * 2
def baseEnd_68415 : Nat := 35129778977455059697871

theorem tailTrace_68415 : CollatzResearch.WordTrace tailWord_68415 prefixEnd_68415 35129778977455059697871 := by
  unfold tailWord_68415
  simp only [CollatzResearch.WordTrace]
  refine ⟨2495300047151614196870699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1663533364767742797913799 2495300047151614196870699)
  ·
    refine ⟨3742950070727421295306049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2495300047151614196870699 3742950070727421295306049)
    ·
      refine ⟨2807212553045565971479537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3742950070727421295306049 2807212553045565971479537)
      ·
        refine ⟨2105409414784174478609653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2807212553045565971479537 2105409414784174478609653)
        ·
          refine ⟨197382132636016357369655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2105409414784174478609653 197382132636016357369655)
          ·
            refine ⟨296073198954024536054483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197382132636016357369655 296073198954024536054483)
            ·
              refine ⟨444109798431036804081725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296073198954024536054483 444109798431036804081725)
              ·
                refine ⟨166541174411638801530647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 444109798431036804081725 166541174411638801530647)
                ·
                  refine ⟨249811761617458202295971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 166541174411638801530647 249811761617458202295971)
                  ·
                    refine ⟨374717642426187303443957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 249811761617458202295971 374717642426187303443957)
                    ·
                      refine ⟨35129778977455059697871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 374717642426187303443957 35129778977455059697871)
                      ·
                        rfl

theorem cell23_68415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 5].length) (baseStart_68415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68415 prefixEnd_68415 := by exact prefixLift 68415
  have htrace : WordTrace (prefixWord ++ tailWord_68415) baseStart_68415 baseEnd_68415 := by
    simpa [prefixWord, tailWord_68415, baseEnd_68415] using wordTrace_append hprefix tailTrace_68415
  have hstable : (prefixWord ++ tailWord_68415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68415).length < 2 ^ (prefixWord ++ tailWord_68415).sum := by decide
  have hdescent : baseEnd_68415 < baseStart_68415 := by decide
  rcases family_descends (prefixWord ++ tailWord_68415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68439 : List Nat := [1, 1, 3, 2, 4, 1, 4, 1, 2, 4]
def baseStart_68439 : Nat := 118140960795 + 68439 * 2 ^ 59
def prefixEnd_68439 : Nat := 4983230072969 + 3 ^ 40 * 68439 * 2
def baseEnd_68439 : Nat := 11714034171054321932587

theorem tailTrace_68439 : CollatzResearch.WordTrace tailWord_68439 prefixEnd_68439 11714034171054321932587 := by
  unfold tailWord_68439
  simp only [CollatzResearch.WordTrace]
  refine ⟨2496175399064666295744371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1664116932709777530496247 2496175399064666295744371)
  ·
    refine ⟨3744263098596999443616557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2496175399064666295744371 3744263098596999443616557)
    ·
      refine ⟨1404098661973874791356209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3744263098596999443616557 1404098661973874791356209)
      ·
        refine ⟨1053073996480406093517157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1404098661973874791356209 1053073996480406093517157)
        ·
          refine ⟨197451374340076142534467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1053073996480406093517157 197451374340076142534467)
          ·
            refine ⟨296177061510114213801701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197451374340076142534467 296177061510114213801701)
            ·
              refine ⟨55533199033146415087819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 296177061510114213801701 55533199033146415087819)
              ·
                refine ⟨83299798549719622631729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55533199033146415087819 83299798549719622631729)
                ·
                  refine ⟨62474848912289716973797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83299798549719622631729 62474848912289716973797)
                  ·
                    refine ⟨11714034171054321932587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62474848912289716973797 11714034171054321932587)
                    ·
                      rfl

theorem cell23_68439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 2, 4].length) (baseStart_68439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68439 prefixEnd_68439 := by exact prefixLift 68439
  have htrace : WordTrace (prefixWord ++ tailWord_68439) baseStart_68439 baseEnd_68439 := by
    simpa [prefixWord, tailWord_68439, baseEnd_68439] using wordTrace_append hprefix tailTrace_68439
  have hstable : (prefixWord ++ tailWord_68439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68439).length < 2 ^ (prefixWord ++ tailWord_68439).sum := by decide
  have hdescent : baseEnd_68439 < baseStart_68439 := by decide
  rcases family_descends (prefixWord ++ tailWord_68439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68485 : List Nat := [1, 3, 1, 1, 3, 3, 1, 1, 2, 3, 4]
def baseStart_68485 : Nat := 118140960795 + 68485 * 2 ^ 59
def prefixEnd_68485 : Nat := 4983230072969 + 3 ^ 40 * 68485 * 2
def baseEnd_68485 : Nat := 35165722623269785822549

theorem tailTrace_68485 : CollatzResearch.WordTrace tailWord_68485 prefixEnd_68485 35165722623269785822549 := by
  unfold tailWord_68485
  simp only [CollatzResearch.WordTrace]
  refine ⟨2497853156898016151918909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1665235437932010767945939 2497853156898016151918909)
  ·
    refine ⟨936694933836756056969591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2497853156898016151918909 936694933836756056969591)
    ·
      refine ⟨1405042400755134085454387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 936694933836756056969591 1405042400755134085454387)
      ·
        refine ⟨2107563601132701128181581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1405042400755134085454387 2107563601132701128181581)
        ·
          refine ⟨790336350424762923068093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2107563601132701128181581 790336350424762923068093)
          ·
            refine ⟨296376131409286096150535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 790336350424762923068093 296376131409286096150535)
            ·
              refine ⟨444564197113929144225803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296376131409286096150535 444564197113929144225803)
              ·
                refine ⟨666846295670893716338705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 444564197113929144225803 666846295670893716338705)
                ·
                  refine ⟨500134721753170287254029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 666846295670893716338705 500134721753170287254029)
                  ·
                    refine ⟨187550520657438857720261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 500134721753170287254029 187550520657438857720261)
                    ·
                      refine ⟨35165722623269785822549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 187550520657438857720261 35165722623269785822549)
                      ·
                        rfl

theorem cell23_68485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_68485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68485 prefixEnd_68485 := by exact prefixLift 68485
  have htrace : WordTrace (prefixWord ++ tailWord_68485) baseStart_68485 baseEnd_68485 := by
    simpa [prefixWord, tailWord_68485, baseEnd_68485] using wordTrace_append hprefix tailTrace_68485
  have hstable : (prefixWord ++ tailWord_68485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68485).length < 2 ^ (prefixWord ++ tailWord_68485).sum := by decide
  have hdescent : baseEnd_68485 < baseStart_68485 := by decide
  rcases family_descends (prefixWord ++ tailWord_68485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68505 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 4, 4, 3]
def baseStart_68505 : Nat := 118140960795 + 68505 * 2 ^ 59
def prefixEnd_68505 : Nat := 4983230072969 + 3 ^ 40 * 68505 * 2
def baseEnd_68505 : Nat := 35175992236359707572457

theorem tailTrace_68505 : CollatzResearch.WordTrace tailWord_68505 prefixEnd_68505 35175992236359707572457 := by
  unfold tailWord_68505
  simp only [CollatzResearch.WordTrace]
  refine ⟨2498582616825559567646969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1665721744550373045097979 2498582616825559567646969)
  ·
    refine ⟨1873936962619169675735227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2498582616825559567646969 1873936962619169675735227)
    ·
      refine ⟨2810905443928754513602841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1873936962619169675735227 2810905443928754513602841)
      ·
        refine ⟨2108179082946565885202131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2810905443928754513602841 2108179082946565885202131)
        ·
          refine ⟨3162268624419848827803197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2108179082946565885202131 3162268624419848827803197)
          ·
            refine ⟨1185850734157443310426199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3162268624419848827803197 1185850734157443310426199)
            ·
              refine ⟨1778776101236164965639299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1185850734157443310426199 1778776101236164965639299)
              ·
                refine ⟨2668164151854247448458949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1778776101236164965639299 2668164151854247448458949)
                ·
                  refine ⟨500280778472671396586053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2668164151854247448458949 500280778472671396586053)
                  ·
                    refine ⟨93802645963625886859885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 500280778472671396586053 93802645963625886859885)
                    ·
                      refine ⟨35175992236359707572457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 93802645963625886859885 35175992236359707572457)
                      ·
                        rfl

theorem cell23_68505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 4, 3].length) (baseStart_68505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68505 prefixEnd_68505 := by exact prefixLift 68505
  have htrace : WordTrace (prefixWord ++ tailWord_68505) baseStart_68505 baseEnd_68505 := by
    simpa [prefixWord, tailWord_68505, baseEnd_68505] using wordTrace_append hprefix tailTrace_68505
  have hstable : (prefixWord ++ tailWord_68505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68505).length < 2 ^ (prefixWord ++ tailWord_68505).sum := by decide
  have hdescent : baseEnd_68505 < baseStart_68505 := by decide
  rcases family_descends (prefixWord ++ tailWord_68505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68536 : List Nat := [2, 1, 2, 1, 2, 4, 3, 2, 2, 2, 2]
def baseStart_68536 : Nat := 118140960795 + 68536 * 2 ^ 59
def prefixEnd_68536 : Nat := 4983230072969 + 3 ^ 40 * 68536 * 2
def baseEnd_68536 : Nat := 35191910136649086284815

theorem tailTrace_68536 : CollatzResearch.WordTrace tailWord_68536 prefixEnd_68536 35191910136649086284815 := by
  unfold tailWord_68536
  simp only [CollatzResearch.WordTrace]
  refine ⟨1249856639856625931012731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1666475519808834574683641 1249856639856625931012731)
  ·
    refine ⟨1874784959784938896519097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1249856639856625931012731 1874784959784938896519097)
    ·
      refine ⟨1406088719838704172389323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1874784959784938896519097 1406088719838704172389323)
      ·
        refine ⟨2109133079758056258583985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1406088719838704172389323 2109133079758056258583985)
        ·
          refine ⟨1581849809818542193937989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2109133079758056258583985 1581849809818542193937989)
          ·
            refine ⟨296596839340976661363373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1581849809818542193937989 296596839340976661363373)
            ·
              refine ⟨111223814752866248011265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 296596839340976661363373 111223814752866248011265)
              ·
                refine ⟨83417861064649686008449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111223814752866248011265 83417861064649686008449)
                ·
                  refine ⟨62563395798487264506337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83417861064649686008449 62563395798487264506337)
                  ·
                    refine ⟨46922546848865448379753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 62563395798487264506337 46922546848865448379753)
                    ·
                      refine ⟨35191910136649086284815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 46922546848865448379753 35191910136649086284815)
                      ·
                        rfl

theorem cell23_68536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 2, 2, 2].length) (baseStart_68536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68536 prefixEnd_68536 := by exact prefixLift 68536
  have htrace : WordTrace (prefixWord ++ tailWord_68536) baseStart_68536 baseEnd_68536 := by
    simpa [prefixWord, tailWord_68536, baseEnd_68536] using wordTrace_append hprefix tailTrace_68536
  have hstable : (prefixWord ++ tailWord_68536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68536).length < 2 ^ (prefixWord ++ tailWord_68536).sum := by decide
  have hdescent : baseEnd_68536 < baseStart_68536 := by decide
  rcases family_descends (prefixWord ++ tailWord_68536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68542 : List Nat := [4, 2, 1, 1, 1, 2, 4, 1, 7]
def baseStart_68542 : Nat := 118140960795 + 68542 * 2 ^ 59
def prefixEnd_68542 : Nat := 4983230072969 + 3 ^ 40 * 68542 * 2
def baseEnd_68542 : Nat := 3910554557841784756643

theorem tailTrace_68542 : CollatzResearch.WordTrace tailWord_68542 prefixEnd_68542 3910554557841784756643 := by
  unfold tailWord_68542
  simp only [CollatzResearch.WordTrace]
  refine ⟨312491514711439360842985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1666621411794343257829253 312491514711439360842985)
  ·
    refine ⟨234368636033579520632239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 312491514711439360842985 234368636033579520632239)
    ·
      refine ⟨351552954050369280948359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234368636033579520632239 351552954050369280948359)
      ·
        refine ⟨527329431075553921422539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351552954050369280948359 527329431075553921422539)
        ·
          refine ⟨790994146613330882133809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 527329431075553921422539 790994146613330882133809)
          ·
            refine ⟨593245609959998161600357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 790994146613330882133809 593245609959998161600357)
            ·
              refine ⟨111233551867499655300067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 593245609959998161600357 111233551867499655300067)
              ·
                refine ⟨166850327801249482950101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111233551867499655300067 166850327801249482950101)
                ·
                  refine ⟨3910554557841784756643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 166850327801249482950101 3910554557841784756643)
                  ·
                    rfl

theorem cell23_68542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_68542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68542 prefixEnd_68542 := by exact prefixLift 68542
  have htrace : WordTrace (prefixWord ++ tailWord_68542) baseStart_68542 baseEnd_68542 := by
    simpa [prefixWord, tailWord_68542, baseEnd_68542] using wordTrace_append hprefix tailTrace_68542
  have hstable : (prefixWord ++ tailWord_68542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68542).length < 2 ^ (prefixWord ++ tailWord_68542).sum := by decide
  have hdescent : baseEnd_68542 < baseStart_68542 := by decide
  rcases family_descends (prefixWord ++ tailWord_68542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68555 : List Nat := [1, 1, 1, 1, 3, 5, 1, 2, 1, 7]
def baseStart_68555 : Nat := 118140960795 + 68555 * 2 ^ 59
def prefixEnd_68555 : Nat := 4983230072969 + 3 ^ 40 * 68555 * 2
def baseEnd_68555 : Nat := 11733888756361503982409

theorem tailTrace_68555 : CollatzResearch.WordTrace tailWord_68555 prefixEnd_68555 11733888756361503982409 := by
  unfold tailWord_68555
  simp only [CollatzResearch.WordTrace]
  refine ⟨2500406266644418106967119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1666937511096278737978079 2500406266644418106967119)
  ·
    refine ⟨3750609399966627160450679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2500406266644418106967119 3750609399966627160450679)
    ·
      refine ⟨5625914099949940740676019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3750609399966627160450679 5625914099949940740676019)
      ·
        refine ⟨8438871149924911111014029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5625914099949940740676019 8438871149924911111014029)
        ·
          refine ⟨3164576681221841666630261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8438871149924911111014029 3164576681221841666630261)
          ·
            refine ⟨296679063864547656246587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3164576681221841666630261 296679063864547656246587)
            ·
              refine ⟨445018595796821484369881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296679063864547656246587 445018595796821484369881)
              ·
                refine ⟨333763946847616113277411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 445018595796821484369881 333763946847616113277411)
                ·
                  refine ⟨500645920271424169916117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 333763946847616113277411 500645920271424169916117)
                  ·
                    refine ⟨11733888756361503982409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 500645920271424169916117 11733888756361503982409)
                    ·
                      rfl

theorem cell23_68555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 7].length) (baseStart_68555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68555 prefixEnd_68555 := by exact prefixLift 68555
  have htrace : WordTrace (prefixWord ++ tailWord_68555) baseStart_68555 baseEnd_68555 := by
    simpa [prefixWord, tailWord_68555, baseEnd_68555] using wordTrace_append hprefix tailTrace_68555
  have hstable : (prefixWord ++ tailWord_68555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68555).length < 2 ^ (prefixWord ++ tailWord_68555).sum := by decide
  have hdescent : baseEnd_68555 < baseStart_68555 := by decide
  rcases family_descends (prefixWord ++ tailWord_68555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68557 : List Nat := [1, 6, 3, 1, 1, 1, 2, 2, 1, 3, 2]
def baseStart_68557 : Nat := 118140960795 + 68557 * 2 ^ 59
def prefixEnd_68557 : Nat := 4983230072969 + 3 ^ 40 * 68557 * 2
def baseEnd_68557 : Nat := 35202693230393504122219

theorem tailTrace_68557 : CollatzResearch.WordTrace tailWord_68557 prefixEnd_68557 35202693230393504122219 := by
  unfold tailWord_68557
  simp only [CollatzResearch.WordTrace]
  refine ⟨2500479212637172448539925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1666986141758114965693283 2500479212637172448539925)
  ·
    refine ⟨117209963092367458525309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2500479212637172448539925 117209963092367458525309)
    ·
      refine ⟨43953736159637796946991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117209963092367458525309 43953736159637796946991)
      ·
        refine ⟨65930604239456695420487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43953736159637796946991 65930604239456695420487)
        ·
          refine ⟨98895906359185043130731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65930604239456695420487 98895906359185043130731)
          ·
            refine ⟨148343859538777564696097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98895906359185043130731 148343859538777564696097)
            ·
              refine ⟨111257894654083173522073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148343859538777564696097 111257894654083173522073)
              ·
                refine ⟨83443420990562380141555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111257894654083173522073 83443420990562380141555)
                ·
                  refine ⟨125165131485843570212333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83443420990562380141555 125165131485843570212333)
                  ·
                    refine ⟨46936924307191338829625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 125165131485843570212333 46936924307191338829625)
                    ·
                      refine ⟨35202693230393504122219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 46936924307191338829625 35202693230393504122219)
                      ·
                        rfl

theorem cell23_68557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_68557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68557 prefixEnd_68557 := by exact prefixLift 68557
  have htrace : WordTrace (prefixWord ++ tailWord_68557) baseStart_68557 baseEnd_68557 := by
    simpa [prefixWord, tailWord_68557, baseEnd_68557] using wordTrace_append hprefix tailTrace_68557
  have hstable : (prefixWord ++ tailWord_68557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68557).length < 2 ^ (prefixWord ++ tailWord_68557).sum := by decide
  have hdescent : baseEnd_68557 < baseStart_68557 := by decide
  rcases family_descends (prefixWord ++ tailWord_68557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68629 : List Nat := [1, 3, 2, 1, 4, 1, 1, 3, 2, 2, 3]
def baseStart_68629 : Nat := 118140960795 + 68629 * 2 ^ 59
def prefixEnd_68629 : Nat := 4983230072969 + 3 ^ 40 * 68629 * 2
def baseEnd_68629 : Nat := 35239663837517222421887

theorem tailTrace_68629 : CollatzResearch.WordTrace tailWord_68629 prefixEnd_68629 35239663837517222421887 := by
  unfold tailWord_68629
  simp only [CollatzResearch.WordTrace]
  refine ⟨2503105268376328745160941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1668736845584219163440627 2503105268376328745160941)
  ·
    refine ⟨938664475641123279435353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2503105268376328745160941 938664475641123279435353)
    ·
      refine ⟨703998356730842459576515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 938664475641123279435353 703998356730842459576515)
      ·
        refine ⟨1055997535096263689364773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 703998356730842459576515 1055997535096263689364773)
        ·
          refine ⟨197999537830549441755895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1055997535096263689364773 197999537830549441755895)
          ·
            refine ⟨296999306745824162633843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197999537830549441755895 296999306745824162633843)
            ·
              refine ⟨445498960118736243950765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296999306745824162633843 445498960118736243950765)
              ·
                refine ⟨167062110044526091481537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 445498960118736243950765 167062110044526091481537)
                ·
                  refine ⟨125296582533394568611153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 167062110044526091481537 125296582533394568611153)
                  ·
                    refine ⟨93972436900045926458365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 125296582533394568611153 93972436900045926458365)
                    ·
                      refine ⟨35239663837517222421887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 93972436900045926458365 35239663837517222421887)
                      ·
                        rfl

theorem cell23_68629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_68629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68629 prefixEnd_68629 := by exact prefixLift 68629
  have htrace : WordTrace (prefixWord ++ tailWord_68629) baseStart_68629 baseEnd_68629 := by
    simpa [prefixWord, tailWord_68629, baseEnd_68629] using wordTrace_append hprefix tailTrace_68629
  have hstable : (prefixWord ++ tailWord_68629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68629).length < 2 ^ (prefixWord ++ tailWord_68629).sum := by decide
  have hdescent : baseEnd_68629 < baseStart_68629 := by decide
  rcases family_descends (prefixWord ++ tailWord_68629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68659 : List Nat := [1, 1, 1, 2, 4, 1, 1, 5, 3, 1, 3]
def baseStart_68659 : Nat := 118140960795 + 68659 * 2 ^ 59
def prefixEnd_68659 : Nat := 4983230072969 + 3 ^ 40 * 68659 * 2
def baseEnd_68659 : Nat := 35255068257152105046749

theorem tailTrace_68659 : CollatzResearch.WordTrace tailWord_68659 prefixEnd_68659 35255068257152105046749 := by
  unfold tailWord_68659
  simp only [CollatzResearch.WordTrace]
  refine ⟨2504199458267643868753031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1669466305511762579168687 2504199458267643868753031)
  ·
    refine ⟨3756299187401465803129547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2504199458267643868753031 3756299187401465803129547)
    ·
      refine ⟨5634448781102198704694321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3756299187401465803129547 5634448781102198704694321)
      ·
        refine ⟨4225836585826649028520741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5634448781102198704694321 4225836585826649028520741)
        ·
          refine ⟨792344359842496692847639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4225836585826649028520741 792344359842496692847639)
          ·
            refine ⟨1188516539763745039271459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 792344359842496692847639 1188516539763745039271459)
            ·
              refine ⟨1782774809645617558907189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1188516539763745039271459 1782774809645617558907189)
              ·
                refine ⟨167135138404276646147549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1782774809645617558907189 167135138404276646147549)
                ·
                  refine ⟨62675676901603742305331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 167135138404276646147549 62675676901603742305331)
                  ·
                    refine ⟨94013515352405613457997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62675676901603742305331 94013515352405613457997)
                    ·
                      refine ⟨35255068257152105046749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 94013515352405613457997 35255068257152105046749)
                      ·
                        rfl

theorem cell23_68659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 3, 1, 3].length) (baseStart_68659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68659 prefixEnd_68659 := by exact prefixLift 68659
  have htrace : WordTrace (prefixWord ++ tailWord_68659) baseStart_68659 baseEnd_68659 := by
    simpa [prefixWord, tailWord_68659, baseEnd_68659] using wordTrace_append hprefix tailTrace_68659
  have hstable : (prefixWord ++ tailWord_68659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68659).length < 2 ^ (prefixWord ++ tailWord_68659).sum := by decide
  have hdescent : baseEnd_68659 < baseStart_68659 := by decide
  rcases family_descends (prefixWord ++ tailWord_68659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68693 : List Nat := [1, 3, 2, 2, 1, 2, 4, 3, 1, 1, 3]
def baseStart_68693 : Nat := 118140960795 + 68693 * 2 ^ 59
def prefixEnd_68693 : Nat := 4983230072969 + 3 ^ 40 * 68693 * 2
def baseEnd_68693 : Nat := 35272526599404972021593

theorem tailTrace_68693 : CollatzResearch.WordTrace tailWord_68693 prefixEnd_68693 35272526599404972021593 := by
  unfold tailWord_68693
  simp only [CollatzResearch.WordTrace]
  refine ⟨2505439540144467675490733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1670293026762978450327155 2505439540144467675490733)
  ·
    refine ⟨939539827554175378309025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2505439540144467675490733 939539827554175378309025)
    ·
      refine ⟨704654870665631533731769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 939539827554175378309025 704654870665631533731769)
      ·
        refine ⟨528491152999223650298827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 704654870665631533731769 528491152999223650298827)
        ·
          refine ⟨792736729498835475448241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 528491152999223650298827 792736729498835475448241)
          ·
            refine ⟨594552547124126606586181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 792736729498835475448241 594552547124126606586181)
            ·
              refine ⟨111478602585773738734909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 594552547124126606586181 111478602585773738734909)
              ·
                refine ⟨41804475969665152025591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111478602585773738734909 41804475969665152025591)
                ·
                  refine ⟨62706713954497728038387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41804475969665152025591 62706713954497728038387)
                  ·
                    refine ⟨94060070931746592057581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62706713954497728038387 94060070931746592057581)
                    ·
                      refine ⟨35272526599404972021593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 94060070931746592057581 35272526599404972021593)
                      ·
                        rfl

theorem cell23_68693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_68693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68693 prefixEnd_68693 := by exact prefixLift 68693
  have htrace : WordTrace (prefixWord ++ tailWord_68693) baseStart_68693 baseEnd_68693 := by
    simpa [prefixWord, tailWord_68693, baseEnd_68693] using wordTrace_append hprefix tailTrace_68693
  have hstable : (prefixWord ++ tailWord_68693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68693).length < 2 ^ (prefixWord ++ tailWord_68693).sum := by decide
  have hdescent : baseEnd_68693 < baseStart_68693 := by decide
  rcases family_descends (prefixWord ++ tailWord_68693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68709 : List Nat := [1, 3, 1, 3, 2, 1, 3, 1, 4, 4]
def baseStart_68709 : Nat := 118140960795 + 68709 * 2 ^ 59
def prefixEnd_68709 : Nat := 4983230072969 + 3 ^ 40 * 68709 * 2
def baseEnd_68709 : Nat := 11760247429958969807173

theorem tailTrace_68709 : CollatzResearch.WordTrace tailWord_68709 prefixEnd_68709 11760247429958969807173 := by
  unfold tailWord_68709
  simp only [CollatzResearch.WordTrace]
  refine ⟨2506023108086502408073181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1670682072057668272048787 2506023108086502408073181)
  ·
    refine ⟨939758665532438403027443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2506023108086502408073181 939758665532438403027443)
    ·
      refine ⟨1409637998298657604541165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 939758665532438403027443 1409637998298657604541165)
      ·
        refine ⟨528614249361996601702937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1409637998298657604541165 528614249361996601702937)
        ·
          refine ⟨396460687021497451277203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 528614249361996601702937 396460687021497451277203)
          ·
            refine ⟨594691030532246176915805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 396460687021497451277203 594691030532246176915805)
            ·
              refine ⟨223009136449592316343427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 594691030532246176915805 223009136449592316343427)
              ·
                refine ⟨334513704674388474515141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223009136449592316343427 334513704674388474515141)
                ·
                  refine ⟨62721319626447838971589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 334513704674388474515141 62721319626447838971589)
                  ·
                    refine ⟨11760247429958969807173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62721319626447838971589 11760247429958969807173)
                    ·
                      rfl

theorem cell23_68709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 4, 4].length) (baseStart_68709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68709 prefixEnd_68709 := by exact prefixLift 68709
  have htrace : WordTrace (prefixWord ++ tailWord_68709) baseStart_68709 baseEnd_68709 := by
    simpa [prefixWord, tailWord_68709, baseEnd_68709] using wordTrace_append hprefix tailTrace_68709
  have hstable : (prefixWord ++ tailWord_68709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68709).length < 2 ^ (prefixWord ++ tailWord_68709).sum := by decide
  have hdescent : baseEnd_68709 < baseStart_68709 := by decide
  rcases family_descends (prefixWord ++ tailWord_68709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68722 : List Nat := [3, 2, 1, 2, 2, 1, 2, 10]
def baseStart_68722 : Nat := 118140960795 + 68722 * 2 ^ 59
def prefixEnd_68722 : Nat := 4983230072969 + 3 ^ 40 * 68722 * 2
def baseEnd_68722 : Nat := 1306941390310568835517

theorem tailTrace_68722 : CollatzResearch.WordTrace tailWord_68722 prefixEnd_68722 1306941390310568835517 := by
  unfold tailWord_68722
  simp only [CollatzResearch.WordTrace]
  refine ⟨626624314259851407074105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1670998171359603752197613 626624314259851407074105)
  ·
    refine ⟨469968235694888555305579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 626624314259851407074105 469968235694888555305579)
    ·
      refine ⟨704952353542332832958369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 469968235694888555305579 704952353542332832958369)
      ·
        refine ⟨528714265156749624718777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 704952353542332832958369 528714265156749624718777)
        ·
          refine ⟨396535698867562218539083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 528714265156749624718777 396535698867562218539083)
          ·
            refine ⟨594803548301343327808625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 396535698867562218539083 594803548301343327808625)
            ·
              refine ⟨446102661226007495856469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 594803548301343327808625 446102661226007495856469)
              ·
                refine ⟨1306941390310568835517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 446102661226007495856469 1306941390310568835517)
                ·
                  rfl

theorem cell23_68722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 10].length) (baseStart_68722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68722 prefixEnd_68722 := by exact prefixLift 68722
  have htrace : WordTrace (prefixWord ++ tailWord_68722) baseStart_68722 baseEnd_68722 := by
    simpa [prefixWord, tailWord_68722, baseEnd_68722] using wordTrace_append hprefix tailTrace_68722
  have hstable : (prefixWord ++ tailWord_68722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68722).length < 2 ^ (prefixWord ++ tailWord_68722).sum := by decide
  have hdescent : baseEnd_68722 < baseStart_68722 := by decide
  rcases family_descends (prefixWord ++ tailWord_68722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68729 : List Nat := [1, 2, 1, 3, 5, 1, 1, 1, 1, 1, 6]
def baseStart_68729 : Nat := 118140960795 + 68729 * 2 ^ 59
def prefixEnd_68729 : Nat := 4983230072969 + 3 ^ 40 * 68729 * 2
def baseEnd_68729 : Nat := 35291011902966831171427

theorem tailTrace_68729 : CollatzResearch.WordTrace tailWord_68729 prefixEnd_68729 35291011902966831171427 := by
  unfold tailWord_68729
  simp only [CollatzResearch.WordTrace]
  refine ⟨2506752568014045823801241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1671168378676030549200827 2506752568014045823801241)
  ·
    refine ⟨1880064426010534367850931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2506752568014045823801241 1880064426010534367850931)
    ·
      refine ⟨2820096639015801551776397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1880064426010534367850931 2820096639015801551776397)
      ·
        refine ⟨1057536239630925581916149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2820096639015801551776397 1057536239630925581916149)
        ·
          refine ⟨99144022465399273304639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1057536239630925581916149 99144022465399273304639)
          ·
            refine ⟨148716033698098909956959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99144022465399273304639 148716033698098909956959)
            ·
              refine ⟨223074050547148364935439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148716033698098909956959 223074050547148364935439)
              ·
                refine ⟨334611075820722547403159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223074050547148364935439 334611075820722547403159)
                ·
                  refine ⟨501916613731083821104739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 334611075820722547403159 501916613731083821104739)
                  ·
                    refine ⟨752874920596625731657109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 501916613731083821104739 752874920596625731657109)
                    ·
                      refine ⟨35291011902966831171427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 752874920596625731657109 35291011902966831171427)
                      ·
                        rfl

theorem cell23_68729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_68729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68729 prefixEnd_68729 := by exact prefixLift 68729
  have htrace : WordTrace (prefixWord ++ tailWord_68729) baseStart_68729 baseEnd_68729 := by
    simpa [prefixWord, tailWord_68729, baseEnd_68729] using wordTrace_append hprefix tailTrace_68729
  have hstable : (prefixWord ++ tailWord_68729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68729).length < 2 ^ (prefixWord ++ tailWord_68729).sum := by decide
  have hdescent : baseEnd_68729 < baseStart_68729 := by decide
  rcases family_descends (prefixWord ++ tailWord_68729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68767 : List Nat := [1, 1, 2, 6, 3, 1, 1, 1, 3, 2, 2]
def baseStart_68767 : Nat := 118140960795 + 68767 * 2 ^ 59
def prefixEnd_68767 : Nat := 4983230072969 + 3 ^ 40 * 68767 * 2
def baseEnd_68767 : Nat := 35310524167837682496253

theorem tailTrace_68767 : CollatzResearch.WordTrace tailWord_68767 prefixEnd_68767 35310524167837682496253 := by
  unfold tailWord_68767
  simp only [CollatzResearch.WordTrace]
  refine ⟨2508138541876378313684555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1672092361250918875789703 2508138541876378313684555)
  ·
    refine ⟨3762207812814567470526833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2508138541876378313684555 3762207812814567470526833)
    ·
      refine ⟨2821655859610925602895125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3762207812814567470526833 2821655859610925602895125)
      ·
        refine ⟨132265118419262137635709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2821655859610925602895125 132265118419262137635709)
        ·
          refine ⟨49599419407223301613391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132265118419262137635709 49599419407223301613391)
          ·
            refine ⟨74399129110834952420087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49599419407223301613391 74399129110834952420087)
            ·
              refine ⟨111598693666252428630131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74399129110834952420087 111598693666252428630131)
              ·
                refine ⟨167398040499378642945197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111598693666252428630131 167398040499378642945197)
                ·
                  refine ⟨62774265187266991104449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 167398040499378642945197 62774265187266991104449)
                  ·
                    refine ⟨47080698890450243328337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 62774265187266991104449 47080698890450243328337)
                    ·
                      refine ⟨35310524167837682496253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 47080698890450243328337 35310524167837682496253)
                      ·
                        rfl

theorem cell23_68767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_68767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68767 prefixEnd_68767 := by exact prefixLift 68767
  have htrace : WordTrace (prefixWord ++ tailWord_68767) baseStart_68767 baseEnd_68767 := by
    simpa [prefixWord, tailWord_68767, baseEnd_68767] using wordTrace_append hprefix tailTrace_68767
  have hstable : (prefixWord ++ tailWord_68767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68767).length < 2 ^ (prefixWord ++ tailWord_68767).sum := by decide
  have hdescent : baseEnd_68767 < baseStart_68767 := by decide
  rcases family_descends (prefixWord ++ tailWord_68767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68783 : List Nat := [1, 1, 2, 1, 2, 3, 6, 1, 2, 1, 3]
def baseStart_68783 : Nat := 118140960795 + 68783 * 2 ^ 59
def prefixEnd_68783 : Nat := 4983230072969 + 3 ^ 40 * 68783 * 2
def baseEnd_68783 : Nat := 35318739858309619896179

theorem tailTrace_68783 : CollatzResearch.WordTrace tailWord_68783 prefixEnd_68783 35318739858309619896179 := by
  unfold tailWord_68783
  simp only [CollatzResearch.WordTrace]
  refine ⟨2508722109818413046267003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1672481406545608697511335 2508722109818413046267003)
  ·
    refine ⟨3763083164727619569400505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2508722109818413046267003 3763083164727619569400505)
    ·
      refine ⟨2822312373545714677050379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3763083164727619569400505 2822312373545714677050379)
      ·
        refine ⟨4233468560318572015575569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2822312373545714677050379 4233468560318572015575569)
        ·
          refine ⟨3175101420238929011681677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4233468560318572015575569 3175101420238929011681677)
          ·
            refine ⟨1190663032589598379380629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3175101420238929011681677 1190663032589598379380629)
            ·
              refine ⟨55812329652637424033467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1190663032589598379380629 55812329652637424033467)
              ·
                refine ⟨83718494478956136050201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55812329652637424033467 83718494478956136050201)
                ·
                  refine ⟨62788870859217102037651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83718494478956136050201 62788870859217102037651)
                  ·
                    refine ⟨94183306288825653056477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62788870859217102037651 94183306288825653056477)
                    ·
                      refine ⟨35318739858309619896179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 94183306288825653056477 35318739858309619896179)
                      ·
                        rfl

theorem cell23_68783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 2, 1, 3].length) (baseStart_68783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68783 prefixEnd_68783 := by exact prefixLift 68783
  have htrace : WordTrace (prefixWord ++ tailWord_68783) baseStart_68783 baseEnd_68783 := by
    simpa [prefixWord, tailWord_68783, baseEnd_68783] using wordTrace_append hprefix tailTrace_68783
  have hstable : (prefixWord ++ tailWord_68783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68783).length < 2 ^ (prefixWord ++ tailWord_68783).sum := by decide
  have hdescent : baseEnd_68783 < baseStart_68783 := by decide
  rcases family_descends (prefixWord ++ tailWord_68783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68793 : List Nat := [1, 2, 1, 4, 1, 3, 3, 2, 1, 3, 2]
def baseStart_68793 : Nat := 118140960795 + 68793 * 2 ^ 59
def prefixEnd_68793 : Nat := 4983230072969 + 3 ^ 40 * 68793 * 2
def baseEnd_68793 : Nat := 35323874664854580771133

theorem tailTrace_68793 : CollatzResearch.WordTrace tailWord_68793 prefixEnd_68793 35323874664854580771133 := by
  unfold tailWord_68793
  simp only [CollatzResearch.WordTrace]
  refine ⟨2509086839782184754131033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1672724559854789836087355 2509086839782184754131033)
  ·
    refine ⟨1881815129836638565598275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2509086839782184754131033 1881815129836638565598275)
    ·
      refine ⟨2822722694754957848397413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1881815129836638565598275 2822722694754957848397413)
      ·
        refine ⟨529260505266554596574515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2822722694754957848397413 529260505266554596574515)
        ·
          refine ⟨793890757899831894861773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529260505266554596574515 793890757899831894861773)
          ·
            refine ⟨297709034212436960573165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 793890757899831894861773 297709034212436960573165)
            ·
              refine ⟨111640887829663860214937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 297709034212436960573165 111640887829663860214937)
              ·
                refine ⟨83730665872247895161203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111640887829663860214937 83730665872247895161203)
                ·
                  refine ⟨125595998808371842741805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83730665872247895161203 125595998808371842741805)
                  ·
                    refine ⟨47098499553139441028177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 125595998808371842741805 47098499553139441028177)
                    ·
                      refine ⟨35323874664854580771133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 47098499553139441028177 35323874664854580771133)
                      ·
                        rfl

theorem cell23_68793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_68793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68793 prefixEnd_68793 := by exact prefixLift 68793
  have htrace : WordTrace (prefixWord ++ tailWord_68793) baseStart_68793 baseEnd_68793 := by
    simpa [prefixWord, tailWord_68793, baseEnd_68793] using wordTrace_append hprefix tailTrace_68793
  have hstable : (prefixWord ++ tailWord_68793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68793).length < 2 ^ (prefixWord ++ tailWord_68793).sum := by decide
  have hdescent : baseEnd_68793 < baseStart_68793 := by decide
  rcases family_descends (prefixWord ++ tailWord_68793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68810 : List Nat := [3, 1, 2, 1, 3, 3, 3, 1, 1, 3, 2]
def baseStart_68810 : Nat := 118140960795 + 68810 * 2 ^ 59
def prefixEnd_68810 : Nat := 4983230072969 + 3 ^ 40 * 68810 * 2
def baseEnd_68810 : Nat := 35332603835981014258555

theorem tailTrace_68810 : CollatzResearch.WordTrace tailWord_68810 prefixEnd_68810 35332603835981014258555 := by
  unfold tailWord_68810
  simp only [CollatzResearch.WordTrace]
  refine ⟨627426720180149164374971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1673137920480397771666589 627426720180149164374971)
  ·
    refine ⟨941140080270223746562457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 627426720180149164374971 941140080270223746562457)
    ·
      refine ⟨705855060202667809921843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 941140080270223746562457 705855060202667809921843)
      ·
        refine ⟨1058782590304001714882765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 705855060202667809921843 1058782590304001714882765)
        ·
          refine ⟨397043471364000643081037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1058782590304001714882765 397043471364000643081037)
          ·
            refine ⟨148891301761500241155389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 397043471364000643081037 148891301761500241155389)
            ·
              refine ⟨55834238160562590433271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148891301761500241155389 55834238160562590433271)
              ·
                refine ⟨83751357240843885649907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55834238160562590433271 83751357240843885649907)
                ·
                  refine ⟨125627035861265828474861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83751357240843885649907 125627035861265828474861)
                  ·
                    refine ⟨47110138447974685678073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 125627035861265828474861 47110138447974685678073)
                    ·
                      refine ⟨35332603835981014258555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 47110138447974685678073 35332603835981014258555)
                      ·
                        rfl

theorem cell23_68810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 1, 3, 2].length) (baseStart_68810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68810 prefixEnd_68810 := by exact prefixLift 68810
  have htrace : WordTrace (prefixWord ++ tailWord_68810) baseStart_68810 baseEnd_68810 := by
    simpa [prefixWord, tailWord_68810, baseEnd_68810] using wordTrace_append hprefix tailTrace_68810
  have hstable : (prefixWord ++ tailWord_68810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68810).length < 2 ^ (prefixWord ++ tailWord_68810).sum := by decide
  have hdescent : baseEnd_68810 < baseStart_68810 := by decide
  rcases family_descends (prefixWord ++ tailWord_68810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68823 : List Nat := [1, 1, 3, 2, 1, 2, 3, 4, 2, 2, 2]
def baseStart_68823 : Nat := 118140960795 + 68823 * 2 ^ 59
def prefixEnd_68823 : Nat := 4983230072969 + 3 ^ 40 * 68823 * 2
def baseEnd_68823 : Nat := 35339279084489463395995

theorem tailTrace_68823 : CollatzResearch.WordTrace tailWord_68823 prefixEnd_68823 35339279084489463395995 := by
  unfold tailWord_68823
  simp only [CollatzResearch.WordTrace]
  refine ⟨2510181029673499877723123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1673454019782333251815415 2510181029673499877723123)
  ·
    refine ⟨3765271544510249816584685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2510181029673499877723123 3765271544510249816584685)
    ·
      refine ⟨1411976829191343681219257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3765271544510249816584685 1411976829191343681219257)
      ·
        refine ⟨1058982621893507760914443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1411976829191343681219257 1058982621893507760914443)
        ·
          refine ⟨1588473932840261641371665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1058982621893507760914443 1588473932840261641371665)
          ·
            refine ⟨1191355449630196231028749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1588473932840261641371665 1191355449630196231028749)
            ·
              refine ⟨446758293611323586635781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1191355449630196231028749 446758293611323586635781)
              ·
                refine ⟨83767180052123172494209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 446758293611323586635781 83767180052123172494209)
                ·
                  refine ⟨62825385039092379370657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83767180052123172494209 62825385039092379370657)
                  ·
                    refine ⟨47119038779319284527993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 62825385039092379370657 47119038779319284527993)
                    ·
                      refine ⟨35339279084489463395995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 47119038779319284527993 35339279084489463395995)
                      ·
                        rfl

theorem cell23_68823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 2, 2, 2].length) (baseStart_68823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68823 prefixEnd_68823 := by exact prefixLift 68823
  have htrace : WordTrace (prefixWord ++ tailWord_68823) baseStart_68823 baseEnd_68823 := by
    simpa [prefixWord, tailWord_68823, baseEnd_68823] using wordTrace_append hprefix tailTrace_68823
  have hstable : (prefixWord ++ tailWord_68823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68823).length < 2 ^ (prefixWord ++ tailWord_68823).sum := by decide
  have hdescent : baseEnd_68823 < baseStart_68823 := by decide
  rcases family_descends (prefixWord ++ tailWord_68823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68983 : List Nat := [1, 1, 3, 1, 1, 2, 7, 1, 1, 5]
def baseStart_68983 : Nat := 118140960795 + 68983 * 2 ^ 59
def prefixEnd_68983 : Nat := 4983230072969 + 3 ^ 40 * 68983 * 2
def baseEnd_68983 : Nat := 11807145329736279131753

theorem tailTrace_68983 : CollatzResearch.WordTrace tailWord_68983 prefixEnd_68983 11807145329736279131753 := by
  unfold tailWord_68983
  simp only [CollatzResearch.WordTrace]
  refine ⟨2516016709093847203547603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1677344472729231469031735 2516016709093847203547603)
  ·
    refine ⟨3774025063640770805321405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2516016709093847203547603 3774025063640770805321405)
    ·
      refine ⟨1415259398865289051995527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3774025063640770805321405 1415259398865289051995527)
      ·
        refine ⟨2122889098297933577993291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1415259398865289051995527 2122889098297933577993291)
        ·
          refine ⟨3184333647446900366989937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2122889098297933577993291 3184333647446900366989937)
          ·
            refine ⟨2388250235585175275242453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3184333647446900366989937 2388250235585175275242453)
            ·
              refine ⟨55974614896527545513495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2388250235585175275242453 55974614896527545513495)
              ·
                refine ⟨83961922344791318270243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55974614896527545513495 83961922344791318270243)
                ·
                  refine ⟨125942883517186977405365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83961922344791318270243 125942883517186977405365)
                  ·
                    refine ⟨11807145329736279131753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 125942883517186977405365 11807145329736279131753)
                    ·
                      rfl

theorem cell23_68983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 1, 5].length) (baseStart_68983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68983 prefixEnd_68983 := by exact prefixLift 68983
  have htrace : WordTrace (prefixWord ++ tailWord_68983) baseStart_68983 baseEnd_68983 := by
    simpa [prefixWord, tailWord_68983, baseEnd_68983] using wordTrace_append hprefix tailTrace_68983
  have hstable : (prefixWord ++ tailWord_68983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68983).length < 2 ^ (prefixWord ++ tailWord_68983).sum := by decide
  have hdescent : baseEnd_68983 < baseStart_68983 := by decide
  rcases family_descends (prefixWord ++ tailWord_68983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68997 : List Nat := [1, 3, 1, 1, 3, 1, 6, 2, 1, 1, 3]
def baseStart_68997 : Nat := 118140960795 + 68997 * 2 ^ 59
def prefixEnd_68997 : Nat := 4983230072969 + 3 ^ 40 * 68997 * 2
def baseEnd_68997 : Nat := 35428624718371782620195

theorem tailTrace_68997 : CollatzResearch.WordTrace tailWord_68997 prefixEnd_68997 35428624718371782620195 := by
  unfold tailWord_68997
  simp only [CollatzResearch.WordTrace]
  refine ⟨2516527331043127594557245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1677684887362085063038163 2516527331043127594557245)
  ·
    refine ⟨943697749141172847958967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2516527331043127594557245 943697749141172847958967)
    ·
      refine ⟨1415546623711759271938451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 943697749141172847958967 1415546623711759271938451)
      ·
        refine ⟨2123319935567638907907677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1415546623711759271938451 2123319935567638907907677)
        ·
          refine ⟨796244975837864590465379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2123319935567638907907677 796244975837864590465379)
          ·
            refine ⟨1194367463756796885698069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 796244975837864590465379 1194367463756796885698069)
            ·
              refine ⟨55985974863599854017097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1194367463756796885698069 55985974863599854017097)
              ·
                refine ⟨41989481147699890512823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55985974863599854017097 41989481147699890512823)
                ·
                  refine ⟨62984221721549835769235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41989481147699890512823 62984221721549835769235)
                  ·
                    refine ⟨94476332582324753653853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62984221721549835769235 94476332582324753653853)
                    ·
                      refine ⟨35428624718371782620195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 94476332582324753653853 35428624718371782620195)
                      ·
                        rfl

theorem cell23_68997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 2, 1, 1, 3].length) (baseStart_68997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_68997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_68997 prefixEnd_68997 := by exact prefixLift 68997
  have htrace : WordTrace (prefixWord ++ tailWord_68997) baseStart_68997 baseEnd_68997 := by
    simpa [prefixWord, tailWord_68997, baseEnd_68997] using wordTrace_append hprefix tailTrace_68997
  have hstable : (prefixWord ++ tailWord_68997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68997).length < 2 ^ (prefixWord ++ tailWord_68997).sum := by decide
  have hdescent : baseEnd_68997 < baseStart_68997 := by decide
  rcases family_descends (prefixWord ++ tailWord_68997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69013 : List Nat := [1, 3, 2, 1, 1, 2, 4, 3, 2, 4]
def baseStart_69013 : Nat := 118140960795 + 69013 * 2 ^ 59
def prefixEnd_69013 : Nat := 4983230072969 + 3 ^ 40 * 69013 * 2
def baseEnd_69013 : Nat := 11812280136281240006707

theorem tailTrace_69013 : CollatzResearch.WordTrace tailWord_69013 prefixEnd_69013 11812280136281240006707 := by
  unfold tailWord_69013
  simp only [CollatzResearch.WordTrace]
  refine ⟨2517110898985162327139693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1678073932656774884759795 2517110898985162327139693)
  ·
    refine ⟨943916587119435872677385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2517110898985162327139693 943916587119435872677385)
    ·
      refine ⟨707937440339576904508039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 943916587119435872677385 707937440339576904508039)
      ·
        refine ⟨1061906160509365356762059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 707937440339576904508039 1061906160509365356762059)
        ·
          refine ⟨1592859240764048035143089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1061906160509365356762059 1592859240764048035143089)
          ·
            refine ⟨1194644430573036026357317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1592859240764048035143089 1194644430573036026357317)
            ·
              refine ⟨223995830732444254941997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1194644430573036026357317 223995830732444254941997)
              ·
                refine ⟨83998436524666595603249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 223995830732444254941997 83998436524666595603249)
                ·
                  refine ⟨62998827393499946702437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83998436524666595603249 62998827393499946702437)
                  ·
                    refine ⟨11812280136281240006707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62998827393499946702437 11812280136281240006707)
                    ·
                      rfl

theorem cell23_69013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_69013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69013 prefixEnd_69013 := by exact prefixLift 69013
  have htrace : WordTrace (prefixWord ++ tailWord_69013) baseStart_69013 baseEnd_69013 := by
    simpa [prefixWord, tailWord_69013, baseEnd_69013] using wordTrace_append hprefix tailTrace_69013
  have hstable : (prefixWord ++ tailWord_69013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69013).length < 2 ^ (prefixWord ++ tailWord_69013).sum := by decide
  have hdescent : baseEnd_69013 < baseStart_69013 := by decide
  rcases family_descends (prefixWord ++ tailWord_69013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69023 : List Nat := [1, 1, 2, 5, 1, 2, 2, 1, 3, 2, 3]
def baseStart_69023 : Nat := 118140960795 + 69023 * 2 ^ 59
def prefixEnd_69023 : Nat := 4983230072969 + 3 ^ 40 * 69023 * 2
def baseEnd_69023 : Nat := 35441975215388680895075

theorem tailTrace_69023 : CollatzResearch.WordTrace tailWord_69023 prefixEnd_69023 35441975215388680895075 := by
  unfold tailWord_69023
  simp only [CollatzResearch.WordTrace]
  refine ⟨2517475628948934035003723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1678317085965956023335815 2517475628948934035003723)
  ·
    refine ⟨3776213443423401052505585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2517475628948934035003723 3776213443423401052505585)
    ·
      refine ⟨2832160082567550789379189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3776213443423401052505585 2832160082567550789379189)
      ·
        refine ⟨265515007740707886504299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2832160082567550789379189 265515007740707886504299)
        ·
          refine ⟨398272511611061829756449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265515007740707886504299 398272511611061829756449)
          ·
            refine ⟨298704383708296372317337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 398272511611061829756449 298704383708296372317337)
            ·
              refine ⟨224028287781222279238003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 298704383708296372317337 224028287781222279238003)
              ·
                refine ⟨336042431671833418857005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224028287781222279238003 336042431671833418857005)
                ·
                  refine ⟨126015911876937532071377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 336042431671833418857005 126015911876937532071377)
                  ·
                    refine ⟨94511933907703149053533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 126015911876937532071377 94511933907703149053533)
                    ·
                      refine ⟨35441975215388680895075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 94511933907703149053533 35441975215388680895075)
                      ·
                        rfl

theorem cell23_69023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_69023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69023 prefixEnd_69023 := by exact prefixLift 69023
  have htrace : WordTrace (prefixWord ++ tailWord_69023) baseStart_69023 baseEnd_69023 := by
    simpa [prefixWord, tailWord_69023, baseEnd_69023] using wordTrace_append hprefix tailTrace_69023
  have hstable : (prefixWord ++ tailWord_69023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69023).length < 2 ^ (prefixWord ++ tailWord_69023).sum := by decide
  have hdescent : baseEnd_69023 < baseStart_69023 := by decide
  rcases family_descends (prefixWord ++ tailWord_69023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69037 : List Nat := [1, 5, 2, 2, 1, 1, 4, 1, 1, 1, 4]
def baseStart_69037 : Nat := 118140960795 + 69037 * 2 ^ 59
def prefixEnd_69037 : Nat := 4983230072969 + 3 ^ 40 * 69037 * 2
def baseEnd_69037 : Nat := 35449163944551626120011

theorem tailTrace_69037 : CollatzResearch.WordTrace tailWord_69037 prefixEnd_69037 35449163944551626120011 := by
  unfold tailWord_69037
  simp only [CollatzResearch.WordTrace]
  refine ⟨2517986250898214426013365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1678657500598809617342243 2517986250898214426013365)
  ·
    refine ⟨236061211021707602438753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2517986250898214426013365 236061211021707602438753)
    ·
      refine ⟨177045908266280701829065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236061211021707602438753 177045908266280701829065)
      ·
        refine ⟨132784431199710526371799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177045908266280701829065 132784431199710526371799)
        ·
          refine ⟨199176646799565789557699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132784431199710526371799 199176646799565789557699)
          ·
            refine ⟨298764970199348684336549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199176646799565789557699 298764970199348684336549)
            ·
              refine ⟨56018431912377878313103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 298764970199348684336549 56018431912377878313103)
              ·
                refine ⟨84027647868566817469655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56018431912377878313103 84027647868566817469655)
                ·
                  refine ⟨126041471802850226204483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84027647868566817469655 126041471802850226204483)
                  ·
                    refine ⟨189062207704275339306725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 126041471802850226204483 189062207704275339306725)
                    ·
                      refine ⟨35449163944551626120011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 189062207704275339306725 35449163944551626120011)
                      ·
                        rfl

theorem cell23_69037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_69037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69037 prefixEnd_69037 := by exact prefixLift 69037
  have htrace : WordTrace (prefixWord ++ tailWord_69037) baseStart_69037 baseEnd_69037 := by
    simpa [prefixWord, tailWord_69037, baseEnd_69037] using wordTrace_append hprefix tailTrace_69037
  have hstable : (prefixWord ++ tailWord_69037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69037).length < 2 ^ (prefixWord ++ tailWord_69037).sum := by decide
  have hdescent : baseEnd_69037 < baseStart_69037 := by decide
  rcases family_descends (prefixWord ++ tailWord_69037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69070 : List Nat := [4, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3]
def baseStart_69070 : Nat := 118140960795 + 69070 * 2 ^ 59
def prefixEnd_69070 : Nat := 4983230072969 + 3 ^ 40 * 69070 * 2
def baseEnd_69070 : Nat := 35466108806149997007359

theorem tailTrace_69070 : CollatzResearch.WordTrace tailWord_69070 prefixEnd_69070 35466108806149997007359 := by
  unfold tailWord_69070
  simp only [CollatzResearch.WordTrace]
  refine ⟨314898732472332632745583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1679459906519107374643109 314898732472332632745583)
  ·
    refine ⟨472348098708498949118375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 314898732472332632745583 472348098708498949118375)
    ·
      refine ⟨708522148062748423677563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 472348098708498949118375 708522148062748423677563)
      ·
        refine ⟨1062783222094122635516345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 708522148062748423677563 1062783222094122635516345)
        ·
          refine ⟨797087416570591976637259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1062783222094122635516345 797087416570591976637259)
          ·
            refine ⟨1195631124855887964955889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 797087416570591976637259 1195631124855887964955889)
            ·
              refine ⟨896723343641915973716917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1195631124855887964955889 896723343641915973716917)
              ·
                refine ⟨84067813466429622535961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 896723343641915973716917 84067813466429622535961)
                ·
                  refine ⟨63050860099822216901971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84067813466429622535961 63050860099822216901971)
                  ·
                    refine ⟨94576290149733325352957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63050860099822216901971 94576290149733325352957)
                    ·
                      refine ⟨35466108806149997007359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 94576290149733325352957 35466108806149997007359)
                      ·
                        rfl

theorem cell23_69070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3].length) (baseStart_69070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69070 prefixEnd_69070 := by exact prefixLift 69070
  have htrace : WordTrace (prefixWord ++ tailWord_69070) baseStart_69070 baseEnd_69070 := by
    simpa [prefixWord, tailWord_69070, baseEnd_69070] using wordTrace_append hprefix tailTrace_69070
  have hstable : (prefixWord ++ tailWord_69070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69070).length < 2 ^ (prefixWord ++ tailWord_69070).sum := by decide
  have hdescent : baseEnd_69070 < baseStart_69070 := by decide
  rcases family_descends (prefixWord ++ tailWord_69070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69080 : List Nat := [2, 1, 2, 2, 2, 1, 3, 4, 1, 3, 2]
def baseStart_69080 : Nat := 118140960795 + 69080 * 2 ^ 59
def prefixEnd_69080 : Nat := 4983230072969 + 3 ^ 40 * 69080 * 2
def baseEnd_69080 : Nat := 35471243612694957882313

theorem tailTrace_69080 : CollatzResearch.WordTrace tailWord_69080 prefixEnd_69080 35471243612694957882313 := by
  unfold tailWord_69080
  simp only [CollatzResearch.WordTrace]
  refine ⟨1259777294871216384914347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1679703059828288513219129 1259777294871216384914347)
  ·
    refine ⟨1889665942306824577371521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1259777294871216384914347 1889665942306824577371521)
    ·
      refine ⟨1417249456730118433028641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1889665942306824577371521 1417249456730118433028641)
      ·
        refine ⟨1062937092547588824771481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1417249456730118433028641 1062937092547588824771481)
        ·
          refine ⟨797202819410691618578611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1062937092547588824771481 797202819410691618578611)
          ·
            refine ⟨1195804229116037427867917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 797202819410691618578611 1195804229116037427867917)
            ·
              refine ⟨448426585918514035450469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1195804229116037427867917 448426585918514035450469)
              ·
                refine ⟨84079984859721381646963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 448426585918514035450469 84079984859721381646963)
                ·
                  refine ⟨126119977289582072470445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84079984859721381646963 126119977289582072470445)
                  ·
                    refine ⟨47294991483593277176417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 126119977289582072470445 47294991483593277176417)
                    ·
                      refine ⟨35471243612694957882313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 47294991483593277176417 35471243612694957882313)
                      ·
                        rfl

theorem cell23_69080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 1, 3, 2].length) (baseStart_69080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69080 prefixEnd_69080 := by exact prefixLift 69080
  have htrace : WordTrace (prefixWord ++ tailWord_69080) baseStart_69080 baseEnd_69080 := by
    simpa [prefixWord, tailWord_69080, baseEnd_69080] using wordTrace_append hprefix tailTrace_69080
  have hstable : (prefixWord ++ tailWord_69080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69080).length < 2 ^ (prefixWord ++ tailWord_69080).sum := by decide
  have hdescent : baseEnd_69080 < baseStart_69080 := by decide
  rcases family_descends (prefixWord ++ tailWord_69080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69121 : List Nat := [1, 2, 4, 1, 5, 1, 2, 1, 2, 1, 3]
def baseStart_69121 : Nat := 118140960795 + 69121 * 2 ^ 59
def prefixEnd_69121 : Nat := 4983230072969 + 3 ^ 40 * 69121 * 2
def baseEnd_69121 : Nat := 35492296319529297469625

theorem tailTrace_69121 : CollatzResearch.WordTrace tailWord_69121 prefixEnd_69121 35492296319529297469625 := by
  unfold tailWord_69121
  simp only [CollatzResearch.WordTrace]
  refine ⟨2521049982593896772071217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1680699988395931181380811 2521049982593896772071217)
  ·
    refine ⟨1890787486945422579053413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2521049982593896772071217 1890787486945422579053413)
    ·
      refine ⟨354522653802266733572515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1890787486945422579053413 354522653802266733572515)
      ·
        refine ⟨531783980703400100358773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354522653802266733572515 531783980703400100358773)
        ·
          refine ⟨49854748190943759408635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 531783980703400100358773 49854748190943759408635)
          ·
            refine ⟨74782122286415639112953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49854748190943759408635 74782122286415639112953)
            ·
              refine ⟨56086591714811729334715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74782122286415639112953 56086591714811729334715)
              ·
                refine ⟨84129887572217594002073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56086591714811729334715 84129887572217594002073)
                ·
                  refine ⟨63097415679163195501555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84129887572217594002073 63097415679163195501555)
                  ·
                    refine ⟨94646123518744793252333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63097415679163195501555 94646123518744793252333)
                    ·
                      refine ⟨35492296319529297469625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 94646123518744793252333 35492296319529297469625)
                      ·
                        rfl

theorem cell23_69121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_69121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69121 prefixEnd_69121 := by exact prefixLift 69121
  have htrace : WordTrace (prefixWord ++ tailWord_69121) baseStart_69121 baseEnd_69121 := by
    simpa [prefixWord, tailWord_69121, baseEnd_69121] using wordTrace_append hprefix tailTrace_69121
  have hstable : (prefixWord ++ tailWord_69121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69121).length < 2 ^ (prefixWord ++ tailWord_69121).sum := by decide
  have hdescent : baseEnd_69121 < baseStart_69121 := by decide
  rcases family_descends (prefixWord ++ tailWord_69121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69173 : List Nat := [1, 3, 3, 1, 1, 3, 2, 1, 1, 2, 5]
def baseStart_69173 : Nat := 118140960795 + 69173 * 2 ^ 59
def prefixEnd_69173 : Nat := 4983230072969 + 3 ^ 40 * 69173 * 2
def baseEnd_69173 : Nat := 35518997313563094019385

theorem tailTrace_69173 : CollatzResearch.WordTrace tailWord_69173 prefixEnd_69173 35518997313563094019385 := by
  unfold tailWord_69173
  simp only [CollatzResearch.WordTrace]
  refine ⟨2522946578405509652964173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1681964385603673101976115 2522946578405509652964173)
  ·
    refine ⟨946104966902066119861565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2522946578405509652964173 946104966902066119861565)
    ·
      refine ⟨354789362588274794948087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 946104966902066119861565 354789362588274794948087)
      ·
        refine ⟨532184043882412192422131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354789362588274794948087 532184043882412192422131)
        ·
          refine ⟨798276065823618288633197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 532184043882412192422131 798276065823618288633197)
          ·
            refine ⟨299353524683856858237449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 798276065823618288633197 299353524683856858237449)
            ·
              refine ⟨224515143512892643678087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 299353524683856858237449 224515143512892643678087)
              ·
                refine ⟨336772715269338965517131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224515143512892643678087 336772715269338965517131)
                ·
                  refine ⟨505159072904008448275697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 336772715269338965517131 505159072904008448275697)
                  ·
                    refine ⟨378869304678006336206773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 505159072904008448275697 378869304678006336206773)
                    ·
                      refine ⟨35518997313563094019385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 378869304678006336206773 35518997313563094019385)
                      ·
                        rfl

theorem cell23_69173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_69173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69173 prefixEnd_69173 := by exact prefixLift 69173
  have htrace : WordTrace (prefixWord ++ tailWord_69173) baseStart_69173 baseEnd_69173 := by
    simpa [prefixWord, tailWord_69173, baseEnd_69173] using wordTrace_append hprefix tailTrace_69173
  have hstable : (prefixWord ++ tailWord_69173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69173).length < 2 ^ (prefixWord ++ tailWord_69173).sum := by decide
  have hdescent : baseEnd_69173 < baseStart_69173 := by decide
  rcases family_descends (prefixWord ++ tailWord_69173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69203 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 8, 2, 3]
def baseStart_69203 : Nat := 118140960795 + 69203 * 2 ^ 59
def prefixEnd_69203 : Nat := 4983230072969 + 3 ^ 40 * 69203 * 2
def baseEnd_69203 : Nat := 35534401733197976644247

theorem tailTrace_69203 : CollatzResearch.WordTrace tailWord_69203 prefixEnd_69203 35534401733197976644247 := by
  unfold tailWord_69203
  simp only [CollatzResearch.WordTrace]
  refine ⟨2524040768296824776556263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1682693845531216517704175 2524040768296824776556263)
  ·
    refine ⟨3786061152445237164834395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2524040768296824776556263 3786061152445237164834395)
    ·
      refine ⟨5679091728667855747251593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3786061152445237164834395 5679091728667855747251593)
      ·
        refine ⟨4259318796500891810438695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5679091728667855747251593 4259318796500891810438695)
        ·
          refine ⟨6388978194751337715658043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4259318796500891810438695 6388978194751337715658043)
          ·
            refine ⟨9583467292127006573487065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6388978194751337715658043 9583467292127006573487065)
            ·
              refine ⟨7187600469095254930115299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9583467292127006573487065 7187600469095254930115299)
              ·
                refine ⟨10781400703642882395172949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7187600469095254930115299 10781400703642882395172949)
                ·
                  refine ⟨126344539495815028068433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10781400703642882395172949 126344539495815028068433)
                  ·
                    refine ⟨94758404621861271051325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 126344539495815028068433 94758404621861271051325)
                    ·
                      refine ⟨35534401733197976644247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 94758404621861271051325 35534401733197976644247)
                      ·
                        rfl

theorem cell23_69203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 2, 3].length) (baseStart_69203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69203 prefixEnd_69203 := by exact prefixLift 69203
  have htrace : WordTrace (prefixWord ++ tailWord_69203) baseStart_69203 baseEnd_69203 := by
    simpa [prefixWord, tailWord_69203, baseEnd_69203] using wordTrace_append hprefix tailTrace_69203
  have hstable : (prefixWord ++ tailWord_69203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69203).length < 2 ^ (prefixWord ++ tailWord_69203).sum := by decide
  have hdescent : baseEnd_69203 < baseStart_69203 := by decide
  rcases family_descends (prefixWord ++ tailWord_69203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69260 : List Nat := [2, 2, 1, 2, 1, 1, 3, 3, 1, 5, 2]
def baseStart_69260 : Nat := 118140960795 + 69260 * 2 ^ 59
def prefixEnd_69260 : Nat := 4983230072969 + 3 ^ 40 * 69260 * 2
def baseEnd_69260 : Nat := 35563670130504253631485

theorem tailTrace_69260 : CollatzResearch.WordTrace tailWord_69260 prefixEnd_69260 35563670130504253631485 := by
  unfold tailWord_69260
  simp only [CollatzResearch.WordTrace]
  refine ⟨1263059864545161755690617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1684079819393549007587489 1263059864545161755690617)
  ·
    refine ⟨947294898408871316767963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1263059864545161755690617 947294898408871316767963)
    ·
      refine ⟨1420942347613306975151945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 947294898408871316767963 1420942347613306975151945)
      ·
        refine ⟨1065706760709980231363959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1420942347613306975151945 1065706760709980231363959)
        ·
          refine ⟨1598560141064970347045939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1065706760709980231363959 1598560141064970347045939)
          ·
            refine ⟨2397840211597455520568909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1598560141064970347045939 2397840211597455520568909)
            ·
              refine ⟨899190079349045820213341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2397840211597455520568909 899190079349045820213341)
              ·
                refine ⟨337196279755892182580003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 899190079349045820213341 337196279755892182580003)
                ·
                  refine ⟨505794419633838273870005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 337196279755892182580003 505794419633838273870005)
                  ·
                    refine ⟨47418226840672338175313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 505794419633838273870005 47418226840672338175313)
                    ·
                      refine ⟨35563670130504253631485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 47418226840672338175313 35563670130504253631485)
                      ·
                        rfl

theorem cell23_69260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 1, 5, 2].length) (baseStart_69260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69260 prefixEnd_69260 := by exact prefixLift 69260
  have htrace : WordTrace (prefixWord ++ tailWord_69260) baseStart_69260 baseEnd_69260 := by
    simpa [prefixWord, tailWord_69260, baseEnd_69260] using wordTrace_append hprefix tailTrace_69260
  have hstable : (prefixWord ++ tailWord_69260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69260).length < 2 ^ (prefixWord ++ tailWord_69260).sum := by decide
  have hdescent : baseEnd_69260 < baseStart_69260 := by decide
  rcases family_descends (prefixWord ++ tailWord_69260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69284 : List Nat := [2, 3, 1, 2, 2, 4, 1, 1, 3, 1, 3]
def baseStart_69284 : Nat := 118140960795 + 69284 * 2 ^ 59
def prefixEnd_69284 : Nat := 4983230072969 + 3 ^ 40 * 69284 * 2
def baseEnd_69284 : Nat := 35575993666212159731375

theorem tailTrace_69284 : CollatzResearch.WordTrace tailWord_69284 prefixEnd_69284 35575993666212159731375 := by
  unfold tailWord_69284
  simp only [CollatzResearch.WordTrace]
  refine ⟨1263497540501687805127453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1684663387335583740169937 1263497540501687805127453)
  ·
    refine ⟨473811577688132926922795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1263497540501687805127453 473811577688132926922795)
    ·
      refine ⟨710717366532199390384193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 473811577688132926922795 710717366532199390384193)
      ·
        refine ⟨533038024899149542788145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 710717366532199390384193 533038024899149542788145)
        ·
          refine ⟨399778518674362157091109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 533038024899149542788145 399778518674362157091109)
          ·
            refine ⟨74958472251442904454583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 399778518674362157091109 74958472251442904454583)
            ·
              refine ⟨112437708377164356681875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74958472251442904454583 112437708377164356681875)
              ·
                refine ⟨168656562565746535022813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112437708377164356681875 168656562565746535022813)
                ·
                  refine ⟨63246210962154950633555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 168656562565746535022813 63246210962154950633555)
                  ·
                    refine ⟨94869316443232425950333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63246210962154950633555 94869316443232425950333)
                    ·
                      refine ⟨35575993666212159731375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 94869316443232425950333 35575993666212159731375)
                      ·
                        rfl

theorem cell23_69284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_69284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69284 prefixEnd_69284 := by exact prefixLift 69284
  have htrace : WordTrace (prefixWord ++ tailWord_69284) baseStart_69284 baseEnd_69284 := by
    simpa [prefixWord, tailWord_69284, baseEnd_69284] using wordTrace_append hprefix tailTrace_69284
  have hstable : (prefixWord ++ tailWord_69284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69284).length < 2 ^ (prefixWord ++ tailWord_69284).sum := by decide
  have hdescent : baseEnd_69284 < baseStart_69284 := by decide
  rcases family_descends (prefixWord ++ tailWord_69284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69307 : List Nat := [1, 1, 1, 1, 1, 2, 3, 6, 3, 2, 2]
def baseStart_69307 : Nat := 118140960795 + 69307 * 2 ^ 59
def prefixEnd_69307 : Nat := 4983230072969 + 3 ^ 40 * 69307 * 2
def baseEnd_69307 : Nat := 35587803721265569743769

theorem tailTrace_69307 : CollatzResearch.WordTrace tailWord_69307 prefixEnd_69307 35587803721265569743769 := by
  unfold tailWord_69307
  simp only [CollatzResearch.WordTrace]
  refine ⟨2527833959920050538342175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1685222639946700358894783 2527833959920050538342175)
  ·
    refine ⟨3791750939880075807513263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2527833959920050538342175 3791750939880075807513263)
    ·
      refine ⟨5687626409820113711269895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3791750939880075807513263 5687626409820113711269895)
      ·
        refine ⟨8531439614730170566904843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5687626409820113711269895 8531439614730170566904843)
        ·
          refine ⟨12797159422095255850357265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8531439614730170566904843 12797159422095255850357265)
          ·
            refine ⟨9597869566571441887767949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12797159422095255850357265 9597869566571441887767949)
            ·
              refine ⟨3599201087464290707912981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9597869566571441887767949 3599201087464290707912981)
              ·
                refine ⟨168712550974888626933421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3599201087464290707912981 168712550974888626933421)
                ·
                  refine ⟨63267206615583235100033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 168712550974888626933421 63267206615583235100033)
                  ·
                    refine ⟨47450404961687426325025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 63267206615583235100033 47450404961687426325025)
                    ·
                      refine ⟨35587803721265569743769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 47450404961687426325025 35587803721265569743769)
                      ·
                        rfl

theorem cell23_69307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 3, 2, 2].length) (baseStart_69307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69307 prefixEnd_69307 := by exact prefixLift 69307
  have htrace : WordTrace (prefixWord ++ tailWord_69307) baseStart_69307 baseEnd_69307 := by
    simpa [prefixWord, tailWord_69307, baseEnd_69307] using wordTrace_append hprefix tailTrace_69307
  have hstable : (prefixWord ++ tailWord_69307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69307).length < 2 ^ (prefixWord ++ tailWord_69307).sum := by decide
  have hdescent : baseEnd_69307 < baseStart_69307 := by decide
  rcases family_descends (prefixWord ++ tailWord_69307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69320 : List Nat := [2, 1, 3, 1, 2, 2, 3, 2, 1, 2, 4]
def baseStart_69320 : Nat := 118140960795 + 69320 * 2 ^ 59
def prefixEnd_69320 : Nat := 4983230072969 + 3 ^ 40 * 69320 * 2
def baseEnd_69320 : Nat := 35594478969774018881209

theorem tailTrace_69320 : CollatzResearch.WordTrace tailWord_69320 prefixEnd_69320 35594478969774018881209 := by
  unfold tailWord_69320
  simp only [CollatzResearch.WordTrace]
  refine ⟨1264154054436476879282707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1685538739248635839043609 1264154054436476879282707)
  ·
    refine ⟨1896231081654715318924061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1264154054436476879282707 1896231081654715318924061)
    ·
      refine ⟨711086655620518244596523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1896231081654715318924061 711086655620518244596523)
      ·
        refine ⟨1066629983430777366894785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 711086655620518244596523 1066629983430777366894785)
        ·
          refine ⟨799972487573083025171089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1066629983430777366894785 799972487573083025171089)
          ·
            refine ⟨599979365679812268878317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 799972487573083025171089 599979365679812268878317)
            ·
              refine ⟨224992262129929600829369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 599979365679812268878317 224992262129929600829369)
              ·
                refine ⟨168744196597447200622027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 224992262129929600829369 168744196597447200622027)
                ·
                  refine ⟨253116294896170800933041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 168744196597447200622027 253116294896170800933041)
                  ·
                    refine ⟨189837221172128100699781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 253116294896170800933041 189837221172128100699781)
                    ·
                      refine ⟨35594478969774018881209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 189837221172128100699781 35594478969774018881209)
                      ·
                        rfl

theorem cell23_69320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_69320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69320 prefixEnd_69320 := by exact prefixLift 69320
  have htrace : WordTrace (prefixWord ++ tailWord_69320) baseStart_69320 baseEnd_69320 := by
    simpa [prefixWord, tailWord_69320, baseEnd_69320] using wordTrace_append hprefix tailTrace_69320
  have hstable : (prefixWord ++ tailWord_69320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69320).length < 2 ^ (prefixWord ++ tailWord_69320).sum := by decide
  have hdescent : baseEnd_69320 < baseStart_69320 := by decide
  rcases family_descends (prefixWord ++ tailWord_69320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69343 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 1, 9]
def baseStart_69343 : Nat := 118140960795 + 69343 * 2 ^ 59
def prefixEnd_69343 : Nat := 4983230072969 + 3 ^ 40 * 69343 * 2
def baseEnd_69343 : Nat := 11868763008275809631201

theorem tailTrace_69343 : CollatzResearch.WordTrace tailWord_69343 prefixEnd_69343 11868763008275809631201 := by
  unfold tailWord_69343
  simp only [CollatzResearch.WordTrace]
  refine ⟨2529146987789628686652683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1686097991859752457768455 2529146987789628686652683)
  ·
    refine ⟨3793720481684443029979025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2529146987789628686652683 3793720481684443029979025)
    ·
      refine ⟨2845290361263332272484269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3793720481684443029979025 2845290361263332272484269)
      ·
        refine ⟨1066983885473749602181601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2845290361263332272484269 1066983885473749602181601)
        ·
          refine ⟨800237914105312201636201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1066983885473749602181601 800237914105312201636201)
          ·
            refine ⟨600178435578984151227151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 800237914105312201636201 600178435578984151227151)
            ·
              refine ⟨900267653368476226840727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 600178435578984151227151 900267653368476226840727)
              ·
                refine ⟨1350401480052714340261091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 900267653368476226840727 1350401480052714340261091)
                ·
                  refine ⟨2025602220079071510391637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1350401480052714340261091 2025602220079071510391637)
                  ·
                    refine ⟨11868763008275809631201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 2025602220079071510391637 11868763008275809631201)
                    ·
                      rfl

theorem cell23_69343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 9].length) (baseStart_69343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69343 prefixEnd_69343 := by exact prefixLift 69343
  have htrace : WordTrace (prefixWord ++ tailWord_69343) baseStart_69343 baseEnd_69343 := by
    simpa [prefixWord, tailWord_69343, baseEnd_69343] using wordTrace_append hprefix tailTrace_69343
  have hstable : (prefixWord ++ tailWord_69343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69343).length < 2 ^ (prefixWord ++ tailWord_69343).sum := by decide
  have hdescent : baseEnd_69343 < baseStart_69343 := by decide
  rcases family_descends (prefixWord ++ tailWord_69343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69347 : List Nat := [1, 1, 1, 7, 2, 2, 1, 8]
def baseStart_69347 : Nat := 118140960795 + 69347 * 2 ^ 59
def prefixEnd_69347 : Nat := 4983230072969 + 3 ^ 40 * 69347 * 2
def baseEnd_69347 : Nat := 1318827516572052342355

theorem tailTrace_69347 : CollatzResearch.WordTrace tailWord_69347 prefixEnd_69347 1318827516572052342355 := by
  unfold tailWord_69347
  simp only [CollatzResearch.WordTrace]
  refine ⟨2529292879775137369798295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1686195253183424913198863 2529292879775137369798295)
  ·
    refine ⟨3793939319662706054697443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2529292879775137369798295 3793939319662706054697443)
    ·
      refine ⟨5690908979494059082046165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3793939319662706054697443 5690908979494059082046165)
      ·
        refine ⟨133380679206892009735457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 5690908979494059082046165 133380679206892009735457)
        ·
          refine ⟨100035509405169007301593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133380679206892009735457 100035509405169007301593)
          ·
            refine ⟨75026632053876755476195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100035509405169007301593 75026632053876755476195)
            ·
              refine ⟨112539948080815133214293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75026632053876755476195 112539948080815133214293)
              ·
                refine ⟨1318827516572052342355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 112539948080815133214293 1318827516572052342355)
                ·
                  rfl

theorem cell23_69347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 8].length) (baseStart_69347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69347 prefixEnd_69347 := by exact prefixLift 69347
  have htrace : WordTrace (prefixWord ++ tailWord_69347) baseStart_69347 baseEnd_69347 := by
    simpa [prefixWord, tailWord_69347, baseEnd_69347] using wordTrace_append hprefix tailTrace_69347
  have hstable : (prefixWord ++ tailWord_69347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69347).length < 2 ^ (prefixWord ++ tailWord_69347).sum := by decide
  have hdescent : baseEnd_69347 < baseStart_69347 := by decide
  rcases family_descends (prefixWord ++ tailWord_69347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69353 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 1, 4, 5]
def baseStart_69353 : Nat := 118140960795 + 69353 * 2 ^ 59
def prefixEnd_69353 : Nat := 4983230072969 + 3 ^ 40 * 69353 * 2
def baseEnd_69353 : Nat := 35611423831372389768557

theorem tailTrace_69353 : CollatzResearch.WordTrace tailWord_69353 prefixEnd_69353 35611423831372389768557 := by
  unfold tailWord_69353
  simp only [CollatzResearch.WordTrace]
  refine ⟨2529511717753400394516713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1686341145168933596344475 2529511717753400394516713)
  ·
    refine ⟨1897133788315050295887535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2529511717753400394516713 1897133788315050295887535)
    ·
      refine ⟨2845700682472575443831303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1897133788315050295887535 2845700682472575443831303)
      ·
        refine ⟨4268551023708863165746955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2845700682472575443831303 4268551023708863165746955)
        ·
          refine ⟨6402826535563294748620433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4268551023708863165746955 6402826535563294748620433)
          ·
            refine ⟨4802119901672471061465325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6402826535563294748620433 4802119901672471061465325)
            ·
              refine ⟨1800794963127176648049497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4802119901672471061465325 1800794963127176648049497)
              ·
                refine ⟨1350596222345382486037123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1800794963127176648049497 1350596222345382486037123)
                ·
                  refine ⟨2025894333518073729055685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1350596222345382486037123 2025894333518073729055685)
                  ·
                    refine ⟨379855187534638824197941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2025894333518073729055685 379855187534638824197941)
                    ·
                      refine ⟨35611423831372389768557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 379855187534638824197941 35611423831372389768557)
                      ·
                        rfl

theorem cell23_69353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 4, 5].length) (baseStart_69353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69353 prefixEnd_69353 := by exact prefixLift 69353
  have htrace : WordTrace (prefixWord ++ tailWord_69353) baseStart_69353 baseEnd_69353 := by
    simpa [prefixWord, tailWord_69353, baseEnd_69353] using wordTrace_append hprefix tailTrace_69353
  have hstable : (prefixWord ++ tailWord_69353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69353).length < 2 ^ (prefixWord ++ tailWord_69353).sum := by decide
  have hdescent : baseEnd_69353 < baseStart_69353 := by decide
  rcases family_descends (prefixWord ++ tailWord_69353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69357 : List Nat := [1, 5, 1, 2, 1, 2, 1, 3, 1, 3, 3]
def baseStart_69357 : Nat := 118140960795 + 69357 * 2 ^ 59
def prefixEnd_69357 : Nat := 4983230072969 + 3 ^ 40 * 69357 * 2
def baseEnd_69357 : Nat := 35613477753990374118539

theorem tailTrace_69357 : CollatzResearch.WordTrace tailWord_69357 prefixEnd_69357 35613477753990374118539 := by
  unfold tailWord_69357
  simp only [CollatzResearch.WordTrace]
  refine ⟨2529657609738909077662325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1686438406492606051774883 2529657609738909077662325)
  ·
    refine ⟨237155400913022726030843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2529657609738909077662325 237155400913022726030843)
    ·
      refine ⟨355733101369534089046265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237155400913022726030843 355733101369534089046265)
      ·
        refine ⟨266799826027150566784699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 355733101369534089046265 266799826027150566784699)
        ·
          refine ⟨400199739040725850177049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266799826027150566784699 400199739040725850177049)
          ·
            refine ⟨300149804280544387632787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 400199739040725850177049 300149804280544387632787)
            ·
              refine ⟨450224706420816581449181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300149804280544387632787 450224706420816581449181)
              ·
                refine ⟨168834264907806218043443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 450224706420816581449181 168834264907806218043443)
                ·
                  refine ⟨253251397361709327065165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 168834264907806218043443 253251397361709327065165)
                  ·
                    refine ⟨94969274010640997649437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 253251397361709327065165 94969274010640997649437)
                    ·
                      refine ⟨35613477753990374118539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 94969274010640997649437 35613477753990374118539)
                      ·
                        rfl

theorem cell23_69357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_69357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69357 prefixEnd_69357 := by exact prefixLift 69357
  have htrace : WordTrace (prefixWord ++ tailWord_69357) baseStart_69357 baseEnd_69357 := by
    simpa [prefixWord, tailWord_69357, baseEnd_69357] using wordTrace_append hprefix tailTrace_69357
  have hstable : (prefixWord ++ tailWord_69357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69357).length < 2 ^ (prefixWord ++ tailWord_69357).sum := by decide
  have hdescent : baseEnd_69357 < baseStart_69357 := by decide
  rcases family_descends (prefixWord ++ tailWord_69357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69367 : List Nat := [1, 1, 3, 1, 1, 1, 6, 1, 3, 3, 2]
def baseStart_69367 : Nat := 118140960795 + 69367 * 2 ^ 59
def prefixEnd_69367 : Nat := 4983230072969 + 3 ^ 40 * 69367 * 2
def baseEnd_69367 : Nat := 35618612560535334993493

theorem tailTrace_69367 : CollatzResearch.WordTrace tailWord_69367 prefixEnd_69367 35618612560535334993493 := by
  unfold tailWord_69367
  simp only [CollatzResearch.WordTrace]
  refine ⟨2530022339702680785526355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1686681559801787190350903 2530022339702680785526355)
  ·
    refine ⟨3795033509554021178289533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2530022339702680785526355 3795033509554021178289533)
    ·
      refine ⟨1423137566082757941858575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3795033509554021178289533 1423137566082757941858575)
      ·
        refine ⟨2134706349124136912787863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1423137566082757941858575 2134706349124136912787863)
        ·
          refine ⟨3202059523686205369181795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2134706349124136912787863 3202059523686205369181795)
          ·
            refine ⟨4803089285529308053772693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3202059523686205369181795 4803089285529308053772693)
            ·
              refine ⟨225144810259186315020595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4803089285529308053772693 225144810259186315020595)
              ·
                refine ⟨337717215388779472530893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225144810259186315020595 337717215388779472530893)
                ·
                  refine ⟨126643955770792302199085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 337717215388779472530893 126643955770792302199085)
                  ·
                    refine ⟨47491483414047113324657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 126643955770792302199085 47491483414047113324657)
                    ·
                      refine ⟨35618612560535334993493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 47491483414047113324657 35618612560535334993493)
                      ·
                        rfl

theorem cell23_69367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 3, 2].length) (baseStart_69367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69367 prefixEnd_69367 := by exact prefixLift 69367
  have htrace : WordTrace (prefixWord ++ tailWord_69367) baseStart_69367 baseEnd_69367 := by
    simpa [prefixWord, tailWord_69367, baseEnd_69367] using wordTrace_append hprefix tailTrace_69367
  have hstable : (prefixWord ++ tailWord_69367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69367).length < 2 ^ (prefixWord ++ tailWord_69367).sum := by decide
  have hdescent : baseEnd_69367 < baseStart_69367 := by decide
  rcases family_descends (prefixWord ++ tailWord_69367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69384 : List Nat := [2, 1, 3, 2, 2, 1, 3, 3, 1, 3, 2]
def baseStart_69384 : Nat := 118140960795 + 69384 * 2 ^ 59
def prefixEnd_69384 : Nat := 4983230072969 + 3 ^ 40 * 69384 * 2
def baseEnd_69384 : Nat := 35627341731661768480915

theorem tailTrace_69384 : CollatzResearch.WordTrace tailWord_69384 prefixEnd_69384 35627341731661768480915 := by
  unfold tailWord_69384
  simp only [CollatzResearch.WordTrace]
  refine ⟨1265321190320546344447603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1687094920427395125930137 1265321190320546344447603)
  ·
    refine ⟨1897981785480819516671405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1265321190320546344447603 1897981785480819516671405)
    ·
      refine ⟨711743169555307318751777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1897981785480819516671405 711743169555307318751777)
      ·
        refine ⟨533807377166480489063833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 711743169555307318751777 533807377166480489063833)
        ·
          refine ⟨400355532874860366797875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 533807377166480489063833 400355532874860366797875)
          ·
            refine ⟨600533299312290550196813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 400355532874860366797875 600533299312290550196813)
            ·
              refine ⟨225199987242108956323805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 600533299312290550196813 225199987242108956323805)
              ·
                refine ⟨84449995215790858621427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 225199987242108956323805 84449995215790858621427)
                ·
                  refine ⟨126674992823686287932141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84449995215790858621427 126674992823686287932141)
                  ·
                    refine ⟨47503122308882357974553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 126674992823686287932141 47503122308882357974553)
                    ·
                      refine ⟨35627341731661768480915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 47503122308882357974553 35627341731661768480915)
                      ·
                        rfl

theorem cell23_69384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_69384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69384 prefixEnd_69384 := by exact prefixLift 69384
  have htrace : WordTrace (prefixWord ++ tailWord_69384) baseStart_69384 baseEnd_69384 := by
    simpa [prefixWord, tailWord_69384, baseEnd_69384] using wordTrace_append hprefix tailTrace_69384
  have hstable : (prefixWord ++ tailWord_69384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69384).length < 2 ^ (prefixWord ++ tailWord_69384).sum := by decide
  have hdescent : baseEnd_69384 < baseStart_69384 := by decide
  rcases family_descends (prefixWord ++ tailWord_69384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69390 : List Nat := [4, 1, 1, 2, 1, 1, 3, 2, 2, 6]
def baseStart_69390 : Nat := 118140960795 + 69390 * 2 ^ 59
def prefixEnd_69390 : Nat := 4983230072969 + 3 ^ 40 * 69390 * 2
def baseEnd_69390 : Nat := 11876807538529581668629

theorem tailTrace_69390 : CollatzResearch.WordTrace tailWord_69390 prefixEnd_69390 11876807538529581668629 := by
  unfold tailWord_69390
  simp only [CollatzResearch.WordTrace]
  refine ⟨316357652327419464201703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1687240812412903809075749 316357652327419464201703)
  ·
    refine ⟨474536478491129196302555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 316357652327419464201703 474536478491129196302555)
    ·
      refine ⟨711804717736693794453833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 474536478491129196302555 711804717736693794453833)
      ·
        refine ⟨533853538302520345840375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 711804717736693794453833 533853538302520345840375)
        ·
          refine ⟨800780307453780518760563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 533853538302520345840375 800780307453780518760563)
          ·
            refine ⟨1201170461180670778140845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 800780307453780518760563 1201170461180670778140845)
            ·
              refine ⟨450438922942751541802817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1201170461180670778140845 450438922942751541802817)
              ·
                refine ⟨337829192207063656352113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 450438922942751541802817 337829192207063656352113)
                ·
                  refine ⟨253371894155297742264085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 337829192207063656352113 253371894155297742264085)
                  ·
                    refine ⟨11876807538529581668629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 253371894155297742264085 11876807538529581668629)
                    ·
                      rfl

theorem cell23_69390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_69390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69390 prefixEnd_69390 := by exact prefixLift 69390
  have htrace : WordTrace (prefixWord ++ tailWord_69390) baseStart_69390 baseEnd_69390 := by
    simpa [prefixWord, tailWord_69390, baseEnd_69390] using wordTrace_append hprefix tailTrace_69390
  have hstable : (prefixWord ++ tailWord_69390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69390).length < 2 ^ (prefixWord ++ tailWord_69390).sum := by decide
  have hdescent : baseEnd_69390 < baseStart_69390 := by decide
  rcases family_descends (prefixWord ++ tailWord_69390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69400 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 1, 6, 3]
def baseStart_69400 : Nat := 118140960795 + 69400 * 2 ^ 59
def prefixEnd_69400 : Nat := 4983230072969 + 3 ^ 40 * 69400 * 2
def baseEnd_69400 : Nat := 35635557422133705880841

theorem tailTrace_69400 : CollatzResearch.WordTrace tailWord_69400 prefixEnd_69400 35635557422133705880841 := by
  unfold tailWord_69400
  simp only [CollatzResearch.WordTrace]
  refine ⟨1265612974291563710738827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1687483965722084947651769 1265612974291563710738827)
  ·
    refine ⟨1898419461437345566108241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1265612974291563710738827 1898419461437345566108241)
    ·
      refine ⟨1423814596078009174581181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1898419461437345566108241 1423814596078009174581181)
      ·
        refine ⟨533930473529253440467943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1423814596078009174581181 533930473529253440467943)
        ·
          refine ⟨800895710293880160701915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 533930473529253440467943 800895710293880160701915)
          ·
            refine ⟨1201343565440820241052873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 800895710293880160701915 1201343565440820241052873)
            ·
              refine ⟨901007674080615180789655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1201343565440820241052873 901007674080615180789655)
              ·
                refine ⟨1351511511120922771184483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 901007674080615180789655 1351511511120922771184483)
                ·
                  refine ⟨2027267266681384156776725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1351511511120922771184483 2027267266681384156776725)
                  ·
                    refine ⟨95028153125689882348909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2027267266681384156776725 95028153125689882348909)
                    ·
                      refine ⟨35635557422133705880841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 95028153125689882348909 35635557422133705880841)
                      ·
                        rfl

theorem cell23_69400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_69400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69400 prefixEnd_69400 := by exact prefixLift 69400
  have htrace : WordTrace (prefixWord ++ tailWord_69400) baseStart_69400 baseEnd_69400 := by
    simpa [prefixWord, tailWord_69400, baseEnd_69400] using wordTrace_append hprefix tailTrace_69400
  have hstable : (prefixWord ++ tailWord_69400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69400).length < 2 ^ (prefixWord ++ tailWord_69400).sum := by decide
  have hdescent : baseEnd_69400 < baseStart_69400 := by decide
  rcases family_descends (prefixWord ++ tailWord_69400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69403 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 11]
def baseStart_69403 : Nat := 118140960795 + 69403 * 2 ^ 59
def prefixEnd_69403 : Nat := 4983230072969 + 3 ^ 40 * 69403 * 2
def baseEnd_69403 : Nat := 3959677540455243793703

theorem tailTrace_69403 : CollatzResearch.WordTrace tailWord_69403 prefixEnd_69403 3959677540455243793703 := by
  unfold tailWord_69403
  simp only [CollatzResearch.WordTrace]
  refine ⟨2531335367572258933836863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1687556911714839289224575 2531335367572258933836863)
  ·
    refine ⟨3797003051358388400755295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2531335367572258933836863 3797003051358388400755295)
    ·
      refine ⟨5695504577037582601132943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3797003051358388400755295 5695504577037582601132943)
      ·
        refine ⟨8543256865556373901699415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5695504577037582601132943 8543256865556373901699415)
        ·
          refine ⟨12814885298334560852549123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8543256865556373901699415 12814885298334560852549123)
          ·
            refine ⟨19222327947501841278823685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12814885298334560852549123 19222327947501841278823685)
            ·
              refine ⟨3604186490156595239779441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19222327947501841278823685 3604186490156595239779441)
              ·
                refine ⟨2703139867617446429834581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3604186490156595239779441 2703139867617446429834581)
                ·
                  refine ⟨3959677540455243793703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 2703139867617446429834581 3959677540455243793703)
                  ·
                    rfl

theorem cell23_69403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 11].length) (baseStart_69403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69403 prefixEnd_69403 := by exact prefixLift 69403
  have htrace : WordTrace (prefixWord ++ tailWord_69403) baseStart_69403 baseEnd_69403 := by
    simpa [prefixWord, tailWord_69403, baseEnd_69403] using wordTrace_append hprefix tailTrace_69403
  have hstable : (prefixWord ++ tailWord_69403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69403).length < 2 ^ (prefixWord ++ tailWord_69403).sum := by decide
  have hdescent : baseEnd_69403 < baseStart_69403 := by decide
  rcases family_descends (prefixWord ++ tailWord_69403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69420 : List Nat := [2, 2, 1, 1, 1, 5, 2, 2, 7]
def baseStart_69420 : Nat := 118140960795 + 69420 * 2 ^ 59
def prefixEnd_69420 : Nat := 4983230072969 + 3 ^ 40 * 69420 * 2
def baseEnd_69420 : Nat := 3960647448358180847861

theorem tailTrace_69420 : CollatzResearch.WordTrace tailWord_69420 prefixEnd_69420 3960647448358180847861 := by
  unfold tailWord_69420
  simp only [CollatzResearch.WordTrace]
  refine ⟨1265977704255335418602857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1687970272340447224803809 1265977704255335418602857)
  ·
    refine ⟨949483278191501563952143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1265977704255335418602857 949483278191501563952143)
    ·
      refine ⟨1424224917287252345928215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 949483278191501563952143 1424224917287252345928215)
      ·
        refine ⟨2136337375930878518892323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1424224917287252345928215 2136337375930878518892323)
        ·
          refine ⟨3204506063896317778338485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2136337375930878518892323 3204506063896317778338485)
          ·
            refine ⟨300422443490279791719233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3204506063896317778338485 300422443490279791719233)
            ·
              refine ⟨225316832617709843789425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 300422443490279791719233 225316832617709843789425)
              ·
                refine ⟨168987624463282382842069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 225316832617709843789425 168987624463282382842069)
                ·
                  refine ⟨3960647448358180847861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 168987624463282382842069 3960647448358180847861)
                  ·
                    rfl

theorem cell23_69420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 7].length) (baseStart_69420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69420 prefixEnd_69420 := by exact prefixLift 69420
  have htrace : WordTrace (prefixWord ++ tailWord_69420) baseStart_69420 baseEnd_69420 := by
    simpa [prefixWord, tailWord_69420, baseEnd_69420] using wordTrace_append hprefix tailTrace_69420
  have hstable : (prefixWord ++ tailWord_69420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69420).length < 2 ^ (prefixWord ++ tailWord_69420).sum := by decide
  have hdescent : baseEnd_69420 < baseStart_69420 := by decide
  rcases family_descends (prefixWord ++ tailWord_69420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69487 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 6, 4, 2]
def baseStart_69487 : Nat := 118140960795 + 69487 * 2 ^ 59
def prefixEnd_69487 : Nat := 4983230072969 + 3 ^ 40 * 69487 * 2
def baseEnd_69487 : Nat := 35680230239074865492941

theorem tailTrace_69487 : CollatzResearch.WordTrace tailWord_69487 prefixEnd_69487 35680230239074865492941 := by
  unfold tailWord_69487
  simp only [CollatzResearch.WordTrace]
  refine ⟨2534399099267941279894715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1689599399511960853263143 2534399099267941279894715)
  ·
    refine ⟨3801598648901911919842073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2534399099267941279894715 3801598648901911919842073)
    ·
      refine ⟨2851198986676433939881555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3801598648901911919842073 2851198986676433939881555)
      ·
        refine ⟨4276798480014650909822333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2851198986676433939881555 4276798480014650909822333)
        ·
          refine ⟨1603799430005494091183375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4276798480014650909822333 1603799430005494091183375)
          ·
            refine ⟨2405699145008241136775063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1603799430005494091183375 2405699145008241136775063)
            ·
              refine ⟨3608548717512361705162595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2405699145008241136775063 3608548717512361705162595)
              ·
                refine ⟨5412823076268542557743893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3608548717512361705162595 5412823076268542557743893)
                ·
                  refine ⟨253726081700087932394245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5412823076268542557743893 253726081700087932394245)
                  ·
                    refine ⟨47573640318766487323921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 253726081700087932394245 47573640318766487323921)
                    ·
                      refine ⟨35680230239074865492941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 47573640318766487323921 35680230239074865492941)
                      ·
                        rfl

theorem cell23_69487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 4, 2].length) (baseStart_69487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69487 prefixEnd_69487 := by exact prefixLift 69487
  have htrace : WordTrace (prefixWord ++ tailWord_69487) baseStart_69487 baseEnd_69487 := by
    simpa [prefixWord, tailWord_69487, baseEnd_69487] using wordTrace_append hprefix tailTrace_69487
  have hstable : (prefixWord ++ tailWord_69487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69487).length < 2 ^ (prefixWord ++ tailWord_69487).sum := by decide
  have hdescent : baseEnd_69487 < baseStart_69487 := by decide
  rcases family_descends (prefixWord ++ tailWord_69487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69505 : List Nat := [1, 2, 4, 4, 2, 1, 2, 2, 5]
def baseStart_69505 : Nat := 118140960795 + 69505 * 2 ^ 59
def prefixEnd_69505 : Nat := 4983230072969 + 3 ^ 40 * 69505 * 2
def baseEnd_69505 : Nat := 3965496987872866118651

theorem tailTrace_69505 : CollatzResearch.WordTrace tailWord_69505 prefixEnd_69505 3965496987872866118651 := by
  unfold tailWord_69505
  simp only [CollatzResearch.WordTrace]
  refine ⟨2535055613202730354049969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1690037075468486902699979 2535055613202730354049969)
  ·
    refine ⟨1901291709902047765537477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2535055613202730354049969 1901291709902047765537477)
    ·
      refine ⟨356492195606633956038277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1901291709902047765537477 356492195606633956038277)
      ·
        refine ⟨66842286676243866757177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 356492195606633956038277 66842286676243866757177)
        ·
          refine ⟨50131715007182900067883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66842286676243866757177 50131715007182900067883)
          ·
            refine ⟨75197572510774350101825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50131715007182900067883 75197572510774350101825)
            ·
              refine ⟨56398179383080762576369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75197572510774350101825 56398179383080762576369)
              ·
                refine ⟨42298634537310571932277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56398179383080762576369 42298634537310571932277)
                ·
                  refine ⟨3965496987872866118651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42298634537310571932277 3965496987872866118651)
                  ·
                    rfl

theorem cell23_69505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 2, 5].length) (baseStart_69505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69505 prefixEnd_69505 := by exact prefixLift 69505
  have htrace : WordTrace (prefixWord ++ tailWord_69505) baseStart_69505 baseEnd_69505 := by
    simpa [prefixWord, tailWord_69505, baseEnd_69505] using wordTrace_append hprefix tailTrace_69505
  have hstable : (prefixWord ++ tailWord_69505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69505).length < 2 ^ (prefixWord ++ tailWord_69505).sum := by decide
  have hdescent : baseEnd_69505 < baseStart_69505 := by decide
  rcases family_descends (prefixWord ++ tailWord_69505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69527 : List Nat := [1, 1, 3, 3, 1, 3, 2, 3, 6]
def baseStart_69527 : Nat := 118140960795 + 69527 * 2 ^ 59
def prefixEnd_69527 : Nat := 4983230072969 + 3 ^ 40 * 69527 * 2
def baseEnd_69527 : Nat := 3966752162806078776973

theorem tailTrace_69527 : CollatzResearch.WordTrace tailWord_69527 prefixEnd_69527 3966752162806078776973 := by
  unfold tailWord_69527
  simp only [CollatzResearch.WordTrace]
  refine ⟨2535858019123028111350835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1690572012748685407567223 2535858019123028111350835)
  ·
    refine ⟨3803787028684542167026253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2535858019123028111350835 3803787028684542167026253)
    ·
      refine ⟨1426420135756703312634845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3803787028684542167026253 1426420135756703312634845)
      ·
        refine ⟨534907550908763742238067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1426420135756703312634845 534907550908763742238067)
        ·
          refine ⟨802361326363145613357101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 534907550908763742238067 802361326363145613357101)
          ·
            refine ⟨300885497386179605008913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 802361326363145613357101 300885497386179605008913)
            ·
              refine ⟨225664123039634703756685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 300885497386179605008913 225664123039634703756685)
              ·
                refine ⟨84624046139863013908757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 225664123039634703756685 84624046139863013908757)
                ·
                  refine ⟨3966752162806078776973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 84624046139863013908757 3966752162806078776973)
                  ·
                    rfl

theorem cell23_69527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 6].length) (baseStart_69527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69527 prefixEnd_69527 := by exact prefixLift 69527
  have htrace : WordTrace (prefixWord ++ tailWord_69527) baseStart_69527 baseEnd_69527 := by
    simpa [prefixWord, tailWord_69527, baseEnd_69527] using wordTrace_append hprefix tailTrace_69527
  have hstable : (prefixWord ++ tailWord_69527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69527).length < 2 ^ (prefixWord ++ tailWord_69527).sum := by decide
  have hdescent : baseEnd_69527 < baseStart_69527 := by decide
  rcases family_descends (prefixWord ++ tailWord_69527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69538 : List Nat := [3, 3, 1, 2, 4, 1, 1, 1, 2, 1, 4]
def baseStart_69538 : Nat := 118140960795 + 69538 * 2 ^ 59
def prefixEnd_69538 : Nat := 4983230072969 + 3 ^ 40 * 69538 * 2
def baseEnd_69538 : Nat := 35706417752454165955207

theorem tailTrace_69538 : CollatzResearch.WordTrace tailWord_69538 prefixEnd_69538 35706417752454165955207 := by
  unfold tailWord_69538
  simp only [CollatzResearch.WordTrace]
  refine ⟨634064805520794247500317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1690839481388784660000845 634064805520794247500317)
  ·
    refine ⟨237774302070297842812619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 634064805520794247500317 237774302070297842812619)
    ·
      refine ⟨356661453105446764218929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237774302070297842812619 356661453105446764218929)
      ·
        refine ⟨267496089829085073164197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 356661453105446764218929 267496089829085073164197)
        ·
          refine ⟨50155516842953451218287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 267496089829085073164197 50155516842953451218287)
          ·
            refine ⟨75233275264430176827431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50155516842953451218287 75233275264430176827431)
            ·
              refine ⟨112849912896645265241147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75233275264430176827431 112849912896645265241147)
              ·
                refine ⟨169274869344967897861721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112849912896645265241147 169274869344967897861721)
                ·
                  refine ⟨126956152008725923396291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169274869344967897861721 126956152008725923396291)
                  ·
                    refine ⟨190434228013088885094437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 126956152008725923396291 190434228013088885094437)
                    ·
                      refine ⟨35706417752454165955207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 190434228013088885094437 35706417752454165955207)
                      ·
                        rfl

theorem cell23_69538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_69538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69538 prefixEnd_69538 := by exact prefixLift 69538
  have htrace : WordTrace (prefixWord ++ tailWord_69538) baseStart_69538 baseEnd_69538 := by
    simpa [prefixWord, tailWord_69538, baseEnd_69538] using wordTrace_append hprefix tailTrace_69538
  have hstable : (prefixWord ++ tailWord_69538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69538).length < 2 ^ (prefixWord ++ tailWord_69538).sum := by decide
  have hdescent : baseEnd_69538 < baseStart_69538 := by decide
  rcases family_descends (prefixWord ++ tailWord_69538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69614 : List Nat := [4, 1, 2, 1, 3, 1, 1, 3, 1, 1, 5]
def baseStart_69614 : Nat := 118140960795 + 69614 * 2 ^ 59
def prefixEnd_69614 : Nat := 4983230072969 + 3 ^ 40 * 69614 * 2
def baseEnd_69614 : Nat := 35745442282195868604857

theorem tailTrace_69614 : CollatzResearch.WordTrace tailWord_69614 prefixEnd_69614 35745442282195868604857 := by
  unfold tailWord_69614
  simp only [CollatzResearch.WordTrace]
  refine ⟨317378896225980246220987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1692687446538561313178597 317378896225980246220987)
  ·
    refine ⟨476068344338970369331481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 317378896225980246220987 476068344338970369331481)
    ·
      refine ⟨357051258254227776998611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 476068344338970369331481 357051258254227776998611)
      ·
        refine ⟨535576887381341665497917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357051258254227776998611 535576887381341665497917)
        ·
          refine ⟨200841332768003124561719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 535576887381341665497917 200841332768003124561719)
          ·
            refine ⟨301261999152004686842579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200841332768003124561719 301261999152004686842579)
            ·
              refine ⟨451892998728007030263869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301261999152004686842579 451892998728007030263869)
              ·
                refine ⟨169459874523002636348951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 451892998728007030263869 169459874523002636348951)
                ·
                  refine ⟨254189811784503954523427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 169459874523002636348951 254189811784503954523427)
                  ·
                    refine ⟨381284717676755931785141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 254189811784503954523427 381284717676755931785141)
                    ·
                      refine ⟨35745442282195868604857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 381284717676755931785141 35745442282195868604857)
                      ·
                        rfl

theorem cell23_69614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_69614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69614 prefixEnd_69614 := by exact prefixLift 69614
  have htrace : WordTrace (prefixWord ++ tailWord_69614) baseStart_69614 baseEnd_69614 := by
    simpa [prefixWord, tailWord_69614, baseEnd_69614] using wordTrace_append hprefix tailTrace_69614
  have hstable : (prefixWord ++ tailWord_69614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69614).length < 2 ^ (prefixWord ++ tailWord_69614).sum := by decide
  have hdescent : baseEnd_69614 < baseStart_69614 := by decide
  rcases family_descends (prefixWord ++ tailWord_69614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69622 : List Nat := [5, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3]
def baseStart_69622 : Nat := 118140960795 + 69622 * 2 ^ 59
def prefixEnd_69622 : Nat := 4983230072969 + 3 ^ 40 * 69622 * 2
def baseEnd_69622 : Nat := 35749550127431837304821

theorem tailTrace_69622 : CollatzResearch.WordTrace tailWord_69622 prefixEnd_69622 35749550127431837304821 := by
  unfold tailWord_69622
  simp only [CollatzResearch.WordTrace]
  refine ⟨158707684611178708503695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1692881969185906224039413 158707684611178708503695)
  ·
    refine ⟨238061526916768062755543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158707684611178708503695 238061526916768062755543)
    ·
      refine ⟨357092290375152094133315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238061526916768062755543 357092290375152094133315)
      ·
        refine ⟨535638435562728141199973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357092290375152094133315 535638435562728141199973)
        ·
          refine ⟨100432206668011526474995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 535638435562728141199973 100432206668011526474995)
          ·
            refine ⟨150648310002017289712493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100432206668011526474995 150648310002017289712493)
            ·
              refine ⟨56493116250756483642185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150648310002017289712493 56493116250756483642185)
              ·
                refine ⟨42369837188067362731639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56493116250756483642185 42369837188067362731639)
                ·
                  refine ⟨63554755782101044097459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42369837188067362731639 63554755782101044097459)
                  ·
                    refine ⟨95332133673151566146189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63554755782101044097459 95332133673151566146189)
                    ·
                      refine ⟨35749550127431837304821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 95332133673151566146189 35749550127431837304821)
                      ·
                        rfl

theorem cell23_69622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_69622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69622 prefixEnd_69622 := by exact prefixLift 69622
  have htrace : WordTrace (prefixWord ++ tailWord_69622) baseStart_69622 baseEnd_69622 := by
    simpa [prefixWord, tailWord_69622, baseEnd_69622] using wordTrace_append hprefix tailTrace_69622
  have hstable : (prefixWord ++ tailWord_69622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69622).length < 2 ^ (prefixWord ++ tailWord_69622).sum := by decide
  have hdescent : baseEnd_69622 < baseStart_69622 := by decide
  rcases family_descends (prefixWord ++ tailWord_69622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69644 : List Nat := [2, 2, 1, 2, 3, 1, 2, 3, 1, 3, 3]
def baseStart_69644 : Nat := 118140960795 + 69644 * 2 ^ 59
def prefixEnd_69644 : Nat := 4983230072969 + 3 ^ 40 * 69644 * 2
def baseEnd_69644 : Nat := 35760846701830751229719

theorem tailTrace_69644 : CollatzResearch.WordTrace tailWord_69644 prefixEnd_69644 35760846701830751229719 := by
  unfold tailWord_69644
  simp only [CollatzResearch.WordTrace]
  refine ⟨1270062679849578546679993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1693416906466104728906657 1270062679849578546679993)
  ·
    refine ⟨952547009887183910009995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1270062679849578546679993 952547009887183910009995)
    ·
      refine ⟨1428820514830775865014993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 952547009887183910009995 1428820514830775865014993)
      ·
        refine ⟨1071615386123081898761245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1428820514830775865014993 1071615386123081898761245)
        ·
          refine ⟨401855769796155712035467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1071615386123081898761245 401855769796155712035467)
          ·
            refine ⟨602783654694233568053201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401855769796155712035467 602783654694233568053201)
            ·
              refine ⟨452087741020675176039901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 602783654694233568053201 452087741020675176039901)
              ·
                refine ⟨169532902882753191014963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 452087741020675176039901 169532902882753191014963)
                ·
                  refine ⟨254299354324129786522445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 169532902882753191014963 254299354324129786522445)
                  ·
                    refine ⟨95362257871548669945917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 254299354324129786522445 95362257871548669945917)
                    ·
                      refine ⟨35760846701830751229719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 95362257871548669945917 35760846701830751229719)
                      ·
                        rfl

theorem cell23_69644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_69644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69644 prefixEnd_69644 := by exact prefixLift 69644
  have htrace : WordTrace (prefixWord ++ tailWord_69644) baseStart_69644 baseEnd_69644 := by
    simpa [prefixWord, tailWord_69644, baseEnd_69644] using wordTrace_append hprefix tailTrace_69644
  have hstable : (prefixWord ++ tailWord_69644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69644).length < 2 ^ (prefixWord ++ tailWord_69644).sum := by decide
  have hdescent : baseEnd_69644 < baseStart_69644 := by decide
  rcases family_descends (prefixWord ++ tailWord_69644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69645 : List Nat := [1, 7, 1, 2, 1, 1, 1, 1, 3, 1, 4]
def baseStart_69645 : Nat := 118140960795 + 69645 * 2 ^ 59
def prefixEnd_69645 : Nat := 4983230072969 + 3 ^ 40 * 69645 * 2
def baseEnd_69645 : Nat := 35761360182485247317215

theorem tailTrace_69645 : CollatzResearch.WordTrace tailWord_69645 prefixEnd_69645 35761360182485247317215 := by
  unfold tailWord_69645
  simp only [CollatzResearch.WordTrace]
  refine ⟨2540161832695534264146389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1693441221797022842764259 2540161832695534264146389)
  ·
    refine ⟨59535042953801584315931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 2540161832695534264146389 59535042953801584315931)
    ·
      refine ⟨89302564430702376473897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59535042953801584315931 89302564430702376473897)
      ·
        refine ⟨66976923323026782355423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89302564430702376473897 66976923323026782355423)
        ·
          refine ⟨100465384984540173533135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66976923323026782355423 100465384984540173533135)
          ·
            refine ⟨150698077476810260299703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100465384984540173533135 150698077476810260299703)
            ·
              refine ⟨226047116215215390449555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150698077476810260299703 226047116215215390449555)
              ·
                refine ⟨339070674322823085674333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 226047116215215390449555 339070674322823085674333)
                ·
                  refine ⟨127151502871058657127875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 339070674322823085674333 127151502871058657127875)
                  ·
                    refine ⟨190727254306587985691813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 127151502871058657127875 190727254306587985691813)
                    ·
                      refine ⟨35761360182485247317215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 190727254306587985691813 35761360182485247317215)
                      ·
                        rfl

theorem cell23_69645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_69645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69645 prefixEnd_69645 := by exact prefixLift 69645
  have htrace : WordTrace (prefixWord ++ tailWord_69645) baseStart_69645 baseEnd_69645 := by
    simpa [prefixWord, tailWord_69645, baseEnd_69645] using wordTrace_append hprefix tailTrace_69645
  have hstable : (prefixWord ++ tailWord_69645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69645).length < 2 ^ (prefixWord ++ tailWord_69645).sum := by decide
  have hdescent : baseEnd_69645 < baseStart_69645 := by decide
  rcases family_descends (prefixWord ++ tailWord_69645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69661 : List Nat := [1, 4, 2, 2, 2, 2, 1, 2, 1, 3, 3]
def baseStart_69661 : Nat := 118140960795 + 69661 * 2 ^ 59
def prefixEnd_69661 : Nat := 4983230072969 + 3 ^ 40 * 69661 * 2
def baseEnd_69661 : Nat := 35769575872957184717141

theorem tailTrace_69661 : CollatzResearch.WordTrace tailWord_69661 prefixEnd_69661 35769575872957184717141 := by
  unfold tailWord_69661
  simp only [CollatzResearch.WordTrace]
  refine ⟨2540745400637568996728837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1693830267091712664485891 2540745400637568996728837)
  ·
    refine ⟨476389762619544186886657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2540745400637568996728837 476389762619544186886657)
    ·
      refine ⟨357292321964658140164993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 476389762619544186886657 357292321964658140164993)
      ·
        refine ⟨267969241473493605123745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 357292321964658140164993 267969241473493605123745)
        ·
          refine ⟨200976931105120203842809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267969241473493605123745 200976931105120203842809)
          ·
            refine ⟨150732698328840152882107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200976931105120203842809 150732698328840152882107)
            ·
              refine ⟨226099047493260229323161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150732698328840152882107 226099047493260229323161)
              ·
                refine ⟨169574285619945171992371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 226099047493260229323161 169574285619945171992371)
                ·
                  refine ⟨254361428429917757988557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 169574285619945171992371 254361428429917757988557)
                  ·
                    refine ⟨95385535661219159245709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 254361428429917757988557 95385535661219159245709)
                    ·
                      refine ⟨35769575872957184717141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 95385535661219159245709 35769575872957184717141)
                      ·
                        rfl

theorem cell23_69661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_69661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69661 prefixEnd_69661 := by exact prefixLift 69661
  have htrace : WordTrace (prefixWord ++ tailWord_69661) baseStart_69661 baseEnd_69661 := by
    simpa [prefixWord, tailWord_69661, baseEnd_69661] using wordTrace_append hprefix tailTrace_69661
  have hstable : (prefixWord ++ tailWord_69661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69661).length < 2 ^ (prefixWord ++ tailWord_69661).sum := by decide
  have hdescent : baseEnd_69661 < baseStart_69661 := by decide
  rcases family_descends (prefixWord ++ tailWord_69661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69678 : List Nat := [4, 1, 3, 1, 1, 2, 1, 4, 2, 1, 3]
def baseStart_69678 : Nat := 118140960795 + 69678 * 2 ^ 59
def prefixEnd_69678 : Nat := 4983230072969 + 3 ^ 40 * 69678 * 2
def baseEnd_69678 : Nat := 35778305044083618204563

theorem tailTrace_69678 : CollatzResearch.WordTrace tailWord_69678 prefixEnd_69678 35778305044083618204563 := by
  unfold tailWord_69678
  simp only [CollatzResearch.WordTrace]
  refine ⟨317670680196997612512211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1694243627717320600065125 317670680196997612512211)
  ·
    refine ⟨476506020295496418768317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 317670680196997612512211 476506020295496418768317)
    ·
      refine ⟨178689757610811157038119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 476506020295496418768317 178689757610811157038119)
      ·
        refine ⟨268034636416216735557179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178689757610811157038119 268034636416216735557179)
        ·
          refine ⟨402051954624325103335769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268034636416216735557179 402051954624325103335769)
          ·
            refine ⟨301538965968243827501827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 402051954624325103335769 301538965968243827501827)
            ·
              refine ⟨452308448952365741252741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301538965968243827501827 452308448952365741252741)
              ·
                refine ⟨84807834178568576484889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 452308448952365741252741 84807834178568576484889)
                ·
                  refine ⟨63605875633926432363667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84807834178568576484889 63605875633926432363667)
                  ·
                    refine ⟨95408813450889648545501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63605875633926432363667 95408813450889648545501)
                    ·
                      refine ⟨35778305044083618204563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 95408813450889648545501 35778305044083618204563)
                      ·
                        rfl

theorem cell23_69678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_69678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69678 prefixEnd_69678 := by exact prefixLift 69678
  have htrace : WordTrace (prefixWord ++ tailWord_69678) baseStart_69678 baseEnd_69678 := by
    simpa [prefixWord, tailWord_69678, baseEnd_69678] using wordTrace_append hprefix tailTrace_69678
  have hstable : (prefixWord ++ tailWord_69678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69678).length < 2 ^ (prefixWord ++ tailWord_69678).sum := by decide
  have hdescent : baseEnd_69678 < baseStart_69678 := by decide
  rcases family_descends (prefixWord ++ tailWord_69678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69687 : List Nat := [1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 5]
def baseStart_69687 : Nat := 118140960795 + 69687 * 2 ^ 59
def prefixEnd_69687 : Nat := 4983230072969 + 3 ^ 40 * 69687 * 2
def baseEnd_69687 : Nat := 35782926369974082992021

theorem tailTrace_69687 : CollatzResearch.WordTrace tailWord_69687 prefixEnd_69687 35782926369974082992021 := by
  unfold tailWord_69687
  simp only [CollatzResearch.WordTrace]
  refine ⟨2541693698543375437175315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1694462465695583624783543 2541693698543375437175315)
  ·
    refine ⟨3812540547815063155762973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2541693698543375437175315 3812540547815063155762973)
    ·
      refine ⟨1429702705430648683411115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3812540547815063155762973 1429702705430648683411115)
      ·
        refine ⟨2144554058145973025116673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1429702705430648683411115 2144554058145973025116673)
        ·
          refine ⟨1608415543609479768837505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2144554058145973025116673 1608415543609479768837505)
          ·
            refine ⟨1206311657707109826628129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1608415543609479768837505 1206311657707109826628129)
            ·
              refine ⟨904733743280332369971097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1206311657707109826628129 904733743280332369971097)
              ·
                refine ⟨678550307460249277478323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 904733743280332369971097 678550307460249277478323)
                ·
                  refine ⟨1017825461190373916217485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 678550307460249277478323 1017825461190373916217485)
                  ·
                    refine ⟨381684547946390218581557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1017825461190373916217485 381684547946390218581557)
                    ·
                      refine ⟨35782926369974082992021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 381684547946390218581557 35782926369974082992021)
                      ·
                        rfl

theorem cell23_69687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_69687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69687 prefixEnd_69687 := by exact prefixLift 69687
  have htrace : WordTrace (prefixWord ++ tailWord_69687) baseStart_69687 baseEnd_69687 := by
    simpa [prefixWord, tailWord_69687, baseEnd_69687] using wordTrace_append hprefix tailTrace_69687
  have hstable : (prefixWord ++ tailWord_69687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69687).length < 2 ^ (prefixWord ++ tailWord_69687).sum := by decide
  have hdescent : baseEnd_69687 < baseStart_69687 := by decide
  rcases family_descends (prefixWord ++ tailWord_69687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69701 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 6, 2, 2]
def baseStart_69701 : Nat := 118140960795 + 69701 * 2 ^ 59
def prefixEnd_69701 : Nat := 4983230072969 + 3 ^ 40 * 69701 * 2
def baseEnd_69701 : Nat := 35790115099137028216957

theorem tailTrace_69701 : CollatzResearch.WordTrace tailWord_69701 prefixEnd_69701 35790115099137028216957 := by
  unfold tailWord_69701
  simp only [CollatzResearch.WordTrace]
  refine ⟨2542204320492655828184957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1694802880328437218789971 2542204320492655828184957)
  ·
    refine ⟨953326620184745935569359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2542204320492655828184957 953326620184745935569359)
    ·
      refine ⟨1429989930277118903354039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 953326620184745935569359 1429989930277118903354039)
      ·
        refine ⟨2144984895415678355031059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1429989930277118903354039 2144984895415678355031059)
        ·
          refine ⟨3217477343123517532546589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2144984895415678355031059 3217477343123517532546589)
          ·
            refine ⟨1206554003671319074704971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3217477343123517532546589 1206554003671319074704971)
            ·
              refine ⟨1809831005506978612057457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1206554003671319074704971 1809831005506978612057457)
              ·
                refine ⟨1357373254130233959043093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1809831005506978612057457 1357373254130233959043093)
                ·
                  refine ⟨63626871287354716830145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1357373254130233959043093 63626871287354716830145)
                  ·
                    refine ⟨47720153465516037622609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 63626871287354716830145 47720153465516037622609)
                    ·
                      refine ⟨35790115099137028216957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 47720153465516037622609 35790115099137028216957)
                      ·
                        rfl

theorem cell23_69701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 6, 2, 2].length) (baseStart_69701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69701 prefixEnd_69701 := by exact prefixLift 69701
  have htrace : WordTrace (prefixWord ++ tailWord_69701) baseStart_69701 baseEnd_69701 := by
    simpa [prefixWord, tailWord_69701, baseEnd_69701] using wordTrace_append hprefix tailTrace_69701
  have hstable : (prefixWord ++ tailWord_69701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69701).length < 2 ^ (prefixWord ++ tailWord_69701).sum := by decide
  have hdescent : baseEnd_69701 < baseStart_69701 := by decide
  rcases family_descends (prefixWord ++ tailWord_69701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69707 : List Nat := [1, 1, 1, 1, 3, 1, 2, 6, 7]
def baseStart_69707 : Nat := 118140960795 + 69707 * 2 ^ 59
def prefixEnd_69707 : Nat := 4983230072969 + 3 ^ 40 * 69707 * 2
def baseEnd_69707 : Nat := 3977021775896000526881

theorem tailTrace_69707 : CollatzResearch.WordTrace tailWord_69707 prefixEnd_69707 3977021775896000526881 := by
  unfold tailWord_69707
  simp only [CollatzResearch.WordTrace]
  refine ⟨2542423158470918852903375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1694948772313945901935583 2542423158470918852903375)
  ·
    refine ⟨3813634737706378279355063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2542423158470918852903375 3813634737706378279355063)
    ·
      refine ⟨5720452106559567419032595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3813634737706378279355063 5720452106559567419032595)
      ·
        refine ⟨8580678159839351128548893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5720452106559567419032595 8580678159839351128548893)
        ·
          refine ⟨3217754309939756673205835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8580678159839351128548893 3217754309939756673205835)
          ·
            refine ⟨4826631464909635009808753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3217754309939756673205835 4826631464909635009808753)
            ·
              refine ⟨3619973598682226257356565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4826631464909635009808753 3619973598682226257356565)
              ·
                refine ⟨169686262438229355813589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3619973598682226257356565 169686262438229355813589)
                ·
                  refine ⟨3977021775896000526881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 169686262438229355813589 3977021775896000526881)
                  ·
                    rfl

theorem cell23_69707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 7].length) (baseStart_69707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69707 prefixEnd_69707 := by exact prefixLift 69707
  have htrace : WordTrace (prefixWord ++ tailWord_69707) baseStart_69707 baseEnd_69707 := by
    simpa [prefixWord, tailWord_69707, baseEnd_69707] using wordTrace_append hprefix tailTrace_69707
  have hstable : (prefixWord ++ tailWord_69707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69707).length < 2 ^ (prefixWord ++ tailWord_69707).sum := by decide
  have hdescent : baseEnd_69707 < baseStart_69707 := by decide
  rcases family_descends (prefixWord ++ tailWord_69707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69741 : List Nat := [1, 5, 1, 1, 2, 1, 1, 6, 5]
def baseStart_69741 : Nat := 118140960795 + 69741 * 2 ^ 59
def prefixEnd_69741 : Nat := 4983230072969 + 3 ^ 40 * 69741 * 2
def baseEnd_69741 : Nat := 3978961591701874635197

theorem tailTrace_69741 : CollatzResearch.WordTrace tailWord_69741 prefixEnd_69741 3978961591701874635197 := by
  unfold tailWord_69741
  simp only [CollatzResearch.WordTrace]
  refine ⟨2543663240347742659641077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1695775493565161773094051 2543663240347742659641077)
  ·
    refine ⟨238468428782600874341351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2543663240347742659641077 238468428782600874341351)
    ·
      refine ⟨357702643173901311512027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238468428782600874341351 357702643173901311512027)
      ·
        refine ⟨536553964760851967268041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357702643173901311512027 536553964760851967268041)
        ·
          refine ⟨402415473570638975451031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 536553964760851967268041 402415473570638975451031)
          ·
            refine ⟨603623210355958463176547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 402415473570638975451031 603623210355958463176547)
            ·
              refine ⟨905434815533937694764821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 603623210355958463176547 905434815533937694764821)
              ·
                refine ⟨42442256978153329442101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 905434815533937694764821 42442256978153329442101)
                ·
                  refine ⟨3978961591701874635197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42442256978153329442101 3978961591701874635197)
                  ·
                    rfl

theorem cell23_69741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_69741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69741 prefixEnd_69741 := by exact prefixLift 69741
  have htrace : WordTrace (prefixWord ++ tailWord_69741) baseStart_69741 baseEnd_69741 := by
    simpa [prefixWord, tailWord_69741, baseEnd_69741] using wordTrace_append hprefix tailTrace_69741
  have hstable : (prefixWord ++ tailWord_69741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69741).length < 2 ^ (prefixWord ++ tailWord_69741).sum := by decide
  have hdescent : baseEnd_69741 < baseStart_69741 := by decide
  rcases family_descends (prefixWord ++ tailWord_69741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69791 : List Nat := [1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 4]
def baseStart_69791 : Nat := 118140960795 + 69791 * 2 ^ 59
def prefixEnd_69791 : Nat := 4983230072969 + 3 ^ 40 * 69791 * 2
def baseEnd_69791 : Nat := 35836328358041676091543

theorem tailTrace_69791 : CollatzResearch.WordTrace tailWord_69791 prefixEnd_69791 35836328358041676091543 := by
  unfold tailWord_69791
  simp only [CollatzResearch.WordTrace]
  refine ⟨2545486890166601198961227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1696991260111067465974151 2545486890166601198961227)
  ·
    refine ⟨3818230335249901798441841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2545486890166601198961227 3818230335249901798441841)
    ·
      refine ⟨2863672751437426348831381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3818230335249901798441841 2863672751437426348831381)
      ·
        refine ⟨134234660223629360101471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2863672751437426348831381 134234660223629360101471)
        ·
          refine ⟨201351990335444040152207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134234660223629360101471 201351990335444040152207)
          ·
            refine ⟨302027985503166060228311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201351990335444040152207 302027985503166060228311)
            ·
              refine ⟨453041978254749090342467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302027985503166060228311 453041978254749090342467)
              ·
                refine ⟨679562967382123635513701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 453041978254749090342467 679562967382123635513701)
                ·
                  refine ⟨127418056384148181658819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 679562967382123635513701 127418056384148181658819)
                  ·
                    refine ⟨191127084576222272488229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 127418056384148181658819 191127084576222272488229)
                    ·
                      refine ⟨35836328358041676091543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 191127084576222272488229 35836328358041676091543)
                      ·
                        rfl

theorem cell23_69791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_69791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69791 prefixEnd_69791 := by exact prefixLift 69791
  have htrace : WordTrace (prefixWord ++ tailWord_69791) baseStart_69791 baseEnd_69791 := by
    simpa [prefixWord, tailWord_69791, baseEnd_69791] using wordTrace_append hprefix tailTrace_69791
  have hstable : (prefixWord ++ tailWord_69791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69791).length < 2 ^ (prefixWord ++ tailWord_69791).sum := by decide
  have hdescent : baseEnd_69791 < baseStart_69791 := by decide
  rcases family_descends (prefixWord ++ tailWord_69791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69825 : List Nat := [1, 2, 6, 1, 2, 1, 2, 1, 2, 1, 4]
def baseStart_69825 : Nat := 118140960795 + 69825 * 2 ^ 59
def prefixEnd_69825 : Nat := 4983230072969 + 3 ^ 40 * 69825 * 2
def baseEnd_69825 : Nat := 35853786700294543066387

theorem tailTrace_69825 : CollatzResearch.WordTrace tailWord_69825 prefixEnd_69825 35853786700294543066387 := by
  unfold tailWord_69825
  simp only [CollatzResearch.WordTrace]
  refine ⟨2546726972043425005698929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1697817981362283337132619 2546726972043425005698929)
  ·
    refine ⟨1910045229032568754274197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2546726972043425005698929 1910045229032568754274197)
    ·
      refine ⟨89533370110901660356603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1910045229032568754274197 89533370110901660356603)
      ·
        refine ⟨134300055166352490534905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89533370110901660356603 134300055166352490534905)
        ·
          refine ⟨100725041374764367901179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134300055166352490534905 100725041374764367901179)
          ·
            refine ⟨151087562062146551851769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100725041374764367901179 151087562062146551851769)
            ·
              refine ⟨113315671546609913888827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151087562062146551851769 113315671546609913888827)
              ·
                refine ⟨169973507319914870833241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113315671546609913888827 169973507319914870833241)
                ·
                  refine ⟨127480130489936153124931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169973507319914870833241 127480130489936153124931)
                  ·
                    refine ⟨191220195734904229687397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 127480130489936153124931 191220195734904229687397)
                    ·
                      refine ⟨35853786700294543066387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 191220195734904229687397 35853786700294543066387)
                      ·
                        rfl

theorem cell23_69825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_69825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69825 prefixEnd_69825 := by exact prefixLift 69825
  have htrace : WordTrace (prefixWord ++ tailWord_69825) baseStart_69825 baseEnd_69825 := by
    simpa [prefixWord, tailWord_69825, baseEnd_69825] using wordTrace_append hprefix tailTrace_69825
  have hstable : (prefixWord ++ tailWord_69825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69825).length < 2 ^ (prefixWord ++ tailWord_69825).sum := by decide
  have hdescent : baseEnd_69825 < baseStart_69825 := by decide
  rcases family_descends (prefixWord ++ tailWord_69825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69828 : List Nat := [2, 3, 3, 1, 2, 1, 1, 3, 2, 2, 3]
def baseStart_69828 : Nat := 118140960795 + 69828 * 2 ^ 59
def prefixEnd_69828 : Nat := 4983230072969 + 3 ^ 40 * 69828 * 2
def baseEnd_69828 : Nat := 35855327142258031328873

theorem tailTrace_69828 : CollatzResearch.WordTrace tailWord_69828 prefixEnd_69828 35855327142258031328873 := by
  unfold tailWord_69828
  simp only [CollatzResearch.WordTrace]
  refine ⟨1273418195516278259029069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1697890927355037678705425 1273418195516278259029069)
  ·
    refine ⟨477531823318604347135901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1273418195516278259029069 477531823318604347135901)
    ·
      refine ⟨179074433744476630175963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 477531823318604347135901 179074433744476630175963)
      ·
        refine ⟨268611650616714945263945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179074433744476630175963 268611650616714945263945)
        ·
          refine ⟨201458737962536208947959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 268611650616714945263945 201458737962536208947959)
          ·
            refine ⟨302188106943804313421939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201458737962536208947959 302188106943804313421939)
            ·
              refine ⟨453282160415706470132909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302188106943804313421939 453282160415706470132909)
              ·
                refine ⟨169980810155889926299841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 453282160415706470132909 169980810155889926299841)
                ·
                  refine ⟨127485607616917444724881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169980810155889926299841 127485607616917444724881)
                  ·
                    refine ⟨95614205712688083543661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 127485607616917444724881 95614205712688083543661)
                    ·
                      refine ⟨35855327142258031328873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 95614205712688083543661 35855327142258031328873)
                      ·
                        rfl

theorem cell23_69828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_69828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69828 prefixEnd_69828 := by exact prefixLift 69828
  have htrace : WordTrace (prefixWord ++ tailWord_69828) baseStart_69828 baseEnd_69828 := by
    simpa [prefixWord, tailWord_69828, baseEnd_69828] using wordTrace_append hprefix tailTrace_69828
  have hstable : (prefixWord ++ tailWord_69828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69828).length < 2 ^ (prefixWord ++ tailWord_69828).sum := by decide
  have hdescent : baseEnd_69828 < baseStart_69828 := by decide
  rcases family_descends (prefixWord ++ tailWord_69828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69861 : List Nat := [1, 3, 1, 4, 2, 1, 1, 2, 3, 5]
def baseStart_69861 : Nat := 118140960795 + 69861 * 2 ^ 59
def prefixEnd_69861 : Nat := 4983230072969 + 3 ^ 40 * 69861 * 2
def baseEnd_69861 : Nat := 11957424001285467405407

theorem tailTrace_69861 : CollatzResearch.WordTrace tailWord_69861 prefixEnd_69861 11957424001285467405407 := by
  unfold tailWord_69861
  simp only [CollatzResearch.WordTrace]
  refine ⟨2548039999913003154009437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1698693333275335436006291 2548039999913003154009437)
  ·
    refine ⟨955514999967376182753539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2548039999913003154009437 955514999967376182753539)
    ·
      refine ⟨1433272499951064274130309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 955514999967376182753539 1433272499951064274130309)
      ·
        refine ⟨268738593740824551399433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1433272499951064274130309 268738593740824551399433)
        ·
          refine ⟨201553945305618413549575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 268738593740824551399433 201553945305618413549575)
          ·
            refine ⟨302330917958427620324363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201553945305618413549575 302330917958427620324363)
            ·
              refine ⟨453496376937641430486545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302330917958427620324363 453496376937641430486545)
              ·
                refine ⟨340122282703231072864909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 453496376937641430486545 340122282703231072864909)
                ·
                  refine ⟨127545856013711652324341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 340122282703231072864909 127545856013711652324341)
                  ·
                    refine ⟨11957424001285467405407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 127545856013711652324341 11957424001285467405407)
                    ·
                      rfl

theorem cell23_69861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 5].length) (baseStart_69861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69861 prefixEnd_69861 := by exact prefixLift 69861
  have htrace : WordTrace (prefixWord ++ tailWord_69861) baseStart_69861 baseEnd_69861 := by
    simpa [prefixWord, tailWord_69861, baseEnd_69861] using wordTrace_append hprefix tailTrace_69861
  have hstable : (prefixWord ++ tailWord_69861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69861).length < 2 ^ (prefixWord ++ tailWord_69861).sum := by decide
  have hdescent : baseEnd_69861 < baseStart_69861 := by decide
  rcases family_descends (prefixWord ++ tailWord_69861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69881 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 1, 8, 2]
def baseStart_69881 : Nat := 118140960795 + 69881 * 2 ^ 59
def prefixEnd_69881 : Nat := 4983230072969 + 3 ^ 40 * 69881 * 2
def baseEnd_69881 : Nat := 35882541616946323966129

theorem tailTrace_69881 : CollatzResearch.WordTrace tailWord_69881 prefixEnd_69881 35882541616946323966129 := by
  unfold tailWord_69881
  simp only [CollatzResearch.WordTrace]
  refine ⟨2548769459840546569737497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1699179639893697713158331 2548769459840546569737497)
  ·
    refine ⟨1911577094880409927303123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2548769459840546569737497 1911577094880409927303123)
    ·
      refine ⟨2867365642320614890954685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1911577094880409927303123 2867365642320614890954685)
      ·
        refine ⟨1075262115870230584108007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2867365642320614890954685 1075262115870230584108007)
        ·
          refine ⟨1612893173805345876162011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1075262115870230584108007 1612893173805345876162011)
          ·
            refine ⟨2419339760708018814243017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1612893173805345876162011 2419339760708018814243017)
            ·
              refine ⟨1814504820531014110682263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2419339760708018814243017 1814504820531014110682263)
              ·
                refine ⟨2721757230796521166023395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1814504820531014110682263 2721757230796521166023395)
                ·
                  refine ⟨4082635846194781749035093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2721757230796521166023395 4082635846194781749035093)
                  ·
                    refine ⟨47843388822595098621505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4082635846194781749035093 47843388822595098621505)
                    ·
                      refine ⟨35882541616946323966129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 47843388822595098621505 35882541616946323966129)
                      ·
                        rfl

theorem cell23_69881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 8, 2].length) (baseStart_69881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69881 prefixEnd_69881 := by exact prefixLift 69881
  have htrace : WordTrace (prefixWord ++ tailWord_69881) baseStart_69881 baseEnd_69881 := by
    simpa [prefixWord, tailWord_69881, baseEnd_69881] using wordTrace_append hprefix tailTrace_69881
  have hstable : (prefixWord ++ tailWord_69881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69881).length < 2 ^ (prefixWord ++ tailWord_69881).sum := by decide
  have hdescent : baseEnd_69881 < baseStart_69881 := by decide
  rcases family_descends (prefixWord ++ tailWord_69881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69891 : List Nat := [1, 1, 1, 3, 2, 3, 2, 2, 4, 4]
def baseStart_69891 : Nat := 118140960795 + 69891 * 2 ^ 59
def prefixEnd_69891 : Nat := 4983230072969 + 3 ^ 40 * 69891 * 2
def baseEnd_69891 : Nat := 11962558807830428280361

theorem tailTrace_69891 : CollatzResearch.WordTrace tailWord_69891 prefixEnd_69891 11962558807830428280361 := by
  unfold tailWord_69891
  simp only [CollatzResearch.WordTrace]
  refine ⟨2549134189804318277601527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1699422793202878851734351 2549134189804318277601527)
  ·
    refine ⟨3823701284706477416402291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2549134189804318277601527 3823701284706477416402291)
    ·
      refine ⟨5735551927059716124603437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3823701284706477416402291 5735551927059716124603437)
      ·
        refine ⟨2150831972647393546726289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5735551927059716124603437 2150831972647393546726289)
        ·
          refine ⟨1613123979485545160044717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2150831972647393546726289 1613123979485545160044717)
          ·
            refine ⟨604921492307079435016769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1613123979485545160044717 604921492307079435016769)
            ·
              refine ⟨453691119230309576262577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 604921492307079435016769 453691119230309576262577)
              ·
                refine ⟨340268339422732182196933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 453691119230309576262577 340268339422732182196933)
                ·
                  refine ⟨63800313641762284161925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 340268339422732182196933 63800313641762284161925)
                  ·
                    refine ⟨11962558807830428280361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 63800313641762284161925 11962558807830428280361)
                    ·
                      rfl

theorem cell23_69891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 4, 4].length) (baseStart_69891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69891 prefixEnd_69891 := by exact prefixLift 69891
  have htrace : WordTrace (prefixWord ++ tailWord_69891) baseStart_69891 baseEnd_69891 := by
    simpa [prefixWord, tailWord_69891, baseEnd_69891] using wordTrace_append hprefix tailTrace_69891
  have hstable : (prefixWord ++ tailWord_69891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69891).length < 2 ^ (prefixWord ++ tailWord_69891).sum := by decide
  have hdescent : baseEnd_69891 < baseStart_69891 := by decide
  rcases family_descends (prefixWord ++ tailWord_69891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69895 : List Nat := [1, 1, 4, 5, 1, 1, 1, 3, 1, 5]
def baseStart_69895 : Nat := 118140960795 + 69895 * 2 ^ 59
def prefixEnd_69895 : Nat := 4983230072969 + 3 ^ 40 * 69895 * 2
def baseEnd_69895 : Nat := 11963243448703089730355

theorem tailTrace_69895 : CollatzResearch.WordTrace tailWord_69895 prefixEnd_69895 11963243448703089730355 := by
  unfold tailWord_69895
  simp only [CollatzResearch.WordTrace]
  refine ⟨2549280081789826960747139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1699520054526551307164759 2549280081789826960747139)
  ·
    refine ⟨3823920122684740441120709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2549280081789826960747139 3823920122684740441120709)
    ·
      refine ⟨716985023003388832710133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3823920122684740441120709 716985023003388832710133)
      ·
        refine ⟨67217345906567703066575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 716985023003388832710133 67217345906567703066575)
        ·
          refine ⟨100826018859851554599863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67217345906567703066575 100826018859851554599863)
          ·
            refine ⟨151239028289777331899795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100826018859851554599863 151239028289777331899795)
            ·
              refine ⟨226858542434665997849693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151239028289777331899795 226858542434665997849693)
              ·
                refine ⟨85071953412999749193635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 226858542434665997849693 85071953412999749193635)
                ·
                  refine ⟨127607930119499623790453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85071953412999749193635 127607930119499623790453)
                  ·
                    refine ⟨11963243448703089730355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 127607930119499623790453 11963243448703089730355)
                    ·
                      rfl

theorem cell23_69895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_69895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69895 prefixEnd_69895 := by exact prefixLift 69895
  have htrace : WordTrace (prefixWord ++ tailWord_69895) baseStart_69895 baseEnd_69895 := by
    simpa [prefixWord, tailWord_69895, baseEnd_69895] using wordTrace_append hprefix tailTrace_69895
  have hstable : (prefixWord ++ tailWord_69895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69895).length < 2 ^ (prefixWord ++ tailWord_69895).sum := by decide
  have hdescent : baseEnd_69895 < baseStart_69895 := by decide
  rcases family_descends (prefixWord ++ tailWord_69895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69925 : List Nat := [1, 3, 1, 2, 6, 1, 1, 1, 1, 6]
def baseStart_69925 : Nat := 118140960795 + 69925 * 2 ^ 59
def prefixEnd_69925 : Nat := 4983230072969 + 3 ^ 40 * 69925 * 2
def baseEnd_69925 : Nat := 11968378255248050605309

theorem tailTrace_69925 : CollatzResearch.WordTrace tailWord_69925 prefixEnd_69925 11968378255248050605309 := by
  unfold tailWord_69925
  simp only [CollatzResearch.WordTrace]
  refine ⟨2550374271681142084339229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1700249514454094722892819 2550374271681142084339229)
  ·
    refine ⟨956390351880428281627211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2550374271681142084339229 956390351880428281627211)
    ·
      refine ⟨1434585527820642422440817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 956390351880428281627211 1434585527820642422440817)
      ·
        refine ⟨1075939145865481816830613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1434585527820642422440817 1075939145865481816830613)
        ·
          refine ⟨50434647462444460163935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1075939145865481816830613 50434647462444460163935)
          ·
            refine ⟨75651971193666690245903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50434647462444460163935 75651971193666690245903)
            ·
              refine ⟨113477956790500035368855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75651971193666690245903 113477956790500035368855)
              ·
                refine ⟨170216935185750053053283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113477956790500035368855 170216935185750053053283)
                ·
                  refine ⟨255325402778625079579925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 170216935185750053053283 255325402778625079579925)
                  ·
                    refine ⟨11968378255248050605309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 255325402778625079579925 11968378255248050605309)
                    ·
                      rfl

theorem cell23_69925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 1, 6].length) (baseStart_69925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69925 prefixEnd_69925 := by exact prefixLift 69925
  have htrace : WordTrace (prefixWord ++ tailWord_69925) baseStart_69925 baseEnd_69925 := by
    simpa [prefixWord, tailWord_69925, baseEnd_69925] using wordTrace_append hprefix tailTrace_69925
  have hstable : (prefixWord ++ tailWord_69925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69925).length < 2 ^ (prefixWord ++ tailWord_69925).sum := by decide
  have hdescent : baseEnd_69925 < baseStart_69925 := by decide
  rcases family_descends (prefixWord ++ tailWord_69925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69928 : List Nat := [2, 1, 5, 1, 3, 1, 1, 1, 1, 1, 6]
def baseStart_69928 : Nat := 118140960795 + 69928 * 2 ^ 59
def prefixEnd_69928 : Nat := 4983230072969 + 3 ^ 40 * 69928 * 2
def baseEnd_69928 : Nat := 35906675207707640078413

theorem tailTrace_69928 : CollatzResearch.WordTrace tailWord_69928 prefixEnd_69928 35906675207707640078413 := by
  unfold tailWord_69928
  simp only [CollatzResearch.WordTrace]
  refine ⟨1275241845335136798349219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1700322460446849064465625 1275241845335136798349219)
  ·
    refine ⟨1912862768002705197523829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1275241845335136798349219 1912862768002705197523829)
    ·
      refine ⟨179330884500253612267859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1912862768002705197523829 179330884500253612267859)
      ·
        refine ⟨268996326750380418401789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179330884500253612267859 268996326750380418401789)
        ·
          refine ⟨100873622531392656900671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 268996326750380418401789 100873622531392656900671)
          ·
            refine ⟨151310433797088985351007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100873622531392656900671 151310433797088985351007)
            ·
              refine ⟨226965650695633478026511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151310433797088985351007 226965650695633478026511)
              ·
                refine ⟨340448476043450217039767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 226965650695633478026511 340448476043450217039767)
                ·
                  refine ⟨510672714065175325559651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 340448476043450217039767 510672714065175325559651)
                  ·
                    refine ⟨766009071097762988339477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 510672714065175325559651 766009071097762988339477)
                    ·
                      refine ⟨35906675207707640078413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 766009071097762988339477 35906675207707640078413)
                      ·
                        rfl

theorem cell23_69928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_69928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69928 prefixEnd_69928 := by exact prefixLift 69928
  have htrace : WordTrace (prefixWord ++ tailWord_69928) baseStart_69928 baseEnd_69928 := by
    simpa [prefixWord, tailWord_69928, baseEnd_69928] using wordTrace_append hprefix tailTrace_69928
  have hstable : (prefixWord ++ tailWord_69928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69928).length < 2 ^ (prefixWord ++ tailWord_69928).sum := by decide
  have hdescent : baseEnd_69928 < baseStart_69928 := by decide
  rcases family_descends (prefixWord ++ tailWord_69928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69948 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 6, 1, 3]
def baseStart_69948 : Nat := 118140960795 + 69948 * 2 ^ 59
def prefixEnd_69948 : Nat := 4983230072969 + 3 ^ 40 * 69948 * 2
def baseEnd_69948 : Nat := 35916944820797561828321

theorem tailTrace_69948 : CollatzResearch.WordTrace tailWord_69948 prefixEnd_69948 35916944820797561828321 := by
  unfold tailWord_69948
  simp only [CollatzResearch.WordTrace]
  refine ⟨1275606575298908506213249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1700808767065211341617665 1275606575298908506213249)
  ·
    refine ⟨956704931474181379659937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1275606575298908506213249 956704931474181379659937)
    ·
      refine ⟨717528698605636034744953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 956704931474181379659937 717528698605636034744953)
      ·
        refine ⟨538146523954227026058715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 717528698605636034744953 538146523954227026058715)
        ·
          refine ⟨807219785931340539088073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 538146523954227026058715 807219785931340539088073)
          ·
            refine ⟨605414839448505404316055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 807219785931340539088073 605414839448505404316055)
            ·
              refine ⟨908122259172758106474083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 605414839448505404316055 908122259172758106474083)
              ·
                refine ⟨1362183388759137159711125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 908122259172758106474083 1362183388759137159711125)
                ·
                  refine ⟨63852346348084554361459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1362183388759137159711125 63852346348084554361459)
                  ·
                    refine ⟨95778519522126831542189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63852346348084554361459 95778519522126831542189)
                    ·
                      refine ⟨35916944820797561828321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 95778519522126831542189 35916944820797561828321)
                      ·
                        rfl

theorem cell23_69948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_69948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69948 prefixEnd_69948 := by exact prefixLift 69948
  have htrace : WordTrace (prefixWord ++ tailWord_69948) baseStart_69948 baseEnd_69948 := by
    simpa [prefixWord, tailWord_69948, baseEnd_69948] using wordTrace_append hprefix tailTrace_69948
  have hstable : (prefixWord ++ tailWord_69948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69948).length < 2 ^ (prefixWord ++ tailWord_69948).sum := by decide
  have hdescent : baseEnd_69948 < baseStart_69948 := by decide
  rcases family_descends (prefixWord ++ tailWord_69948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69992 : List Nat := [2, 1, 4, 2, 2, 1, 3, 2, 1, 3, 2]
def baseStart_69992 : Nat := 118140960795 + 69992 * 2 ^ 59
def prefixEnd_69992 : Nat := 4983230072969 + 3 ^ 40 * 69992 * 2
def baseEnd_69992 : Nat := 35939537969595389678119

theorem tailTrace_69992 : CollatzResearch.WordTrace tailWord_69992 prefixEnd_69992 35939537969595389678119 := by
  unfold tailWord_69992
  simp only [CollatzResearch.WordTrace]
  refine ⟨1276408981219206263514115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1701878641625608351352153 1276408981219206263514115)
  ·
    refine ⟨1914613471828809395271173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1276408981219206263514115 1914613471828809395271173)
    ·
      refine ⟨358990025967901761613345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1914613471828809395271173 358990025967901761613345)
      ·
        refine ⟨269242519475926321210009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 358990025967901761613345 269242519475926321210009)
        ·
          refine ⟨201931889606944740907507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 269242519475926321210009 201931889606944740907507)
          ·
            refine ⟨302897834410417111361261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201931889606944740907507 302897834410417111361261)
            ·
              refine ⟨113586687903906416760473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 302897834410417111361261 113586687903906416760473)
              ·
                refine ⟨85190015927929812570355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113586687903906416760473 85190015927929812570355)
                ·
                  refine ⟨127785023891894718855533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85190015927929812570355 127785023891894718855533)
                  ·
                    refine ⟨47919383959460519570825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 127785023891894718855533 47919383959460519570825)
                    ·
                      refine ⟨35939537969595389678119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 47919383959460519570825 35939537969595389678119)
                      ·
                        rfl

theorem cell23_69992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_69992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_69992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_69992 prefixEnd_69992 := by exact prefixLift 69992
  have htrace : WordTrace (prefixWord ++ tailWord_69992) baseStart_69992 baseEnd_69992 := by
    simpa [prefixWord, tailWord_69992, baseEnd_69992] using wordTrace_append hprefix tailTrace_69992
  have hstable : (prefixWord ++ tailWord_69992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69992).length < 2 ^ (prefixWord ++ tailWord_69992).sum := by decide
  have hdescent : baseEnd_69992 < baseStart_69992 := by decide
  rcases family_descends (prefixWord ++ tailWord_69992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70001 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 4, 2, 4]
def baseStart_70001 : Nat := 118140960795 + 70001 * 2 ^ 59
def prefixEnd_70001 : Nat := 4983230072969 + 3 ^ 40 * 70001 * 2
def baseEnd_70001 : Nat := 35944159295485854465577

theorem tailTrace_70001 : CollatzResearch.WordTrace tailWord_70001 prefixEnd_70001 35944159295485854465577 := by
  unfold tailWord_70001
  simp only [CollatzResearch.WordTrace]
  refine ⟨2553146219405807064105857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1702097479603871376070571 2553146219405807064105857)
  ·
    refine ⟨1914859664554355298079393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2553146219405807064105857 1914859664554355298079393)
    ·
      refine ⟨1436144748415766473559545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1914859664554355298079393 1436144748415766473559545)
      ·
        refine ⟨1077108561311824855169659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1436144748415766473559545 1077108561311824855169659)
        ·
          refine ⟨1615662841967737282754489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1077108561311824855169659 1615662841967737282754489)
          ·
            refine ⟨1211747131475802962065867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1615662841967737282754489 1211747131475802962065867)
            ·
              refine ⟨1817620697213704443098801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1211747131475802962065867 1817620697213704443098801)
              ·
                refine ⟨1363215522910278332324101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1817620697213704443098801 1363215522910278332324101)
                ·
                  refine ⟨255602910545677187310769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1363215522910278332324101 255602910545677187310769)
                  ·
                    refine ⟨191702182909257890483077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 255602910545677187310769 191702182909257890483077)
                    ·
                      refine ⟨35944159295485854465577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 191702182909257890483077 35944159295485854465577)
                      ·
                        rfl

theorem cell23_70001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_70001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70001 prefixEnd_70001 := by exact prefixLift 70001
  have htrace : WordTrace (prefixWord ++ tailWord_70001) baseStart_70001 baseEnd_70001 := by
    simpa [prefixWord, tailWord_70001, baseEnd_70001] using wordTrace_append hprefix tailTrace_70001
  have hstable : (prefixWord ++ tailWord_70001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70001).length < 2 ^ (prefixWord ++ tailWord_70001).sum := by decide
  have hdescent : baseEnd_70001 < baseStart_70001 := by decide
  rcases family_descends (prefixWord ++ tailWord_70001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70005 : List Nat := [1, 3, 4, 1, 2, 1, 1, 1, 3, 4, 2]
def baseStart_70005 : Nat := 118140960795 + 70005 * 2 ^ 59
def prefixEnd_70005 : Nat := 4983230072969 + 3 ^ 40 * 70005 * 2
def baseEnd_70005 : Nat := 35946213218103838815559

theorem tailTrace_70005 : CollatzResearch.WordTrace tailWord_70005 prefixEnd_70005 35946213218103838815559 := by
  unfold tailWord_70005
  simp only [CollatzResearch.WordTrace]
  refine ⟨2553292111391315747251469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1702194740927543831500979 2553292111391315747251469)
  ·
    refine ⟨957484541771743405219301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2553292111391315747251469 957484541771743405219301)
    ·
      refine ⟨179528351582201888478619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 957484541771743405219301 179528351582201888478619)
      ·
        refine ⟨269292527373302832717929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179528351582201888478619 269292527373302832717929)
        ·
          refine ⟨201969395529977124538447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 269292527373302832717929 201969395529977124538447)
          ·
            refine ⟨302954093294965686807671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201969395529977124538447 302954093294965686807671)
            ·
              refine ⟨454431139942448530211507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302954093294965686807671 454431139942448530211507)
              ·
                refine ⟨681646709913672795317261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 454431139942448530211507 681646709913672795317261)
                ·
                  refine ⟨255617516217627298243973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 681646709913672795317261 255617516217627298243973)
                  ·
                    refine ⟨47928284290805118420745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 255617516217627298243973 47928284290805118420745)
                    ·
                      refine ⟨35946213218103838815559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 47928284290805118420745 35946213218103838815559)
                      ·
                        rfl

theorem cell23_70005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_70005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70005 prefixEnd_70005 := by exact prefixLift 70005
  have htrace : WordTrace (prefixWord ++ tailWord_70005) baseStart_70005 baseEnd_70005 := by
    simpa [prefixWord, tailWord_70005, baseEnd_70005] using wordTrace_append hprefix tailTrace_70005
  have hstable : (prefixWord ++ tailWord_70005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70005).length < 2 ^ (prefixWord ++ tailWord_70005).sum := by decide
  have hdescent : baseEnd_70005 < baseStart_70005 := by decide
  rcases family_descends (prefixWord ++ tailWord_70005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70041 : List Nat := [1, 2, 1, 2, 1, 4, 2, 2, 1, 7]
def baseStart_70041 : Nat := 118140960795 + 70041 * 2 ^ 59
def prefixEnd_70041 : Nat := 4983230072969 + 3 ^ 40 * 70041 * 2
def baseEnd_70041 : Nat := 11988232840555232655131

theorem tailTrace_70041 : CollatzResearch.WordTrace tailWord_70041 prefixEnd_70041 11988232840555232655131 := by
  unfold tailWord_70041
  simp only [CollatzResearch.WordTrace]
  refine ⟨2554605139260893895561977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1703070092840595930374651 2554605139260893895561977)
  ·
    refine ⟨1915953854445670421671483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2554605139260893895561977 1915953854445670421671483)
    ·
      refine ⟨2873930781668505632507225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1915953854445670421671483 2873930781668505632507225)
      ·
        refine ⟨2155448086251379224380419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2873930781668505632507225 2155448086251379224380419)
        ·
          refine ⟨3233172129377068836570629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2155448086251379224380419 3233172129377068836570629)
          ·
            refine ⟨606219774258200406856993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3233172129377068836570629 606219774258200406856993)
            ·
              refine ⟨454664830693650305142745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 606219774258200406856993 454664830693650305142745)
              ·
                refine ⟨340998623020237728857059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 454664830693650305142745 340998623020237728857059)
                ·
                  refine ⟨511497934530356593285589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 340998623020237728857059 511497934530356593285589)
                  ·
                    refine ⟨11988232840555232655131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 511497934530356593285589 11988232840555232655131)
                    ·
                      rfl

theorem cell23_70041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 7].length) (baseStart_70041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70041 prefixEnd_70041 := by exact prefixLift 70041
  have htrace : WordTrace (prefixWord ++ tailWord_70041) baseStart_70041 baseEnd_70041 := by
    simpa [prefixWord, tailWord_70041, baseEnd_70041] using wordTrace_append hprefix tailTrace_70041
  have hstable : (prefixWord ++ tailWord_70041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70041).length < 2 ^ (prefixWord ++ tailWord_70041).sum := by decide
  have hdescent : baseEnd_70041 < baseStart_70041 := by decide
  rcases family_descends (prefixWord ++ tailWord_70041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70091 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 6]
def baseStart_70091 : Nat := 118140960795 + 70091 * 2 ^ 59
def prefixEnd_70091 : Nat := 4983230072969 + 3 ^ 40 * 70091 * 2
def baseEnd_70091 : Nat := 35990372554390502340163

theorem tailTrace_70091 : CollatzResearch.WordTrace tailWord_70091 prefixEnd_70091 35990372554390502340163 := by
  unfold tailWord_70091
  simp only [CollatzResearch.WordTrace]
  refine ⟨2556428789079752434882127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1704285859386501623254751 2556428789079752434882127)
  ·
    refine ⟨3834643183619628652323191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2556428789079752434882127 3834643183619628652323191)
    ·
      refine ⟨5751964775429442978484787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3834643183619628652323191 5751964775429442978484787)
      ·
        refine ⟨8627947163144164467727181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5751964775429442978484787 8627947163144164467727181)
        ·
          refine ⟨3235480186179061675397693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8627947163144164467727181 3235480186179061675397693)
          ·
            refine ⟨1213305069817148128274135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3235480186179061675397693 1213305069817148128274135)
            ·
              refine ⟨1819957604725722192411203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1213305069817148128274135 1819957604725722192411203)
              ·
                refine ⟨2729936407088583288616805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1819957604725722192411203 2729936407088583288616805)
                ·
                  refine ⟨511863076329109366615651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2729936407088583288616805 511863076329109366615651)
                  ·
                    refine ⟨767794614493664049923477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 511863076329109366615651 767794614493664049923477)
                    ·
                      refine ⟨35990372554390502340163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 767794614493664049923477 35990372554390502340163)
                      ·
                        rfl

theorem cell23_70091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 6].length) (baseStart_70091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70091 prefixEnd_70091 := by exact prefixLift 70091
  have htrace : WordTrace (prefixWord ++ tailWord_70091) baseStart_70091 baseEnd_70091 := by
    simpa [prefixWord, tailWord_70091, baseEnd_70091] using wordTrace_append hprefix tailTrace_70091
  have hstable : (prefixWord ++ tailWord_70091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70091).length < 2 ^ (prefixWord ++ tailWord_70091).sum := by decide
  have hdescent : baseEnd_70091 < baseStart_70091 := by decide
  rcases family_descends (prefixWord ++ tailWord_70091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70121 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 8]
def baseStart_70121 : Nat := 118140960795 + 70121 * 2 ^ 59
def prefixEnd_70121 : Nat := 4983230072969 + 3 ^ 40 * 70121 * 2
def baseEnd_70121 : Nat := 36005776974025384965025

theorem tailTrace_70121 : CollatzResearch.WordTrace tailWord_70121 prefixEnd_70121 36005776974025384965025 := by
  unfold tailWord_70121
  simp only [CollatzResearch.WordTrace]
  refine ⟨2557522978971067558474217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1705015319314045038982811 2557522978971067558474217)
  ·
    refine ⟨1918142234228300668855663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2557522978971067558474217 1918142234228300668855663)
    ·
      refine ⟨2877213351342451003283495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1918142234228300668855663 2877213351342451003283495)
      ·
        refine ⟨4315820027013676504925243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2877213351342451003283495 4315820027013676504925243)
        ·
          refine ⟨6473730040520514757387865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4315820027013676504925243 6473730040520514757387865)
          ·
            refine ⟨4855297530390386068040899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6473730040520514757387865 4855297530390386068040899)
            ·
              refine ⟨7282946295585579102061349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4855297530390386068040899 7282946295585579102061349)
              ·
                refine ⟨1365552430422296081636503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7282946295585579102061349 1365552430422296081636503)
                ·
                  refine ⟨2048328645633444122454755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1365552430422296081636503 2048328645633444122454755)
                  ·
                    refine ⟨3072492968450166183682133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2048328645633444122454755 3072492968450166183682133)
                    ·
                      refine ⟨36005776974025384965025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 3072492968450166183682133 36005776974025384965025)
                      ·
                        rfl

theorem cell23_70121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 8].length) (baseStart_70121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70121 prefixEnd_70121 := by exact prefixLift 70121
  have htrace : WordTrace (prefixWord ++ tailWord_70121) baseStart_70121 baseEnd_70121 := by
    simpa [prefixWord, tailWord_70121, baseEnd_70121] using wordTrace_append hprefix tailTrace_70121
  have hstable : (prefixWord ++ tailWord_70121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70121).length < 2 ^ (prefixWord ++ tailWord_70121).sum := by decide
  have hdescent : baseEnd_70121 < baseStart_70121 := by decide
  rcases family_descends (prefixWord ++ tailWord_70121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70172 : List Nat := [2, 2, 3, 1, 2, 2, 1, 3, 2, 3, 2]
def baseStart_70172 : Nat := 118140960795 + 70172 * 2 ^ 59
def prefixEnd_70172 : Nat := 4983230072969 + 3 ^ 40 * 70172 * 2
def baseEnd_70172 : Nat := 36031964487404685427291

theorem tailTrace_70172 : CollatzResearch.WordTrace tailWord_70172 prefixEnd_70172 36031964487404685427291 := by
  unfold tailWord_70172
  simp only [CollatzResearch.WordTrace]
  refine ⟨1279691550893151634290385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1706255401190868845720513 1279691550893151634290385)
  ·
    refine ⟨959768663169863725717789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1279691550893151634290385 959768663169863725717789)
    ·
      refine ⟨359913248688698897144171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 959768663169863725717789 359913248688698897144171)
      ·
        refine ⟨539869873033048345716257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359913248688698897144171 539869873033048345716257)
        ·
          refine ⟨404902404774786259287193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 539869873033048345716257 404902404774786259287193)
          ·
            refine ⟨303676803581089694465395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 404902404774786259287193 303676803581089694465395)
            ·
              refine ⟨455515205371634541698093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 303676803581089694465395 455515205371634541698093)
              ·
                refine ⟨170818202014362953136785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 455515205371634541698093 170818202014362953136785)
                ·
                  refine ⟨128113651510772214852589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170818202014362953136785 128113651510772214852589)
                  ·
                    refine ⟨48042619316539580569721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 128113651510772214852589 48042619316539580569721)
                    ·
                      refine ⟨36031964487404685427291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 48042619316539580569721 36031964487404685427291)
                      ·
                        rfl

theorem cell23_70172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_70172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70172 prefixEnd_70172 := by exact prefixLift 70172
  have htrace : WordTrace (prefixWord ++ tailWord_70172) baseStart_70172 baseEnd_70172 := by
    simpa [prefixWord, tailWord_70172, baseEnd_70172] using wordTrace_append hprefix tailTrace_70172
  have hstable : (prefixWord ++ tailWord_70172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70172).length < 2 ^ (prefixWord ++ tailWord_70172).sum := by decide
  have hdescent : baseEnd_70172 < baseStart_70172 := by decide
  rcases family_descends (prefixWord ++ tailWord_70172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70208 : List Nat := [2, 1, 1, 2, 2, 2, 5, 8]
def baseStart_70208 : Nat := 118140960795 + 70208 * 2 ^ 59
def prefixEnd_70208 : Nat := 4983230072969 + 3 ^ 40 * 70208 * 2
def baseEnd_70208 : Nat := 1335201844109872021375

theorem tailTrace_70208 : CollatzResearch.WordTrace tailWord_70208 prefixEnd_70208 1335201844109872021375 := by
  unfold tailWord_70208
  simp only [CollatzResearch.WordTrace]
  refine ⟨1280348064827940708445639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1707130753103920944594185 1280348064827940708445639)
  ·
    refine ⟨1920522097241911062668459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1280348064827940708445639 1920522097241911062668459)
    ·
      refine ⟨2880783145862866594002689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1920522097241911062668459 2880783145862866594002689)
      ·
        refine ⟨2160587359397149945502017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2880783145862866594002689 2160587359397149945502017)
        ·
          refine ⟨1620440519547862459126513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2160587359397149945502017 1620440519547862459126513)
          ·
            refine ⟨1215330389660896844344885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1620440519547862459126513 1215330389660896844344885)
            ·
              refine ⟨113937224030709079157333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1215330389660896844344885 113937224030709079157333)
              ·
                refine ⟨1335201844109872021375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 113937224030709079157333 1335201844109872021375)
                ·
                  rfl

theorem cell23_70208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 8].length) (baseStart_70208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70208 prefixEnd_70208 := by exact prefixLift 70208
  have htrace : WordTrace (prefixWord ++ tailWord_70208) baseStart_70208 baseEnd_70208 := by
    simpa [prefixWord, tailWord_70208, baseEnd_70208] using wordTrace_append hprefix tailTrace_70208
  have hstable : (prefixWord ++ tailWord_70208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70208).length < 2 ^ (prefixWord ++ tailWord_70208).sum := by decide
  have hdescent : baseEnd_70208 < baseStart_70208 := by decide
  rcases family_descends (prefixWord ++ tailWord_70208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70215 : List Nat := [1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 4]
def baseStart_70215 : Nat := 118140960795 + 70215 * 2 ^ 59
def prefixEnd_70215 : Nat := 4983230072969 + 3 ^ 40 * 70215 * 2
def baseEnd_70215 : Nat := 36054044155548017189593

theorem tailTrace_70215 : CollatzResearch.WordTrace tailWord_70215 prefixEnd_70215 36054044155548017189593 := by
  unfold tailWord_70215
  simp only [CollatzResearch.WordTrace]
  refine ⟨2560951440630521612396099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1707300960420347741597399 2560951440630521612396099)
  ·
    refine ⟨3841427160945782418594149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2560951440630521612396099 3841427160945782418594149)
    ·
      refine ⟨720267592677334203486403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3841427160945782418594149 720267592677334203486403)
      ·
        refine ⟨1080401389016001305229605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 720267592677334203486403 1080401389016001305229605)
        ·
          refine ⟨202575260440500244730551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1080401389016001305229605 202575260440500244730551)
          ·
            refine ⟨303862890660750367095827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202575260440500244730551 303862890660750367095827)
            ·
              refine ⟨455794335991125550643741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 303862890660750367095827 455794335991125550643741)
              ·
                refine ⟨170922875996672081491403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 455794335991125550643741 170922875996672081491403)
                ·
                  refine ⟨256384313995008122237105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 170922875996672081491403 256384313995008122237105)
                  ·
                    refine ⟨192288235496256091677829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 256384313995008122237105 192288235496256091677829)
                    ·
                      refine ⟨36054044155548017189593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 192288235496256091677829 36054044155548017189593)
                      ·
                        rfl

theorem cell23_70215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_70215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70215 prefixEnd_70215 := by exact prefixLift 70215
  have htrace : WordTrace (prefixWord ++ tailWord_70215) baseStart_70215 baseEnd_70215 := by
    simpa [prefixWord, tailWord_70215, baseEnd_70215] using wordTrace_append hprefix tailTrace_70215
  have hstable : (prefixWord ++ tailWord_70215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70215).length < 2 ^ (prefixWord ++ tailWord_70215).sum := by decide
  have hdescent : baseEnd_70215 < baseStart_70215 := by decide
  rcases family_descends (prefixWord ++ tailWord_70215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70225 : List Nat := [1, 2, 2, 1, 3, 4, 3, 7]
def baseStart_70225 : Nat := 118140960795 + 70225 * 2 ^ 59
def prefixEnd_70225 : Nat := 4983230072969 + 3 ^ 40 * 70225 * 2
def baseEnd_70225 : Nat := 1335525146744184372761

theorem tailTrace_70225 : CollatzResearch.WordTrace tailWord_70225 prefixEnd_70225 1335525146744184372761 := by
  unfold tailWord_70225
  simp only [CollatzResearch.WordTrace]
  refine ⟨2561316170594293320260129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1707544113729528880173419 2561316170594293320260129)
  ·
    refine ⟨1920987127945719990195097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2561316170594293320260129 1920987127945719990195097)
    ·
      refine ⟨1440740345959289992646323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1920987127945719990195097 1440740345959289992646323)
      ·
        refine ⟨2161110518938934988969485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1440740345959289992646323 2161110518938934988969485)
        ·
          refine ⟨810416444602100620863557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2161110518938934988969485 810416444602100620863557)
          ·
            refine ⟨151953083362893866411917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 810416444602100620863557 151953083362893866411917)
            ·
              refine ⟨56982406261085199904469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 151953083362893866411917 56982406261085199904469)
              ·
                refine ⟨1335525146744184372761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 56982406261085199904469 1335525146744184372761)
                ·
                  rfl

theorem cell23_70225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 7].length) (baseStart_70225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70225 prefixEnd_70225 := by exact prefixLift 70225
  have htrace : WordTrace (prefixWord ++ tailWord_70225) baseStart_70225 baseEnd_70225 := by
    simpa [prefixWord, tailWord_70225, baseEnd_70225] using wordTrace_append hprefix tailTrace_70225
  have hstable : (prefixWord ++ tailWord_70225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70225).length < 2 ^ (prefixWord ++ tailWord_70225).sum := by decide
  have hdescent : baseEnd_70225 < baseStart_70225 := by decide
  rcases family_descends (prefixWord ++ tailWord_70225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70236 : List Nat := [2, 2, 4, 1, 3, 2, 2, 1, 1, 1, 4]
def baseStart_70236 : Nat := 118140960795 + 70236 * 2 ^ 59
def prefixEnd_70236 : Nat := 4983230072969 + 3 ^ 40 * 70236 * 2
def baseEnd_70236 : Nat := 36064827249292435026997

theorem tailTrace_70236 : CollatzResearch.WordTrace tailWord_70236 prefixEnd_70236 36064827249292435026997 := by
  unfold tailWord_70236
  simp only [CollatzResearch.WordTrace]
  refine ⟨1280858686777221099455281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1707811582369628132607041 1280858686777221099455281)
  ·
    refine ⟨960644015082915824591461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1280858686777221099455281 960644015082915824591461)
    ·
      refine ⟨180120752828046717110899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 960644015082915824591461 180120752828046717110899)
      ·
        refine ⟨270181129242070075666349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180120752828046717110899 270181129242070075666349)
        ·
          refine ⟨101317923465776278374881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 270181129242070075666349 101317923465776278374881)
          ·
            refine ⟨75988442599332208781161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101317923465776278374881 75988442599332208781161)
            ·
              refine ⟨56991331949499156585871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75988442599332208781161 56991331949499156585871)
              ·
                refine ⟨85486997924248734878807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56991331949499156585871 85486997924248734878807)
                ·
                  refine ⟨128230496886373102318211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85486997924248734878807 128230496886373102318211)
                  ·
                    refine ⟨192345745329559653477317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 128230496886373102318211 192345745329559653477317)
                    ·
                      refine ⟨36064827249292435026997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 192345745329559653477317 36064827249292435026997)
                      ·
                        rfl

theorem cell23_70236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_70236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70236 prefixEnd_70236 := by exact prefixLift 70236
  have htrace : WordTrace (prefixWord ++ tailWord_70236) baseStart_70236 baseEnd_70236 := by
    simpa [prefixWord, tailWord_70236, baseEnd_70236] using wordTrace_append hprefix tailTrace_70236
  have hstable : (prefixWord ++ tailWord_70236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70236).length < 2 ^ (prefixWord ++ tailWord_70236).sum := by decide
  have hdescent : baseEnd_70236 < baseStart_70236 := by decide
  rcases family_descends (prefixWord ++ tailWord_70236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70242 : List Nat := [3, 3, 2, 3, 1, 1, 10]
def baseStart_70242 : Nat := 118140960795 + 70242 * 2 ^ 59
def prefixEnd_70242 : Nat := 4983230072969 + 3 ^ 40 * 70242 * 2
def baseEnd_70242 : Nat := 445282816459498908049

theorem tailTrace_70242 : CollatzResearch.WordTrace tailWord_70242 prefixEnd_70242 445282816459498908049 := by
  unfold tailWord_70242
  simp only [CollatzResearch.WordTrace]
  refine ⟨640484052883176305907245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1707957474355136815752653 640484052883176305907245)
  ·
    refine ⟨240181519831191114715217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 640484052883176305907245 240181519831191114715217)
    ·
      refine ⟨180136139873393336036413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240181519831191114715217 180136139873393336036413)
      ·
        refine ⟨67551052452522501013655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180136139873393336036413 67551052452522501013655)
        ·
          refine ⟨101326578678783751520483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67551052452522501013655 101326578678783751520483)
          ·
            refine ⟨151989868018175627280725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101326578678783751520483 151989868018175627280725)
            ·
              refine ⟨445282816459498908049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 151989868018175627280725 445282816459498908049)
              ·
                rfl

theorem cell23_70242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 10].length) (baseStart_70242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70242 prefixEnd_70242 := by exact prefixLift 70242
  have htrace : WordTrace (prefixWord ++ tailWord_70242) baseStart_70242 baseEnd_70242 := by
    simpa [prefixWord, tailWord_70242, baseEnd_70242] using wordTrace_append hprefix tailTrace_70242
  have hstable : (prefixWord ++ tailWord_70242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70242).length < 2 ^ (prefixWord ++ tailWord_70242).sum := by decide
  have hdescent : baseEnd_70242 < baseStart_70242 := by decide
  rcases family_descends (prefixWord ++ tailWord_70242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70269 : List Nat := [1, 4, 1, 1, 5, 2, 1, 1, 1, 3, 3]
def baseStart_70269 : Nat := 118140960795 + 70269 * 2 ^ 59
def prefixEnd_70269 : Nat := 4983230072969 + 3 ^ 40 * 70269 * 2
def baseEnd_70269 : Nat := 36081772110890805914345

theorem tailTrace_70269 : CollatzResearch.WordTrace tailWord_70269 prefixEnd_70269 36081772110890805914345 := by
  unfold tailWord_70269
  simp only [CollatzResearch.WordTrace]
  refine ⟨2562920982434888834861861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1708613988289925889907907 2562920982434888834861861)
  ·
    refine ⟨480547684206541656536599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2562920982434888834861861 480547684206541656536599)
    ·
      refine ⟨720821526309812484804899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 480547684206541656536599 720821526309812484804899)
      ·
        refine ⟨1081232289464718727207349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 720821526309812484804899 1081232289464718727207349)
        ·
          refine ⟨101365527137317380675689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1081232289464718727207349 101365527137317380675689)
          ·
            refine ⟨76024145352988035506767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101365527137317380675689 76024145352988035506767)
            ·
              refine ⟨114036218029482053260151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76024145352988035506767 114036218029482053260151)
              ·
                refine ⟨171054327044223079890227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114036218029482053260151 171054327044223079890227)
                ·
                  refine ⟨256581490566334619835341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 171054327044223079890227 256581490566334619835341)
                  ·
                    refine ⟨96218058962375482438253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 256581490566334619835341 96218058962375482438253)
                    ·
                      refine ⟨36081772110890805914345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 96218058962375482438253 36081772110890805914345)
                      ·
                        rfl

theorem cell23_70269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 3, 3].length) (baseStart_70269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_70269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_70269 prefixEnd_70269 := by exact prefixLift 70269
  have htrace : WordTrace (prefixWord ++ tailWord_70269) baseStart_70269 baseEnd_70269 := by
    simpa [prefixWord, tailWord_70269, baseEnd_70269] using wordTrace_append hprefix tailTrace_70269
  have hstable : (prefixWord ++ tailWord_70269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70269).length < 2 ^ (prefixWord ++ tailWord_70269).sum := by decide
  have hdescent : baseEnd_70269 < baseStart_70269 := by decide
  rcases family_descends (prefixWord ++ tailWord_70269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
