import V185TrunkScan20Chunk091

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_560249 : List Nat := [1, 2, 1, 3, 5, 1, 1, 1, 5]
def baseStart_560249 : Nat := 118140960795 + 560249 * 2 ^ 59
def prefixEnd_560249 : Nat := 4983230072969 + 3 ^ 40 * 560249 * 2
def baseEnd_560249 : Nat := 255712909511896672809749

theorem tailTrace_560249 : CollatzResearch.WordTrace tailWord_560249 prefixEnd_560249 255712909511896672809749 := by
  unfold tailWord_560249
  simp only [CollatzResearch.WordTrace]
  refine ⟨20433959747321030756603801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13622639831547353837735867 20433959747321030756603801)
  ·
    refine ⟨15325469810490773067452851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20433959747321030756603801 15325469810490773067452851)
    ·
      refine ⟨22988204715736159601179277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15325469810490773067452851 22988204715736159601179277)
      ·
        refine ⟨8620576768401059850442229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22988204715736159601179277 8620576768401059850442229)
        ·
          refine ⟨808179072037599360978959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8620576768401059850442229 808179072037599360978959)
          ·
            refine ⟨1212268608056399041468439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 808179072037599360978959 1212268608056399041468439)
            ·
              refine ⟨1818402912084598562202659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1212268608056399041468439 1818402912084598562202659)
              ·
                refine ⟨2727604368126897843303989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1818402912084598562202659 2727604368126897843303989)
                ·
                  refine ⟨255712909511896672809749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2727604368126897843303989 255712909511896672809749)
                  ·
                    rfl

theorem cell20_560249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 5].length) (baseStart_560249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560249 prefixEnd_560249 := by exact prefixLift 560249
  have htrace : WordTrace (prefixWord ++ tailWord_560249) baseStart_560249 baseEnd_560249 := by
    simpa [prefixWord, tailWord_560249, baseEnd_560249] using wordTrace_append hprefix tailTrace_560249
  have hstable : (prefixWord ++ tailWord_560249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560249).length < 2 ^ (prefixWord ++ tailWord_560249).sum := by decide
  have hdescent : baseEnd_560249 < baseStart_560249 := by decide
  rcases family_descends (prefixWord ++ tailWord_560249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560266 : List Nat := [3, 1, 2, 3, 1, 1, 5, 1, 3]
def baseStart_560266 : Nat := 118140960795 + 560266 * 2 ^ 59
def prefixEnd_560266 : Nat := 4983230072969 + 3 ^ 40 * 560266 * 2
def baseEnd_560266 : Nat := 255720668775120169243013

theorem tailTrace_560266 : CollatzResearch.WordTrace tailWord_560266 prefixEnd_560266 255720668775120169243013 := by
  unfold tailWord_560266
  simp only [CollatzResearch.WordTrace]
  refine ⟨5108644947064860664993163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13623053192172961773315101 5108644947064860664993163)
  ·
    refine ⟨7662967420597290997489745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5108644947064860664993163 7662967420597290997489745)
    ·
      refine ⟨5747225565447968248117309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7662967420597290997489745 5747225565447968248117309)
      ·
        refine ⟨2155209587042988093043991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5747225565447968248117309 2155209587042988093043991)
        ·
          refine ⟨3232814380564482139565987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2155209587042988093043991 3232814380564482139565987)
          ·
            refine ⟨4849221570846723209348981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3232814380564482139565987 4849221570846723209348981)
            ·
              refine ⟨454614522266880300876467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4849221570846723209348981 454614522266880300876467)
              ·
                refine ⟨681921783400320451314701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 454614522266880300876467 681921783400320451314701)
                ·
                  refine ⟨255720668775120169243013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 681921783400320451314701 255720668775120169243013)
                  ·
                    rfl

theorem cell20_560266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 3].length) (baseStart_560266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560266 prefixEnd_560266 := by exact prefixLift 560266
  have htrace : WordTrace (prefixWord ++ tailWord_560266) baseStart_560266 baseEnd_560266 := by
    simpa [prefixWord, tailWord_560266, baseEnd_560266] using wordTrace_append hprefix tailTrace_560266
  have hstable : (prefixWord ++ tailWord_560266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560266).length < 2 ^ (prefixWord ++ tailWord_560266).sum := by decide
  have hdescent : baseEnd_560266 < baseStart_560266 := by decide
  rcases family_descends (prefixWord ++ tailWord_560266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560277 : List Nat := [1, 3, 2, 1, 1, 1, 2, 3, 6]
def baseStart_560277 : Nat := 118140960795 + 560277 * 2 ^ 59
def prefixEnd_560277 : Nat := 4983230072969 + 3 ^ 40 * 560277 * 2
def baseEnd_560277 : Nat := 255725689474853019876301

theorem tailTrace_560277 : CollatzResearch.WordTrace tailWord_560277 prefixEnd_560277 255725689474853019876301 := by
  unfold tailWord_560277
  simp only [CollatzResearch.WordTrace]
  refine ⟨20434980991219591538623085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13623320660813061025748723 20434980991219591538623085)
  ·
    refine ⟨7663117871707346826983657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20434980991219591538623085 7663117871707346826983657)
    ·
      refine ⟨5747338403780510120237743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7663117871707346826983657 5747338403780510120237743)
      ·
        refine ⟨8621007605670765180356615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5747338403780510120237743 8621007605670765180356615)
        ·
          refine ⟨12931511408506147770534923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8621007605670765180356615 12931511408506147770534923)
          ·
            refine ⟨19397267112759221655802385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12931511408506147770534923 19397267112759221655802385)
            ·
              refine ⟨14547950334569416241851789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19397267112759221655802385 14547950334569416241851789)
              ·
                refine ⟨5455481375463531090694421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14547950334569416241851789 5455481375463531090694421)
                ·
                  refine ⟨255725689474853019876301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5455481375463531090694421 255725689474853019876301)
                  ·
                    rfl

theorem cell20_560277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_560277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560277 prefixEnd_560277 := by exact prefixLift 560277
  have htrace : WordTrace (prefixWord ++ tailWord_560277) baseStart_560277 baseEnd_560277 := by
    simpa [prefixWord, tailWord_560277, baseEnd_560277] using wordTrace_append hprefix tailTrace_560277
  have hstable : (prefixWord ++ tailWord_560277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560277).length < 2 ^ (prefixWord ++ tailWord_560277).sum := by decide
  have hdescent : baseEnd_560277 < baseStart_560277 := by decide
  rcases family_descends (prefixWord ++ tailWord_560277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560280 : List Nat := [2, 1, 2, 4, 2, 1, 4, 4]
def baseStart_560280 : Nat := 118140960795 + 560280 * 2 ^ 59
def prefixEnd_560280 : Nat := 4983230072969 + 3 ^ 40 * 560280 * 2
def baseEnd_560280 : Nat := 85242352918866114258763

theorem tailTrace_560280 : CollatzResearch.WordTrace tailWord_560280 prefixEnd_560280 85242352918866114258763 := by
  unfold tailWord_560280
  simp only [CollatzResearch.WordTrace]
  refine ⟨10217545205104361525491147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13623393606805815367321529 10217545205104361525491147)
  ·
    refine ⟨15326317807656542288236721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10217545205104361525491147 15326317807656542288236721)
    ·
      refine ⟨11494738355742406716177541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15326317807656542288236721 11494738355742406716177541)
      ·
        refine ⟨2155263441701701259283289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11494738355742406716177541 2155263441701701259283289)
        ·
          refine ⟨1616447581276275944462467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2155263441701701259283289 1616447581276275944462467)
          ·
            refine ⟨2424671371914413916693701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1616447581276275944462467 2424671371914413916693701)
            ·
              refine ⟨454625882233952609380069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2424671371914413916693701 454625882233952609380069)
              ·
                refine ⟨85242352918866114258763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 454625882233952609380069 85242352918866114258763)
                ·
                  rfl

theorem cell20_560280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 4].length) (baseStart_560280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560280 prefixEnd_560280 := by exact prefixLift 560280
  have htrace : WordTrace (prefixWord ++ tailWord_560280) baseStart_560280 baseEnd_560280 := by
    simpa [prefixWord, tailWord_560280, baseEnd_560280] using wordTrace_append hprefix tailTrace_560280
  have hstable : (prefixWord ++ tailWord_560280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560280).length < 2 ^ (prefixWord ++ tailWord_560280).sum := by decide
  have hdescent : baseEnd_560280 < baseStart_560280 := by decide
  rcases family_descends (prefixWord ++ tailWord_560280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560315 : List Nat := [1, 1, 1, 1, 1, 2, 4, 5, 4]
def baseStart_560315 : Nat := 118140960795 + 560315 * 2 ^ 59
def prefixEnd_560315 : Nat := 4983230072969 + 3 ^ 40 * 560315 * 2
def baseEnd_560315 : Nat := 255743033710293776609479

theorem tailTrace_560315 : CollatzResearch.WordTrace tailWord_560315 prefixEnd_560315 255743033710293776609479 := by
  unfold tailWord_560315
  simp only [CollatzResearch.WordTrace]
  refine ⟨20436366965081924028506399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13624244643387949352337599 20436366965081924028506399)
  ·
    refine ⟨30654550447622886042759599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20436366965081924028506399 30654550447622886042759599)
    ·
      refine ⟨45981825671434329064139399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30654550447622886042759599 45981825671434329064139399)
      ·
        refine ⟨68972738507151493596209099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45981825671434329064139399 68972738507151493596209099)
        ·
          refine ⟨103459107760727240394313649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68972738507151493596209099 103459107760727240394313649)
          ·
            refine ⟨77594330820545430295735237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103459107760727240394313649 77594330820545430295735237)
            ·
              refine ⟨14548937028852268180450357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77594330820545430295735237 14548937028852268180450357)
              ·
                refine ⟨1363962846454900141917221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14548937028852268180450357 1363962846454900141917221)
                ·
                  refine ⟨255743033710293776609479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1363962846454900141917221 255743033710293776609479)
                  ·
                    rfl

theorem cell20_560315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 4].length) (baseStart_560315 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560315 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560315 prefixEnd_560315 := by exact prefixLift 560315
  have htrace : WordTrace (prefixWord ++ tailWord_560315) baseStart_560315 baseEnd_560315 := by
    simpa [prefixWord, tailWord_560315, baseEnd_560315] using wordTrace_append hprefix tailTrace_560315
  have hstable : (prefixWord ++ tailWord_560315).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560315).length < 2 ^ (prefixWord ++ tailWord_560315).sum := by decide
  have hdescent : baseEnd_560315 < baseStart_560315 := by decide
  rcases family_descends (prefixWord ++ tailWord_560315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560318 : List Nat := [4, 2, 1, 1, 3, 2, 2, 5]
def baseStart_560318 : Nat := 118140960795 + 560318 * 2 ^ 59
def prefixEnd_560318 : Nat := 4983230072969 + 3 ^ 40 * 560318 * 2
def baseEnd_560318 : Nat := 85248134330679699836489

theorem tailTrace_560318 : CollatzResearch.WordTrace tailWord_560318 prefixEnd_560318 85248134330679699836489 := by
  unfold tailWord_560318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2554559548008881942608201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13624317589380703693910405 2554559548008881942608201)
  ·
    refine ⟨1915919661006661456956151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2554559548008881942608201 1915919661006661456956151)
    ·
      refine ⟨2873879491509992185434227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1915919661006661456956151 2873879491509992185434227)
      ·
        refine ⟨4310819237264988278151341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2873879491509992185434227 4310819237264988278151341)
        ·
          refine ⟨1616557213974370604306753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4310819237264988278151341 1616557213974370604306753)
          ·
            refine ⟨1212417910480777953230065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1616557213974370604306753 1212417910480777953230065)
            ·
              refine ⟨909313432860583464922549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1212417910480777953230065 909313432860583464922549)
              ·
                refine ⟨85248134330679699836489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 909313432860583464922549 85248134330679699836489)
                ·
                  rfl

theorem cell20_560318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_560318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560318 prefixEnd_560318 := by exact prefixLift 560318
  have htrace : WordTrace (prefixWord ++ tailWord_560318) baseStart_560318 baseEnd_560318 := by
    simpa [prefixWord, tailWord_560318, baseEnd_560318] using wordTrace_append hprefix tailTrace_560318
  have hstable : (prefixWord ++ tailWord_560318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560318).length < 2 ^ (prefixWord ++ tailWord_560318).sum := by decide
  have hdescent : baseEnd_560318 < baseStart_560318 := by decide
  rcases family_descends (prefixWord ++ tailWord_560318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560321 : List Nat := [1, 2, 6, 1, 1, 1, 4, 1, 3]
def baseStart_560321 : Nat := 118140960795 + 560321 * 2 ^ 59
def prefixEnd_560321 : Nat := 4983230072969 + 3 ^ 40 * 560321 * 2
def baseEnd_560321 : Nat := 255745772273784422409455

theorem tailTrace_560321 : CollatzResearch.WordTrace tailWord_560321 prefixEnd_560321 255745772273784422409455 := by
  unfold tailWord_560321
  simp only [CollatzResearch.WordTrace]
  refine ⟨20436585803060187053224817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13624390535373458035483211 20436585803060187053224817)
  ·
    refine ⟨15327439352295140289918613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20436585803060187053224817 15327439352295140289918613)
    ·
      refine ⟨718473719638834701089935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15327439352295140289918613 718473719638834701089935)
      ·
        refine ⟨1077710579458252051634903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 718473719638834701089935 1077710579458252051634903)
        ·
          refine ⟨1616565869187378077452355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1077710579458252051634903 1616565869187378077452355)
          ·
            refine ⟨2424848803781067116178533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1616565869187378077452355 2424848803781067116178533)
            ·
              refine ⟨454659150708950084283475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2424848803781067116178533 454659150708950084283475)
              ·
                refine ⟨681988726063425126425213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 454659150708950084283475 681988726063425126425213)
                ·
                  refine ⟨255745772273784422409455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 681988726063425126425213 255745772273784422409455)
                  ·
                    rfl

theorem cell20_560321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 3].length) (baseStart_560321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560321 prefixEnd_560321 := by exact prefixLift 560321
  have htrace : WordTrace (prefixWord ++ tailWord_560321) baseStart_560321 baseEnd_560321 := by
    simpa [prefixWord, tailWord_560321, baseEnd_560321] using wordTrace_append hprefix tailTrace_560321
  have hstable : (prefixWord ++ tailWord_560321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560321).length < 2 ^ (prefixWord ++ tailWord_560321).sum := by decide
  have hdescent : baseEnd_560321 < baseStart_560321 := by decide
  rcases family_descends (prefixWord ++ tailWord_560321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560363 : List Nat := [1, 1, 1, 1, 2, 7, 2, 2, 3]
def baseStart_560363 : Nat := 118140960795 + 560363 * 2 ^ 59
def prefixEnd_560363 : Nat := 4983230072969 + 3 ^ 40 * 560363 * 2
def baseEnd_560363 : Nat := 255764942218218943009283

theorem tailTrace_560363 : CollatzResearch.WordTrace tailWord_560363 prefixEnd_560363 255764942218218943009283 := by
  unfold tailWord_560363
  simp only [CollatzResearch.WordTrace]
  refine ⟨20438117668908028226253743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13625411779272018817502495 20438117668908028226253743)
  ·
    refine ⟨30657176503362042339380615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20438117668908028226253743 30657176503362042339380615)
    ·
      refine ⟨45985764755043063509070923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30657176503362042339380615 45985764755043063509070923)
      ·
        refine ⟨68978647132564595263606385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45985764755043063509070923 68978647132564595263606385)
        ·
          refine ⟨51733985349423446447704789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68978647132564595263606385 51733985349423446447704789)
          ·
            refine ⟨1212515281627112026118081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 51733985349423446447704789 1212515281627112026118081)
            ·
              refine ⟨909386461220334019588561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1212515281627112026118081 909386461220334019588561)
              ·
                refine ⟨682039845915250514691421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 909386461220334019588561 682039845915250514691421)
                ·
                  refine ⟨255764942218218943009283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 682039845915250514691421 255764942218218943009283)
                  ·
                    rfl

theorem cell20_560363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 3].length) (baseStart_560363 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560363 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560363 prefixEnd_560363 := by exact prefixLift 560363
  have htrace : WordTrace (prefixWord ++ tailWord_560363) baseStart_560363 baseEnd_560363 := by
    simpa [prefixWord, tailWord_560363, baseEnd_560363] using wordTrace_append hprefix tailTrace_560363
  have hstable : (prefixWord ++ tailWord_560363).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560363).length < 2 ^ (prefixWord ++ tailWord_560363).sum := by decide
  have hdescent : baseEnd_560363 < baseStart_560363 := by decide
  rcases family_descends (prefixWord ++ tailWord_560363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560366 : List Nat := [4, 1, 2, 1, 1, 1, 6, 2, 2]
def baseStart_560366 : Nat := 118140960795 + 560366 * 2 ^ 59
def prefixEnd_560366 : Nat := 4983230072969 + 3 ^ 40 * 560366 * 2
def baseEnd_560366 : Nat := 255766311499964265909271

theorem tailTrace_560366 : CollatzResearch.WordTrace tailWord_560366 prefixEnd_560366 255766311499964265909271 := by
  unfold tailWord_560366
  simp only [CollatzResearch.WordTrace]
  refine ⟨2554778385987144967326619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13625484725264773159075301 2554778385987144967326619)
  ·
    refine ⟨3832167578980717450989929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2554778385987144967326619 3832167578980717450989929)
    ·
      refine ⟨2874125684235538088242447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3832167578980717450989929 2874125684235538088242447)
      ·
        refine ⟨4311188526353307132363671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2874125684235538088242447 4311188526353307132363671)
        ·
          refine ⟨6466782789529960698545507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4311188526353307132363671 6466782789529960698545507)
          ·
            refine ⟨9700174184294941047818261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6466782789529960698545507 9700174184294941047818261)
            ·
              refine ⟨454695664888825361616481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9700174184294941047818261 454695664888825361616481)
              ·
                refine ⟨341021748666619021212361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 454695664888825361616481 341021748666619021212361)
                ·
                  refine ⟨255766311499964265909271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 341021748666619021212361 255766311499964265909271)
                  ·
                    rfl

theorem cell20_560366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_560366 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560366 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560366 prefixEnd_560366 := by exact prefixLift 560366
  have htrace : WordTrace (prefixWord ++ tailWord_560366) baseStart_560366 baseEnd_560366 := by
    simpa [prefixWord, tailWord_560366, baseEnd_560366] using wordTrace_append hprefix tailTrace_560366
  have hstable : (prefixWord ++ tailWord_560366).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560366).length < 2 ^ (prefixWord ++ tailWord_560366).sum := by decide
  have hdescent : baseEnd_560366 < baseStart_560366 := by decide
  rcases family_descends (prefixWord ++ tailWord_560366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560414 : List Nat := [4, 3, 2, 1, 2, 2, 1, 2, 3]
def baseStart_560414 : Nat := 118140960795 + 560414 * 2 ^ 59
def prefixEnd_560414 : Nat := 4983230072969 + 3 ^ 40 * 560414 * 2
def baseEnd_560414 : Nat := 255788220007889432309075

theorem tailTrace_560414 : CollatzResearch.WordTrace tailWord_560414 prefixEnd_560414 255788220007889432309075 := by
  unfold tailWord_560414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2554997223965407992045037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13626651861148842624240197 2554997223965407992045037)
  ·
    refine ⟨958123958987027997016889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2554997223965407992045037 958123958987027997016889)
    ·
      refine ⟨718592969240270997762667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 958123958987027997016889 718592969240270997762667)
      ·
        refine ⟨1077889453860406496644001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 718592969240270997762667 1077889453860406496644001)
        ·
          refine ⟨808417090395304872483001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1077889453860406496644001 808417090395304872483001)
          ·
            refine ⟨606312817796478654362251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 808417090395304872483001 606312817796478654362251)
            ·
              refine ⟨909469226694717981543377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 606312817796478654362251 909469226694717981543377)
              ·
                refine ⟨682101920021038486157533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 909469226694717981543377 682101920021038486157533)
                ·
                  refine ⟨255788220007889432309075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 682101920021038486157533 255788220007889432309075)
                  ·
                    rfl

theorem cell20_560414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_560414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560414 prefixEnd_560414 := by exact prefixLift 560414
  have htrace : WordTrace (prefixWord ++ tailWord_560414) baseStart_560414 baseEnd_560414 := by
    simpa [prefixWord, tailWord_560414, baseEnd_560414] using wordTrace_append hprefix tailTrace_560414
  have hstable : (prefixWord ++ tailWord_560414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560414).length < 2 ^ (prefixWord ++ tailWord_560414).sum := by decide
  have hdescent : baseEnd_560414 < baseStart_560414 := by decide
  rcases family_descends (prefixWord ++ tailWord_560414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560415 : List Nat := [1, 1, 2, 4, 4, 1, 7]
def baseStart_560415 : Nat := 118140960795 + 560415 * 2 ^ 59
def prefixEnd_560415 : Nat := 4983230072969 + 3 ^ 40 * 560415 * 2
def baseEnd_560415 : Nat := 28420964048348652586193

theorem tailTrace_560415 : CollatzResearch.WordTrace tailWord_560415 prefixEnd_560415 28420964048348652586193 := by
  unfold tailWord_560415
  simp only [CollatzResearch.WordTrace]
  refine ⟨20440014264719641107146699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13626676176479760738097799 20440014264719641107146699)
  ·
    refine ⟨30660021397079461660720049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20440014264719641107146699 30660021397079461660720049)
    ·
      refine ⟨22995016047809596245540037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30660021397079461660720049 22995016047809596245540037)
      ·
        refine ⟨4311565508964299296038757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22995016047809596245540037 4311565508964299296038757)
        ·
          refine ⟨808418532930806118007267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4311565508964299296038757 808418532930806118007267)
          ·
            refine ⟨1212627799396209177010901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 808418532930806118007267 1212627799396209177010901)
            ·
              refine ⟨28420964048348652586193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1212627799396209177010901 28420964048348652586193)
              ·
                rfl

theorem cell20_560415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 7].length) (baseStart_560415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560415 prefixEnd_560415 := by exact prefixLift 560415
  have htrace : WordTrace (prefixWord ++ tailWord_560415) baseStart_560415 baseEnd_560415 := by
    simpa [prefixWord, tailWord_560415, baseEnd_560415] using wordTrace_append hprefix tailTrace_560415
  have hstable : (prefixWord ++ tailWord_560415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560415).length < 2 ^ (prefixWord ++ tailWord_560415).sum := by decide
  have hdescent : baseEnd_560415 < baseStart_560415 := by decide
  rcases family_descends (prefixWord ++ tailWord_560415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560446 : List Nat := [4, 2, 1, 2, 1, 1, 1, 4, 4]
def baseStart_560446 : Nat := 118140960795 + 560446 * 2 ^ 59
def prefixEnd_560446 : Nat := 4983230072969 + 3 ^ 40 * 560446 * 2
def baseEnd_560446 : Nat := 255802825679839543242277

theorem tailTrace_560446 : CollatzResearch.WordTrace tailWord_560446 prefixEnd_560446 255802825679839543242277 := by
  unfold tailWord_560446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2555143115950916675190649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13627429951738222267683461 2555143115950916675190649)
  ·
    refine ⟨1916357336963187506392987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2555143115950916675190649 1916357336963187506392987)
    ·
      refine ⟨2874536005444781259589481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1916357336963187506392987 2874536005444781259589481)
      ·
        refine ⟨2155902004083585944692111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2874536005444781259589481 2155902004083585944692111)
        ·
          refine ⟨3233853006125378917038167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2155902004083585944692111 3233853006125378917038167)
          ·
            refine ⟨4850779509188068375557251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3233853006125378917038167 4850779509188068375557251)
            ·
              refine ⟨7276169263782102563335877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4850779509188068375557251 7276169263782102563335877)
              ·
                refine ⟨1364281736959144230625477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7276169263782102563335877 1364281736959144230625477)
                ·
                  refine ⟨255802825679839543242277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1364281736959144230625477 255802825679839543242277)
                  ·
                    rfl

theorem cell20_560446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_560446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560446 prefixEnd_560446 := by exact prefixLift 560446
  have htrace : WordTrace (prefixWord ++ tailWord_560446) baseStart_560446 baseEnd_560446 := by
    simpa [prefixWord, tailWord_560446, baseEnd_560446] using wordTrace_append hprefix tailTrace_560446
  have hstable : (prefixWord ++ tailWord_560446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560446).length < 2 ^ (prefixWord ++ tailWord_560446).sum := by decide
  have hdescent : baseEnd_560446 < baseStart_560446 := by decide
  rcases family_descends (prefixWord ++ tailWord_560446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560449 : List Nat := [1, 2, 5, 2, 1, 3, 2, 4]
def baseStart_560449 : Nat := 118140960795 + 560449 * 2 ^ 59
def prefixEnd_560449 : Nat := 4983230072969 + 3 ^ 40 * 560449 * 2
def baseEnd_560449 : Nat := 85268064987194955380755

theorem tailTrace_560449 : CollatzResearch.WordTrace tailWord_560449 prefixEnd_560449 85268064987194955380755 := by
  unfold tailWord_560449
  simp only [CollatzResearch.WordTrace]
  refine ⟨20441254346596464913884401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13627502897730976609256267 20441254346596464913884401)
  ·
    refine ⟨15330940759947348685413301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20441254346596464913884401 15330940759947348685413301)
    ·
      refine ⟨1437275696245063939257497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15330940759947348685413301 1437275696245063939257497)
      ·
        refine ⟨1077956772183797954443123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1437275696245063939257497 1077956772183797954443123)
        ·
          refine ⟨1616935158275696931664685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1077956772183797954443123 1616935158275696931664685)
          ·
            refine ⟨606350684353386349374257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1616935158275696931664685 606350684353386349374257)
            ·
              refine ⟨454763013265039762030693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 606350684353386349374257 454763013265039762030693)
              ·
                refine ⟨85268064987194955380755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 454763013265039762030693 85268064987194955380755)
                ·
                  rfl

theorem cell20_560449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 4].length) (baseStart_560449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560449 prefixEnd_560449 := by exact prefixLift 560449
  have htrace : WordTrace (prefixWord ++ tailWord_560449) baseStart_560449 baseEnd_560449 := by
    simpa [prefixWord, tailWord_560449, baseEnd_560449] using wordTrace_append hprefix tailTrace_560449
  have hstable : (prefixWord ++ tailWord_560449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560449).length < 2 ^ (prefixWord ++ tailWord_560449).sum := by decide
  have hdescent : baseEnd_560449 < baseStart_560449 := by decide
  rcases family_descends (prefixWord ++ tailWord_560449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560460 : List Nat := [2, 2, 1, 3, 2, 2, 1, 2, 5]
def baseStart_560460 : Nat := 118140960795 + 560460 * 2 ^ 59
def prefixEnd_560460 : Nat := 4983230072969 + 3 ^ 40 * 560460 * 2
def baseEnd_560460 : Nat := 255809215661317716775553

theorem tailTrace_560460 : CollatzResearch.WordTrace tailWord_560460 prefixEnd_560460 255809215661317716775553 := by
  unfold tailWord_560460
  simp only [CollatzResearch.WordTrace]
  refine ⟨10220827774778306896267417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13627770366371075861689889 10220827774778306896267417)
  ·
    refine ⟨7665620831083730172200563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10220827774778306896267417 7665620831083730172200563)
    ·
      refine ⟨11498431246625595258300845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7665620831083730172200563 11498431246625595258300845)
      ·
        refine ⟨4311911717484598221862817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11498431246625595258300845 4311911717484598221862817)
        ·
          refine ⟨3233933788113448666397113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4311911717484598221862817 3233933788113448666397113)
          ·
            refine ⟨2425450341085086499797835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3233933788113448666397113 2425450341085086499797835)
            ·
              refine ⟨3638175511627629749696753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2425450341085086499797835 3638175511627629749696753)
              ·
                refine ⟨2728631633720722312272565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3638175511627629749696753 2728631633720722312272565)
                ·
                  refine ⟨255809215661317716775553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2728631633720722312272565 255809215661317716775553)
                  ·
                    rfl

theorem cell20_560460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_560460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560460 prefixEnd_560460 := by exact prefixLift 560460
  have htrace : WordTrace (prefixWord ++ tailWord_560460) baseStart_560460 baseEnd_560460 := by
    simpa [prefixWord, tailWord_560460, baseEnd_560460] using wordTrace_append hprefix tailTrace_560460
  have hstable : (prefixWord ++ tailWord_560460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560460).length < 2 ^ (prefixWord ++ tailWord_560460).sum := by decide
  have hdescent : baseEnd_560460 < baseStart_560460 := by decide
  rcases family_descends (prefixWord ++ tailWord_560460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560474 : List Nat := [3, 1, 1, 2, 1, 2, 10]
def baseStart_560474 : Nat := 118140960795 + 560474 * 2 ^ 59
def prefixEnd_560474 : Nat := 4983230072969 + 3 ^ 40 * 560474 * 2
def baseEnd_560474 : Nat := 28423956182532876700981

theorem tailTrace_560474 : CollatzResearch.WordTrace tailWord_560474 prefixEnd_560474 28423956182532876700981 := by
  unfold tailWord_560474
  simp only [CollatzResearch.WordTrace]
  refine ⟨5110541542876473545886119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13628110781003929455696317 5110541542876473545886119)
  ·
    refine ⟨7665812314314710318829179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5110541542876473545886119 7665812314314710318829179)
    ·
      refine ⟨11498718471472065478243769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7665812314314710318829179 11498718471472065478243769)
      ·
        refine ⟨8624038853604049108682827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11498718471472065478243769 8624038853604049108682827)
        ·
          refine ⟨12936058280406073663024241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8624038853604049108682827 12936058280406073663024241)
          ·
            refine ⟨9702043710304555247268181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12936058280406073663024241 9702043710304555247268181)
            ·
              refine ⟨28423956182532876700981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9702043710304555247268181 28423956182532876700981)
              ·
                rfl

theorem cell20_560474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 10].length) (baseStart_560474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560474 prefixEnd_560474 := by exact prefixLift 560474
  have htrace : WordTrace (prefixWord ++ tailWord_560474) baseStart_560474 baseEnd_560474 := by
    simpa [prefixWord, tailWord_560474, baseEnd_560474] using wordTrace_append hprefix tailTrace_560474
  have hstable : (prefixWord ++ tailWord_560474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560474).length < 2 ^ (prefixWord ++ tailWord_560474).sum := by decide
  have hdescent : baseEnd_560474 < baseStart_560474 := by decide
  rcases family_descends (prefixWord ++ tailWord_560474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560480 : List Nat := [2, 1, 1, 3, 4, 2, 3, 2, 2]
def baseStart_560480 : Nat := 118140960795 + 560480 * 2 ^ 59
def prefixEnd_560480 : Nat := 4983230072969 + 3 ^ 40 * 560480 * 2
def baseEnd_560480 : Nat := 255818344206286536108805

theorem tailTrace_560480 : CollatzResearch.WordTrace tailWord_560480 prefixEnd_560480 255818344206286536108805 := by
  unfold tailWord_560480
  simp only [CollatzResearch.WordTrace]
  refine ⟨10221192504742078604131447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13628256672989438138841929 10221192504742078604131447)
  ·
    refine ⟨15331788757113117906197171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10221192504742078604131447 15331788757113117906197171)
    ·
      refine ⟨22997683135669676859295757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15331788757113117906197171 22997683135669676859295757)
      ·
        refine ⟨8624131175876128822235909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22997683135669676859295757 8624131175876128822235909)
        ·
          refine ⟨1617024595476774154169233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8624131175876128822235909 1617024595476774154169233)
          ·
            refine ⟨1212768446607580615626925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1617024595476774154169233 1212768446607580615626925)
            ·
              refine ⟨454788167477842730860097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1212768446607580615626925 454788167477842730860097)
              ·
                refine ⟨341091125608382048145073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 454788167477842730860097 341091125608382048145073)
                ·
                  refine ⟨255818344206286536108805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 341091125608382048145073 255818344206286536108805)
                  ·
                    rfl

theorem cell20_560480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 2, 2].length) (baseStart_560480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560480 prefixEnd_560480 := by exact prefixLift 560480
  have htrace : WordTrace (prefixWord ++ tailWord_560480) baseStart_560480 baseEnd_560480 := by
    simpa [prefixWord, tailWord_560480, baseEnd_560480] using wordTrace_append hprefix tailTrace_560480
  have hstable : (prefixWord ++ tailWord_560480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560480).length < 2 ^ (prefixWord ++ tailWord_560480).sum := by decide
  have hdescent : baseEnd_560480 < baseStart_560480 := by decide
  rcases family_descends (prefixWord ++ tailWord_560480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560484 : List Nat := [2, 3, 1, 1, 3, 2, 3, 1, 4]
def baseStart_560484 : Nat := 118140960795 + 560484 * 2 ^ 59
def prefixEnd_560484 : Nat := 4983230072969 + 3 ^ 40 * 560484 * 2
def baseEnd_560484 : Nat := 255820169915280299975455

theorem tailTrace_560484 : CollatzResearch.WordTrace tailWord_560484 prefixEnd_560484 255820169915280299975455 := by
  unfold tailWord_560484
  simp only [CollatzResearch.WordTrace]
  refine ⟨10221265450734832945704253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13628353934313110594272337 10221265450734832945704253)
  ·
    refine ⟨3832974544025562354639095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10221265450734832945704253 3832974544025562354639095)
    ·
      refine ⟨5749461816038343531958643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3832974544025562354639095 5749461816038343531958643)
      ·
        refine ⟨8624192724057515297937965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5749461816038343531958643 8624192724057515297937965)
        ·
          refine ⟨3234072271521568236726737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8624192724057515297937965 3234072271521568236726737)
          ·
            refine ⟨2425554203641176177545053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3234072271521568236726737 2425554203641176177545053)
            ·
              refine ⟨909582826365441066579395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2425554203641176177545053 909582826365441066579395)
              ·
                refine ⟨1364374239548161599869093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 909582826365441066579395 1364374239548161599869093)
                ·
                  refine ⟨255820169915280299975455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1364374239548161599869093 255820169915280299975455)
                  ·
                    rfl

theorem cell20_560484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_560484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560484 prefixEnd_560484 := by exact prefixLift 560484
  have htrace : WordTrace (prefixWord ++ tailWord_560484) baseStart_560484 baseEnd_560484 := by
    simpa [prefixWord, tailWord_560484, baseEnd_560484] using wordTrace_append hprefix tailTrace_560484
  have hstable : (prefixWord ++ tailWord_560484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560484).length < 2 ^ (prefixWord ++ tailWord_560484).sum := by decide
  have hdescent : baseEnd_560484 < baseStart_560484 := by decide
  rcases family_descends (prefixWord ++ tailWord_560484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560490 : List Nat := [3, 1, 3, 3, 3, 1, 2, 1, 3]
def baseStart_560490 : Nat := 118140960795 + 560490 * 2 ^ 59
def prefixEnd_560490 : Nat := 4983230072969 + 3 ^ 40 * 560490 * 2
def baseEnd_560490 : Nat := 255822908478770945775431

theorem tailTrace_560490 : CollatzResearch.WordTrace tailWord_560490 prefixEnd_560490 255822908478770945775431 := by
  unfold tailWord_560490
  simp only [CollatzResearch.WordTrace]
  refine ⟨5110687434861982229031731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13628499826298619277417949 5110687434861982229031731)
  ·
    refine ⟨7666031152292973343547597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5110687434861982229031731 7666031152292973343547597)
    ·
      refine ⟨2874761682109865003830349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7666031152292973343547597 2874761682109865003830349)
      ·
        refine ⟨1078035630791199376436381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2874761682109865003830349 1078035630791199376436381)
        ·
          refine ⟨404263361546699766163643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1078035630791199376436381 404263361546699766163643)
          ·
            refine ⟨606395042320049649245465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404263361546699766163643 606395042320049649245465)
            ·
              refine ⟨454796281740037236934099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 606395042320049649245465 454796281740037236934099)
              ·
                refine ⟨682194422610055855401149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 454796281740037236934099 682194422610055855401149)
                ·
                  refine ⟨255822908478770945775431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 682194422610055855401149 255822908478770945775431)
                  ·
                    rfl

theorem cell20_560490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 3].length) (baseStart_560490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560490 prefixEnd_560490 := by exact prefixLift 560490
  have htrace : WordTrace (prefixWord ++ tailWord_560490) baseStart_560490 baseEnd_560490 := by
    simpa [prefixWord, tailWord_560490, baseEnd_560490] using wordTrace_append hprefix tailTrace_560490
  have hstable : (prefixWord ++ tailWord_560490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560490).length < 2 ^ (prefixWord ++ tailWord_560490).sum := by decide
  have hdescent : baseEnd_560490 < baseStart_560490 := by decide
  rcases family_descends (prefixWord ++ tailWord_560490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560505 : List Nat := [1, 2, 1, 3, 2, 1, 2, 4, 4]
def baseStart_560505 : Nat := 118140960795 + 560505 * 2 ^ 59
def prefixEnd_560505 : Nat := 4983230072969 + 3 ^ 40 * 560505 * 2
def baseEnd_560505 : Nat := 255829754887497560275369

theorem tailTrace_560505 : CollatzResearch.WordTrace tailWord_560505 prefixEnd_560505 255829754887497560275369 := by
  unfold tailWord_560505
  simp only [CollatzResearch.WordTrace]
  refine ⟨20443296834393586477922969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13628864556262390985281979 20443296834393586477922969)
  ·
    refine ⟨15332472625795189858442227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20443296834393586477922969 15332472625795189858442227)
    ·
      refine ⟨22998708938692784787663341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15332472625795189858442227 22998708938692784787663341)
      ·
        refine ⟨8624515852009794295373753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22998708938692784787663341 8624515852009794295373753)
        ·
          refine ⟨6468386889007345721530315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8624515852009794295373753 6468386889007345721530315)
          ·
            refine ⟨9702580333511018582295473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6468386889007345721530315 9702580333511018582295473)
            ·
              refine ⟨7276935250133263936721605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9702580333511018582295473 7276935250133263936721605)
              ·
                refine ⟨1364425359399986988135301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7276935250133263936721605 1364425359399986988135301)
                ·
                  refine ⟨255829754887497560275369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1364425359399986988135301 255829754887497560275369)
                  ·
                    rfl

theorem cell20_560505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_560505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560505 prefixEnd_560505 := by exact prefixLift 560505
  have htrace : WordTrace (prefixWord ++ tailWord_560505) baseStart_560505 baseEnd_560505 := by
    simpa [prefixWord, tailWord_560505, baseEnd_560505] using wordTrace_append hprefix tailTrace_560505
  have hstable : (prefixWord ++ tailWord_560505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560505).length < 2 ^ (prefixWord ++ tailWord_560505).sum := by decide
  have hdescent : baseEnd_560505 < baseStart_560505 := by decide
  rcases family_descends (prefixWord ++ tailWord_560505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560532 : List Nat := [2, 4, 2, 1, 2, 2, 2, 2, 3]
def baseStart_560532 : Nat := 118140960795 + 560532 * 2 ^ 59
def prefixEnd_560532 : Nat := 4983230072969 + 3 ^ 40 * 560532 * 2
def baseEnd_560532 : Nat := 255842078423205466375259

theorem tailTrace_560532 : CollatzResearch.WordTrace tailWord_560532 prefixEnd_560532 255842078423205466375259 := by
  unfold tailWord_560532
  simp only [CollatzResearch.WordTrace]
  refine ⟨10222140802647885044577925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13629521070197180059437233 10222140802647885044577925)
  ·
    refine ⟨1916651400496478445858361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10222140802647885044577925 1916651400496478445858361)
    ·
      refine ⟨1437488550372358834393771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1916651400496478445858361 1437488550372358834393771)
      ·
        refine ⟨2156232825558538251590657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1437488550372358834393771 2156232825558538251590657)
        ·
          refine ⟨1617174619168903688692993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2156232825558538251590657 1617174619168903688692993)
          ·
            refine ⟨1212880964376677766519745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1617174619168903688692993 1212880964376677766519745)
            ·
              refine ⟨909660723282508324889809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1212880964376677766519745 909660723282508324889809)
              ·
                refine ⟨682245542461881243667357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 909660723282508324889809 682245542461881243667357)
                ·
                  refine ⟨255842078423205466375259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 682245542461881243667357 255842078423205466375259)
                  ·
                    rfl

theorem cell20_560532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_560532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560532 prefixEnd_560532 := by exact prefixLift 560532
  have htrace : WordTrace (prefixWord ++ tailWord_560532) baseStart_560532 baseEnd_560532 := by
    simpa [prefixWord, tailWord_560532, baseEnd_560532] using wordTrace_append hprefix tailTrace_560532
  have hstable : (prefixWord ++ tailWord_560532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560532).length < 2 ^ (prefixWord ++ tailWord_560532).sum := by decide
  have hdescent : baseEnd_560532 < baseStart_560532 := by decide
  rcases family_descends (prefixWord ++ tailWord_560532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560542 : List Nat := [4, 3, 1, 2, 3, 1, 1, 5]
def baseStart_560542 : Nat := 118140960795 + 560542 * 2 ^ 59
def prefixEnd_560542 : Nat := 4983230072969 + 3 ^ 40 * 560542 * 2
def baseEnd_560542 : Nat := 85282214231896625347295

theorem tailTrace_560542 : CollatzResearch.WordTrace tailWord_560542 prefixEnd_560542 85282214231896625347295 := by
  unfold tailWord_560542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2555580791907442724627485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13629764223506361198013253 2555580791907442724627485)
  ·
    refine ⟨958342796965291021735307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2555580791907442724627485 958342796965291021735307)
    ·
      refine ⟨1437514195447936532602961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 958342796965291021735307 1437514195447936532602961)
      ·
        refine ⟨1078135646585952399452221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1437514195447936532602961 1078135646585952399452221)
        ·
          refine ⟨404300867469732149794583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1078135646585952399452221 404300867469732149794583)
          ·
            refine ⟨606451301204598224691875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404300867469732149794583 606451301204598224691875)
            ·
              refine ⟨909676951806897337037813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 606451301204598224691875 909676951806897337037813)
              ·
                refine ⟨85282214231896625347295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 909676951806897337037813 85282214231896625347295)
                ·
                  rfl

theorem cell20_560542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_560542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560542 prefixEnd_560542 := by exact prefixLift 560542
  have htrace : WordTrace (prefixWord ++ tailWord_560542) baseStart_560542 baseEnd_560542 := by
    simpa [prefixWord, tailWord_560542, baseEnd_560542] using wordTrace_append hprefix tailTrace_560542
  have hstable : (prefixWord ++ tailWord_560542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560542).length < 2 ^ (prefixWord ++ tailWord_560542).sum := by decide
  have hdescent : baseEnd_560542 < baseStart_560542 := by decide
  rcases family_descends (prefixWord ++ tailWord_560542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560546 : List Nat := [3, 3, 1, 2, 1, 4, 1, 5]
def baseStart_560546 : Nat := 118140960795 + 560546 * 2 ^ 59
def prefixEnd_560546 : Nat := 4983230072969 + 3 ^ 40 * 560546 * 2
def baseEnd_560546 : Nat := 85282822801561213302845

theorem tailTrace_560546 : CollatzResearch.WordTrace tailWord_560546 prefixEnd_560546 85282822801561213302845 := by
  unfold tailWord_560546
  simp only [CollatzResearch.WordTrace]
  refine ⟨5111198056811262620041373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13629861484830033653443661 5111198056811262620041373)
  ·
    refine ⟨1916699271304223482515515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5111198056811262620041373 1916699271304223482515515)
    ·
      refine ⟨2875048906956335223773273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1916699271304223482515515 2875048906956335223773273)
      ·
        refine ⟨2156286680217251417829955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2875048906956335223773273 2156286680217251417829955)
        ·
          refine ⟨3234430020325877126744933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2156286680217251417829955 3234430020325877126744933)
          ·
            refine ⟨606455628811101961264675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3234430020325877126744933 606455628811101961264675)
            ·
              refine ⟨909683443216652941897013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 606455628811101961264675 909683443216652941897013)
              ·
                refine ⟨85282822801561213302845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 909683443216652941897013 85282822801561213302845)
                ·
                  rfl

theorem cell20_560546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_560546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560546 prefixEnd_560546 := by exact prefixLift 560546
  have htrace : WordTrace (prefixWord ++ tailWord_560546) baseStart_560546 baseEnd_560546 := by
    simpa [prefixWord, tailWord_560546, baseEnd_560546] using wordTrace_append hprefix tailTrace_560546
  have hstable : (prefixWord ++ tailWord_560546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560546).length < 2 ^ (prefixWord ++ tailWord_560546).sum := by decide
  have hdescent : baseEnd_560546 < baseStart_560546 := by decide
  rcases family_descends (prefixWord ++ tailWord_560546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560567 : List Nat := [1, 1, 3, 1, 3, 2, 5, 4]
def baseStart_560567 : Nat := 118140960795 + 560567 * 2 ^ 59
def prefixEnd_560567 : Nat := 4983230072969 + 3 ^ 40 * 560567 * 2
def baseEnd_560567 : Nat := 85286017792300300069483

theorem tailTrace_560567 : CollatzResearch.WordTrace tailWord_560567 prefixEnd_560567 85286017792300300069483 := by
  unfold tailWord_560567
  simp only [CollatzResearch.WordTrace]
  refine ⟨20445558160168971066679955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13630372106779314044453303 20445558160168971066679955)
  ·
    refine ⟨30668337240253456600019933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20445558160168971066679955 30668337240253456600019933)
    ·
      refine ⟨11500626465095046225007475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30668337240253456600019933 11500626465095046225007475)
      ·
        refine ⟨17250939697642569337511213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11500626465095046225007475 17250939697642569337511213)
        ·
          refine ⟨6469102386615963501566705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17250939697642569337511213 6469102386615963501566705)
          ·
            refine ⟨4851826789961972626175029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6469102386615963501566705 4851826789961972626175029)
            ·
              refine ⟨454858761558934933703909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4851826789961972626175029 454858761558934933703909)
              ·
                refine ⟨85286017792300300069483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 454858761558934933703909 85286017792300300069483)
                ·
                  rfl

theorem cell20_560567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 4].length) (baseStart_560567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560567 prefixEnd_560567 := by exact prefixLift 560567
  have htrace : WordTrace (prefixWord ++ tailWord_560567) baseStart_560567 baseEnd_560567 := by
    simpa [prefixWord, tailWord_560567, baseEnd_560567] using wordTrace_append hprefix tailTrace_560567
  have hstable : (prefixWord ++ tailWord_560567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560567).length < 2 ^ (prefixWord ++ tailWord_560567).sum := by decide
  have hdescent : baseEnd_560567 < baseStart_560567 := by decide
  rcases family_descends (prefixWord ++ tailWord_560567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560574 : List Nat := [4, 2, 1, 1, 1, 1, 1, 4, 5]
def baseStart_560574 : Nat := 118140960795 + 560574 * 2 ^ 59
def prefixEnd_560574 : Nat := 4983230072969 + 3 ^ 40 * 560574 * 2
def baseEnd_560574 : Nat := 255861248367639986975087

theorem tailTrace_560574 : CollatzResearch.WordTrace tailWord_560574 prefixEnd_560574 255861248367639986975087 := by
  unfold tailWord_560574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2555726683892951407773097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13630542314095740841456517 2555726683892951407773097)
  ·
    refine ⟨1916795012919713555829823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2555726683892951407773097 1916795012919713555829823)
    ·
      refine ⟨2875192519379570333744735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1916795012919713555829823 2875192519379570333744735)
      ·
        refine ⟨4312788779069355500617103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2875192519379570333744735 4312788779069355500617103)
        ·
          refine ⟨6469183168604033250925655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4312788779069355500617103 6469183168604033250925655)
          ·
            refine ⟨9703774752906049876388483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6469183168604033250925655 9703774752906049876388483)
            ·
              refine ⟨14555662129359074814582725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9703774752906049876388483 14555662129359074814582725)
              ·
                refine ⟨2729186649254826527734261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14555662129359074814582725 2729186649254826527734261)
                ·
                  refine ⟨255861248367639986975087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2729186649254826527734261 255861248367639986975087)
                  ·
                    rfl

theorem cell20_560574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_560574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560574 prefixEnd_560574 := by exact prefixLift 560574
  have htrace : WordTrace (prefixWord ++ tailWord_560574) baseStart_560574 baseEnd_560574 := by
    simpa [prefixWord, tailWord_560574, baseEnd_560574] using wordTrace_append hprefix tailTrace_560574
  have hstable : (prefixWord ++ tailWord_560574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560574).length < 2 ^ (prefixWord ++ tailWord_560574).sum := by decide
  have hdescent : baseEnd_560574 < baseStart_560574 := by decide
  rcases family_descends (prefixWord ++ tailWord_560574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560612 : List Nat := [2, 3, 1, 1, 1, 1, 1, 7, 3]
def baseStart_560612 : Nat := 118140960795 + 560612 * 2 ^ 59
def prefixEnd_560612 : Nat := 4983230072969 + 3 ^ 40 * 560612 * 2
def baseEnd_560612 : Nat := 255878592603080743708265

theorem tailTrace_560612 : CollatzResearch.WordTrace tailWord_560612 prefixEnd_560612 255878592603080743708265 := by
  unfold tailWord_560612
  simp only [CollatzResearch.WordTrace]
  refine ⟨10223599722502971876034045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13631466296670629168045393 10223599722502971876034045)
  ·
    refine ⟨3833849895938614453512767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10223599722502971876034045 3833849895938614453512767)
    ·
      refine ⟨5750774843907921680269151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3833849895938614453512767 5750774843907921680269151)
      ·
        refine ⟨8626162265861882520403727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5750774843907921680269151 8626162265861882520403727)
        ·
          refine ⟨12939243398792823780605591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8626162265861882520403727 12939243398792823780605591)
          ·
            refine ⟨19408865098189235670908387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12939243398792823780605591 19408865098189235670908387)
            ·
              refine ⟨29113297647283853506362581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19408865098189235670908387 29113297647283853506362581)
              ·
                refine ⟨682342913608215316555373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 29113297647283853506362581 682342913608215316555373)
                ·
                  refine ⟨255878592603080743708265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 682342913608215316555373 255878592603080743708265)
                  ·
                    rfl

theorem cell20_560612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_560612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560612 prefixEnd_560612 := by exact prefixLift 560612
  have htrace : WordTrace (prefixWord ++ tailWord_560612) baseStart_560612 baseEnd_560612 := by
    simpa [prefixWord, tailWord_560612, baseEnd_560612] using wordTrace_append hprefix tailTrace_560612
  have hstable : (prefixWord ++ tailWord_560612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560612).length < 2 ^ (prefixWord ++ tailWord_560612).sum := by decide
  have hdescent : baseEnd_560612 < baseStart_560612 := by decide
  rcases family_descends (prefixWord ++ tailWord_560612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560629 : List Nat := [1, 3, 5, 1, 1, 1, 1, 2, 5]
def baseStart_560629 : Nat := 118140960795 + 560629 * 2 ^ 59
def prefixEnd_560629 : Nat := 4983230072969 + 3 ^ 40 * 560629 * 2
def baseEnd_560629 : Nat := 255886351866304240141529

theorem tailTrace_560629 : CollatzResearch.WordTrace tailWord_560629 prefixEnd_560629 255886351866304240141529 := by
  unfold tailWord_560629
  simp only [CollatzResearch.WordTrace]
  refine ⟨20447819485944355655436941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13631879657296237103624627 20447819485944355655436941)
  ·
    refine ⟨7667932307229133370788853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20447819485944355655436941 7667932307229133370788853)
    ·
      refine ⟨718868653802731253511455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7667932307229133370788853 718868653802731253511455)
      ·
        refine ⟨1078302980704096880267183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 718868653802731253511455 1078302980704096880267183)
        ·
          refine ⟨1617454471056145320400775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1078302980704096880267183 1617454471056145320400775)
          ·
            refine ⟨2426181706584217980601163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1617454471056145320400775 2426181706584217980601163)
            ·
              refine ⟨3639272559876326970901745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2426181706584217980601163 3639272559876326970901745)
              ·
                refine ⟨2729454419907245228176309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3639272559876326970901745 2729454419907245228176309)
                ·
                  refine ⟨255886351866304240141529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2729454419907245228176309 255886351866304240141529)
                  ·
                    rfl

theorem cell20_560629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_560629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560629 prefixEnd_560629 := by exact prefixLift 560629
  have htrace : WordTrace (prefixWord ++ tailWord_560629) baseStart_560629 baseEnd_560629 := by
    simpa [prefixWord, tailWord_560629, baseEnd_560629] using wordTrace_append hprefix tailTrace_560629
  have hstable : (prefixWord ++ tailWord_560629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560629).length < 2 ^ (prefixWord ++ tailWord_560629).sum := by decide
  have hdescent : baseEnd_560629 < baseStart_560629 := by decide
  rcases family_descends (prefixWord ++ tailWord_560629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560650 : List Nat := [3, 1, 2, 2, 2, 2, 2, 1, 5]
def baseStart_560650 : Nat := 118140960795 + 560650 * 2 ^ 59
def prefixEnd_560650 : Nat := 4983230072969 + 3 ^ 40 * 560650 * 2
def baseEnd_560650 : Nat := 255895936838521500441443

theorem tailTrace_560650 : CollatzResearch.WordTrace tailWord_560650 prefixEnd_560650 255895936838521500441443 := by
  unfold tailWord_560650
  simp only [CollatzResearch.WordTrace]
  refine ⟨5112146354717069060487851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13632390279245517494634269 5112146354717069060487851)
  ·
    refine ⟨7668219532075603590731777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5112146354717069060487851 7668219532075603590731777)
    ·
      refine ⟨5751164649056702693048833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7668219532075603590731777 5751164649056702693048833)
      ·
        refine ⟨4313373486792527019786625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5751164649056702693048833 4313373486792527019786625)
        ·
          refine ⟨3235030115094395264839969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4313373486792527019786625 3235030115094395264839969)
          ·
            refine ⟨2426272586320796448629977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3235030115094395264839969 2426272586320796448629977)
            ·
              refine ⟨1819704439740597336472483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2426272586320796448629977 1819704439740597336472483)
              ·
                refine ⟨2729556659610896004708725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1819704439740597336472483 2729556659610896004708725)
                ·
                  refine ⟨255895936838521500441443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2729556659610896004708725 255895936838521500441443)
                  ·
                    rfl

theorem cell20_560650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_560650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560650 prefixEnd_560650 := by exact prefixLift 560650
  have htrace : WordTrace (prefixWord ++ tailWord_560650) baseStart_560650 baseEnd_560650 := by
    simpa [prefixWord, tailWord_560650, baseEnd_560650] using wordTrace_append hprefix tailTrace_560650
  have hstable : (prefixWord ++ tailWord_560650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560650).length < 2 ^ (prefixWord ++ tailWord_560650).sum := by decide
  have hdescent : baseEnd_560650 < baseStart_560650 := by decide
  rcases family_descends (prefixWord ++ tailWord_560650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560702 : List Nat := [4, 2, 1, 13]
def baseStart_560702 : Nat := 118140960795 + 560702 * 2 ^ 59
def prefixEnd_560702 : Nat := 4983230072969 + 3 ^ 40 * 560702 * 2
def baseEnd_560702 : Nat := 1053167370598520290979

theorem tailTrace_560702 : CollatzResearch.WordTrace tailWord_560702 prefixEnd_560702 1053167370598520290979 := by
  unfold tailWord_560702
  simp only [CollatzResearch.WordTrace]
  refine ⟨2556310251834986140355545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13633654676453259415229573 2556310251834986140355545)
  ·
    refine ⟨1917232688876239605266659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2556310251834986140355545 1917232688876239605266659)
    ·
      refine ⟨2875849033314359407899989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1917232688876239605266659 2875849033314359407899989)
      ·
        refine ⟨1053167370598520290979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 2875849033314359407899989 1053167370598520290979)
        ·
          rfl

theorem cell20_560702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 13].length) (baseStart_560702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560702 prefixEnd_560702 := by exact prefixLift 560702
  have htrace : WordTrace (prefixWord ++ tailWord_560702) baseStart_560702 baseEnd_560702 := by
    simpa [prefixWord, tailWord_560702, baseEnd_560702] using wordTrace_append hprefix tailTrace_560702
  have hstable : (prefixWord ++ tailWord_560702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560702).length < 2 ^ (prefixWord ++ tailWord_560702).sum := by decide
  have hdescent : baseEnd_560702 < baseStart_560702 := by decide
  rcases family_descends (prefixWord ++ tailWord_560702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560705 : List Nat := [1, 2, 5, 1, 1, 1, 4, 2, 3]
def baseStart_560705 : Nat := 118140960795 + 560705 * 2 ^ 59
def prefixEnd_560705 : Nat := 4983230072969 + 3 ^ 40 * 560705 * 2
def baseEnd_560705 : Nat := 255921040337185753607885

theorem tailTrace_560705 : CollatzResearch.WordTrace tailWord_560705 prefixEnd_560705 255921040337185753607885 := by
  unfold tailWord_560705
  simp only [CollatzResearch.WordTrace]
  refine ⟨20450591433669020635203569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13633727622446013756802379 20450591433669020635203569)
  ·
    refine ⟨15337943575251765476402677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20450591433669020635203569 15337943575251765476402677)
    ·
      refine ⟨1437932210179853013412751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15337943575251765476402677 1437932210179853013412751)
      ·
        refine ⟨2156898315269779520119127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1437932210179853013412751 2156898315269779520119127)
        ·
          refine ⟨3235347472904669280178691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2156898315269779520119127 3235347472904669280178691)
          ·
            refine ⟨4853021209357003920268037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3235347472904669280178691 4853021209357003920268037)
            ·
              refine ⟨909941476754438235050257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4853021209357003920268037 909941476754438235050257)
              ·
                refine ⟨682456107565828676287693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 909941476754438235050257 682456107565828676287693)
                ·
                  refine ⟨255921040337185753607885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 682456107565828676287693 255921040337185753607885)
                  ·
                    rfl

theorem cell20_560705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 3].length) (baseStart_560705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560705 prefixEnd_560705 := by exact prefixLift 560705
  have htrace : WordTrace (prefixWord ++ tailWord_560705) baseStart_560705 baseEnd_560705 := by
    simpa [prefixWord, tailWord_560705, baseEnd_560705] using wordTrace_append hprefix tailTrace_560705
  have hstable : (prefixWord ++ tailWord_560705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560705).length < 2 ^ (prefixWord ++ tailWord_560705).sum := by decide
  have hdescent : baseEnd_560705 < baseStart_560705 := by decide
  rcases family_descends (prefixWord ++ tailWord_560705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560757 : List Nat := [1, 3, 4, 2, 1, 2, 7]
def baseStart_560757 : Nat := 118140960795 + 560757 * 2 ^ 59
def prefixEnd_560757 : Nat := 4983230072969 + 3 ^ 40 * 560757 * 2
def baseEnd_560757 : Nat := 28438308283789409319371

theorem tailTrace_560757 : CollatzResearch.WordTrace tailWord_560757 prefixEnd_560757 28438308283789409319371 := by
  unfold tailWord_560757
  simp only [CollatzResearch.WordTrace]
  refine ⟨20452488029480633516096525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13634992019653755677397683 20452488029480633516096525)
  ·
    refine ⟨7669683011055237568536197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20452488029480633516096525 7669683011055237568536197)
    ·
      refine ⟨1438065564572857044100537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7669683011055237568536197 1438065564572857044100537)
      ·
        refine ⟨1078549173429642783075403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1438065564572857044100537 1078549173429642783075403)
        ·
          refine ⟨1617823760144464174613105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1078549173429642783075403 1617823760144464174613105)
          ·
            refine ⟨1213367820108348130959829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1617823760144464174613105 1213367820108348130959829)
            ·
              refine ⟨28438308283789409319371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1213367820108348130959829 28438308283789409319371)
              ·
                rfl

theorem cell20_560757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 7].length) (baseStart_560757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560757 prefixEnd_560757 := by exact prefixLift 560757
  have htrace : WordTrace (prefixWord ++ tailWord_560757) baseStart_560757 baseEnd_560757 := by
    simpa [prefixWord, tailWord_560757, baseEnd_560757] using wordTrace_append hprefix tailTrace_560757
  have hstable : (prefixWord ++ tailWord_560757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560757).length < 2 ^ (prefixWord ++ tailWord_560757).sum := by decide
  have hdescent : baseEnd_560757 < baseStart_560757 := by decide
  rcases family_descends (prefixWord ++ tailWord_560757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560808 : List Nat := [2, 1, 7, 1, 2, 1, 6]
def baseStart_560808 : Nat := 118140960795 + 560808 * 2 ^ 59
def prefixEnd_560808 : Nat := 4983230072969 + 3 ^ 40 * 560808 * 2
def baseEnd_560808 : Nat := 28440894704863908130459

theorem tailTrace_560808 : CollatzResearch.WordTrace tailWord_560808 prefixEnd_560808 28440894704863908130459 := by
  unfold tailWord_560808
  simp only [CollatzResearch.WordTrace]
  refine ⟨10227174076147934613101539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13636232101530579484135385 10227174076147934613101539)
  ·
    refine ⟨15340761114221901919652309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10227174076147934613101539 15340761114221901919652309)
    ·
      refine ⟨359549088614575826241851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 15340761114221901919652309 359549088614575826241851)
      ·
        refine ⟨539323632921863739362777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359549088614575826241851 539323632921863739362777)
        ·
          refine ⟨404492724691397804522083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 539323632921863739362777 404492724691397804522083)
          ·
            refine ⟨606739087037096706783125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404492724691397804522083 606739087037096706783125)
            ·
              refine ⟨28440894704863908130459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 606739087037096706783125 28440894704863908130459)
              ·
                rfl

theorem cell20_560808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 6].length) (baseStart_560808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560808 prefixEnd_560808 := by exact prefixLift 560808
  have htrace : WordTrace (prefixWord ++ tailWord_560808) baseStart_560808 baseEnd_560808 := by
    simpa [prefixWord, tailWord_560808, baseEnd_560808] using wordTrace_append hprefix tailTrace_560808
  have hstable : (prefixWord ++ tailWord_560808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560808).length < 2 ^ (prefixWord ++ tailWord_560808).sum := by decide
  have hdescent : baseEnd_560808 < baseStart_560808 := by decide
  rcases family_descends (prefixWord ++ tailWord_560808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560822 : List Nat := [5, 1, 3, 1, 1, 3, 1, 1, 4]
def baseStart_560822 : Nat := 118140960795 + 560822 * 2 ^ 59
def prefixEnd_560822 : Nat := 4983230072969 + 3 ^ 40 * 560822 * 2
def baseEnd_560822 : Nat := 255974442325253346707407

theorem tailTrace_560822 : CollatzResearch.WordTrace tailWord_560822 prefixEnd_560822 255974442325253346707407 := by
  unfold tailWord_560822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1278428673390321851075795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13636572516163433078141813 1278428673390321851075795)
  ·
    refine ⟨1917643010085482776613693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1278428673390321851075795 1917643010085482776613693)
    ·
      refine ⟨719116128782056041230135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1917643010085482776613693 719116128782056041230135)
      ·
        refine ⟨1078674193173084061845203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 719116128782056041230135 1078674193173084061845203)
        ·
          refine ⟨1618011289759626092767805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1078674193173084061845203 1618011289759626092767805)
          ·
            refine ⟨606754233659859784787927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1618011289759626092767805 606754233659859784787927)
            ·
              refine ⟨910131350489789677181891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 606754233659859784787927 910131350489789677181891)
              ·
                refine ⟨1365197025734684515772837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 910131350489789677181891 1365197025734684515772837)
                ·
                  refine ⟨255974442325253346707407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1365197025734684515772837 255974442325253346707407)
                  ·
                    rfl

theorem cell20_560822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_560822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560822 prefixEnd_560822 := by exact prefixLift 560822
  have htrace : WordTrace (prefixWord ++ tailWord_560822) baseStart_560822 baseEnd_560822 := by
    simpa [prefixWord, tailWord_560822, baseEnd_560822] using wordTrace_append hprefix tailTrace_560822
  have hstable : (prefixWord ++ tailWord_560822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560822).length < 2 ^ (prefixWord ++ tailWord_560822).sum := by decide
  have hdescent : baseEnd_560822 < baseStart_560822 := by decide
  rcases family_descends (prefixWord ++ tailWord_560822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560826 : List Nat := [3, 1, 1, 1, 2, 6, 1, 1, 4]
def baseStart_560826 : Nat := 118140960795 + 560826 * 2 ^ 59
def prefixEnd_560826 : Nat := 4983230072969 + 3 ^ 40 * 560826 * 2
def baseEnd_560826 : Nat := 255976268034247110574057

theorem tailTrace_560826 : CollatzResearch.WordTrace tailWord_560826 prefixEnd_560826 255976268034247110574057 := by
  unfold tailWord_560826
  simp only [CollatzResearch.WordTrace]
  refine ⟨5113751166557664575089583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13636669777487105533572221 5113751166557664575089583)
  ·
    refine ⟨7670626749836496862634375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5113751166557664575089583 7670626749836496862634375)
    ·
      refine ⟨11505940124754745293951563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7670626749836496862634375 11505940124754745293951563)
      ·
        refine ⟨17258910187132117940927345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11505940124754745293951563 17258910187132117940927345)
        ·
          refine ⟨12944182640349088455695509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17258910187132117940927345 12944182640349088455695509)
          ·
            refine ⟨606758561266363521360727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12944182640349088455695509 606758561266363521360727)
            ·
              refine ⟨910137841899545282041091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 606758561266363521360727 910137841899545282041091)
              ·
                refine ⟨1365206762849317923061637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 910137841899545282041091 1365206762849317923061637)
                ·
                  refine ⟨255976268034247110574057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1365206762849317923061637 255976268034247110574057)
                  ·
                    rfl

theorem cell20_560826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 4].length) (baseStart_560826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560826 prefixEnd_560826 := by exact prefixLift 560826
  have htrace : WordTrace (prefixWord ++ tailWord_560826) baseStart_560826 baseEnd_560826 := by
    simpa [prefixWord, tailWord_560826, baseEnd_560826] using wordTrace_append hprefix tailTrace_560826
  have hstable : (prefixWord ++ tailWord_560826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560826).length < 2 ^ (prefixWord ++ tailWord_560826).sum := by decide
  have hdescent : baseEnd_560826 < baseStart_560826 := by decide
  rcases family_descends (prefixWord ++ tailWord_560826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560840 : List Nat := [2, 1, 3, 1, 2, 2, 3, 3, 3]
def baseStart_560840 : Nat := 118140960795 + 560840 * 2 ^ 59
def prefixEnd_560840 : Nat := 4983230072969 + 3 ^ 40 * 560840 * 2
def baseEnd_560840 : Nat := 255982658015725284107333

theorem tailTrace_560840 : CollatzResearch.WordTrace tailWord_560840 prefixEnd_560840 255982658015725284107333 := by
  unfold tailWord_560840
  simp only [CollatzResearch.WordTrace]
  refine ⟨10227757644089969345683987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13637010192119959127578649 10227757644089969345683987)
  ·
    refine ⟨15341636466134954018525981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10227757644089969345683987 15341636466134954018525981)
    ·
      refine ⟨5753113674800607756947243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15341636466134954018525981 5753113674800607756947243)
      ·
        refine ⟨8629670512200911635420865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5753113674800607756947243 8629670512200911635420865)
        ·
          refine ⟨6472252884150683726565649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8629670512200911635420865 6472252884150683726565649)
          ·
            refine ⟨4854189663113012794924237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6472252884150683726565649 4854189663113012794924237)
            ·
              refine ⟨1820321123667379798096589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4854189663113012794924237 1820321123667379798096589)
              ·
                refine ⟨682620421375267424286221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1820321123667379798096589 682620421375267424286221)
                ·
                  refine ⟨255982658015725284107333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 682620421375267424286221 255982658015725284107333)
                  ·
                    rfl

theorem cell20_560840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 3].length) (baseStart_560840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560840 prefixEnd_560840 := by exact prefixLift 560840
  have htrace : WordTrace (prefixWord ++ tailWord_560840) baseStart_560840 baseEnd_560840 := by
    simpa [prefixWord, tailWord_560840, baseEnd_560840] using wordTrace_append hprefix tailTrace_560840
  have hstable : (prefixWord ++ tailWord_560840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560840).length < 2 ^ (prefixWord ++ tailWord_560840).sum := by decide
  have hdescent : baseEnd_560840 < baseStart_560840 := by decide
  rcases family_descends (prefixWord ++ tailWord_560840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560871 : List Nat := [1, 1, 5, 4, 1, 8]
def baseStart_560871 : Nat := 118140960795 + 560871 * 2 ^ 59
def prefixEnd_560871 : Nat := 4983230072969 + 3 ^ 40 * 560871 * 2
def baseEnd_560871 : Nat := 9481363231867664965699

theorem tailTrace_560871 : CollatzResearch.WordTrace tailWord_560871 prefixEnd_560871 9481363231867664965699 := by
  unfold tailWord_560871
  simp only [CollatzResearch.WordTrace]
  refine ⟨20456645951067630985746467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13637763967378420657164311 20456645951067630985746467)
  ·
    refine ⟨30684968926601446478619701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20456645951067630985746467 30684968926601446478619701)
    ·
      refine ⟨2876715836868885607370597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30684968926601446478619701 2876715836868885607370597)
      ·
        refine ⟨539384219412916051381987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2876715836868885607370597 539384219412916051381987)
        ·
          refine ⟨809076329119374077072981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 539384219412916051381987 809076329119374077072981)
          ·
            refine ⟨9481363231867664965699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 809076329119374077072981 9481363231867664965699)
            ·
              rfl

theorem cell20_560871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 8].length) (baseStart_560871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560871 prefixEnd_560871 := by exact prefixLift 560871
  have htrace : WordTrace (prefixWord ++ tailWord_560871) baseStart_560871 baseEnd_560871 := by
    simpa [prefixWord, tailWord_560871, baseEnd_560871] using wordTrace_append hprefix tailTrace_560871
  have hstable : (prefixWord ++ tailWord_560871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560871).length < 2 ^ (prefixWord ++ tailWord_560871).sum := by decide
  have hdescent : baseEnd_560871 < baseStart_560871 := by decide
  rcases family_descends (prefixWord ++ tailWord_560871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560881 : List Nat := [1, 2, 2, 2, 2, 3, 4, 2, 2]
def baseStart_560881 : Nat := 118140960795 + 560881 * 2 ^ 59
def prefixEnd_560881 : Nat := 4983230072969 + 3 ^ 40 * 560881 * 2
def baseEnd_560881 : Nat := 256001371532911363740499

theorem tailTrace_560881 : CollatzResearch.WordTrace tailWord_560881 prefixEnd_560881 256001371532911363740499 := by
  unfold tailWord_560881
  simp only [CollatzResearch.WordTrace]
  refine ⟨20457010681031402693610497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13638007120687601795740331 20457010681031402693610497)
  ·
    refine ⟨15342758010773552020207873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20457010681031402693610497 15342758010773552020207873)
    ·
      refine ⟨11507068508080164015155905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15342758010773552020207873 11507068508080164015155905)
      ·
        refine ⟨8630301381060123011366929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11507068508080164015155905 8630301381060123011366929)
        ·
          refine ⟨6472726035795092258525197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8630301381060123011366929 6472726035795092258525197)
          ·
            refine ⟨2427272263423159596946949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6472726035795092258525197 2427272263423159596946949)
            ·
              refine ⟨455113549391842424427553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2427272263423159596946949 455113549391842424427553)
              ·
                refine ⟨341335162043881818320665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 455113549391842424427553 341335162043881818320665)
                ·
                  refine ⟨256001371532911363740499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 341335162043881818320665 256001371532911363740499)
                  ·
                    rfl

theorem cell20_560881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 2, 2].length) (baseStart_560881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560881 prefixEnd_560881 := by exact prefixLift 560881
  have htrace : WordTrace (prefixWord ++ tailWord_560881) baseStart_560881 baseEnd_560881 := by
    simpa [prefixWord, tailWord_560881, baseEnd_560881] using wordTrace_append hprefix tailTrace_560881
  have hstable : (prefixWord ++ tailWord_560881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560881).length < 2 ^ (prefixWord ++ tailWord_560881).sum := by decide
  have hdescent : baseEnd_560881 < baseStart_560881 := by decide
  rcases family_descends (prefixWord ++ tailWord_560881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560919 : List Nat := [1, 1, 3, 4, 2, 2, 2, 3, 2]
def baseStart_560919 : Nat := 118140960795 + 560919 * 2 ^ 59
def prefixEnd_560919 : Nat := 4983230072969 + 3 ^ 40 * 560919 * 2
def baseEnd_560919 : Nat := 256018715768352120473677

theorem tailTrace_560919 : CollatzResearch.WordTrace tailWord_560919 prefixEnd_560919 256018715768352120473677 := by
  unfold tailWord_560919
  simp only [CollatzResearch.WordTrace]
  refine ⟨20458396654893735183493811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13638931103262490122329207 20458396654893735183493811)
  ·
    refine ⟨30687594982340602775240717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20458396654893735183493811 30687594982340602775240717)
    ·
      refine ⟨11507848118377726040715269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30687594982340602775240717 11507848118377726040715269)
      ·
        refine ⟨2157721522195823632634113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11507848118377726040715269 2157721522195823632634113)
        ·
          refine ⟨1618291141646867724475585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2157721522195823632634113 1618291141646867724475585)
          ·
            refine ⟨1213718356235150793356689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1618291141646867724475585 1213718356235150793356689)
            ·
              refine ⟨910288767176363095017517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1213718356235150793356689 910288767176363095017517)
              ·
                refine ⟨341358287691136160631569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 910288767176363095017517 341358287691136160631569)
                ·
                  refine ⟨256018715768352120473677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 341358287691136160631569 256018715768352120473677)
                  ·
                    rfl

theorem cell20_560919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 3, 2].length) (baseStart_560919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560919 prefixEnd_560919 := by exact prefixLift 560919
  have htrace : WordTrace (prefixWord ++ tailWord_560919) baseStart_560919 baseEnd_560919 := by
    simpa [prefixWord, tailWord_560919, baseEnd_560919] using wordTrace_append hprefix tailTrace_560919
  have hstable : (prefixWord ++ tailWord_560919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560919).length < 2 ^ (prefixWord ++ tailWord_560919).sum := by decide
  have hdescent : baseEnd_560919 < baseStart_560919 := by decide
  rcases family_descends (prefixWord ++ tailWord_560919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560930 : List Nat := [3, 3, 1, 1, 2, 1, 9]
def baseStart_560930 : Nat := 118140960795 + 560930 * 2 ^ 59
def prefixEnd_560930 : Nat := 4983230072969 + 3 ^ 40 * 560930 * 2
def baseEnd_560930 : Nat := 28447081829787219011885

theorem tailTrace_560930 : CollatzResearch.WordTrace tailWord_560930 prefixEnd_560930 28447081829787219011885 := by
  unfold tailWord_560930
  simp only [CollatzResearch.WordTrace]
  refine ⟨5114699464463471015536061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13639198571902589374762829 5114699464463471015536061)
  ·
    refine ⟨1918012299173801630826023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5114699464463471015536061 1918012299173801630826023)
    ·
      refine ⟨2877018448760702446239035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1918012299173801630826023 2877018448760702446239035)
      ·
        refine ⟨4315527673141053669358553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2877018448760702446239035 4315527673141053669358553)
        ·
          refine ⟨3236645754855790252018915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4315527673141053669358553 3236645754855790252018915)
          ·
            refine ⟨4854968632283685378028373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3236645754855790252018915 4854968632283685378028373)
            ·
              refine ⟨28447081829787219011885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4854968632283685378028373 28447081829787219011885)
              ·
                rfl

theorem cell20_560930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 9].length) (baseStart_560930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560930 prefixEnd_560930 := by exact prefixLift 560930
  have htrace : WordTrace (prefixWord ++ tailWord_560930) baseStart_560930 baseEnd_560930 := by
    simpa [prefixWord, tailWord_560930, baseEnd_560930] using wordTrace_append hprefix tailTrace_560930
  have hstable : (prefixWord ++ tailWord_560930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560930).length < 2 ^ (prefixWord ++ tailWord_560930).sum := by decide
  have hdescent : baseEnd_560930 < baseStart_560930 := by decide
  rcases family_descends (prefixWord ++ tailWord_560930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560933 : List Nat := [1, 3, 1, 2, 3, 4, 1, 2, 3]
def baseStart_560933 : Nat := 118140960795 + 560933 * 2 ^ 59
def prefixEnd_560933 : Nat := 4983230072969 + 3 ^ 40 * 560933 * 2
def baseEnd_560933 : Nat := 256025105749830294006953

theorem tailTrace_560933 : CollatzResearch.WordTrace tailWord_560933 prefixEnd_560933 256025105749830294006953 := by
  unfold tailWord_560933
  simp only [CollatzResearch.WordTrace]
  refine ⟨20458907276843015574503453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13639271517895343716335635 20458907276843015574503453)
  ·
    refine ⟨7672090228816130840438795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20458907276843015574503453 7672090228816130840438795)
    ·
      refine ⟨11508135343224196260658193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7672090228816130840438795 11508135343224196260658193)
      ·
        refine ⟨8631101507418147195493645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11508135343224196260658193 8631101507418147195493645)
        ·
          refine ⟨3236663065281805198310117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8631101507418147195493645 3236663065281805198310117)
          ·
            refine ⟨606874324740338474683147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3236663065281805198310117 606874324740338474683147)
            ·
              refine ⟨910311487110507712024721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 606874324740338474683147 910311487110507712024721)
              ·
                refine ⟨682733615332880784018541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 910311487110507712024721 682733615332880784018541)
                ·
                  refine ⟨256025105749830294006953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 682733615332880784018541 256025105749830294006953)
                  ·
                    rfl

theorem cell20_560933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 3].length) (baseStart_560933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560933 prefixEnd_560933 := by exact prefixLift 560933
  have htrace : WordTrace (prefixWord ++ tailWord_560933) baseStart_560933 baseEnd_560933 := by
    simpa [prefixWord, tailWord_560933, baseEnd_560933] using wordTrace_append hprefix tailTrace_560933
  have hstable : (prefixWord ++ tailWord_560933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560933).length < 2 ^ (prefixWord ++ tailWord_560933).sum := by decide
  have hdescent : baseEnd_560933 < baseStart_560933 := by decide
  rcases family_descends (prefixWord ++ tailWord_560933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560940 : List Nat := [2, 2, 1, 1, 1, 5, 2, 4, 2]
def baseStart_560940 : Nat := 118140960795 + 560940 * 2 ^ 59
def prefixEnd_560940 : Nat := 4983230072969 + 3 ^ 40 * 560940 * 2
def baseEnd_560940 : Nat := 256028300740569380773591

theorem tailTrace_560940 : CollatzResearch.WordTrace tailWord_560940 prefixEnd_560940 256028300740569380773591 := by
  unfold tailWord_560940
  simp only [CollatzResearch.WordTrace]
  refine ⟨10229581293908827885004137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13639441725211770513338849 10229581293908827885004137)
  ·
    refine ⟨7672185970431620913753103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10229581293908827885004137 7672185970431620913753103)
    ·
      refine ⟨11508278955647431370629655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7672185970431620913753103 11508278955647431370629655)
      ·
        refine ⟨17262418433471147055944483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11508278955647431370629655 17262418433471147055944483)
        ·
          refine ⟨25893627650206720583916725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17262418433471147055944483 25893627650206720583916725)
          ·
            refine ⟨2427527592206880054742193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25893627650206720583916725 2427527592206880054742193)
            ·
              refine ⟨1820645694155160041056645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2427527592206880054742193 1820645694155160041056645)
              ·
                refine ⟨341371067654092507698121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1820645694155160041056645 341371067654092507698121)
                ·
                  refine ⟨256028300740569380773591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 341371067654092507698121 256028300740569380773591)
                  ·
                    rfl

theorem cell20_560940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 4, 2].length) (baseStart_560940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560940 prefixEnd_560940 := by exact prefixLift 560940
  have htrace : WordTrace (prefixWord ++ tailWord_560940) baseStart_560940 baseEnd_560940 := by
    simpa [prefixWord, tailWord_560940, baseEnd_560940] using wordTrace_append hprefix tailTrace_560940
  have hstable : (prefixWord ++ tailWord_560940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560940).length < 2 ^ (prefixWord ++ tailWord_560940).sum := by decide
  have hdescent : baseEnd_560940 < baseStart_560940 := by decide
  rcases family_descends (prefixWord ++ tailWord_560940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560968 : List Nat := [2, 1, 3, 1, 1, 5, 1, 6]
def baseStart_560968 : Nat := 118140960795 + 560968 * 2 ^ 59
def prefixEnd_560968 : Nat := 4983230072969 + 3 ^ 40 * 560968 * 2
def baseEnd_560968 : Nat := 85347026901175242613381

theorem tailTrace_560968 : CollatzResearch.WordTrace tailWord_560968 prefixEnd_560968 85347026901175242613381 := by
  unfold tailWord_560968
  simp only [CollatzResearch.WordTrace]
  refine ⟨10230091915858108276013779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13640122554477477701351705 10230091915858108276013779)
  ·
    refine ⟨15345137873787162414020669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10230091915858108276013779 15345137873787162414020669)
    ·
      refine ⟨5754426702670185905257751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15345137873787162414020669 5754426702670185905257751)
      ·
        refine ⟨8631640054005278857886627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5754426702670185905257751 8631640054005278857886627)
        ·
          refine ⟨12947460081007918286829941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8631640054005278857886627 12947460081007918286829941)
          ·
            refine ⟨1213824382594492339390307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12947460081007918286829941 1213824382594492339390307)
            ·
              refine ⟨1820736573891738509085461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1213824382594492339390307 1820736573891738509085461)
              ·
                refine ⟨85347026901175242613381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1820736573891738509085461 85347026901175242613381)
                ·
                  rfl

theorem cell20_560968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 6].length) (baseStart_560968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560968 prefixEnd_560968 := by exact prefixLift 560968
  have htrace : WordTrace (prefixWord ++ tailWord_560968) baseStart_560968 baseEnd_560968 := by
    simpa [prefixWord, tailWord_560968, baseEnd_560968] using wordTrace_append hprefix tailTrace_560968
  have hstable : (prefixWord ++ tailWord_560968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560968).length < 2 ^ (prefixWord ++ tailWord_560968).sum := by decide
  have hdescent : baseEnd_560968 < baseStart_560968 := by decide
  rcases family_descends (prefixWord ++ tailWord_560968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_560995 : List Nat := [1, 1, 1, 5, 5, 1, 1, 1, 4]
def baseStart_560995 : Nat := 118140960795 + 560995 * 2 ^ 59
def prefixEnd_560995 : Nat := 4983230072969 + 3 ^ 40 * 560995 * 2
def baseEnd_560995 : Nat := 256053404239233633940033

theorem tailTrace_560995 : CollatzResearch.WordTrace tailWord_560995 prefixEnd_560995 256053404239233633940033 := by
  unfold tailWord_560995
  simp only [CollatzResearch.WordTrace]
  refine ⟨20461168602618400163260439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13640779068412266775506959 20461168602618400163260439)
  ·
    refine ⟨30691752903927600244890659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20461168602618400163260439 30691752903927600244890659)
    ·
      refine ⟨46037629355891400367335989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30691752903927600244890659 46037629355891400367335989)
      ·
        refine ⟨4316027752114818784437749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46037629355891400367335989 4316027752114818784437749)
        ·
          refine ⟨404627601760764261041039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4316027752114818784437749 404627601760764261041039)
          ·
            refine ⟨606941402641146391561559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404627601760764261041039 606941402641146391561559)
            ·
              refine ⟨910412103961719587342339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 606941402641146391561559 910412103961719587342339)
              ·
                refine ⟨1365618155942579381013509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 910412103961719587342339 1365618155942579381013509)
                ·
                  refine ⟨256053404239233633940033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1365618155942579381013509 256053404239233633940033)
                  ·
                    rfl

theorem cell20_560995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 4].length) (baseStart_560995 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_560995 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_560995 prefixEnd_560995 := by exact prefixLift 560995
  have htrace : WordTrace (prefixWord ++ tailWord_560995) baseStart_560995 baseEnd_560995 := by
    simpa [prefixWord, tailWord_560995, baseEnd_560995] using wordTrace_append hprefix tailTrace_560995
  have hstable : (prefixWord ++ tailWord_560995).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_560995).length < 2 ^ (prefixWord ++ tailWord_560995).sum := by decide
  have hdescent : baseEnd_560995 < baseStart_560995 := by decide
  rcases family_descends (prefixWord ++ tailWord_560995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561002 : List Nat := [3, 1, 3, 4, 1, 1, 2, 5]
def baseStart_561002 : Nat := 118140960795 + 561002 * 2 ^ 59
def prefixEnd_561002 : Nat := 4983230072969 + 3 ^ 40 * 561002 * 2
def baseEnd_561002 : Nat := 85352199743324240235557

theorem tailTrace_561002 : CollatzResearch.WordTrace tailWord_561002 prefixEnd_561002 85352199743324240235557 := by
  unfold tailWord_561002
  simp only [CollatzResearch.WordTrace]
  refine ⟨5115355978398260089691315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13640949275728693572510173 5115355978398260089691315)
  ·
    refine ⟨7673033967597390134536973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5115355978398260089691315 7673033967597390134536973)
    ·
      refine ⟨2877387737849021300451365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7673033967597390134536973 2877387737849021300451365)
      ·
        refine ⟨539510200846691493834631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2877387737849021300451365 539510200846691493834631)
        ·
          refine ⟨809265301270037240751947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 539510200846691493834631 809265301270037240751947)
          ·
            refine ⟨1213897951905055861127921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 809265301270037240751947 1213897951905055861127921)
            ·
              refine ⟨910423463928791895845941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1213897951905055861127921 910423463928791895845941)
              ·
                refine ⟨85352199743324240235557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 910423463928791895845941 85352199743324240235557)
                ·
                  rfl

theorem cell20_561002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_561002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561002 prefixEnd_561002 := by exact prefixLift 561002
  have htrace : WordTrace (prefixWord ++ tailWord_561002) baseStart_561002 baseEnd_561002 := by
    simpa [prefixWord, tailWord_561002, baseEnd_561002] using wordTrace_append hprefix tailTrace_561002
  have hstable : (prefixWord ++ tailWord_561002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561002).length < 2 ^ (prefixWord ++ tailWord_561002).sum := by decide
  have hdescent : baseEnd_561002 < baseStart_561002 := by decide
  rcases family_descends (prefixWord ++ tailWord_561002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561044 : List Nat := [2, 4, 2, 1, 1, 10]
def baseStart_561044 : Nat := 118140960795 + 561044 * 2 ^ 59
def prefixEnd_561044 : Nat := 4983230072969 + 3 ^ 40 * 561044 * 2
def baseEnd_561044 : Nat := 9484287747200268196537

theorem tailTrace_561044 : CollatzResearch.WordTrace tailWord_561044 prefixEnd_561044 9484287747200268196537 := by
  unfold tailWord_561044
  simp only [CollatzResearch.WordTrace]
  refine ⟨10231477889720440765897093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13641970519627254354529457 10231477889720440765897093)
  ·
    refine ⟨1918402104322582643605705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10231477889720440765897093 1918402104322582643605705)
    ·
      refine ⟨1438801578241936982704279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1918402104322582643605705 1438801578241936982704279)
      ·
        refine ⟨2158202367362905474056419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1438801578241936982704279 2158202367362905474056419)
        ·
          refine ⟨3237303551044358211084629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2158202367362905474056419 3237303551044358211084629)
          ·
            refine ⟨9484287747200268196537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3237303551044358211084629 9484287747200268196537)
            ·
              rfl

theorem cell20_561044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 10].length) (baseStart_561044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561044 prefixEnd_561044 := by exact prefixLift 561044
  have htrace : WordTrace (prefixWord ++ tailWord_561044) baseStart_561044 baseEnd_561044 := by
    simpa [prefixWord, tailWord_561044, baseEnd_561044] using wordTrace_append hprefix tailTrace_561044
  have hstable : (prefixWord ++ tailWord_561044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561044).length < 2 ^ (prefixWord ++ tailWord_561044).sum := by decide
  have hdescent : baseEnd_561044 < baseStart_561044 := by decide
  rcases family_descends (prefixWord ++ tailWord_561044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561050 : List Nat := [3, 1, 1, 4, 2, 3, 2, 2, 2]
def baseStart_561050 : Nat := 118140960795 + 561050 * 2 ^ 59
def prefixEnd_561050 : Nat := 4983230072969 + 3 ^ 40 * 561050 * 2
def baseEnd_561050 : Nat := 256078507737897887106475

theorem tailTrace_561050 : CollatzResearch.WordTrace tailWord_561050 prefixEnd_561050 256078507737897887106475 := by
  unfold tailWord_561050
  simp only [CollatzResearch.WordTrace]
  refine ⟨5115793654354786139128151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13642116411612763037675069 5115793654354786139128151)
  ·
    refine ⟨7673690481532179208692227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5115793654354786139128151 7673690481532179208692227)
    ·
      refine ⟨11510535722298268813038341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7673690481532179208692227 11510535722298268813038341)
      ·
        refine ⟨2158225447930925402444689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11510535722298268813038341 2158225447930925402444689)
        ·
          refine ⟨1618669085948194051833517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2158225447930925402444689 1618669085948194051833517)
          ·
            refine ⟨607000907230572769437569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1618669085948194051833517 607000907230572769437569)
            ·
              refine ⟨455250680422929577078177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 607000907230572769437569 455250680422929577078177)
              ·
                refine ⟨341438010317197182808633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 455250680422929577078177 341438010317197182808633)
                ·
                  refine ⟨256078507737897887106475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 341438010317197182808633 256078507737897887106475)
                  ·
                    rfl

theorem cell20_561050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 2, 2].length) (baseStart_561050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561050 prefixEnd_561050 := by exact prefixLift 561050
  have htrace : WordTrace (prefixWord ++ tailWord_561050) baseStart_561050 baseEnd_561050 := by
    simpa [prefixWord, tailWord_561050, baseEnd_561050] using wordTrace_append hprefix tailTrace_561050
  have hstable : (prefixWord ++ tailWord_561050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561050).length < 2 ^ (prefixWord ++ tailWord_561050).sum := by decide
  have hdescent : baseEnd_561050 < baseStart_561050 := by decide
  rcases family_descends (prefixWord ++ tailWord_561050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561065 : List Nat := [1, 2, 1, 1, 1, 1, 4, 9]
def baseStart_561065 : Nat := 118140960795 + 561065 * 2 ^ 59
def prefixEnd_561065 : Nat := 4983230072969 + 3 ^ 40 * 561065 * 2
def baseEnd_561065 : Nat := 85361784715541500535471

theorem tailTrace_561065 : CollatzResearch.WordTrace tailWord_561065 prefixEnd_561065 85361784715541500535471 := by
  unfold tailWord_561065
  simp only [CollatzResearch.WordTrace]
  refine ⟨20463721712364802118308649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13642481141576534745539099 20463721712364802118308649)
  ·
    refine ⟨15347791284273601588731487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20463721712364802118308649 15347791284273601588731487)
    ·
      refine ⟨23021686926410402383097231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15347791284273601588731487 23021686926410402383097231)
      ·
        refine ⟨34532530389615603574645847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23021686926410402383097231 34532530389615603574645847)
        ·
          refine ⟨51798795584423405361968771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34532530389615603574645847 51798795584423405361968771)
          ·
            refine ⟨77698193376635108042953157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51798795584423405361968771 77698193376635108042953157)
            ·
              refine ⟨14568411258119082758053717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77698193376635108042953157 14568411258119082758053717)
              ·
                refine ⟨85361784715541500535471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14568411258119082758053717 85361784715541500535471)
                ·
                  rfl

theorem cell20_561065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 9].length) (baseStart_561065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561065 prefixEnd_561065 := by exact prefixLift 561065
  have htrace : WordTrace (prefixWord ++ tailWord_561065) baseStart_561065 baseEnd_561065 := by
    simpa [prefixWord, tailWord_561065, baseEnd_561065] using wordTrace_append hprefix tailTrace_561065
  have hstable : (prefixWord ++ tailWord_561065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561065).length < 2 ^ (prefixWord ++ tailWord_561065).sum := by decide
  have hdescent : baseEnd_561065 < baseStart_561065 := by decide
  rcases family_descends (prefixWord ++ tailWord_561065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561103 : List Nat := [1, 1, 2, 1, 1, 5, 9]
def baseStart_561103 : Nat := 118140960795 + 561103 * 2 ^ 59
def prefixEnd_561103 : Nat := 4983230072969 + 3 ^ 40 * 561103 * 2
def baseEnd_561103 : Nat := 28455855375785028704399

theorem tailTrace_561103 : CollatzResearch.WordTrace tailWord_561103 prefixEnd_561103 28455855375785028704399 := by
  unfold tailWord_561103
  simp only [CollatzResearch.WordTrace]
  refine ⟨20465107686227134608191963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13643405124151423072127975 20465107686227134608191963)
  ·
    refine ⟨30697661529340701912287945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20465107686227134608191963 30697661529340701912287945)
    ·
      refine ⟨23023246147005526434215959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30697661529340701912287945 23023246147005526434215959)
      ·
        refine ⟨34534869220508289651323939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23023246147005526434215959 34534869220508289651323939)
        ·
          refine ⟨51802303830762434476985909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34534869220508289651323939 51802303830762434476985909)
          ·
            refine ⟨4856465984133978232217429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51802303830762434476985909 4856465984133978232217429)
            ·
              refine ⟨28455855375785028704399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4856465984133978232217429 28455855375785028704399)
              ·
                rfl

theorem cell20_561103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 9].length) (baseStart_561103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561103 prefixEnd_561103 := by exact prefixLift 561103
  have htrace : WordTrace (prefixWord ++ tailWord_561103) baseStart_561103 baseEnd_561103 := by
    simpa [prefixWord, tailWord_561103, baseEnd_561103] using wordTrace_append hprefix tailTrace_561103
  have hstable : (prefixWord ++ tailWord_561103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561103).length < 2 ^ (prefixWord ++ tailWord_561103).sum := by decide
  have hdescent : baseEnd_561103 < baseStart_561103 := by decide
  rcases family_descends (prefixWord ++ tailWord_561103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561123 : List Nat := [1, 1, 1, 6, 1, 3, 3, 1, 3]
def baseStart_561123 : Nat := 118140960795 + 561123 * 2 ^ 59
def prefixEnd_561123 : Nat := 4983230072969 + 3 ^ 40 * 561123 * 2
def baseEnd_561123 : Nat := 256111826927034077672843

theorem tailTrace_561123 : CollatzResearch.WordTrace tailWord_561123 prefixEnd_561123 256111826927034077672843 := by
  unfold tailWord_561123
  simp only [CollatzResearch.WordTrace]
  refine ⟨20465837146154678023920023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13643891430769785349280015 20465837146154678023920023)
  ·
    refine ⟨30698755719232017035880035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20465837146154678023920023 30698755719232017035880035)
    ·
      refine ⟨46048133578848025553820053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30698755719232017035880035 46048133578848025553820053)
      ·
        refine ⟨2158506261508501197835315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 46048133578848025553820053 2158506261508501197835315)
        ·
          refine ⟨3237759392262751796752973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2158506261508501197835315 3237759392262751796752973)
          ·
            refine ⟨1214159772098531923782365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3237759392262751796752973 1214159772098531923782365)
            ·
              refine ⟨455309914536949471418387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1214159772098531923782365 455309914536949471418387)
              ·
                refine ⟨682964871805424207127581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 455309914536949471418387 682964871805424207127581)
                ·
                  refine ⟨256111826927034077672843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 682964871805424207127581 256111826927034077672843)
                  ·
                    rfl

theorem cell20_561123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 3].length) (baseStart_561123 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561123 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561123 prefixEnd_561123 := by exact prefixLift 561123
  have htrace : WordTrace (prefixWord ++ tailWord_561123) baseStart_561123 baseEnd_561123 := by
    simpa [prefixWord, tailWord_561123, baseEnd_561123] using wordTrace_append hprefix tailTrace_561123
  have hstable : (prefixWord ++ tailWord_561123).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561123).length < 2 ^ (prefixWord ++ tailWord_561123).sum := by decide
  have hdescent : baseEnd_561123 < baseStart_561123 := by decide
  rcases family_descends (prefixWord ++ tailWord_561123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561133 : List Nat := [1, 5, 1, 4, 1, 2, 2, 4]
def baseStart_561133 : Nat := 118140960795 + 561133 * 2 ^ 59
def prefixEnd_561133 : Nat := 4983230072969 + 3 ^ 40 * 561133 * 2
def baseEnd_561133 : Nat := 85372130399839495779823

theorem tailTrace_561133 : CollatzResearch.WordTrace tailWord_561133 prefixEnd_561133 85372130399839495779823 := by
  unfold tailWord_561133
  simp only [CollatzResearch.WordTrace]
  refine ⟨20466201876118449731784053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13644134584078966487856035 20466201876118449731784053)
  ·
    refine ⟨1918706425886104662354755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20466201876118449731784053 1918706425886104662354755)
    ·
      refine ⟨2878059638829156993532133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1918706425886104662354755 2878059638829156993532133)
      ·
        refine ⟨539636182280466936287275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2878059638829156993532133 539636182280466936287275)
        ·
          refine ⟨809454273420700404430913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 539636182280466936287275 809454273420700404430913)
          ·
            refine ⟨607090705065525303323185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 809454273420700404430913 607090705065525303323185)
            ·
              refine ⟨455318028799143977492389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 607090705065525303323185 455318028799143977492389)
              ·
                refine ⟨85372130399839495779823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 455318028799143977492389 85372130399839495779823)
                ·
                  rfl

theorem cell20_561133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 4].length) (baseStart_561133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561133 prefixEnd_561133 := by exact prefixLift 561133
  have htrace : WordTrace (prefixWord ++ tailWord_561133) baseStart_561133 baseEnd_561133 := by
    simpa [prefixWord, tailWord_561133, baseEnd_561133] using wordTrace_append hprefix tailTrace_561133
  have hstable : (prefixWord ++ tailWord_561133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561133).length < 2 ^ (prefixWord ++ tailWord_561133).sum := by decide
  have hdescent : baseEnd_561133 < baseStart_561133 := by decide
  rcases family_descends (prefixWord ++ tailWord_561133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561175 : List Nat := [1, 1, 3, 5, 2, 1, 2, 5]
def baseStart_561175 : Nat := 118140960795 + 561175 * 2 ^ 59
def prefixEnd_561175 : Nat := 4983230072969 + 3 ^ 40 * 561175 * 2
def baseEnd_561175 : Nat := 85378520381317669313099

theorem tailTrace_561175 : CollatzResearch.WordTrace tailWord_561175 prefixEnd_561175 85378520381317669313099 := by
  unfold tailWord_561175
  simp only [CollatzResearch.WordTrace]
  refine ⟨20467733741966290904812979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13645155827977527269875319 20467733741966290904812979)
  ·
    refine ⟨30701600612949436357219469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20467733741966290904812979 30701600612949436357219469)
    ·
      refine ⟨11513100229856038633957301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30701600612949436357219469 11513100229856038633957301)
      ·
        refine ⟨1079353146549003621933497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11513100229856038633957301 1079353146549003621933497)
        ·
          refine ⟨809514859911752716450123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1079353146549003621933497 809514859911752716450123)
          ·
            refine ⟨1214272289867629074675185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 809514859911752716450123 1214272289867629074675185)
            ·
              refine ⟨910704217400721806006389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1214272289867629074675185 910704217400721806006389)
              ·
                refine ⟨85378520381317669313099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 910704217400721806006389 85378520381317669313099)
                ·
                  rfl

theorem cell20_561175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 5].length) (baseStart_561175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561175 prefixEnd_561175 := by exact prefixLift 561175
  have htrace : WordTrace (prefixWord ++ tailWord_561175) baseStart_561175 baseEnd_561175 := by
    simpa [prefixWord, tailWord_561175, baseEnd_561175] using wordTrace_append hprefix tailTrace_561175
  have hstable : (prefixWord ++ tailWord_561175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561175).length < 2 ^ (prefixWord ++ tailWord_561175).sum := by decide
  have hdescent : baseEnd_561175 < baseStart_561175 := by decide
  rcases family_descends (prefixWord ++ tailWord_561175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561227 : List Nat := [1, 1, 1, 1, 3, 1, 2, 8, 2]
def baseStart_561227 : Nat := 118140960795 + 561227 * 2 ^ 59
def prefixEnd_561227 : Nat := 4983230072969 + 3 ^ 40 * 561227 * 2
def baseEnd_561227 : Nat := 256159295360871938205751

theorem tailTrace_561227 : CollatzResearch.WordTrace tailWord_561227 prefixEnd_561227 256159295360871938205751 := by
  unfold tailWord_561227
  simp only [CollatzResearch.WordTrace]
  refine ⟨20469630337777903785705935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13646420225185269190470623 20469630337777903785705935)
  ·
    refine ⟨30704445506666855678558903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20469630337777903785705935 30704445506666855678558903)
    ·
      refine ⟨46056668260000283517838355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30704445506666855678558903 46056668260000283517838355)
      ·
        refine ⟨69085002390000425276757533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46056668260000283517838355 69085002390000425276757533)
        ·
          refine ⟨25906875896250159478784075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69085002390000425276757533 25906875896250159478784075)
          ·
            refine ⟨38860313844375239218176113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25906875896250159478784075 38860313844375239218176113)
            ·
              refine ⟨29145235383281429413632085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38860313844375239218176113 29145235383281429413632085)
              ·
                refine ⟨341545727147829250941001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 29145235383281429413632085 341545727147829250941001)
                ·
                  refine ⟨256159295360871938205751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 341545727147829250941001 256159295360871938205751)
                  ·
                    rfl

theorem cell20_561227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 8, 2].length) (baseStart_561227 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561227 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561227 prefixEnd_561227 := by exact prefixLift 561227
  have htrace : WordTrace (prefixWord ++ tailWord_561227) baseStart_561227 baseEnd_561227 := by
    simpa [prefixWord, tailWord_561227, baseEnd_561227] using wordTrace_append hprefix tailTrace_561227
  have hstable : (prefixWord ++ tailWord_561227).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561227).length < 2 ^ (prefixWord ++ tailWord_561227).sum := by decide
  have hdescent : baseEnd_561227 < baseStart_561227 := by decide
  rcases family_descends (prefixWord ++ tailWord_561227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561241 : List Nat := [1, 2, 1, 2, 2, 1, 3, 5, 3]
def baseStart_561241 : Nat := 118140960795 + 561241 * 2 ^ 59
def prefixEnd_561241 : Nat := 4983230072969 + 3 ^ 40 * 561241 * 2
def baseEnd_561241 : Nat := 256165685342350111739027

theorem tailTrace_561241 : CollatzResearch.WordTrace tailWord_561241 prefixEnd_561241 256165685342350111739027 := by
  unfold tailWord_561241
  simp only [CollatzResearch.WordTrace]
  refine ⟨20470140959727184176715577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13646760639818122784477051 20470140959727184176715577)
  ·
    refine ⟨15352605719795388132536683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20470140959727184176715577 15352605719795388132536683)
    ·
      refine ⟨23028908579693082198805025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15352605719795388132536683 23028908579693082198805025)
      ·
        refine ⟨17271681434769811649103769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23028908579693082198805025 17271681434769811649103769)
        ·
          refine ⟨12953761076077358736827827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17271681434769811649103769 12953761076077358736827827)
          ·
            refine ⟨19430641614116038105241741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12953761076077358736827827 19430641614116038105241741)
            ·
              refine ⟨7286490605293514289465653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19430641614116038105241741 7286490605293514289465653)
              ·
                refine ⟨683108494246266964637405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7286490605293514289465653 683108494246266964637405)
                ·
                  refine ⟨256165685342350111739027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 683108494246266964637405 256165685342350111739027)
                  ·
                    rfl

theorem cell20_561241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 3].length) (baseStart_561241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561241 prefixEnd_561241 := by exact prefixLift 561241
  have htrace : WordTrace (prefixWord ++ tailWord_561241) baseStart_561241 baseEnd_561241 := by
    simpa [prefixWord, tailWord_561241, baseEnd_561241] using wordTrace_append hprefix tailTrace_561241
  have hstable : (prefixWord ++ tailWord_561241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561241).length < 2 ^ (prefixWord ++ tailWord_561241).sum := by decide
  have hdescent : baseEnd_561241 < baseStart_561241 := by decide
  rcases family_descends (prefixWord ++ tailWord_561241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561248 : List Nat := [2, 1, 1, 3, 2, 3, 1, 1, 6]
def baseStart_561248 : Nat := 118140960795 + 561248 * 2 ^ 59
def prefixEnd_561248 : Nat := 4983230072969 + 3 ^ 40 * 561248 * 2
def baseEnd_561248 : Nat := 256168880333089198505665

theorem tailTrace_561248 : CollatzResearch.WordTrace tailWord_561248 prefixEnd_561248 256168880333089198505665 := by
  unfold tailWord_561248
  simp only [CollatzResearch.WordTrace]
  refine ⟨10235198135350912186110199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13646930847134549581480265 10235198135350912186110199)
  ·
    refine ⟨15352797203026368279165299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10235198135350912186110199 15352797203026368279165299)
    ·
      refine ⟨23029195804539552418747949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15352797203026368279165299 23029195804539552418747949)
      ·
        refine ⟨8635948426702332157030481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23029195804539552418747949 8635948426702332157030481)
        ·
          refine ⟨6476961320026749117772861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8635948426702332157030481 6476961320026749117772861)
          ·
            refine ⟨2428860495010030919164823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6476961320026749117772861 2428860495010030919164823)
            ·
              refine ⟨3643290742515046378747235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2428860495010030919164823 3643290742515046378747235)
              ·
                refine ⟨5464936113772569568120853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3643290742515046378747235 5464936113772569568120853)
                ·
                  refine ⟨256168880333089198505665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5464936113772569568120853 256168880333089198505665)
                  ·
                    rfl

theorem cell20_561248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_561248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561248 prefixEnd_561248 := by exact prefixLift 561248
  have htrace : WordTrace (prefixWord ++ tailWord_561248) baseStart_561248 baseEnd_561248 := by
    simpa [prefixWord, tailWord_561248, baseEnd_561248] using wordTrace_append hprefix tailTrace_561248
  have hstable : (prefixWord ++ tailWord_561248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561248).length < 2 ^ (prefixWord ++ tailWord_561248).sum := by decide
  have hdescent : baseEnd_561248 < baseStart_561248 := by decide
  rcases family_descends (prefixWord ++ tailWord_561248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561296 : List Nat := [2, 1, 1, 1, 1, 1, 9, 1, 3]
def baseStart_561296 : Nat := 118140960795 + 561296 * 2 ^ 59
def prefixEnd_561296 : Nat := 4983230072969 + 3 ^ 40 * 561296 * 2
def baseEnd_561296 : Nat := 256190788841014364905469

theorem tailTrace_561296 : CollatzResearch.WordTrace tailWord_561296 prefixEnd_561296 256190788841014364905469 := by
  unfold tailWord_561296
  simp only [CollatzResearch.WordTrace]
  refine ⟨10236073487263964284983871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13648097983018619046645161 10236073487263964284983871)
  ·
    refine ⟨15354110230895946427475807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10236073487263964284983871 15354110230895946427475807)
    ·
      refine ⟨23031165346343919641213711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15354110230895946427475807 23031165346343919641213711)
      ·
        refine ⟨34546748019515879461820567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23031165346343919641213711 34546748019515879461820567)
        ·
          refine ⟨51820122029273819192730851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34546748019515879461820567 51820122029273819192730851)
          ·
            refine ⟨77730183043910728789096277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51820122029273819192730851 77730183043910728789096277)
            ·
              refine ⟨455450291272914426498611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 77730183043910728789096277 455450291272914426498611)
              ·
                refine ⟨683175436909371639747917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 455450291272914426498611 683175436909371639747917)
                ·
                  refine ⟨256190788841014364905469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 683175436909371639747917 256190788841014364905469)
                  ·
                    rfl

theorem cell20_561296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 3].length) (baseStart_561296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561296 prefixEnd_561296 := by exact prefixLift 561296
  have htrace : WordTrace (prefixWord ++ tailWord_561296) baseStart_561296 baseEnd_561296 := by
    simpa [prefixWord, tailWord_561296, baseEnd_561296] using wordTrace_append hprefix tailTrace_561296
  have hstable : (prefixWord ++ tailWord_561296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561296).length < 2 ^ (prefixWord ++ tailWord_561296).sum := by decide
  have hdescent : baseEnd_561296 < baseStart_561296 := by decide
  rcases family_descends (prefixWord ++ tailWord_561296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561302 : List Nat := [5, 3, 2, 1, 1, 1, 1, 6]
def baseStart_561302 : Nat := 118140960795 + 561302 * 2 ^ 59
def prefixEnd_561302 : Nat := 4983230072969 + 3 ^ 40 * 561302 * 2
def baseEnd_561302 : Nat := 85397842468168336901815

theorem tailTrace_561302 : CollatzResearch.WordTrace tailWord_561302 prefixEnd_561302 85397842468168336901815 := by
  unfold tailWord_561302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1279522863281636974667885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13648243875004127729790773 1279522863281636974667885)
  ·
    refine ⟨479821073730613865500457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1279522863281636974667885 479821073730613865500457)
    ·
      refine ⟨359865805297960399125343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 479821073730613865500457 359865805297960399125343)
      ·
        refine ⟨539798707946940598688015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359865805297960399125343 539798707946940598688015)
        ·
          refine ⟨809698061920410898032023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 539798707946940598688015 809698061920410898032023)
          ·
            refine ⟨1214547092880616347048035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 809698061920410898032023 1214547092880616347048035)
            ·
              refine ⟨1821820639320924520572053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1214547092880616347048035 1821820639320924520572053)
              ·
                refine ⟨85397842468168336901815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1821820639320924520572053 85397842468168336901815)
                ·
                  rfl

theorem cell20_561302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_561302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561302 prefixEnd_561302 := by exact prefixLift 561302
  have htrace : WordTrace (prefixWord ++ tailWord_561302) baseStart_561302 baseEnd_561302 := by
    simpa [prefixWord, tailWord_561302, baseEnd_561302] using wordTrace_append hprefix tailTrace_561302
  have hstable : (prefixWord ++ tailWord_561302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561302).length < 2 ^ (prefixWord ++ tailWord_561302).sum := by decide
  have hdescent : baseEnd_561302 < baseStart_561302 := by decide
  rcases family_descends (prefixWord ++ tailWord_561302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561306 : List Nat := [3, 1, 1, 5, 2, 2, 2, 4]
def baseStart_561306 : Nat := 118140960795 + 561306 * 2 ^ 59
def prefixEnd_561306 : Nat := 4983230072969 + 3 ^ 40 * 561306 * 2
def baseEnd_561306 : Nat := 85398451037832924857365

theorem tailTrace_561306 : CollatzResearch.WordTrace tailWord_561306 prefixEnd_561306 85398451037832924857365 := by
  unfold tailWord_561306
  simp only [CollatzResearch.WordTrace]
  refine ⟨5118127926122925069457943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13648341136327800185221181 5118127926122925069457943)
  ·
    refine ⟨7677191889184387604186915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5118127926122925069457943 7677191889184387604186915)
    ·
      refine ⟨11515787833776581406280373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7677191889184387604186915 11515787833776581406280373)
      ·
        refine ⟨1079605109416554506838785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11515787833776581406280373 1079605109416554506838785)
        ·
          refine ⟨809703832062415880129089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1079605109416554506838785 809703832062415880129089)
          ·
            refine ⟨607277874046811910096817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 809703832062415880129089 607277874046811910096817)
            ·
              refine ⟨455458405535108932572613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 607277874046811910096817 455458405535108932572613)
              ·
                refine ⟨85398451037832924857365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 455458405535108932572613 85398451037832924857365)
                ·
                  rfl

theorem cell20_561306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_561306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561306 prefixEnd_561306 := by exact prefixLift 561306
  have htrace : WordTrace (prefixWord ++ tailWord_561306) baseStart_561306 baseEnd_561306 := by
    simpa [prefixWord, tailWord_561306, baseEnd_561306] using wordTrace_append hprefix tailTrace_561306
  have hstable : (prefixWord ++ tailWord_561306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561306).length < 2 ^ (prefixWord ++ tailWord_561306).sum := by decide
  have hdescent : baseEnd_561306 < baseStart_561306 := by decide
  rcases family_descends (prefixWord ++ tailWord_561306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561316 : List Nat := [2, 3, 1, 2, 5, 1, 1, 3, 2]
def baseStart_561316 : Nat := 118140960795 + 561316 * 2 ^ 59
def prefixEnd_561316 : Nat := 4983230072969 + 3 ^ 40 * 561316 * 2
def baseEnd_561316 : Nat := 256199917385983184238721

theorem tailTrace_561316 : CollatzResearch.WordTrace tailWord_561316 prefixEnd_561316 256199917385983184238721 := by
  unfold tailWord_561316
  simp only [CollatzResearch.WordTrace]
  refine ⟨10236438217227735992847901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13648584289636981323797201 10236438217227735992847901)
  ·
    refine ⟨3838664331460400997317963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10236438217227735992847901 3838664331460400997317963)
    ·
      refine ⟨5757996497190601495976945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3838664331460400997317963 5757996497190601495976945)
      ·
        refine ⟨4318497372892951121982709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5757996497190601495976945 4318497372892951121982709)
        ·
          refine ⟨404859128708714167685879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4318497372892951121982709 404859128708714167685879)
          ·
            refine ⟨607288693063071251528819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404859128708714167685879 607288693063071251528819)
            ·
              refine ⟨910933039594606877293229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 607288693063071251528819 910933039594606877293229)
              ·
                refine ⟨341599889847977578984961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 910933039594606877293229 341599889847977578984961)
                ·
                  refine ⟨256199917385983184238721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 341599889847977578984961 256199917385983184238721)
                  ·
                    rfl

theorem cell20_561316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_561316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561316 prefixEnd_561316 := by exact prefixLift 561316
  have htrace : WordTrace (prefixWord ++ tailWord_561316) baseStart_561316 baseEnd_561316 := by
    simpa [prefixWord, tailWord_561316, baseEnd_561316] using wordTrace_append hprefix tailTrace_561316
  have hstable : (prefixWord ++ tailWord_561316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561316).length < 2 ^ (prefixWord ++ tailWord_561316).sum := by decide
  have hdescent : baseEnd_561316 < baseStart_561316 := by decide
  rcases family_descends (prefixWord ++ tailWord_561316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561348 : List Nat := [2, 3, 3, 1, 2, 1, 1, 7]
def baseStart_561348 : Nat := 118140960795 + 561348 * 2 ^ 59
def prefixEnd_561348 : Nat := 4983230072969 + 3 ^ 40 * 561348 * 2
def baseEnd_561348 : Nat := 85404841019311098390641

theorem tailTrace_561348 : CollatzResearch.WordTrace tailWord_561348 prefixEnd_561348 85404841019311098390641 := by
  unfold tailWord_561348
  simp only [CollatzResearch.WordTrace]
  refine ⟨10237021785169770725430349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13649362380226360967240465 10237021785169770725430349)
  ·
    refine ⟨3838883169438664022036381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10237021785169770725430349 3838883169438664022036381)
    ·
      refine ⟨1439581188539499008263643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3838883169438664022036381 1439581188539499008263643)
      ·
        refine ⟨2159371782809248512395465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1439581188539499008263643 2159371782809248512395465)
        ·
          refine ⟨1619528837106936384296599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2159371782809248512395465 1619528837106936384296599)
          ·
            refine ⟨2429293255660404576444899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1619528837106936384296599 2429293255660404576444899)
            ·
              refine ⟨3643939883490606864667349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2429293255660404576444899 3643939883490606864667349)
              ·
                refine ⟨85404841019311098390641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3643939883490606864667349 85404841019311098390641)
                ·
                  rfl

theorem cell20_561348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 7].length) (baseStart_561348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561348 prefixEnd_561348 := by exact prefixLift 561348
  have htrace : WordTrace (prefixWord ++ tailWord_561348) baseStart_561348 baseEnd_561348 := by
    simpa [prefixWord, tailWord_561348, baseEnd_561348] using wordTrace_append hprefix tailTrace_561348
  have hstable : (prefixWord ++ tailWord_561348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561348).length < 2 ^ (prefixWord ++ tailWord_561348).sum := by decide
  have hdescent : baseEnd_561348 < baseStart_561348 := by decide
  rcases family_descends (prefixWord ++ tailWord_561348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561355 : List Nat := [1, 1, 1, 1, 3, 2, 5, 3, 3]
def baseStart_561355 : Nat := 118140960795 + 561355 * 2 ^ 59
def prefixEnd_561355 : Nat := 4983230072969 + 3 ^ 40 * 561355 * 2
def baseEnd_561355 : Nat := 256217718048672381938561

theorem tailTrace_561355 : CollatzResearch.WordTrace tailWord_561355 prefixEnd_561355 256217718048672381938561 := by
  unfold tailWord_561355
  simp only [CollatzResearch.WordTrace]
  refine ⟨20474298881314181646365519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13649532587542787764243679 20474298881314181646365519)
  ·
    refine ⟨30711448321971272469548279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20474298881314181646365519 30711448321971272469548279)
    ·
      refine ⟨46067172482956908704322419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30711448321971272469548279 46067172482956908704322419)
      ·
        refine ⟨69100758724435363056483629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46067172482956908704322419 69100758724435363056483629)
        ·
          refine ⟨25912784521663261146181361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69100758724435363056483629 25912784521663261146181361)
          ·
            refine ⟨19434588391247445859636021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25912784521663261146181361 19434588391247445859636021)
            ·
              refine ⟨1821992661679448049340877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19434588391247445859636021 1821992661679448049340877)
              ·
                refine ⟨683247248129793018502829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1821992661679448049340877 683247248129793018502829)
                ·
                  refine ⟨256217718048672381938561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 683247248129793018502829 256217718048672381938561)
                  ·
                    rfl

theorem cell20_561355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 3].length) (baseStart_561355 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561355 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561355 prefixEnd_561355 := by exact prefixLift 561355
  have htrace : WordTrace (prefixWord ++ tailWord_561355) baseStart_561355 baseEnd_561355 := by
    simpa [prefixWord, tailWord_561355, baseEnd_561355] using wordTrace_append hprefix tailTrace_561355
  have hstable : (prefixWord ++ tailWord_561355).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561355).length < 2 ^ (prefixWord ++ tailWord_561355).sum := by decide
  have hdescent : baseEnd_561355 < baseStart_561355 := by decide
  rcases family_descends (prefixWord ++ tailWord_561355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561369 : List Nat := [1, 2, 1, 2, 3, 1, 4, 6]
def baseStart_561369 : Nat := 118140960795 + 561369 * 2 ^ 59
def prefixEnd_561369 : Nat := 4983230072969 + 3 ^ 40 * 561369 * 2
def baseEnd_561369 : Nat := 85408036010050185157279

theorem tailTrace_561369 : CollatzResearch.WordTrace tailWord_561369 prefixEnd_561369 85408036010050185157279 := by
  unfold tailWord_561369
  simp only [CollatzResearch.WordTrace]
  refine ⟨20474809503263462037375161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13649873002175641358250107 20474809503263462037375161)
  ·
    refine ⟨15356107127447596528031371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20474809503263462037375161 15356107127447596528031371)
    ·
      refine ⟨23034160691171394792047057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15356107127447596528031371 23034160691171394792047057)
      ·
        refine ⟨17275620518378546094035293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23034160691171394792047057 17275620518378546094035293)
        ·
          refine ⟨6478357694391954785263235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17275620518378546094035293 6478357694391954785263235)
          ·
            refine ⟨9717536541587932177894853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6478357694391954785263235 9717536541587932177894853)
            ·
              refine ⟨1822038101547737283355285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9717536541587932177894853 1822038101547737283355285)
              ·
                refine ⟨85408036010050185157279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1822038101547737283355285 85408036010050185157279)
                ·
                  rfl

theorem cell20_561369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 6].length) (baseStart_561369 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561369 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561369 prefixEnd_561369 := by exact prefixLift 561369
  have htrace : WordTrace (prefixWord ++ tailWord_561369) baseStart_561369 baseEnd_561369 := by
    simpa [prefixWord, tailWord_561369, baseEnd_561369] using wordTrace_append hprefix tailTrace_561369
  have hstable : (prefixWord ++ tailWord_561369).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561369).length < 2 ^ (prefixWord ++ tailWord_561369).sum := by decide
  have hdescent : baseEnd_561369 < baseStart_561369 := by decide
  rcases family_descends (prefixWord ++ tailWord_561369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561389 : List Nat := [1, 5, 1, 2, 3, 1, 2, 2, 3]
def baseStart_561389 : Nat := 118140960795 + 561389 * 2 ^ 59
def prefixEnd_561389 : Nat := 4983230072969 + 3 ^ 40 * 561389 * 2
def baseEnd_561389 : Nat := 256233236575119374805089

theorem tailTrace_561389 : CollatzResearch.WordTrace tailWord_561389 prefixEnd_561389 256233236575119374805089 := by
  unfold tailWord_561389
  simp only [CollatzResearch.WordTrace]
  refine ⟨20475538963191005453103221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13650359308794003635402147 20475538963191005453103221)
  ·
    refine ⟨1919581777799156761228427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20475538963191005453103221 1919581777799156761228427)
    ·
      refine ⟨2879372666698735141842641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1919581777799156761228427 2879372666698735141842641)
      ·
        refine ⟨2159529500024051356381981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2879372666698735141842641 2159529500024051356381981)
        ·
          refine ⟨809823562509019258643243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2159529500024051356381981 809823562509019258643243)
          ·
            refine ⟨1214735343763528887964865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 809823562509019258643243 1214735343763528887964865)
            ·
              refine ⟨911051507822646665973649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1214735343763528887964865 911051507822646665973649)
              ·
                refine ⟨683288630866984999480237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 911051507822646665973649 683288630866984999480237)
                ·
                  refine ⟨256233236575119374805089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 683288630866984999480237 256233236575119374805089)
                  ·
                    rfl

theorem cell20_561389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_561389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561389 prefixEnd_561389 := by exact prefixLift 561389
  have htrace : WordTrace (prefixWord ++ tailWord_561389) baseStart_561389 baseEnd_561389 := by
    simpa [prefixWord, tailWord_561389, baseEnd_561389] using wordTrace_append hprefix tailTrace_561389
  have hstable : (prefixWord ++ tailWord_561389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561389).length < 2 ^ (prefixWord ++ tailWord_561389).sum := by decide
  have hdescent : baseEnd_561389 < baseStart_561389 := by decide
  rcases family_descends (prefixWord ++ tailWord_561389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561393 : List Nat := [1, 2, 2, 2, 2, 1, 3, 4, 3]
def baseStart_561393 : Nat := 118140960795 + 561393 * 2 ^ 59
def prefixEnd_561393 : Nat := 4983230072969 + 3 ^ 40 * 561393 * 2
def baseEnd_561393 : Nat := 256235062284113138671739

theorem tailTrace_561393 : CollatzResearch.WordTrace tailWord_561393 prefixEnd_561393 256235062284113138671739 := by
  unfold tailWord_561393
  simp only [CollatzResearch.WordTrace]
  refine ⟨20475684855176514136248833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13650456570117676090832555 20475684855176514136248833)
  ·
    refine ⟨15356763641382385602186625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20475684855176514136248833 15356763641382385602186625)
    ·
      refine ⟨11517572731036789201639969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15356763641382385602186625 11517572731036789201639969)
      ·
        refine ⟨8638179548277591901229977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11517572731036789201639969 8638179548277591901229977)
        ·
          refine ⟨6478634661208193925922483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8638179548277591901229977 6478634661208193925922483)
          ·
            refine ⟨9717951991812290888883725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6478634661208193925922483 9717951991812290888883725)
            ·
              refine ⟨3644231996929609083331397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9717951991812290888883725 3644231996929609083331397)
              ·
                refine ⟨683293499424301703124637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3644231996929609083331397 683293499424301703124637)
                ·
                  refine ⟨256235062284113138671739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 683293499424301703124637 256235062284113138671739)
                  ·
                    rfl

theorem cell20_561393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 3].length) (baseStart_561393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561393 prefixEnd_561393 := by exact prefixLift 561393
  have htrace : WordTrace (prefixWord ++ tailWord_561393) baseStart_561393 baseEnd_561393 := by
    simpa [prefixWord, tailWord_561393, baseEnd_561393] using wordTrace_append hprefix tailTrace_561393
  have hstable : (prefixWord ++ tailWord_561393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561393).length < 2 ^ (prefixWord ++ tailWord_561393).sum := by decide
  have hdescent : baseEnd_561393 < baseStart_561393 := by decide
  rcases family_descends (prefixWord ++ tailWord_561393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561448 : List Nat := [2, 1, 5, 1, 3, 1, 1, 1, 5]
def baseStart_561448 : Nat := 118140960795 + 561448 * 2 ^ 59
def prefixEnd_561448 : Nat := 4983230072969 + 3 ^ 40 * 561448 * 2
def baseEnd_561448 : Nat := 256260165782777391838181

theorem tailTrace_561448 : CollatzResearch.WordTrace tailWord_561448 prefixEnd_561448 256260165782777391838181 := by
  unfold tailWord_561448
  simp only [CollatzResearch.WordTrace]
  refine ⟨10238845434988629264750499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13651793913318172353000665 10238845434988629264750499)
  ·
    refine ⟨15358268152482943897125749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10238845434988629264750499 15358268152482943897125749)
    ·
      refine ⟨1439837639295275990355539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15358268152482943897125749 1439837639295275990355539)
      ·
        refine ⟨2159756458942913985533309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1439837639295275990355539 2159756458942913985533309)
        ·
          refine ⟨809908672103592744574991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2159756458942913985533309 809908672103592744574991)
          ·
            refine ⟨1214863008155389116862487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 809908672103592744574991 1214863008155389116862487)
            ·
              refine ⟨1822294512233083675293731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1214863008155389116862487 1822294512233083675293731)
              ·
                refine ⟨2733441768349625512940597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1822294512233083675293731 2733441768349625512940597)
                ·
                  refine ⟨256260165782777391838181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2733441768349625512940597 256260165782777391838181)
                  ·
                    rfl

theorem cell20_561448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 5].length) (baseStart_561448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561448 prefixEnd_561448 := by exact prefixLift 561448
  have htrace : WordTrace (prefixWord ++ tailWord_561448) baseStart_561448 baseEnd_561448 := by
    simpa [prefixWord, tailWord_561448, baseEnd_561448] using wordTrace_append hprefix tailTrace_561448
  have hstable : (prefixWord ++ tailWord_561448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561448).length < 2 ^ (prefixWord ++ tailWord_561448).sum := by decide
  have hdescent : baseEnd_561448 < baseStart_561448 := by decide
  rcases family_descends (prefixWord ++ tailWord_561448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561455 : List Nat := [1, 1, 2, 1, 2, 1, 6, 4, 2]
def baseStart_561455 : Nat := 118140960795 + 561455 * 2 ^ 59
def prefixEnd_561455 : Nat := 4983230072969 + 3 ^ 40 * 561455 * 2
def baseEnd_561455 : Nat := 256263360773516478604819

theorem tailTrace_561455 : CollatzResearch.WordTrace tailWord_561455 prefixEnd_561455 256263360773516478604819 := by
  unfold tailWord_561455
  simp only [CollatzResearch.WordTrace]
  refine ⟨20477946180951898725005819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13651964120634599150003879 20477946180951898725005819)
  ·
    refine ⟨30716919271427848087508729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20477946180951898725005819 30716919271427848087508729)
    ·
      refine ⟨23037689453570886065631547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30716919271427848087508729 23037689453570886065631547)
      ·
        refine ⟨34556534180356329098447321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23037689453570886065631547 34556534180356329098447321)
        ·
          refine ⟨25917400635267246823835491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34556534180356329098447321 25917400635267246823835491)
          ·
            refine ⟨38876100952900870235753237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25917400635267246823835491 38876100952900870235753237)
            ·
              refine ⟨1822317232167228292300933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38876100952900870235753237 1822317232167228292300933)
              ·
                refine ⟨341684481031355304806425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1822317232167228292300933 341684481031355304806425)
                ·
                  refine ⟨256263360773516478604819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 341684481031355304806425 256263360773516478604819)
                  ·
                    rfl

theorem cell20_561455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 4, 2].length) (baseStart_561455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561455 prefixEnd_561455 := by exact prefixLift 561455
  have htrace : WordTrace (prefixWord ++ tailWord_561455) baseStart_561455 baseEnd_561455 := by
    simpa [prefixWord, tailWord_561455, baseEnd_561455] using wordTrace_append hprefix tailTrace_561455
  have hstable : (prefixWord ++ tailWord_561455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561455).length < 2 ^ (prefixWord ++ tailWord_561455).sum := by decide
  have hdescent : baseEnd_561455 < baseStart_561455 := by decide
  rcases family_descends (prefixWord ++ tailWord_561455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561465 : List Nat := [1, 2, 1, 6, 1, 2, 3, 1, 3]
def baseStart_561465 : Nat := 118140960795 + 561465 * 2 ^ 59
def prefixEnd_561465 : Nat := 4983230072969 + 3 ^ 40 * 561465 * 2
def baseEnd_561465 : Nat := 256267925046000888271445

theorem tailTrace_561465 : CollatzResearch.WordTrace tailWord_561465 prefixEnd_561465 256267925046000888271445 := by
  unfold tailWord_561465
  simp only [CollatzResearch.WordTrace]
  refine ⟨20478310910915670432869849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13652207273943780288579899 20478310910915670432869849)
  ·
    refine ⟨15358733183186752824652387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20478310910915670432869849 15358733183186752824652387)
    ·
      refine ⟨23038099774780129236978581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15358733183186752824652387 23038099774780129236978581)
      ·
        refine ⟨1079910926942818557983371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 23038099774780129236978581 1079910926942818557983371)
        ·
          refine ⟨1619866390414227836975057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1079910926942818557983371 1619866390414227836975057)
          ·
            refine ⟨1214899792810670877731293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1619866390414227836975057 1214899792810670877731293)
            ·
              refine ⟨455587422304001579149235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1214899792810670877731293 455587422304001579149235)
              ·
                refine ⟨683381133456002368723853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 455587422304001579149235 683381133456002368723853)
                ·
                  refine ⟨256267925046000888271445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 683381133456002368723853 256267925046000888271445)
                  ·
                    rfl

theorem cell20_561465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 3].length) (baseStart_561465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561465 prefixEnd_561465 := by exact prefixLift 561465
  have htrace : WordTrace (prefixWord ++ tailWord_561465) baseStart_561465 baseEnd_561465 := by
    simpa [prefixWord, tailWord_561465, baseEnd_561465] using wordTrace_append hprefix tailTrace_561465
  have hstable : (prefixWord ++ tailWord_561465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561465).length < 2 ^ (prefixWord ++ tailWord_561465).sum := by decide
  have hdescent : baseEnd_561465 < baseStart_561465 := by decide
  rcases family_descends (prefixWord ++ tailWord_561465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561502 : List Nat := [4, 4, 2, 1, 2, 1, 1, 1, 4]
def baseStart_561502 : Nat := 118140960795 + 561502 * 2 ^ 59
def prefixEnd_561502 : Nat := 4983230072969 + 3 ^ 40 * 561502 * 2
def baseEnd_561502 : Nat := 256284812854193204037961

theorem tailTrace_561502 : CollatzResearch.WordTrace tailWord_561502 prefixEnd_561502 256284812854193204037961 := by
  unfold tailWord_561502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2559957551472703218995845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13653106941187750501311173 2559957551472703218995845)
  ·
    refine ⟨479992040901131853561721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2559957551472703218995845 479992040901131853561721)
    ·
      refine ⟨359994030675848890171291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 479992040901131853561721 359994030675848890171291)
      ·
        refine ⟨539991046013773335256937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359994030675848890171291 539991046013773335256937)
        ·
          refine ⟨404993284510330001442703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 539991046013773335256937 404993284510330001442703)
          ·
            refine ⟨607489926765495002164055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404993284510330001442703 607489926765495002164055)
            ·
              refine ⟨911234890148242503246083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 607489926765495002164055 911234890148242503246083)
              ·
                refine ⟨1366852335222363754869125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 911234890148242503246083 1366852335222363754869125)
                ·
                  refine ⟨256284812854193204037961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1366852335222363754869125 256284812854193204037961)
                  ·
                    rfl

theorem cell20_561502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_561502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561502 prefixEnd_561502 := by exact prefixLift 561502
  have htrace : WordTrace (prefixWord ++ tailWord_561502) baseStart_561502 baseEnd_561502 := by
    simpa [prefixWord, tailWord_561502, baseEnd_561502] using wordTrace_append hprefix tailTrace_561502
  have hstable : (prefixWord ++ tailWord_561502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561502).length < 2 ^ (prefixWord ++ tailWord_561502).sum := by decide
  have hdescent : baseEnd_561502 < baseStart_561502 := by decide
  rcases family_descends (prefixWord ++ tailWord_561502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561507 : List Nat := [1, 1, 1, 5, 2, 1, 2, 4, 3]
def baseStart_561507 : Nat := 118140960795 + 561507 * 2 ^ 59
def prefixEnd_561507 : Nat := 4983230072969 + 3 ^ 40 * 561507 * 2
def baseEnd_561507 : Nat := 256287094990435408871273

theorem tailTrace_561507 : CollatzResearch.WordTrace tailWord_561507 prefixEnd_561507 256287094990435408871273 := by
  unfold tailWord_561507
  simp only [CollatzResearch.WordTrace]
  refine ⟨20479842776763511605898775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13653228517842341070599183 20479842776763511605898775)
  ·
    refine ⟨30719764165145267408848163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20479842776763511605898775 30719764165145267408848163)
    ·
      refine ⟨46079646247717901113272245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30719764165145267408848163 46079646247717901113272245)
      ·
        refine ⟨4319966835723553229369273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46079646247717901113272245 4319966835723553229369273)
        ·
          refine ⟨3239975126792664922026955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4319966835723553229369273 3239975126792664922026955)
          ·
            refine ⟨4859962690188997383040433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3239975126792664922026955 4859962690188997383040433)
            ·
              refine ⟨3644972017641748037280325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4859962690188997383040433 3644972017641748037280325)
              ·
                refine ⟨683432253307827756990061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3644972017641748037280325 683432253307827756990061)
                ·
                  refine ⟨256287094990435408871273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 683432253307827756990061 256287094990435408871273)
                  ·
                    rfl

theorem cell20_561507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 3].length) (baseStart_561507 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561507 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561507 prefixEnd_561507 := by exact prefixLift 561507
  have htrace : WordTrace (prefixWord ++ tailWord_561507) baseStart_561507 baseEnd_561507 := by
    simpa [prefixWord, tailWord_561507, baseEnd_561507] using wordTrace_append hprefix tailTrace_561507
  have hstable : (prefixWord ++ tailWord_561507).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561507).length < 2 ^ (prefixWord ++ tailWord_561507).sum := by decide
  have hdescent : baseEnd_561507 < baseStart_561507 := by decide
  rcases family_descends (prefixWord ++ tailWord_561507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561562 : List Nat := [3, 1, 1, 4, 1, 3, 2, 2, 3]
def baseStart_561562 : Nat := 118140960795 + 561562 * 2 ^ 59
def prefixEnd_561562 : Nat := 4983230072969 + 3 ^ 40 * 561562 * 2
def baseEnd_561562 : Nat := 256312198489099662037715

theorem tailTrace_561562 : CollatzResearch.WordTrace tailWord_561562 prefixEnd_561562 256312198489099662037715 := by
  unfold tailWord_561562
  simp only [CollatzResearch.WordTrace]
  refine ⟨5120462197891063999787735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13654565861042837332767293 5120462197891063999787735)
  ·
    refine ⟨7680693296836595999681603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5120462197891063999787735 7680693296836595999681603)
    ·
      refine ⟨11521039945254893999522405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7680693296836595999681603 11521039945254893999522405)
      ·
        refine ⟨2160194989735292624910451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11521039945254893999522405 2160194989735292624910451)
        ·
          refine ⟨3240292484602938937365677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2160194989735292624910451 3240292484602938937365677)
          ·
            refine ⟨1215109681726102101512129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3240292484602938937365677 1215109681726102101512129)
            ·
              refine ⟨911332261294576576134097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1215109681726102101512129 911332261294576576134097)
              ·
                refine ⟨683499195970932432100573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 911332261294576576134097 683499195970932432100573)
                ·
                  refine ⟨256312198489099662037715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 683499195970932432100573 256312198489099662037715)
                  ·
                    rfl

theorem cell20_561562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_561562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561562 prefixEnd_561562 := by exact prefixLift 561562
  have htrace : WordTrace (prefixWord ++ tailWord_561562) baseStart_561562 baseEnd_561562 := by
    simpa [prefixWord, tailWord_561562, baseEnd_561562] using wordTrace_append hprefix tailTrace_561562
  have hstable : (prefixWord ++ tailWord_561562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561562).length < 2 ^ (prefixWord ++ tailWord_561562).sum := by decide
  have hdescent : baseEnd_561562 < baseStart_561562 := by decide
  rcases family_descends (prefixWord ++ tailWord_561562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561607 : List Nat := [1, 1, 4, 1, 1, 4, 1, 5, 2]
def baseStart_561607 : Nat := 118140960795 + 561607 * 2 ^ 59
def prefixEnd_561607 : Nat := 4983230072969 + 3 ^ 40 * 561607 * 2
def baseEnd_561607 : Nat := 256332737715279505537531

theorem tailTrace_561607 : CollatzResearch.WordTrace tailWord_561607 prefixEnd_561607 256332737715279505537531 := by
  unfold tailWord_561607
  simp only [CollatzResearch.WordTrace]
  refine ⟨20483490076401228684539075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13655660050934152456359383 20483490076401228684539075)
  ·
    refine ⟨30725235114601843026808613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20483490076401228684539075 30725235114601843026808613)
    ·
      refine ⟨5760981583987845567526615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30725235114601843026808613 5760981583987845567526615)
      ·
        refine ⟨8641472375981768351289923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5760981583987845567526615 8641472375981768351289923)
        ·
          refine ⟨12962208563972652526934885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8641472375981768351289923 12962208563972652526934885)
          ·
            refine ⟨2430414105744872348800291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12962208563972652526934885 2430414105744872348800291)
            ·
              refine ⟨3645621158617308523200437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2430414105744872348800291 3645621158617308523200437)
              ·
                refine ⟨341776983620372674050041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3645621158617308523200437 341776983620372674050041)
                ·
                  refine ⟨256332737715279505537531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 341776983620372674050041 256332737715279505537531)
                  ·
                    rfl

theorem cell20_561607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 5, 2].length) (baseStart_561607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561607 prefixEnd_561607 := by exact prefixLift 561607
  have htrace : WordTrace (prefixWord ++ tailWord_561607) baseStart_561607 baseEnd_561607 := by
    simpa [prefixWord, tailWord_561607, baseEnd_561607] using wordTrace_append hprefix tailTrace_561607
  have hstable : (prefixWord ++ tailWord_561607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561607).length < 2 ^ (prefixWord ++ tailWord_561607).sum := by decide
  have hdescent : baseEnd_561607 < baseStart_561607 := by decide
  rcases family_descends (prefixWord ++ tailWord_561607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561611 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 8]
def baseStart_561611 : Nat := 118140960795 + 561611 * 2 ^ 59
def prefixEnd_561611 : Nat := 4983230072969 + 3 ^ 40 * 561611 * 2
def baseEnd_561611 : Nat := 256334563424273269404181

theorem tailTrace_561611 : CollatzResearch.WordTrace tailWord_561611 prefixEnd_561611 256334563424273269404181 := by
  unfold tailWord_561611
  simp only [CollatzResearch.WordTrace]
  refine ⟨20483635968386737367684687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13655757312257824911789791 20483635968386737367684687)
  ·
    refine ⟨30725453952580106051527031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20483635968386737367684687 30725453952580106051527031)
    ·
      refine ⟨46088180928870159077290547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30725453952580106051527031 46088180928870159077290547)
      ·
        refine ⟨69132271393305238615935821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46088180928870159077290547 69132271393305238615935821)
        ·
          refine ⟨25924601772489464480975933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69132271393305238615935821 25924601772489464480975933)
          ·
            refine ⟨9721725664683549180365975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25924601772489464480975933 9721725664683549180365975)
            ·
              refine ⟨14582588497025323770548963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9721725664683549180365975 14582588497025323770548963)
              ·
                refine ⟨21873882745537985655823445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14582588497025323770548963 21873882745537985655823445)
                ·
                  refine ⟨256334563424273269404181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21873882745537985655823445 256334563424273269404181)
                  ·
                    rfl

theorem cell20_561611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 8].length) (baseStart_561611 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561611 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561611 prefixEnd_561611 := by exact prefixLift 561611
  have htrace : WordTrace (prefixWord ++ tailWord_561611) baseStart_561611 baseEnd_561611 := by
    simpa [prefixWord, tailWord_561611, baseEnd_561611] using wordTrace_append hprefix tailTrace_561611
  have hstable : (prefixWord ++ tailWord_561611).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561611).length < 2 ^ (prefixWord ++ tailWord_561611).sum := by decide
  have hdescent : baseEnd_561611 < baseStart_561611 := by decide
  rcases family_descends (prefixWord ++ tailWord_561611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561621 : List Nat := [1, 3, 2, 3, 1, 3, 1, 1, 5]
def baseStart_561621 : Nat := 118140960795 + 561621 * 2 ^ 59
def prefixEnd_561621 : Nat := 4983230072969 + 3 ^ 40 * 561621 * 2
def baseEnd_561621 : Nat := 256339127696757679070807

theorem tailTrace_561621 : CollatzResearch.WordTrace tailWord_561621 prefixEnd_561621 256339127696757679070807 := by
  unfold tailWord_561621
  simp only [CollatzResearch.WordTrace]
  refine ⟨20484000698350509075548717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13656000465567006050365811 20484000698350509075548717)
  ·
    refine ⟨7681500261881440903330769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20484000698350509075548717 7681500261881440903330769)
    ·
      refine ⟨5761125196411080677498077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7681500261881440903330769 5761125196411080677498077)
      ·
        refine ⟨2160421948654155254061779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5761125196411080677498077 2160421948654155254061779)
        ·
          refine ⟨3240632922981232881092669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2160421948654155254061779 3240632922981232881092669)
          ·
            refine ⟨1215237346117962330409751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3240632922981232881092669 1215237346117962330409751)
            ·
              refine ⟨1822856019176943495614627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1215237346117962330409751 1822856019176943495614627)
              ·
                refine ⟨2734284028765415243421941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1822856019176943495614627 2734284028765415243421941)
                ·
                  refine ⟨256339127696757679070807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2734284028765415243421941 256339127696757679070807)
                  ·
                    rfl

theorem cell20_561621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_561621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561621 prefixEnd_561621 := by exact prefixLift 561621
  have htrace : WordTrace (prefixWord ++ tailWord_561621) baseStart_561621 baseEnd_561621 := by
    simpa [prefixWord, tailWord_561621, baseEnd_561621] using wordTrace_append hprefix tailTrace_561621
  have hstable : (prefixWord ++ tailWord_561621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561621).length < 2 ^ (prefixWord ++ tailWord_561621).sum := by decide
  have hdescent : baseEnd_561621 < baseStart_561621 := by decide
  rcases family_descends (prefixWord ++ tailWord_561621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561645 : List Nat := [1, 5, 1, 3, 1, 1, 2, 2, 4]
def baseStart_561645 : Nat := 118140960795 + 561645 * 2 ^ 59
def prefixEnd_561645 : Nat := 4983230072969 + 3 ^ 40 * 561645 * 2
def baseEnd_561645 : Nat := 256350081950720262270709

theorem tailTrace_561645 : CollatzResearch.WordTrace tailWord_561645 prefixEnd_561645 256350081950720262270709 := by
  unfold tailWord_561645
  simp only [CollatzResearch.WordTrace]
  refine ⟨20484876050263561174422389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13656584033509040782948259 20484876050263561174422389)
  ·
    refine ⟨1920457129712208860102099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20484876050263561174422389 1920457129712208860102099)
    ·
      refine ⟨2880685694568313290153149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1920457129712208860102099 2880685694568313290153149)
      ·
        refine ⟨1080257135463117483807431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2880685694568313290153149 1080257135463117483807431)
        ·
          refine ⟨1620385703194676225711147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1080257135463117483807431 1620385703194676225711147)
          ·
            refine ⟨2430578554792014338566721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1620385703194676225711147 2430578554792014338566721)
            ·
              refine ⟨1822933916094010753925041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2430578554792014338566721 1822933916094010753925041)
              ·
                refine ⟨1367200437070508065443781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1822933916094010753925041 1367200437070508065443781)
                ·
                  refine ⟨256350081950720262270709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1367200437070508065443781 256350081950720262270709)
                  ·
                    rfl

theorem cell20_561645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_561645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561645 prefixEnd_561645 := by exact prefixLift 561645
  have htrace : WordTrace (prefixWord ++ tailWord_561645) baseStart_561645 baseEnd_561645 := by
    simpa [prefixWord, tailWord_561645, baseEnd_561645] using wordTrace_append hprefix tailTrace_561645
  have hstable : (prefixWord ++ tailWord_561645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561645).length < 2 ^ (prefixWord ++ tailWord_561645).sum := by decide
  have hdescent : baseEnd_561645 < baseStart_561645 := by decide
  rcases family_descends (prefixWord ++ tailWord_561645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561693 : List Nat := [1, 4, 2, 2, 1, 4, 2, 1, 3]
def baseStart_561693 : Nat := 118140960795 + 561693 * 2 ^ 59
def prefixEnd_561693 : Nat := 4983230072969 + 3 ^ 40 * 561693 * 2
def baseEnd_561693 : Nat := 256371990458645428670513

theorem tailTrace_561693 : CollatzResearch.WordTrace tailWord_561693 prefixEnd_561693 256371990458645428670513 := by
  unfold tailWord_561693
  simp only [CollatzResearch.WordTrace]
  refine ⟨20486626754089665372169733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13657751169393110248113155 20486626754089665372169733)
  ·
    refine ⟨3841242516391812257281825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20486626754089665372169733 3841242516391812257281825)
    ·
      refine ⟨2880931887293859192961369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3841242516391812257281825 2880931887293859192961369)
      ·
        refine ⟨2160698915470394394721027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2880931887293859192961369 2160698915470394394721027)
        ·
          refine ⟨3241048373205591592081541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2160698915470394394721027 3241048373205591592081541)
          ·
            refine ⟨607696569976048423515289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3241048373205591592081541 607696569976048423515289)
            ·
              refine ⟨455772427482036317636467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 607696569976048423515289 455772427482036317636467)
              ·
                refine ⟨683658641223054476454701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 455772427482036317636467 683658641223054476454701)
                ·
                  refine ⟨256371990458645428670513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 683658641223054476454701 256371990458645428670513)
                  ·
                    rfl

theorem cell20_561693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_561693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561693 prefixEnd_561693 := by exact prefixLift 561693
  have htrace : WordTrace (prefixWord ++ tailWord_561693) baseStart_561693 baseEnd_561693 := by
    simpa [prefixWord, tailWord_561693, baseEnd_561693] using wordTrace_append hprefix tailTrace_561693
  have hstable : (prefixWord ++ tailWord_561693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561693).length < 2 ^ (prefixWord ++ tailWord_561693).sum := by decide
  have hdescent : baseEnd_561693 < baseStart_561693 := by decide
  rcases family_descends (prefixWord ++ tailWord_561693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561697 : List Nat := [1, 2, 3, 2, 2, 1, 3, 3, 3]
def baseStart_561697 : Nat := 118140960795 + 561697 * 2 ^ 59
def prefixEnd_561697 : Nat := 4983230072969 + 3 ^ 40 * 561697 * 2
def baseEnd_561697 : Nat := 256373816167639192537163

theorem tailTrace_561697 : CollatzResearch.WordTrace tailWord_561697 prefixEnd_561697 256373816167639192537163 := by
  unfold tailWord_561697
  simp only [CollatzResearch.WordTrace]
  refine ⟨20486772646075174055315345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13657848430716782703543563 20486772646075174055315345)
  ·
    refine ⟨15365079484556380541486509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20486772646075174055315345 15365079484556380541486509)
    ·
      refine ⟨5761904806708642703057441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15365079484556380541486509 5761904806708642703057441)
      ·
        refine ⟨4321428605031482027293081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5761904806708642703057441 4321428605031482027293081)
        ·
          refine ⟨3241071453773611520469811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4321428605031482027293081 3241071453773611520469811)
          ·
            refine ⟨4861607180660417280704717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3241071453773611520469811 4861607180660417280704717)
            ·
              refine ⟨1823102692747656480264269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4861607180660417280704717 1823102692747656480264269)
              ·
                refine ⟨683663509780371180099101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1823102692747656480264269 683663509780371180099101)
                ·
                  refine ⟨256373816167639192537163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 683663509780371180099101 256373816167639192537163)
                  ·
                    rfl

theorem cell20_561697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 3].length) (baseStart_561697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561697 prefixEnd_561697 := by exact prefixLift 561697
  have htrace : WordTrace (prefixWord ++ tailWord_561697) baseStart_561697 baseEnd_561697 := by
    simpa [prefixWord, tailWord_561697, baseEnd_561697] using wordTrace_append hprefix tailTrace_561697
  have hstable : (prefixWord ++ tailWord_561697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561697).length < 2 ^ (prefixWord ++ tailWord_561697).sum := by decide
  have hdescent : baseEnd_561697 < baseStart_561697 := by decide
  rcases family_descends (prefixWord ++ tailWord_561697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561721 : List Nat := [1, 2, 1, 5, 1, 1, 2, 5, 2]
def baseStart_561721 : Nat := 118140960795 + 561721 * 2 ^ 59
def prefixEnd_561721 : Nat := 4983230072969 + 3 ^ 40 * 561721 * 2
def baseEnd_561721 : Nat := 256384770421601775737065

theorem tailTrace_561721 : CollatzResearch.WordTrace tailWord_561721 prefixEnd_561721 256384770421601775737065 := by
  unfold tailWord_561721
  simp only [CollatzResearch.WordTrace]
  refine ⟨20487647997988226154189017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13658431998658817436126011 20487647997988226154189017)
  ·
    refine ⟨15365735998491169615641763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20487647997988226154189017 15365735998491169615641763)
    ·
      refine ⟨23048603997736754423462645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15365735998491169615641763 23048603997736754423462645)
      ·
        refine ⟨2160806624787820727199623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23048603997736754423462645 2160806624787820727199623)
        ·
          refine ⟨3241209937181731090799435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2160806624787820727199623 3241209937181731090799435)
          ·
            refine ⟨4861814905772596636199153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3241209937181731090799435 4861814905772596636199153)
            ·
              refine ⟨3646361179329447477149365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4861814905772596636199153 3646361179329447477149365)
              ·
                refine ⟨341846360562135700982753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3646361179329447477149365 341846360562135700982753)
                ·
                  refine ⟨256384770421601775737065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 341846360562135700982753 256384770421601775737065)
                  ·
                    rfl

theorem cell20_561721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 5, 2].length) (baseStart_561721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561721 prefixEnd_561721 := by exact prefixLift 561721
  have htrace : WordTrace (prefixWord ++ tailWord_561721) baseStart_561721 baseEnd_561721 := by
    simpa [prefixWord, tailWord_561721, baseEnd_561721] using wordTrace_append hprefix tailTrace_561721
  have hstable : (prefixWord ++ tailWord_561721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561721).length < 2 ^ (prefixWord ++ tailWord_561721).sum := by decide
  have hdescent : baseEnd_561721 < baseStart_561721 := by decide
  rcases family_descends (prefixWord ++ tailWord_561721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561734 : List Nat := [6, 1, 1, 1, 2, 1, 4, 2, 2]
def baseStart_561734 : Nat := 118140960795 + 561734 * 2 ^ 59
def prefixEnd_561734 : Nat := 4983230072969 + 3 ^ 40 * 561734 * 2
def baseEnd_561734 : Nat := 256390703975831508303679

theorem tailTrace_561734 : CollatzResearch.WordTrace tailWord_561734 prefixEnd_561734 256390703975831508303679 := by
  unfold tailWord_561734
  simp only [CollatzResearch.WordTrace]
  refine ⟨640253817091910292950383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13658748097960752916274837 640253817091910292950383)
  ·
    refine ⟨960380725637865439425575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 640253817091910292950383 960380725637865439425575)
    ·
      refine ⟨1440571088456798159138363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 960380725637865439425575 1440571088456798159138363)
      ·
        refine ⟨2160856632685197238707545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1440571088456798159138363 2160856632685197238707545)
        ·
          refine ⟨1620642474513897929030659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2160856632685197238707545 1620642474513897929030659)
          ·
            refine ⟨2430963711770846893545989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1620642474513897929030659 2430963711770846893545989)
            ·
              refine ⟨455805695957033792539873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2430963711770846893545989 455805695957033792539873)
              ·
                refine ⟨341854271967775344404905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 455805695957033792539873 341854271967775344404905)
                ·
                  refine ⟨256390703975831508303679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 341854271967775344404905 256390703975831508303679)
                  ·
                    rfl

theorem cell20_561734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_561734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561734 prefixEnd_561734 := by exact prefixLift 561734
  have htrace : WordTrace (prefixWord ++ tailWord_561734) baseStart_561734 baseEnd_561734 := by
    simpa [prefixWord, tailWord_561734, baseEnd_561734] using wordTrace_append hprefix tailTrace_561734
  have hstable : (prefixWord ++ tailWord_561734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561734).length < 2 ^ (prefixWord ++ tailWord_561734).sum := by decide
  have hdescent : baseEnd_561734 < baseStart_561734 := by decide
  rcases family_descends (prefixWord ++ tailWord_561734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561735 : List Nat := [1, 1, 4, 1, 4, 1, 1, 4, 3]
def baseStart_561735 : Nat := 118140960795 + 561735 * 2 ^ 59
def prefixEnd_561735 : Nat := 4983230072969 + 3 ^ 40 * 561735 * 2
def baseEnd_561735 : Nat := 256391160403079949270341

theorem tailTrace_561735 : CollatzResearch.WordTrace tailWord_561735 prefixEnd_561735 256391160403079949270341 := by
  unfold tailWord_561735
  simp only [CollatzResearch.WordTrace]
  refine ⟨20488158619937506545198659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13658772413291671030132439 20488158619937506545198659)
  ·
    refine ⟨30732237929906259817797989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20488158619937506545198659 30732237929906259817797989)
    ·
      refine ⟨5762294611857423715837123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30732237929906259817797989 5762294611857423715837123)
      ·
        refine ⟨8643441917786135573755685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5762294611857423715837123 8643441917786135573755685)
        ·
          refine ⟨1620645359584900420079191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8643441917786135573755685 1620645359584900420079191)
          ·
            refine ⟨2430968039377350630118787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1620645359584900420079191 2430968039377350630118787)
            ·
              refine ⟨3646452059066025945178181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2430968039377350630118787 3646452059066025945178181)
              ·
                refine ⟨683709761074879864720909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3646452059066025945178181 683709761074879864720909)
                ·
                  refine ⟨256391160403079949270341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 683709761074879864720909 256391160403079949270341)
                  ·
                    rfl

theorem cell20_561735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 3].length) (baseStart_561735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561735 prefixEnd_561735 := by exact prefixLift 561735
  have htrace : WordTrace (prefixWord ++ tailWord_561735) baseStart_561735 baseEnd_561735 := by
    simpa [prefixWord, tailWord_561735, baseEnd_561735] using wordTrace_append hprefix tailTrace_561735
  have hstable : (prefixWord ++ tailWord_561735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561735).length < 2 ^ (prefixWord ++ tailWord_561735).sum := by decide
  have hdescent : baseEnd_561735 < baseStart_561735 := by decide
  rcases family_descends (prefixWord ++ tailWord_561735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561738 : List Nat := [3, 1, 2, 1, 1, 4, 4, 2, 2]
def baseStart_561738 : Nat := 118140960795 + 561738 * 2 ^ 59
def prefixEnd_561738 : Nat := 4983230072969 + 3 ^ 40 * 561738 * 2
def baseEnd_561738 : Nat := 256392529684825272170329

theorem tailTrace_561738 : CollatzResearch.WordTrace tailWord_561738 prefixEnd_561738 256392529684825272170329 := by
  unfold tailWord_561738
  simp only [CollatzResearch.WordTrace]
  refine ⟨5122067009731659514389467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13658845359284425371705245 5122067009731659514389467)
  ·
    refine ⟨7683100514597489271584201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5122067009731659514389467 7683100514597489271584201)
    ·
      refine ⟨5762325385948116953688151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7683100514597489271584201 5762325385948116953688151)
      ·
        refine ⟨8643488078922175430532227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5762325385948116953688151 8643488078922175430532227)
        ·
          refine ⟨12965232118383263145798341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8643488078922175430532227 12965232118383263145798341)
          ·
            refine ⟨2430981022196861839837189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12965232118383263145798341 2430981022196861839837189)
            ·
              refine ⟨455808941661911594969473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2430981022196861839837189 455808941661911594969473)
              ·
                refine ⟨341856706246433696227105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 455808941661911594969473 341856706246433696227105)
                ·
                  refine ⟨256392529684825272170329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 341856706246433696227105 256392529684825272170329)
                  ·
                    rfl

theorem cell20_561738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 2, 2].length) (baseStart_561738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561738 prefixEnd_561738 := by exact prefixLift 561738
  have htrace : WordTrace (prefixWord ++ tailWord_561738) baseStart_561738 baseEnd_561738 := by
    simpa [prefixWord, tailWord_561738, baseEnd_561738] using wordTrace_append hprefix tailTrace_561738
  have hstable : (prefixWord ++ tailWord_561738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561738).length < 2 ^ (prefixWord ++ tailWord_561738).sum := by decide
  have hdescent : baseEnd_561738 < baseStart_561738 := by decide
  rcases family_descends (prefixWord ++ tailWord_561738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561749 : List Nat := [1, 3, 2, 2, 1, 1, 5, 5]
def baseStart_561749 : Nat := 118140960795 + 561749 * 2 ^ 59
def prefixEnd_561749 : Nat := 4983230072969 + 3 ^ 40 * 561749 * 2
def baseEnd_561749 : Nat := 85465850128186040934539

theorem tailTrace_561749 : CollatzResearch.WordTrace tailWord_561749 prefixEnd_561749 85465850128186040934539 := by
  unfold tailWord_561749
  simp only [CollatzResearch.WordTrace]
  refine ⟨20488669241886786936208301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13659112827924524624138867 20488669241886786936208301)
  ·
    refine ⟨7683250965707545101078113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20488669241886786936208301 7683250965707545101078113)
    ·
      refine ⟨5762438224280658825808585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7683250965707545101078113 5762438224280658825808585)
      ·
        refine ⟨4321828668210494119356439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5762438224280658825808585 4321828668210494119356439)
        ·
          refine ⟨6482743002315741179034659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4321828668210494119356439 6482743002315741179034659)
          ·
            refine ⟨9724114503473611768551989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6482743002315741179034659 9724114503473611768551989)
            ·
              refine ⟨911635734700651103301749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9724114503473611768551989 911635734700651103301749)
              ·
                refine ⟨85465850128186040934539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 911635734700651103301749 85465850128186040934539)
                ·
                  rfl

theorem cell20_561749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 5].length) (baseStart_561749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561749 prefixEnd_561749 := by exact prefixLift 561749
  have htrace : WordTrace (prefixWord ++ tailWord_561749) baseStart_561749 baseEnd_561749 := by
    simpa [prefixWord, tailWord_561749, baseEnd_561749] using wordTrace_append hprefix tailTrace_561749
  have hstable : (prefixWord ++ tailWord_561749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561749).length < 2 ^ (prefixWord ++ tailWord_561749).sum := by decide
  have hdescent : baseEnd_561749 < baseStart_561749 := by decide
  rcases family_descends (prefixWord ++ tailWord_561749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561762 : List Nat := [3, 3, 2, 3, 1, 1, 3, 4]
def baseStart_561762 : Nat := 118140960795 + 561762 * 2 ^ 59
def prefixEnd_561762 : Nat := 4983230072969 + 3 ^ 40 * 561762 * 2
def baseEnd_561762 : Nat := 85467827979595951790077

theorem tailTrace_561762 : CollatzResearch.WordTrace tailWord_561762 prefixEnd_561762 85467827979595951790077 := by
  unfold tailWord_561762
  simp only [CollatzResearch.WordTrace]
  refine ⟨5122285847709922539107885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13659428927226460104287693 5122285847709922539107885)
  ·
    refine ⟨1920857192891220952165457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5122285847709922539107885 1920857192891220952165457)
    ·
      refine ⟨1440642894668415714124093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1920857192891220952165457 1440642894668415714124093)
      ·
        refine ⟨540241085500655892796535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1440642894668415714124093 540241085500655892796535)
        ·
          refine ⟨810361628250983839194803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 540241085500655892796535 810361628250983839194803)
          ·
            refine ⟨1215542442376475758792205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 810361628250983839194803 1215542442376475758792205)
            ·
              refine ⟨455828415891178409547077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1215542442376475758792205 455828415891178409547077)
              ·
                refine ⟨85467827979595951790077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 455828415891178409547077 85467827979595951790077)
                ·
                  rfl

theorem cell20_561762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_561762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561762 prefixEnd_561762 := by exact prefixLift 561762
  have htrace : WordTrace (prefixWord ++ tailWord_561762) baseStart_561762 baseEnd_561762 := by
    simpa [prefixWord, tailWord_561762, baseEnd_561762] using wordTrace_append hprefix tailTrace_561762
  have hstable : (prefixWord ++ tailWord_561762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561762).length < 2 ^ (prefixWord ++ tailWord_561762).sum := by decide
  have hdescent : baseEnd_561762 < baseStart_561762 := by decide
  rcases family_descends (prefixWord ++ tailWord_561762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561776 : List Nat := [2, 1, 1, 1, 7, 1, 2, 3, 2]
def baseStart_561776 : Nat := 118140960795 + 561776 * 2 ^ 59
def prefixEnd_561776 : Nat := 4983230072969 + 3 ^ 40 * 561776 * 2
def baseEnd_561776 : Nat := 256409873920266028903507

theorem tailTrace_561776 : CollatzResearch.WordTrace tailWord_561776 prefixEnd_561776 256409873920266028903507 := by
  unfold tailWord_561776
  simp only [CollatzResearch.WordTrace]
  refine ⟨10244827006394485273720591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13659769341859313698294121 10244827006394485273720591)
  ·
    refine ⟨15367240509591727910580887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10244827006394485273720591 15367240509591727910580887)
    ·
      refine ⟨23050860764387591865871331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15367240509591727910580887 23050860764387591865871331)
      ·
        refine ⟨34576291146581387798806997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23050860764387591865871331 34576291146581387798806997)
        ·
          refine ⟨810381823748001276534539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 34576291146581387798806997 810381823748001276534539)
          ·
            refine ⟨1215572735622001914801809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 810381823748001276534539 1215572735622001914801809)
            ·
              refine ⟨911679551716501436101357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1215572735622001914801809 911679551716501436101357)
              ·
                refine ⟨341879831893688038538009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 911679551716501436101357 341879831893688038538009)
                ·
                  refine ⟨256409873920266028903507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 341879831893688038538009 256409873920266028903507)
                  ·
                    rfl

theorem cell20_561776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 3, 2].length) (baseStart_561776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561776 prefixEnd_561776 := by exact prefixLift 561776
  have htrace : WordTrace (prefixWord ++ tailWord_561776) baseStart_561776 baseEnd_561776 := by
    simpa [prefixWord, tailWord_561776, baseEnd_561776] using wordTrace_append hprefix tailTrace_561776
  have hstable : (prefixWord ++ tailWord_561776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561776).length < 2 ^ (prefixWord ++ tailWord_561776).sum := by decide
  have hdescent : baseEnd_561776 < baseStart_561776 := by decide
  rcases family_descends (prefixWord ++ tailWord_561776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561797 : List Nat := [1, 3, 1, 1, 4, 2, 2, 4, 2]
def baseStart_561797 : Nat := 118140960795 + 561797 * 2 ^ 59
def prefixEnd_561797 : Nat := 4983230072969 + 3 ^ 40 * 561797 * 2
def baseEnd_561797 : Nat := 256419458892483289203421

theorem tailTrace_561797 : CollatzResearch.WordTrace tailWord_561797 prefixEnd_561797 256419458892483289203421 := by
  unfold tailWord_561797
  simp only [CollatzResearch.WordTrace]
  refine ⟨20490419945712891133955645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13660279963808594089303763 20490419945712891133955645)
  ·
    refine ⟨7683907479642334175233367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20490419945712891133955645 7683907479642334175233367)
    ·
      refine ⟨11525861219463501262850051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7683907479642334175233367 11525861219463501262850051)
      ·
        refine ⟨17288791829195251894275077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11525861219463501262850051 17288791829195251894275077)
        ·
          refine ⟨3241648467974109730176577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17288791829195251894275077 3241648467974109730176577)
          ·
            refine ⟨2431236350980582297632433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3241648467974109730176577 2431236350980582297632433)
            ·
              refine ⟨1823427263235436723224325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2431236350980582297632433 1823427263235436723224325)
              ·
                refine ⟨341892611856644385604561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1823427263235436723224325 341892611856644385604561)
                ·
                  refine ⟨256419458892483289203421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 341892611856644385604561 256419458892483289203421)
                  ·
                    rfl

theorem cell20_561797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 4, 2].length) (baseStart_561797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561797 prefixEnd_561797 := by exact prefixLift 561797
  have htrace : WordTrace (prefixWord ++ tailWord_561797) baseStart_561797 baseEnd_561797 := by
    simpa [prefixWord, tailWord_561797, baseEnd_561797] using wordTrace_append hprefix tailTrace_561797
  have hstable : (prefixWord ++ tailWord_561797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561797).length < 2 ^ (prefixWord ++ tailWord_561797).sum := by decide
  have hdescent : baseEnd_561797 < baseStart_561797 := by decide
  rcases family_descends (prefixWord ++ tailWord_561797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561852 : List Nat := [2, 2, 2, 3, 1, 1, 5, 2, 2]
def baseStart_561852 : Nat := 118140960795 + 561852 * 2 ^ 59
def prefixEnd_561852 : Nat := 4983230072969 + 3 ^ 40 * 561852 * 2
def baseEnd_561852 : Nat := 256444562391147542369863

theorem tailTrace_561852 : CollatzResearch.WordTrace tailWord_561852 prefixEnd_561852 256444562391147542369863 := by
  unfold tailWord_561852
  simp only [CollatzResearch.WordTrace]
  refine ⟨10246212980256817763603905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13661617307009090351471873 10246212980256817763603905)
  ·
    refine ⟨7684659735192613322702929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10246212980256817763603905 7684659735192613322702929)
    ·
      refine ⟨5763494801394459992027197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7684659735192613322702929 5763494801394459992027197)
      ·
        refine ⟨2161310550522922497010199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5763494801394459992027197 2161310550522922497010199)
        ·
          refine ⟨3241965825784383745515299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2161310550522922497010199 3241965825784383745515299)
          ·
            refine ⟨4862948738676575618272949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3241965825784383745515299 4862948738676575618272949)
            ·
              refine ⟨455901444250928964213089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4862948738676575618272949 455901444250928964213089)
              ·
                refine ⟨341926083188196723159817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 455901444250928964213089 341926083188196723159817)
                ·
                  refine ⟨256444562391147542369863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 341926083188196723159817 256444562391147542369863)
                  ·
                    rfl

theorem cell20_561852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 2, 2].length) (baseStart_561852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561852 prefixEnd_561852 := by exact prefixLift 561852
  have htrace : WordTrace (prefixWord ++ tailWord_561852) baseStart_561852 baseEnd_561852 := by
    simpa [prefixWord, tailWord_561852, baseEnd_561852] using wordTrace_append hprefix tailTrace_561852
  have hstable : (prefixWord ++ tailWord_561852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561852).length < 2 ^ (prefixWord ++ tailWord_561852).sum := by decide
  have hdescent : baseEnd_561852 < baseStart_561852 := by decide
  rcases family_descends (prefixWord ++ tailWord_561852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561856 : List Nat := [2, 1, 1, 2, 4, 2, 3, 1, 4]
def baseStart_561856 : Nat := 118140960795 + 561856 * 2 ^ 59
def prefixEnd_561856 : Nat := 4983230072969 + 3 ^ 40 * 561856 * 2
def baseEnd_561856 : Nat := 256446388100141306236513

theorem tailTrace_561856 : CollatzResearch.WordTrace tailWord_561856 prefixEnd_561856 256446388100141306236513 := by
  unfold tailWord_561856
  simp only [CollatzResearch.WordTrace]
  refine ⟨10246285926249572105176711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13661714568332762806902281 10246285926249572105176711)
  ·
    refine ⟨15369428889374358157765067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10246285926249572105176711 15369428889374358157765067)
    ·
      refine ⟨23054143334061537236647601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15369428889374358157765067 23054143334061537236647601)
      ·
        refine ⟨17290607500546152927485701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23054143334061537236647601 17290607500546152927485701)
        ·
          refine ⟨3241988906352403673903569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17290607500546152927485701 3241988906352403673903569)
          ·
            refine ⟨2431491679764302755427677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3241988906352403673903569 2431491679764302755427677)
            ·
              refine ⟨911809379911613533285379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2431491679764302755427677 911809379911613533285379)
              ·
                refine ⟨1367714069867420299928069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 911809379911613533285379 1367714069867420299928069)
                ·
                  refine ⟨256446388100141306236513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1367714069867420299928069 256446388100141306236513)
                  ·
                    rfl

theorem cell20_561856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 4].length) (baseStart_561856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561856 prefixEnd_561856 := by exact prefixLift 561856
  have htrace : WordTrace (prefixWord ++ tailWord_561856) baseStart_561856 baseEnd_561856 := by
    simpa [prefixWord, tailWord_561856, baseEnd_561856] using wordTrace_append hprefix tailTrace_561856
  have hstable : (prefixWord ++ tailWord_561856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561856).length < 2 ^ (prefixWord ++ tailWord_561856).sum := by decide
  have hdescent : baseEnd_561856 < baseStart_561856 := by decide
  rcases family_descends (prefixWord ++ tailWord_561856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561862 : List Nat := [6, 1, 2, 1, 2, 1, 1, 3, 3]
def baseStart_561862 : Nat := 118140960795 + 561862 * 2 ^ 59
def prefixEnd_561862 : Nat := 4983230072969 + 3 ^ 40 * 561862 * 2
def baseEnd_561862 : Nat := 256449126663631952036489

theorem tailTrace_561862 : CollatzResearch.WordTrace tailWord_561862 prefixEnd_561862 256449126663631952036489 := by
  unfold tailWord_561862
  simp only [CollatzResearch.WordTrace]
  refine ⟨640399709077418976095995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13661860460318271490047893 640399709077418976095995)
  ·
    refine ⟨960599563616128464143993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 640399709077418976095995 960599563616128464143993)
    ·
      refine ⟨720449672712096348107995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 960599563616128464143993 720449672712096348107995)
      ·
        refine ⟨1080674509068144522161993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 720449672712096348107995 1080674509068144522161993)
        ·
          refine ⟨810505881801108391621495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1080674509068144522161993 810505881801108391621495)
          ·
            refine ⟨1215758822701662587432243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 810505881801108391621495 1215758822701662587432243)
            ·
              refine ⟨1823638234052493881148365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1215758822701662587432243 1823638234052493881148365)
              ·
                refine ⟨683864337769685205430637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1823638234052493881148365 683864337769685205430637)
                ·
                  refine ⟨256449126663631952036489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 683864337769685205430637 256449126663631952036489)
                  ·
                    rfl

theorem cell20_561862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_561862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561862 prefixEnd_561862 := by exact prefixLift 561862
  have htrace : WordTrace (prefixWord ++ tailWord_561862) baseStart_561862 baseEnd_561862 := by
    simpa [prefixWord, tailWord_561862, baseEnd_561862] using wordTrace_append hprefix tailTrace_561862
  have hstable : (prefixWord ++ tailWord_561862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561862).length < 2 ^ (prefixWord ++ tailWord_561862).sum := by decide
  have hdescent : baseEnd_561862 < baseStart_561862 := by decide
  rcases family_descends (prefixWord ++ tailWord_561862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561866 : List Nat := [3, 1, 2, 1, 4, 1, 4, 1, 3]
def baseStart_561866 : Nat := 118140960795 + 561866 * 2 ^ 59
def prefixEnd_561866 : Nat := 4983230072969 + 3 ^ 40 * 561866 * 2
def baseEnd_561866 : Nat := 256450952372625715903139

theorem tailTrace_561866 : CollatzResearch.WordTrace tailWord_561866 prefixEnd_561866 256450952372625715903139 := by
  unfold tailWord_561866
  simp only [CollatzResearch.WordTrace]
  refine ⟨5123234145615728979554363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13661957721641943945478301 5123234145615728979554363)
  ·
    refine ⟨7684851218423593469331545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5123234145615728979554363 7684851218423593469331545)
    ·
      refine ⟨5763638413817695101998659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7684851218423593469331545 5763638413817695101998659)
      ·
        refine ⟨8645457620726542652997989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5763638413817695101998659 8645457620726542652997989)
        ·
          refine ⟨1621023303886226747437123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8645457620726542652997989 1621023303886226747437123)
          ·
            refine ⟨2431534955829340121155685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1621023303886226747437123 2431534955829340121155685)
            ·
              refine ⟨455912804218001272716691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2431534955829340121155685 455912804218001272716691)
              ·
                refine ⟨683869206327001909075037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 455912804218001272716691 683869206327001909075037)
                ·
                  refine ⟨256450952372625715903139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 683869206327001909075037 256450952372625715903139)
                  ·
                    rfl

theorem cell20_561866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 3].length) (baseStart_561866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561866 prefixEnd_561866 := by exact prefixLift 561866
  have htrace : WordTrace (prefixWord ++ tailWord_561866) baseStart_561866 baseEnd_561866 := by
    simpa [prefixWord, tailWord_561866, baseEnd_561866] using wordTrace_append hprefix tailTrace_561866
  have hstable : (prefixWord ++ tailWord_561866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561866).length < 2 ^ (prefixWord ++ tailWord_561866).sum := by decide
  have hdescent : baseEnd_561866 < baseStart_561866 := by decide
  rcases family_descends (prefixWord ++ tailWord_561866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561918 : List Nat := [4, 2, 2, 1, 2, 1, 3, 5]
def baseStart_561918 : Nat := 118140960795 + 561918 * 2 ^ 59
def prefixEnd_561918 : Nat := 4983230072969 + 3 ^ 40 * 561918 * 2
def baseEnd_561918 : Nat := 85491562196514882056531

theorem tailTrace_561918 : CollatzResearch.WordTrace tailWord_561918 prefixEnd_561918 85491562196514882056531 := by
  unfold tailWord_561918
  simp only [CollatzResearch.WordTrace]
  refine ⟨2561854147284316099888801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13663222118849685866073605 2561854147284316099888801)
  ·
    refine ⟨1921390610463237074916601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2561854147284316099888801 1921390610463237074916601)
    ·
      refine ⟨1441042957847427806187451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1921390610463237074916601 1441042957847427806187451)
      ·
        refine ⟨2161564436771141709281177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1441042957847427806187451 2161564436771141709281177)
        ·
          refine ⟨1621173327578356281960883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2161564436771141709281177 1621173327578356281960883)
          ·
            refine ⟨2431759991367534422941325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1621173327578356281960883 2431759991367534422941325)
            ·
              refine ⟨911909996762825408602997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2431759991367534422941325 911909996762825408602997)
              ·
                refine ⟨85491562196514882056531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 911909996762825408602997 85491562196514882056531)
                ·
                  rfl

theorem cell20_561918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_561918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561918 prefixEnd_561918 := by exact prefixLift 561918
  have htrace : WordTrace (prefixWord ++ tailWord_561918) baseStart_561918 baseEnd_561918 := by
    simpa [prefixWord, tailWord_561918, baseEnd_561918] using wordTrace_append hprefix tailTrace_561918
  have hstable : (prefixWord ++ tailWord_561918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561918).length < 2 ^ (prefixWord ++ tailWord_561918).sum := by decide
  have hdescent : baseEnd_561918 < baseStart_561918 := by decide
  rcases family_descends (prefixWord ++ tailWord_561918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561939 : List Nat := [1, 1, 1, 2, 1, 3, 7, 4]
def baseStart_561939 : Nat := 118140960795 + 561939 * 2 ^ 59
def prefixEnd_561939 : Nat := 4983230072969 + 3 ^ 40 * 561939 * 2
def baseEnd_561939 : Nat := 85494757187253968823169

theorem tailTrace_561939 : CollatzResearch.WordTrace tailWord_561939 prefixEnd_561939 85494757187253968823169 := by
  unfold tailWord_561939
  simp only [CollatzResearch.WordTrace]
  refine ⟨20495599111198449385624871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13663732740798966257083247 20495599111198449385624871)
  ·
    refine ⟨30743398666797674078437307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20495599111198449385624871 30743398666797674078437307)
    ·
      refine ⟨46115098000196511117655961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30743398666797674078437307 46115098000196511117655961)
      ·
        refine ⟨34586323500147383338241971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46115098000196511117655961 34586323500147383338241971)
        ·
          refine ⟨51879485250221075007362957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34586323500147383338241971 51879485250221075007362957)
          ·
            refine ⟨19454806968832903127761109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51879485250221075007362957 19454806968832903127761109)
            ·
              refine ⟨455972038332021167056901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 19454806968832903127761109 455972038332021167056901)
              ·
                refine ⟨85494757187253968823169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 455972038332021167056901 85494757187253968823169)
                ·
                  rfl

theorem cell20_561939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 4].length) (baseStart_561939 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561939 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561939 prefixEnd_561939 := by exact prefixLift 561939
  have htrace : WordTrace (prefixWord ++ tailWord_561939) baseStart_561939 baseEnd_561939 := by
    simpa [prefixWord, tailWord_561939, baseEnd_561939] using wordTrace_append hprefix tailTrace_561939
  have hstable : (prefixWord ++ tailWord_561939).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561939).length < 2 ^ (prefixWord ++ tailWord_561939).sum := by decide
  have hdescent : baseEnd_561939 < baseStart_561939 := by decide
  rcases family_descends (prefixWord ++ tailWord_561939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561946 : List Nat := [3, 1, 1, 3, 2, 1, 2, 2, 5]
def baseStart_561946 : Nat := 118140960795 + 561946 * 2 ^ 59
def prefixEnd_561946 : Nat := 4983230072969 + 3 ^ 40 * 561946 * 2
def baseEnd_561946 : Nat := 256487466552500993236145

theorem tailTrace_561946 : CollatzResearch.WordTrace tailWord_561946 prefixEnd_561946 256487466552500993236145 := by
  unfold tailWord_561946
  simp only [CollatzResearch.WordTrace]
  refine ⟨5123963605543272395282423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13663902948115393054086461 5123963605543272395282423)
  ·
    refine ⟨7685945408314908592923635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5123963605543272395282423 7685945408314908592923635)
    ·
      refine ⟨11528918112472362889385453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7685945408314908592923635 11528918112472362889385453)
      ·
        refine ⟨4323344292177136083519545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11528918112472362889385453 4323344292177136083519545)
        ·
          refine ⟨3242508219132852062639659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4323344292177136083519545 3242508219132852062639659)
          ·
            refine ⟨4863762328699278093959489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3242508219132852062639659 4863762328699278093959489)
            ·
              refine ⟨3647821746524458570469617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4863762328699278093959489 3647821746524458570469617)
              ·
                refine ⟨2735866309893343927852213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3647821746524458570469617 2735866309893343927852213)
                ·
                  refine ⟨256487466552500993236145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2735866309893343927852213 256487466552500993236145)
                  ·
                    rfl

theorem cell20_561946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_561946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561946 prefixEnd_561946 := by exact prefixLift 561946
  have htrace : WordTrace (prefixWord ++ tailWord_561946) baseStart_561946 baseEnd_561946 := by
    simpa [prefixWord, tailWord_561946, baseEnd_561946] using wordTrace_append hprefix tailTrace_561946
  have hstable : (prefixWord ++ tailWord_561946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561946).length < 2 ^ (prefixWord ++ tailWord_561946).sum := by decide
  have hdescent : baseEnd_561946 < baseStart_561946 := by decide
  rcases family_descends (prefixWord ++ tailWord_561946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561953 : List Nat := [1, 2, 3, 2, 1, 2, 1, 2, 6]
def baseStart_561953 : Nat := 118140960795 + 561953 * 2 ^ 59
def prefixEnd_561953 : Nat := 4983230072969 + 3 ^ 40 * 561953 * 2
def baseEnd_561953 : Nat := 256490661543240080002783

theorem tailTrace_561953 : CollatzResearch.WordTrace tailWord_561953 prefixEnd_561953 256490661543240080002783 := by
  unfold tailWord_561953
  simp only [CollatzResearch.WordTrace]
  refine ⟨20496109733147729776634513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13664073155431819851089675 20496109733147729776634513)
  ·
    refine ⟨15372082299860797332475885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20496109733147729776634513 15372082299860797332475885)
    ·
      refine ⟨5764530862447798999678457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15372082299860797332475885 5764530862447798999678457)
      ·
        refine ⟨4323398146835849249758843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5764530862447798999678457 4323398146835849249758843)
        ·
          refine ⟨6485097220253773874638265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4323398146835849249758843 6485097220253773874638265)
          ·
            refine ⟨4863822915190330405978699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6485097220253773874638265 4863822915190330405978699)
            ·
              refine ⟨7295734372785495608968049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4863822915190330405978699 7295734372785495608968049)
              ·
                refine ⟨5471800779589121706726037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7295734372785495608968049 5471800779589121706726037)
                ·
                  refine ⟨256490661543240080002783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5471800779589121706726037 256490661543240080002783)
                  ·
                    rfl

theorem cell20_561953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_561953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561953 prefixEnd_561953 := by exact prefixLift 561953
  have htrace : WordTrace (prefixWord ++ tailWord_561953) baseStart_561953 baseEnd_561953 := by
    simpa [prefixWord, tailWord_561953, baseEnd_561953] using wordTrace_append hprefix tailTrace_561953
  have hstable : (prefixWord ++ tailWord_561953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561953).length < 2 ^ (prefixWord ++ tailWord_561953).sum := by decide
  have hdescent : baseEnd_561953 < baseStart_561953 := by decide
  rcases family_descends (prefixWord ++ tailWord_561953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561966 : List Nat := [4, 1, 3, 2, 1, 1, 2, 4, 2]
def baseStart_561966 : Nat := 118140960795 + 561966 * 2 ^ 59
def prefixEnd_561966 : Nat := 4983230072969 + 3 ^ 40 * 561966 * 2
def baseEnd_561966 : Nat := 256496595097469812569397

theorem tailTrace_561966 : CollatzResearch.WordTrace tailWord_561966 prefixEnd_561966 256496595097469812569397 := by
  unfold tailWord_561966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2562072985262579124607219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13664389254733755331238501 2562072985262579124607219)
  ·
    refine ⟨3843109477893868686910829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2562072985262579124607219 3843109477893868686910829)
    ·
      refine ⟨1441166054210200757591561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3843109477893868686910829 1441166054210200757591561)
      ·
        refine ⟨1080874540657650568193671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1441166054210200757591561 1080874540657650568193671)
        ·
          refine ⟨1621311810986475852290507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1080874540657650568193671 1621311810986475852290507)
          ·
            refine ⟨2431967716479713778435761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1621311810986475852290507 2431967716479713778435761)
            ·
              refine ⟨1823975787359785333826821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2431967716479713778435761 1823975787359785333826821)
              ·
                refine ⟨341995460129959750092529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1823975787359785333826821 341995460129959750092529)
                ·
                  refine ⟨256496595097469812569397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 341995460129959750092529 256496595097469812569397)
                  ·
                    rfl

theorem cell20_561966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_561966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561966 prefixEnd_561966 := by exact prefixLift 561966
  have htrace : WordTrace (prefixWord ++ tailWord_561966) baseStart_561966 baseEnd_561966 := by
    simpa [prefixWord, tailWord_561966, baseEnd_561966] using wordTrace_append hprefix tailTrace_561966
  have hstable : (prefixWord ++ tailWord_561966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561966).length < 2 ^ (prefixWord ++ tailWord_561966).sum := by decide
  have hdescent : baseEnd_561966 < baseStart_561966 := by decide
  rcases family_descends (prefixWord ++ tailWord_561966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561970 : List Nat := [3, 2, 1, 1, 3, 1, 4, 1, 4]
def baseStart_561970 : Nat := 118140960795 + 561970 * 2 ^ 59
def prefixEnd_561970 : Nat := 4983230072969 + 3 ^ 40 * 561970 * 2
def baseEnd_561970 : Nat := 256498420806463576436047

theorem tailTrace_561970 : CollatzResearch.WordTrace tailWord_561970 prefixEnd_561970 256498420806463576436047 := by
  unfold tailWord_561970
  simp only [CollatzResearch.WordTrace]
  refine ⟨5124182443521535420000841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13664486516057427786668909 5124182443521535420000841)
  ·
    refine ⟨3843136832641151565000631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5124182443521535420000841 3843136832641151565000631)
    ·
      refine ⟨5764705248961727347500947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3843136832641151565000631 5764705248961727347500947)
      ·
        refine ⟨8647057873442591021251421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5764705248961727347500947 8647057873442591021251421)
        ·
          refine ⟨3242646702540971632969283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8647057873442591021251421 3242646702540971632969283)
          ·
            refine ⟨4863970053811457449453925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3242646702540971632969283 4863970053811457449453925)
            ·
              refine ⟨911994385089648271772611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4863970053811457449453925 911994385089648271772611)
              ·
                refine ⟨1367991577634472407658917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 911994385089648271772611 1367991577634472407658917)
                ·
                  refine ⟨256498420806463576436047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1367991577634472407658917 256498420806463576436047)
                  ·
                    rfl

theorem cell20_561970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_561970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561970 prefixEnd_561970 := by exact prefixLift 561970
  have htrace : WordTrace (prefixWord ++ tailWord_561970) baseStart_561970 baseEnd_561970 := by
    simpa [prefixWord, tailWord_561970, baseEnd_561970] using wordTrace_append hprefix tailTrace_561970
  have hstable : (prefixWord ++ tailWord_561970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561970).length < 2 ^ (prefixWord ++ tailWord_561970).sum := by decide
  have hdescent : baseEnd_561970 < baseStart_561970 := by decide
  rcases family_descends (prefixWord ++ tailWord_561970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_561984 : List Nat := [2, 1, 1, 2, 2, 1, 1, 7, 3]
def baseStart_561984 : Nat := 118140960795 + 561984 * 2 ^ 59
def prefixEnd_561984 : Nat := 4983230072969 + 3 ^ 40 * 561984 * 2
def baseEnd_561984 : Nat := 256504810787941749969323

theorem tailTrace_561984 : CollatzResearch.WordTrace tailWord_561984 prefixEnd_561984 256504810787941749969323 := by
  unfold tailWord_561984
  simp only [CollatzResearch.WordTrace]
  refine ⟨10248620198017711035506503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13664826930690281380675337 10248620198017711035506503)
  ·
    refine ⟨15372930297026566553259755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10248620198017711035506503 15372930297026566553259755)
    ·
      refine ⟨23059395445539849829889633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15372930297026566553259755 23059395445539849829889633)
      ·
        refine ⟨17294546584154887372417225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23059395445539849829889633 17294546584154887372417225)
        ·
          refine ⟨12970909938116165529312919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17294546584154887372417225 12970909938116165529312919)
          ·
            refine ⟨19456364907174248293969379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12970909938116165529312919 19456364907174248293969379)
            ·
              refine ⟨29184547360761372440954069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19456364907174248293969379 29184547360761372440954069)
              ·
                refine ⟨684012828767844666584861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 29184547360761372440954069 684012828767844666584861)
                ·
                  refine ⟨256504810787941749969323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 684012828767844666584861 256504810787941749969323)
                  ·
                    rfl

theorem cell20_561984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 3].length) (baseStart_561984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_561984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_561984 prefixEnd_561984 := by exact prefixLift 561984
  have htrace : WordTrace (prefixWord ++ tailWord_561984) baseStart_561984 baseEnd_561984 := by
    simpa [prefixWord, tailWord_561984, baseEnd_561984] using wordTrace_append hprefix tailTrace_561984
  have hstable : (prefixWord ++ tailWord_561984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_561984).length < 2 ^ (prefixWord ++ tailWord_561984).sum := by decide
  have hdescent : baseEnd_561984 < baseStart_561984 := by decide
  rcases family_descends (prefixWord ++ tailWord_561984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562074 : List Nat := [3, 1, 1, 4, 11]
def baseStart_562074 : Nat := 118140960795 + 562074 * 2 ^ 59
def prefixEnd_562074 : Nat := 4983230072969 + 3 ^ 40 * 562074 * 2
def baseEnd_562074 : Nat := 3167233200497548604555

theorem tailTrace_562074 : CollatzResearch.WordTrace tailWord_562074 prefixEnd_562074 3167233200497548604555 := by
  unfold tailWord_562074
  simp only [CollatzResearch.WordTrace]
  refine ⟨5125130741427341860447319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13667015310472911627859517 5125130741427341860447319)
  ·
    refine ⟨7687696112141012790670979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5125130741427341860447319 7687696112141012790670979)
    ·
      refine ⟨11531544168211519186006469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7687696112141012790670979 11531544168211519186006469)
      ·
        refine ⟨2162164531539659847376213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11531544168211519186006469 2162164531539659847376213)
        ·
          refine ⟨3167233200497548604555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2162164531539659847376213 3167233200497548604555)
          ·
            rfl

theorem cell20_562074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 11].length) (baseStart_562074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562074 prefixEnd_562074 := by exact prefixLift 562074
  have htrace : WordTrace (prefixWord ++ tailWord_562074) baseStart_562074 baseEnd_562074 := by
    simpa [prefixWord, tailWord_562074, baseEnd_562074] using wordTrace_append hprefix tailTrace_562074
  have hstable : (prefixWord ++ tailWord_562074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562074).length < 2 ^ (prefixWord ++ tailWord_562074).sum := by decide
  have hdescent : baseEnd_562074 < baseStart_562074 := by decide
  rcases family_descends (prefixWord ++ tailWord_562074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562076 : List Nat := [2, 2, 3, 3, 3, 1, 2, 2, 2]
def baseStart_562076 : Nat := 118140960795 + 562076 * 2 ^ 59
def prefixEnd_562076 : Nat := 4983230072969 + 3 ^ 40 * 562076 * 2
def baseEnd_562076 : Nat := 256546802094798318902281

theorem tailTrace_562076 : CollatzResearch.WordTrace tailWord_562076 prefixEnd_562076 256546802094798318902281 := by
  unfold tailWord_562076
  simp only [CollatzResearch.WordTrace]
  refine ⟨10250297955851060891681041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13667063941134747855574721 10250297955851060891681041)
  ·
    refine ⟨7687723466888295668760781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10250297955851060891681041 7687723466888295668760781)
    ·
      refine ⟨2882896300083110875785293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7687723466888295668760781 2882896300083110875785293)
      ·
        refine ⟨1081086112531166578419485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2882896300083110875785293 1081086112531166578419485)
        ·
          refine ⟨405407292199187466907307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1081086112531166578419485 405407292199187466907307)
          ·
            refine ⟨608110938298781200360961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405407292199187466907307 608110938298781200360961)
            ·
              refine ⟨456083203724085900270721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 608110938298781200360961 456083203724085900270721)
              ·
                refine ⟨342062402793064425203041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 456083203724085900270721 342062402793064425203041)
                ·
                  refine ⟨256546802094798318902281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 342062402793064425203041 256546802094798318902281)
                  ·
                    rfl

theorem cell20_562076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 2, 2].length) (baseStart_562076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562076 prefixEnd_562076 := by exact prefixLift 562076
  have htrace : WordTrace (prefixWord ++ tailWord_562076) baseStart_562076 baseEnd_562076 := by
    simpa [prefixWord, tailWord_562076, baseEnd_562076] using wordTrace_append hprefix tailTrace_562076
  have hstable : (prefixWord ++ tailWord_562076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562076).length < 2 ^ (prefixWord ++ tailWord_562076).sum := by decide
  have hdescent : baseEnd_562076 < baseStart_562076 := by decide
  rcases family_descends (prefixWord ++ tailWord_562076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562077 : List Nat := [1, 4, 2, 1, 2, 1, 4, 2, 3]
def baseStart_562077 : Nat := 118140960795 + 562077 * 2 ^ 59
def prefixEnd_562077 : Nat := 4983230072969 + 3 ^ 40 * 562077 * 2
def baseEnd_562077 : Nat := 256547258522046759868943

theorem tailTrace_562077 : CollatzResearch.WordTrace tailWord_562077 prefixEnd_562077 256547258522046759868943 := by
  unfold tailWord_562077
  simp only [CollatzResearch.WordTrace]
  refine ⟨20500632384698498954148485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13667088256465665969432323 20500632384698498954148485)
  ·
    refine ⟨3843868572130968553902841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20500632384698498954148485 3843868572130968553902841)
    ·
      refine ⟨2882901429098226415427131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3843868572130968553902841 2882901429098226415427131)
      ·
        refine ⟨4324352143647339623140697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2882901429098226415427131 4324352143647339623140697)
        ·
          refine ⟨3243264107735504717355523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4324352143647339623140697 3243264107735504717355523)
          ·
            refine ⟨4864896161603257076033285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3243264107735504717355523 4864896161603257076033285)
            ·
              refine ⟨912168030300610701756241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4864896161603257076033285 912168030300610701756241)
              ·
                refine ⟨684126022725458026317181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 912168030300610701756241 684126022725458026317181)
                ·
                  refine ⟨256547258522046759868943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 684126022725458026317181 256547258522046759868943)
                  ·
                    rfl

theorem cell20_562077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_562077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562077 prefixEnd_562077 := by exact prefixLift 562077
  have htrace : WordTrace (prefixWord ++ tailWord_562077) baseStart_562077 baseEnd_562077 := by
    simpa [prefixWord, tailWord_562077, baseEnd_562077] using wordTrace_append hprefix tailTrace_562077
  have hstable : (prefixWord ++ tailWord_562077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562077).length < 2 ^ (prefixWord ++ tailWord_562077).sum := by decide
  have hdescent : baseEnd_562077 < baseStart_562077 := by decide
  rcases family_descends (prefixWord ++ tailWord_562077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562087 : List Nat := [1, 1, 6, 1, 4, 1, 1, 5]
def baseStart_562087 : Nat := 118140960795 + 562087 * 2 ^ 59
def prefixEnd_562087 : Nat := 4983230072969 + 3 ^ 40 * 562087 * 2
def baseEnd_562087 : Nat := 85517274264843723178523

theorem tailTrace_562087 : CollatzResearch.WordTrace tailWord_562087 prefixEnd_562087 85517274264843723178523 := by
  unfold tailWord_562087
  simp only [CollatzResearch.WordTrace]
  refine ⟨20500997114662270662012515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13667331409774847108008343 20500997114662270662012515)
  ·
    refine ⟨30751495671993405993018773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20500997114662270662012515 30751495671993405993018773)
    ·
      refine ⟨1441476359624690905922755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30751495671993405993018773 1441476359624690905922755)
      ·
        refine ⟨2162214539437036358884133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1441476359624690905922755 2162214539437036358884133)
        ·
          refine ⟨405415226144444317290775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2162214539437036358884133 405415226144444317290775)
          ·
            refine ⟨608122839216666475936163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405415226144444317290775 608122839216666475936163)
            ·
              refine ⟨912184258824999713904245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 608122839216666475936163 912184258824999713904245)
              ·
                refine ⟨85517274264843723178523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 912184258824999713904245 85517274264843723178523)
                ·
                  rfl

theorem cell20_562087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 5].length) (baseStart_562087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562087 prefixEnd_562087 := by exact prefixLift 562087
  have htrace : WordTrace (prefixWord ++ tailWord_562087) baseStart_562087 baseEnd_562087 := by
    simpa [prefixWord, tailWord_562087, baseEnd_562087] using wordTrace_append hprefix tailTrace_562087
  have hstable : (prefixWord ++ tailWord_562087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562087).length < 2 ^ (prefixWord ++ tailWord_562087).sum := by decide
  have hdescent : baseEnd_562087 < baseStart_562087 := by decide
  rcases family_descends (prefixWord ++ tailWord_562087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562105 : List Nat := [1, 2, 1, 4, 2, 2, 1, 1, 6]
def baseStart_562105 : Nat := 118140960795 + 562105 * 2 ^ 59
def prefixEnd_562105 : Nat := 4983230072969 + 3 ^ 40 * 562105 * 2
def baseEnd_562105 : Nat := 256560038485003106935495

theorem tailTrace_562105 : CollatzResearch.WordTrace tailWord_562105 prefixEnd_562105 256560038485003106935495 := by
  unfold tailWord_562105
  simp only [CollatzResearch.WordTrace]
  refine ⟨20501653628597059736167769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13667769085731373157445179 20501653628597059736167769)
  ·
    refine ⟨15376240221447794802125827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20501653628597059736167769 15376240221447794802125827)
    ·
      refine ⟨23064360332171692203188741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15376240221447794802125827 23064360332171692203188741)
      ·
        refine ⟨4324567562282192288097889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23064360332171692203188741 4324567562282192288097889)
        ·
          refine ⟨3243425671711644216073417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4324567562282192288097889 3243425671711644216073417)
          ·
            refine ⟨2432569253783733162055063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3243425671711644216073417 2432569253783733162055063)
            ·
              refine ⟨3648853880675599743082595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2432569253783733162055063 3648853880675599743082595)
              ·
                refine ⟨5473280821013399614623893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3648853880675599743082595 5473280821013399614623893)
                ·
                  refine ⟨256560038485003106935495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5473280821013399614623893 256560038485003106935495)
                  ·
                    rfl

theorem cell20_562105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_562105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562105 prefixEnd_562105 := by exact prefixLift 562105
  have htrace : WordTrace (prefixWord ++ tailWord_562105) baseStart_562105 baseEnd_562105 := by
    simpa [prefixWord, tailWord_562105, baseEnd_562105] using wordTrace_append hprefix tailTrace_562105
  have hstable : (prefixWord ++ tailWord_562105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562105).length < 2 ^ (prefixWord ++ tailWord_562105).sum := by decide
  have hdescent : baseEnd_562105 < baseStart_562105 := by decide
  rcases family_descends (prefixWord ++ tailWord_562105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562132 : List Nat := [2, 4, 1, 2, 1, 4, 1, 2, 3]
def baseStart_562132 : Nat := 118140960795 + 562132 * 2 ^ 59
def prefixEnd_562132 : Nat := 4983230072969 + 3 ^ 40 * 562132 * 2
def baseEnd_562132 : Nat := 256572362020711013035385

theorem tailTrace_562132 : CollatzResearch.WordTrace tailWord_562132 prefixEnd_562132 256572362020711013035385 := by
  unfold tailWord_562132
  simp only [CollatzResearch.WordTrace]
  refine ⟨10251319199749621673700325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13668425599666162231600433 10251319199749621673700325)
  ·
    refine ⟨1922122349953054063818811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10251319199749621673700325 1922122349953054063818811)
    ·
      refine ⟨2883183524929581095728217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1922122349953054063818811 2883183524929581095728217)
      ·
        refine ⟨2162387643697185821796163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2883183524929581095728217 2162387643697185821796163)
        ·
          refine ⟨3243581465545778732694245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2162387643697185821796163 3243581465545778732694245)
          ·
            refine ⟨608171524789833512380171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3243581465545778732694245 608171524789833512380171)
            ·
              refine ⟨912257287184750268570257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 608171524789833512380171 912257287184750268570257)
              ·
                refine ⟨684192965388562701427693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 912257287184750268570257 684192965388562701427693)
                ·
                  refine ⟨256572362020711013035385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 684192965388562701427693 256572362020711013035385)
                  ·
                    rfl

theorem cell20_562132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_562132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562132 prefixEnd_562132 := by exact prefixLift 562132
  have htrace : WordTrace (prefixWord ++ tailWord_562132) baseStart_562132 baseEnd_562132 := by
    simpa [prefixWord, tailWord_562132, baseEnd_562132] using wordTrace_append hprefix tailTrace_562132
  have hstable : (prefixWord ++ tailWord_562132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562132).length < 2 ^ (prefixWord ++ tailWord_562132).sum := by decide
  have hdescent : baseEnd_562132 < baseStart_562132 := by decide
  rcases family_descends (prefixWord ++ tailWord_562132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562136 : List Nat := [2, 1, 2, 2, 2, 4, 1, 1, 5]
def baseStart_562136 : Nat := 118140960795 + 562136 * 2 ^ 59
def prefixEnd_562136 : Nat := 4983230072969 + 3 ^ 40 * 562136 * 2
def baseEnd_562136 : Nat := 256574187729704776902035

theorem tailTrace_562136 : CollatzResearch.WordTrace tailWord_562136 prefixEnd_562136 256574187729704776902035 := by
  unfold tailWord_562136
  simp only [CollatzResearch.WordTrace]
  refine ⟨10251392145742376015273131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13668522860989834687030841 10251392145742376015273131)
  ·
    refine ⟨15377088218613564022909697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10251392145742376015273131 15377088218613564022909697)
    ·
      refine ⟨11532816163960173017182273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15377088218613564022909697 11532816163960173017182273)
      ·
        refine ⟨8649612122970129762886705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11532816163960173017182273 8649612122970129762886705)
        ·
          refine ⟨6487209092227597322165029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8649612122970129762886705 6487209092227597322165029)
          ·
            refine ⟨1216351704792674497905943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6487209092227597322165029 1216351704792674497905943)
            ·
              refine ⟨1824527557189011746858915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1216351704792674497905943 1824527557189011746858915)
              ·
                refine ⟨2736791335783517620288373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1824527557189011746858915 2736791335783517620288373)
                ·
                  refine ⟨256574187729704776902035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2736791335783517620288373 256574187729704776902035)
                  ·
                    rfl

theorem cell20_562136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 5].length) (baseStart_562136 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562136 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562136 prefixEnd_562136 := by exact prefixLift 562136
  have htrace : WordTrace (prefixWord ++ tailWord_562136) baseStart_562136 baseEnd_562136 := by
    simpa [prefixWord, tailWord_562136, baseEnd_562136] using wordTrace_append hprefix tailTrace_562136
  have hstable : (prefixWord ++ tailWord_562136).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562136).length < 2 ^ (prefixWord ++ tailWord_562136).sum := by decide
  have hdescent : baseEnd_562136 < baseStart_562136 := by decide
  rcases family_descends (prefixWord ++ tailWord_562136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562149 : List Nat := [1, 3, 1, 6, 1, 1, 3, 1, 3]
def baseStart_562149 : Nat := 118140960795 + 562149 * 2 ^ 59
def prefixEnd_562149 : Nat := 4983230072969 + 3 ^ 40 * 562149 * 2
def baseEnd_562149 : Nat := 256580121283934509468649

theorem tailTrace_562149 : CollatzResearch.WordTrace tailWord_562149 prefixEnd_562149 256580121283934509468649 := by
  unfold tailWord_562149
  simp only [CollatzResearch.WordTrace]
  refine ⟨20503258440437655250769501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13668838960291770167179667 20503258440437655250769501)
  ·
    refine ⟨7688721915164120719038563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20503258440437655250769501 7688721915164120719038563)
    ·
      refine ⟨11533082872746181078557845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7688721915164120719038563 11533082872746181078557845)
      ·
        refine ⟨540613259659977238057399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11533082872746181078557845 540613259659977238057399)
        ·
          refine ⟨810919889489965857086099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 540613259659977238057399 810919889489965857086099)
          ·
            refine ⟨1216379834234948785629149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 810919889489965857086099 1216379834234948785629149)
            ·
              refine ⟨456142437838105794610931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1216379834234948785629149 456142437838105794610931)
              ·
                refine ⟨684213656757158691916397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 456142437838105794610931 684213656757158691916397)
                ·
                  refine ⟨256580121283934509468649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 684213656757158691916397 256580121283934509468649)
                  ·
                    rfl

theorem cell20_562149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 3].length) (baseStart_562149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562149 prefixEnd_562149 := by exact prefixLift 562149
  have htrace : WordTrace (prefixWord ++ tailWord_562149) baseStart_562149 baseEnd_562149 := by
    simpa [prefixWord, tailWord_562149, baseEnd_562149] using wordTrace_append hprefix tailTrace_562149
  have hstable : (prefixWord ++ tailWord_562149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562149).length < 2 ^ (prefixWord ++ tailWord_562149).sum := by decide
  have hdescent : baseEnd_562149 < baseStart_562149 := by decide
  rcases family_descends (prefixWord ++ tailWord_562149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562177 : List Nat := [1, 2, 4, 1, 2, 2, 3, 3, 2]
def baseStart_562177 : Nat := 118140960795 + 562177 * 2 ^ 59
def prefixEnd_562177 : Nat := 4983230072969 + 3 ^ 40 * 562177 * 2
def baseEnd_562177 : Nat := 256592901246890856535201

theorem tailTrace_562177 : CollatzResearch.WordTrace tailWord_562177 prefixEnd_562177 256592901246890856535201 := by
  unfold tailWord_562177
  simp only [CollatzResearch.WordTrace]
  refine ⟨20504279684336216032788785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13669519789557477355192523 20504279684336216032788785)
  ·
    refine ⟨15378209763252162024591589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20504279684336216032788785 15378209763252162024591589)
    ·
      refine ⟨2883414330609780379610923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15378209763252162024591589 2883414330609780379610923)
      ·
        refine ⟨4325121495914670569416385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2883414330609780379610923 4325121495914670569416385)
        ·
          refine ⟨3243841121936002927062289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4325121495914670569416385 3243841121936002927062289)
          ·
            refine ⟨2432880841452002195296717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3243841121936002927062289 2432880841452002195296717)
            ·
              refine ⟨912330315544500823236269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2432880841452002195296717 912330315544500823236269)
              ·
                refine ⟨342123868329187808713601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 912330315544500823236269 342123868329187808713601)
                ·
                  refine ⟨256592901246890856535201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 342123868329187808713601 256592901246890856535201)
                  ·
                    rfl

theorem cell20_562177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 3, 2].length) (baseStart_562177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562177 prefixEnd_562177 := by exact prefixLift 562177
  have htrace : WordTrace (prefixWord ++ tailWord_562177) baseStart_562177 baseEnd_562177 := by
    simpa [prefixWord, tailWord_562177, baseEnd_562177] using wordTrace_append hprefix tailTrace_562177
  have hstable : (prefixWord ++ tailWord_562177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562177).length < 2 ^ (prefixWord ++ tailWord_562177).sum := by decide
  have hdescent : baseEnd_562177 < baseStart_562177 := by decide
  rcases family_descends (prefixWord ++ tailWord_562177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562188 : List Nat := [2, 2, 1, 2, 3, 2, 8]
def baseStart_562188 : Nat := 118140960795 + 562188 * 2 ^ 59
def prefixEnd_562188 : Nat := 4983230072969 + 3 ^ 40 * 562188 * 2
def baseEnd_562188 : Nat := 28510880216291523018721

theorem tailTrace_562188 : CollatzResearch.WordTrace tailWord_562188 prefixEnd_562188 28510880216291523018721 := by
  unfold tailWord_562188
  simp only [CollatzResearch.WordTrace]
  refine ⟨10252340443648182455719609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13669787258197576607626145 10252340443648182455719609)
  ·
    refine ⟨7689255332736136841789707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10252340443648182455719609 7689255332736136841789707)
    ·
      refine ⟨11533882999104205262684561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7689255332736136841789707 11533882999104205262684561)
      ·
        refine ⟨8650412249328153947013421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11533882999104205262684561 8650412249328153947013421)
        ·
          refine ⟨3243904593498057730130033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8650412249328153947013421 3243904593498057730130033)
          ·
            refine ⟨2432928445123543297597525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3243904593498057730130033 2432928445123543297597525)
            ·
              refine ⟨28510880216291523018721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2432928445123543297597525 28510880216291523018721)
              ·
                rfl

theorem cell20_562188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 8].length) (baseStart_562188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562188 prefixEnd_562188 := by exact prefixLift 562188
  have htrace : WordTrace (prefixWord ++ tailWord_562188) baseStart_562188 baseEnd_562188 := by
    simpa [prefixWord, tailWord_562188, baseEnd_562188] using wordTrace_append hprefix tailTrace_562188
  have hstable : (prefixWord ++ tailWord_562188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562188).length < 2 ^ (prefixWord ++ tailWord_562188).sum := by decide
  have hdescent : baseEnd_562188 < baseStart_562188 := by decide
  rcases family_descends (prefixWord ++ tailWord_562188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562208 : List Nat := [2, 1, 1, 7, 1, 1, 1, 3, 3]
def baseStart_562208 : Nat := 118140960795 + 562208 * 2 ^ 59
def prefixEnd_562208 : Nat := 4983230072969 + 3 ^ 40 * 562208 * 2
def baseEnd_562208 : Nat := 256607050491592526501741

theorem tailTrace_562208 : CollatzResearch.WordTrace tailWord_562208 prefixEnd_562208 256607050491592526501741 := by
  unfold tailWord_562208
  simp only [CollatzResearch.WordTrace]
  refine ⟨10252705173611954163583639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13670273564815938884778185 10252705173611954163583639)
  ·
    refine ⟨15379057760417931245375459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10252705173611954163583639 15379057760417931245375459)
    ·
      refine ⟨23068586640626896868063189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15379057760417931245375459 23068586640626896868063189)
      ·
        refine ⟨540669999389692895345231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 23068586640626896868063189 540669999389692895345231)
        ·
          refine ⟨811004999084539343017847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 540669999389692895345231 811004999084539343017847)
          ·
            refine ⟨1216507498626809014526771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 811004999084539343017847 1216507498626809014526771)
            ·
              refine ⟨1824761247940213521790157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1216507498626809014526771 1824761247940213521790157)
              ·
                refine ⟨684285467977580070671309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1824761247940213521790157 684285467977580070671309)
                ·
                  refine ⟨256607050491592526501741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 684285467977580070671309 256607050491592526501741)
                  ·
                    rfl

theorem cell20_562208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 3].length) (baseStart_562208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562208 prefixEnd_562208 := by exact prefixLift 562208
  have htrace : WordTrace (prefixWord ++ tailWord_562208) baseStart_562208 baseEnd_562208 := by
    simpa [prefixWord, tailWord_562208, baseEnd_562208] using wordTrace_append hprefix tailTrace_562208
  have hstable : (prefixWord ++ tailWord_562208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562208).length < 2 ^ (prefixWord ++ tailWord_562208).sum := by decide
  have hdescent : baseEnd_562208 < baseStart_562208 := by decide
  rcases family_descends (prefixWord ++ tailWord_562208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562226 : List Nat := [3, 2, 1, 1, 2, 2, 1, 8]
def baseStart_562226 : Nat := 118140960795 + 562226 * 2 ^ 59
def prefixEnd_562226 : Nat := 4983230072969 + 3 ^ 40 * 562226 * 2
def baseEnd_562226 : Nat := 85538422060688154633889

theorem tailTrace_562226 : CollatzResearch.WordTrace tailWord_562226 prefixEnd_562226 85538422060688154633889 := by
  unfold tailWord_562226
  simp only [CollatzResearch.WordTrace]
  refine ⟨5126516715289674350330633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13670711240772464934215021 5126516715289674350330633)
  ·
    refine ⟨3844887536467255762747975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5126516715289674350330633 3844887536467255762747975)
    ·
      refine ⟨5767331304700883644121963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3844887536467255762747975 5767331304700883644121963)
      ·
        refine ⟨8650996957051325466182945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5767331304700883644121963 8650996957051325466182945)
        ·
          refine ⟨6488247717788494099637209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8650996957051325466182945 6488247717788494099637209)
          ·
            refine ⟨4866185788341370574727907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6488247717788494099637209 4866185788341370574727907)
            ·
              refine ⟨7299278682512055862091861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4866185788341370574727907 7299278682512055862091861)
              ·
                refine ⟨85538422060688154633889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7299278682512055862091861 85538422060688154633889)
                ·
                  rfl

theorem cell20_562226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_562226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562226 prefixEnd_562226 := by exact prefixLift 562226
  have htrace : WordTrace (prefixWord ++ tailWord_562226) baseStart_562226 baseEnd_562226 := by
    simpa [prefixWord, tailWord_562226, baseEnd_562226] using wordTrace_append hprefix tailTrace_562226
  have hstable : (prefixWord ++ tailWord_562226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562226).length < 2 ^ (prefixWord ++ tailWord_562226).sum := by decide
  have hdescent : baseEnd_562226 < baseStart_562226 := by decide
  rcases family_descends (prefixWord ++ tailWord_562226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562246 : List Nat := [6, 1, 1, 1, 1, 2, 1, 4, 3]
def baseStart_562246 : Nat := 118140960795 + 562246 * 2 ^ 59
def prefixEnd_562246 : Nat := 4983230072969 + 3 ^ 40 * 562246 * 2
def baseEnd_562246 : Nat := 256624394727033283234919

theorem tailTrace_562246 : CollatzResearch.WordTrace tailWord_562246 prefixEnd_562246 256624394727033283234919 := by
  unfold tailWord_562246
  simp only [CollatzResearch.WordTrace]
  refine ⟨640837385033945025532831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13671197547390827211367061 640837385033945025532831)
  ·
    refine ⟨961256077550917538299247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 640837385033945025532831 961256077550917538299247)
    ·
      refine ⟨1441884116326376307448871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 961256077550917538299247 1441884116326376307448871)
      ·
        refine ⟨2162826174489564461173307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1441884116326376307448871 2162826174489564461173307)
        ·
          refine ⟨3244239261734346691759961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2162826174489564461173307 3244239261734346691759961)
          ·
            refine ⟨2433179446300760018819971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3244239261734346691759961 2433179446300760018819971)
            ·
              refine ⟨3649769169451140028229957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2433179446300760018819971 3649769169451140028229957)
              ·
                refine ⟨684331719272088755293117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3649769169451140028229957 684331719272088755293117)
                ·
                  refine ⟨256624394727033283234919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 684331719272088755293117 256624394727033283234919)
                  ·
                    rfl

theorem cell20_562246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_562246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562246 prefixEnd_562246 := by exact prefixLift 562246
  have htrace : WordTrace (prefixWord ++ tailWord_562246) baseStart_562246 baseEnd_562246 := by
    simpa [prefixWord, tailWord_562246, baseEnd_562246] using wordTrace_append hprefix tailTrace_562246
  have hstable : (prefixWord ++ tailWord_562246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562246).length < 2 ^ (prefixWord ++ tailWord_562246).sum := by decide
  have hdescent : baseEnd_562246 < baseStart_562246 := by decide
  rcases family_descends (prefixWord ++ tailWord_562246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562250 : List Nat := [3, 1, 2, 1, 1, 2, 3, 4, 3]
def baseStart_562250 : Nat := 118140960795 + 562250 * 2 ^ 59
def prefixEnd_562250 : Nat := 4983230072969 + 3 ^ 40 * 562250 * 2
def baseEnd_562250 : Nat := 256626220436027047101569

theorem tailTrace_562250 : CollatzResearch.WordTrace tailWord_562250 prefixEnd_562250 256626220436027047101569 := by
  unfold tailWord_562250
  simp only [CollatzResearch.WordTrace]
  refine ⟨5126735553267937375049051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13671294808714499666797469 5126735553267937375049051)
  ·
    refine ⟨7690103329901906062573577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5126735553267937375049051 7690103329901906062573577)
    ·
      refine ⟨5767577497426429546930183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7690103329901906062573577 5767577497426429546930183)
      ·
        refine ⟨8651366246139644320395275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5767577497426429546930183 8651366246139644320395275)
        ·
          refine ⟨12977049369209466480592913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8651366246139644320395275 12977049369209466480592913)
          ·
            refine ⟨9732787026907099860444685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12977049369209466480592913 9732787026907099860444685)
            ·
              refine ⟨3649795135090162447666757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9732787026907099860444685 3649795135090162447666757)
              ·
                refine ⟨684336587829405458937517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3649795135090162447666757 684336587829405458937517)
                ·
                  refine ⟨256626220436027047101569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 684336587829405458937517 256626220436027047101569)
                  ·
                    rfl

theorem cell20_562250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_562250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562250 prefixEnd_562250 := by exact prefixLift 562250
  have htrace : WordTrace (prefixWord ++ tailWord_562250) baseStart_562250 baseEnd_562250 := by
    simpa [prefixWord, tailWord_562250, baseEnd_562250] using wordTrace_append hprefix tailTrace_562250
  have hstable : (prefixWord ++ tailWord_562250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562250).length < 2 ^ (prefixWord ++ tailWord_562250).sum := by decide
  have hdescent : baseEnd_562250 < baseStart_562250 := by decide
  rcases family_descends (prefixWord ++ tailWord_562250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562270 : List Nat := [4, 4, 1, 1, 1, 2, 1, 2, 4]
def baseStart_562270 : Nat := 118140960795 + 562270 * 2 ^ 59
def prefixEnd_562270 : Nat := 4983230072969 + 3 ^ 40 * 562270 * 2
def baseEnd_562270 : Nat := 256635348980995866434821

theorem tailTrace_562270 : CollatzResearch.WordTrace tailWord_562270 prefixEnd_562270 256635348980995866434821 := by
  unfold tailWord_562270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2563458959124911614490533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13671781115332861943949509 2563458959124911614490533)
  ·
    refine ⟨480648554835920927716975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2563458959124911614490533 480648554835920927716975)
    ·
      refine ⟨720972832253881391575463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 480648554835920927716975 720972832253881391575463)
      ·
        refine ⟨1081459248380822087363195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 720972832253881391575463 1081459248380822087363195)
        ·
          refine ⟨1622188872571233131044793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1081459248380822087363195 1622188872571233131044793)
          ·
            refine ⟨1216641654428424848283595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1622188872571233131044793 1216641654428424848283595)
            ·
              refine ⟨1824962481642637272425393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1216641654428424848283595 1824962481642637272425393)
              ·
                refine ⟨1368721861231977954319045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1824962481642637272425393 1368721861231977954319045)
                ·
                  refine ⟨256635348980995866434821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1368721861231977954319045 256635348980995866434821)
                  ·
                    rfl

theorem cell20_562270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_562270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562270 prefixEnd_562270 := by exact prefixLift 562270
  have htrace : WordTrace (prefixWord ++ tailWord_562270) baseStart_562270 baseEnd_562270 := by
    simpa [prefixWord, tailWord_562270, baseEnd_562270] using wordTrace_append hprefix tailTrace_562270
  have hstable : (prefixWord ++ tailWord_562270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562270).length < 2 ^ (prefixWord ++ tailWord_562270).sum := by decide
  have hdescent : baseEnd_562270 < baseStart_562270 := by decide
  rcases family_descends (prefixWord ++ tailWord_562270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562274 : List Nat := [3, 3, 2, 2, 1, 1, 1, 1, 6]
def baseStart_562274 : Nat := 118140960795 + 562274 * 2 ^ 59
def prefixEnd_562274 : Nat := 4983230072969 + 3 ^ 40 * 562274 * 2
def baseEnd_562274 : Nat := 256637174689989630301471

theorem tailTrace_562274 : CollatzResearch.WordTrace tailWord_562274 prefixEnd_562274 256637174689989630301471 := by
  unfold tailWord_562274
  simp only [CollatzResearch.WordTrace]
  refine ⟨5126954391246200399767469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13671878376656534399379917 5126954391246200399767469)
  ·
    refine ⟨1922607896717325149912801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5126954391246200399767469 1922607896717325149912801)
    ·
      refine ⟨1441955922537993862434601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1922607896717325149912801 1441955922537993862434601)
      ·
        refine ⟨1081466941903495396825951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1441955922537993862434601 1081466941903495396825951)
        ·
          refine ⟨1622200412855243095238927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1081466941903495396825951 1622200412855243095238927)
          ·
            refine ⟨2433300619282864642858391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1622200412855243095238927 2433300619282864642858391)
            ·
              refine ⟨3649950928924296964287587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2433300619282864642858391 3649950928924296964287587)
              ·
                refine ⟨5474926393386445446431381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3649950928924296964287587 5474926393386445446431381)
                ·
                  refine ⟨256637174689989630301471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5474926393386445446431381 256637174689989630301471)
                  ·
                    rfl

theorem cell20_562274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_562274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562274 prefixEnd_562274 := by exact prefixLift 562274
  have htrace : WordTrace (prefixWord ++ tailWord_562274) baseStart_562274 baseEnd_562274 := by
    simpa [prefixWord, tailWord_562274, baseEnd_562274] using wordTrace_append hprefix tailTrace_562274
  have hstable : (prefixWord ++ tailWord_562274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562274).length < 2 ^ (prefixWord ++ tailWord_562274).sum := by decide
  have hdescent : baseEnd_562274 < baseStart_562274 := by decide
  rcases family_descends (prefixWord ++ tailWord_562274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562281 : List Nat := [1, 2, 1, 1, 1, 7, 3, 4]
def baseStart_562281 : Nat := 118140960795 + 562281 * 2 ^ 59
def prefixEnd_562281 : Nat := 4983230072969 + 3 ^ 40 * 562281 * 2
def baseEnd_562281 : Nat := 85546789893576239022703

theorem tailTrace_562281 : CollatzResearch.WordTrace tailWord_562281 prefixEnd_562281 85546789893576239022703 := by
  unfold tailWord_562281
  simp only [CollatzResearch.WordTrace]
  refine ⟨20508072875959441794574697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13672048583972961196383131 20508072875959441794574697)
  ·
    refine ⟨15381054656969581345931023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20508072875959441794574697 15381054656969581345931023)
    ·
      refine ⟨23071581985454372018896535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15381054656969581345931023 23071581985454372018896535)
      ·
        refine ⟨34607372978181558028344803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23071581985454372018896535 34607372978181558028344803)
        ·
          refine ⟨51911059467272337042517205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34607372978181558028344803 51911059467272337042517205)
          ·
            refine ⟨1216665456264195399433997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 51911059467272337042517205 1216665456264195399433997)
            ·
              refine ⟨456249546099073274787749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1216665456264195399433997 456249546099073274787749)
              ·
                refine ⟨85546789893576239022703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 456249546099073274787749 85546789893576239022703)
                ·
                  rfl

theorem cell20_562281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 4].length) (baseStart_562281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562281 prefixEnd_562281 := by exact prefixLift 562281
  have htrace : WordTrace (prefixWord ++ tailWord_562281) baseStart_562281 baseEnd_562281 := by
    simpa [prefixWord, tailWord_562281, baseEnd_562281] using wordTrace_append hprefix tailTrace_562281
  have hstable : (prefixWord ++ tailWord_562281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562281).length < 2 ^ (prefixWord ++ tailWord_562281).sum := by decide
  have hdescent : baseEnd_562281 < baseStart_562281 := by decide
  rcases family_descends (prefixWord ++ tailWord_562281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562305 : List Nat := [1, 2, 4, 2, 2, 1, 3, 2, 3]
def baseStart_562305 : Nat := 118140960795 + 562305 * 2 ^ 59
def prefixEnd_562305 : Nat := 4983230072969 + 3 ^ 40 * 562305 * 2
def baseEnd_562305 : Nat := 256651323934691300268011

theorem tailTrace_562305 : CollatzResearch.WordTrace tailWord_562305 prefixEnd_562305 256651323934691300268011 := by
  unfold tailWord_562305
  simp only [CollatzResearch.WordTrace]
  refine ⟨20508948227872493893448369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13672632151914995928965579 20508948227872493893448369)
  ·
    refine ⟨15381711170904370420086277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20508948227872493893448369 15381711170904370420086277)
    ·
      refine ⟨2884070844544569453766177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15381711170904370420086277 2884070844544569453766177)
      ·
        refine ⟨2163053133408427090324633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2884070844544569453766177 2163053133408427090324633)
        ·
          refine ⟨1622289850056320317743475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2163053133408427090324633 1622289850056320317743475)
          ·
            refine ⟨2433434775084480476615213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1622289850056320317743475 2433434775084480476615213)
            ·
              refine ⟨912538040656680178730705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2433434775084480476615213 912538040656680178730705)
              ·
                refine ⟨684403530492510134048029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 912538040656680178730705 684403530492510134048029)
                ·
                  refine ⟨256651323934691300268011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 684403530492510134048029 256651323934691300268011)
                  ·
                    rfl

theorem cell20_562305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 3].length) (baseStart_562305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562305 prefixEnd_562305 := by exact prefixLift 562305
  have htrace : WordTrace (prefixWord ++ tailWord_562305) baseStart_562305 baseEnd_562305 := by
    simpa [prefixWord, tailWord_562305, baseEnd_562305] using wordTrace_append hprefix tailTrace_562305
  have hstable : (prefixWord ++ tailWord_562305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562305).length < 2 ^ (prefixWord ++ tailWord_562305).sum := by decide
  have hdescent : baseEnd_562305 < baseStart_562305 := by decide
  rcases family_descends (prefixWord ++ tailWord_562305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562322 : List Nat := [3, 2, 3, 1, 1, 3, 3, 1, 3]
def baseStart_562322 : Nat := 118140960795 + 562322 * 2 ^ 59
def prefixEnd_562322 : Nat := 4983230072969 + 3 ^ 40 * 562322 * 2
def baseEnd_562322 : Nat := 256659083197914796701275

theorem tailTrace_562322 : CollatzResearch.WordTrace tailWord_562322 prefixEnd_562322 256659083197914796701275 := by
  unfold tailWord_562322
  simp only [CollatzResearch.WordTrace]
  refine ⟨5127392067202726449204305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13673045512540603864544813 5127392067202726449204305)
  ·
    refine ⟨3845544050402044836903229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5127392067202726449204305 3845544050402044836903229)
    ·
      refine ⟨1442079018900766813838711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3845544050402044836903229 1442079018900766813838711)
      ·
        refine ⟨2163118528351150220758067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1442079018900766813838711 2163118528351150220758067)
        ·
          refine ⟨3244677792526725331137101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2163118528351150220758067 3244677792526725331137101)
          ·
            refine ⟨1216754172197521999176413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3244677792526725331137101 1216754172197521999176413)
            ·
              refine ⟨456282814574070749691155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1216754172197521999176413 456282814574070749691155)
              ·
                refine ⟨684424221861106124536733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 456282814574070749691155 684424221861106124536733)
                ·
                  refine ⟨256659083197914796701275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 684424221861106124536733 256659083197914796701275)
                  ·
                    rfl

theorem cell20_562322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_562322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562322 prefixEnd_562322 := by exact prefixLift 562322
  have htrace : WordTrace (prefixWord ++ tailWord_562322) baseStart_562322 baseEnd_562322 := by
    simpa [prefixWord, tailWord_562322, baseEnd_562322] using wordTrace_append hprefix tailTrace_562322
  have hstable : (prefixWord ++ tailWord_562322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562322).length < 2 ^ (prefixWord ++ tailWord_562322).sum := by decide
  have hdescent : baseEnd_562322 < baseStart_562322 := by decide
  rcases family_descends (prefixWord ++ tailWord_562322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562333 : List Nat := [1, 4, 2, 1, 1, 2, 1, 4, 4]
def baseStart_562333 : Nat := 118140960795 + 562333 * 2 ^ 59
def prefixEnd_562333 : Nat := 4983230072969 + 3 ^ 40 * 562333 * 2
def baseEnd_562333 : Nat := 256664103897647647334563

theorem tailTrace_562333 : CollatzResearch.WordTrace tailWord_562333 prefixEnd_562333 256664103897647647334563 := by
  unfold tailWord_562333
  simp only [CollatzResearch.WordTrace]
  refine ⟨20509969471771054675467653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13673312981180703116978435 20509969471771054675467653)
  ·
    refine ⟨3845619275957072751650185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20509969471771054675467653 3845619275957072751650185)
    ·
      refine ⟨2884214456967804563737639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3845619275957072751650185 2884214456967804563737639)
      ·
        refine ⟨4326321685451706845606459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2884214456967804563737639 4326321685451706845606459)
        ·
          refine ⟨6489482528177560268409689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4326321685451706845606459 6489482528177560268409689)
          ·
            refine ⟨4867111896133170201307267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6489482528177560268409689 4867111896133170201307267)
            ·
              refine ⟨7300667844199755301960901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4867111896133170201307267 7300667844199755301960901)
              ·
                refine ⟨1368875220787454119117669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7300667844199755301960901 1368875220787454119117669)
                ·
                  refine ⟨256664103897647647334563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1368875220787454119117669 256664103897647647334563)
                  ·
                    rfl

theorem cell20_562333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_562333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562333 prefixEnd_562333 := by exact prefixLift 562333
  have htrace : WordTrace (prefixWord ++ tailWord_562333) baseStart_562333 baseEnd_562333 := by
    simpa [prefixWord, tailWord_562333, baseEnd_562333] using wordTrace_append hprefix tailTrace_562333
  have hstable : (prefixWord ++ tailWord_562333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562333).length < 2 ^ (prefixWord ++ tailWord_562333).sum := by decide
  have hdescent : baseEnd_562333 < baseStart_562333 := by decide
  rcases family_descends (prefixWord ++ tailWord_562333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562346 : List Nat := [3, 1, 5, 1, 1, 1, 3, 3, 2]
def baseStart_562346 : Nat := 118140960795 + 562346 * 2 ^ 59
def prefixEnd_562346 : Nat := 4983230072969 + 3 ^ 40 * 562346 * 2
def baseEnd_562346 : Nat := 256670037451877379901177

theorem tailTrace_562346 : CollatzResearch.WordTrace tailWord_562346 prefixEnd_562346 256670037451877379901177 := by
  unfold tailWord_562346
  simp only [CollatzResearch.WordTrace]
  refine ⟨5127610905180989473922723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13673629080482638597127261 5127610905180989473922723)
  ·
    refine ⟨7691416357771484210884085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5127610905180989473922723 7691416357771484210884085)
    ·
      refine ⟨721070283541076644770383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7691416357771484210884085 721070283541076644770383)
      ·
        refine ⟨1081605425311614967155575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 721070283541076644770383 1081605425311614967155575)
        ·
          refine ⟨1622408137967422450733363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1081605425311614967155575 1622408137967422450733363)
          ·
            refine ⟨2433612206951133676100045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1622408137967422450733363 2433612206951133676100045)
            ·
              refine ⟨912604577606675128537517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2433612206951133676100045 912604577606675128537517)
              ·
                refine ⟨342226716602503173201569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 912604577606675128537517 342226716602503173201569)
                ·
                  refine ⟨256670037451877379901177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 342226716602503173201569 256670037451877379901177)
                  ·
                    rfl

theorem cell20_562346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 3, 2].length) (baseStart_562346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562346 prefixEnd_562346 := by exact prefixLift 562346
  have htrace : WordTrace (prefixWord ++ tailWord_562346) baseStart_562346 baseEnd_562346 := by
    simpa [prefixWord, tailWord_562346, baseEnd_562346] using wordTrace_append hprefix tailTrace_562346
  have hstable : (prefixWord ++ tailWord_562346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562346).length < 2 ^ (prefixWord ++ tailWord_562346).sum := by decide
  have hdescent : baseEnd_562346 < baseStart_562346 := by decide
  rcases family_descends (prefixWord ++ tailWord_562346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562364 : List Nat := [2, 2, 2, 3, 2, 1, 2, 1, 5]
def baseStart_562364 : Nat := 118140960795 + 562364 * 2 ^ 59
def prefixEnd_562364 : Nat := 4983230072969 + 3 ^ 40 * 562364 * 2
def baseEnd_562364 : Nat := 256678253142349317301103

theorem tailTrace_562364 : CollatzResearch.WordTrace tailWord_562364 prefixEnd_562364 256678253142349317301103 := by
  unfold tailWord_562364
  simp only [CollatzResearch.WordTrace]
  refine ⟨10255550067329373484923073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13674066756439164646564097 10255550067329373484923073)
  ·
    refine ⟨7691662550497030113692305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10255550067329373484923073 7691662550497030113692305)
    ·
      refine ⟨5768746912872772585269229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7691662550497030113692305 5768746912872772585269229)
      ·
        refine ⟨2163280092327289719475961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5768746912872772585269229 2163280092327289719475961)
        ·
          refine ⟨1622460069245467289606971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2163280092327289719475961 1622460069245467289606971)
          ·
            refine ⟨2433690103868200934410457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1622460069245467289606971 2433690103868200934410457)
            ·
              refine ⟨1825267577901150700807843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2433690103868200934410457 1825267577901150700807843)
              ·
                refine ⟨2737901366851726051211765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1825267577901150700807843 2737901366851726051211765)
                ·
                  refine ⟨256678253142349317301103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2737901366851726051211765 256678253142349317301103)
                  ·
                    rfl

theorem cell20_562364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_562364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562364 prefixEnd_562364 := by exact prefixLift 562364
  have htrace : WordTrace (prefixWord ++ tailWord_562364) baseStart_562364 baseEnd_562364 := by
    simpa [prefixWord, tailWord_562364, baseEnd_562364] using wordTrace_append hprefix tailTrace_562364
  have hstable : (prefixWord ++ tailWord_562364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562364).length < 2 ^ (prefixWord ++ tailWord_562364).sum := by decide
  have hdescent : baseEnd_562364 < baseStart_562364 := by decide
  rcases family_descends (prefixWord ++ tailWord_562364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562378 : List Nat := [3, 1, 2, 1, 3, 2, 1, 7]
def baseStart_562378 : Nat := 118140960795 + 562378 * 2 ^ 59
def prefixEnd_562378 : Nat := 4983230072969 + 3 ^ 40 * 562378 * 2
def baseEnd_562378 : Nat := 85561547707942496944793

theorem tailTrace_562378 : CollatzResearch.WordTrace tailWord_562378 prefixEnd_562378 85561547707942496944793 := by
  unfold tailWord_562378
  simp only [CollatzResearch.WordTrace]
  refine ⟨5127902689152006840213947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13674407171072018240570525 5127902689152006840213947)
  ·
    refine ⟨7691854033728010260320921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5127902689152006840213947 7691854033728010260320921)
    ·
      refine ⟨5768890525296007695240691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7691854033728010260320921 5768890525296007695240691)
      ·
        refine ⟨8653335787944011542861037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5768890525296007695240691 8653335787944011542861037)
        ·
          refine ⟨3245000920479004328572889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8653335787944011542861037 3245000920479004328572889)
          ·
            refine ⟨2433750690359253246429667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3245000920479004328572889 2433750690359253246429667)
            ·
              refine ⟨3650626035538879869644501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2433750690359253246429667 3650626035538879869644501)
              ·
                refine ⟨85561547707942496944793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3650626035538879869644501 85561547707942496944793)
                ·
                  rfl

theorem cell20_562378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_562378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562378 prefixEnd_562378 := by exact prefixLift 562378
  have htrace : WordTrace (prefixWord ++ tailWord_562378) baseStart_562378 baseEnd_562378 := by
    simpa [prefixWord, tailWord_562378, baseEnd_562378] using wordTrace_append hprefix tailTrace_562378
  have hstable : (prefixWord ++ tailWord_562378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562378).length < 2 ^ (prefixWord ++ tailWord_562378).sum := by decide
  have hdescent : baseEnd_562378 < baseStart_562378 := by decide
  rcases family_descends (prefixWord ++ tailWord_562378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562426 : List Nat := [3, 1, 1, 1, 1, 4, 3, 4, 2]
def baseStart_562426 : Nat := 118140960795 + 562426 * 2 ^ 59
def prefixEnd_562426 : Nat := 4983230072969 + 3 ^ 40 * 562426 * 2
def baseEnd_562426 : Nat := 256706551631752657234183

theorem tailTrace_562426 : CollatzResearch.WordTrace tailWord_562426 prefixEnd_562426 256706551631752657234183 := by
  unfold tailWord_562426
  simp only [CollatzResearch.WordTrace]
  refine ⟨5128340365108532889650783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13675574306956087705735421 5128340365108532889650783)
  ·
    refine ⟨7692510547662799334476175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5128340365108532889650783 7692510547662799334476175)
    ·
      refine ⟨11538765821494199001714263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7692510547662799334476175 11538765821494199001714263)
      ·
        refine ⟨17308148732241298502571395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11538765821494199001714263 17308148732241298502571395)
        ·
          refine ⟨25962223098361947753857093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17308148732241298502571395 25962223098361947753857093)
          ·
            refine ⟨4867916830942865203848205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25962223098361947753857093 4867916830942865203848205)
            ·
              refine ⟨1825468811603574451443077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4867916830942865203848205 1825468811603574451443077)
              ·
                refine ⟨342275402175670209645577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1825468811603574451443077 342275402175670209645577)
                ·
                  refine ⟨256706551631752657234183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 342275402175670209645577 256706551631752657234183)
                  ·
                    rfl

theorem cell20_562426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 4, 2].length) (baseStart_562426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562426 prefixEnd_562426 := by exact prefixLift 562426
  have htrace : WordTrace (prefixWord ++ tailWord_562426) baseStart_562426 baseEnd_562426 := by
    simpa [prefixWord, tailWord_562426, baseEnd_562426] using wordTrace_append hprefix tailTrace_562426
  have hstable : (prefixWord ++ tailWord_562426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562426).length < 2 ^ (prefixWord ++ tailWord_562426).sum := by decide
  have hdescent : baseEnd_562426 < baseStart_562426 := by decide
  rcases family_descends (prefixWord ++ tailWord_562426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562433 : List Nat := [1, 2, 4, 1, 1, 5, 1, 5]
def baseStart_562433 : Nat := 118140960795 + 562433 * 2 ^ 59
def prefixEnd_562433 : Nat := 4983230072969 + 3 ^ 40 * 562433 * 2
def baseEnd_562433 : Nat := 85569915540830581333607

theorem tailTrace_562433 : CollatzResearch.WordTrace tailWord_562433 prefixEnd_562433 85569915540830581333607 := by
  unfold tailWord_562433
  simp only [CollatzResearch.WordTrace]
  refine ⟨20513616771408771754107953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13675744514272514502738635 20513616771408771754107953)
  ·
    refine ⟨15385212578556578815580965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20513616771408771754107953 15385212578556578815580965)
    ·
      refine ⟨2884727358479358527921431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15385212578556578815580965 2884727358479358527921431)
      ·
        refine ⟨4327091037719037791882147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2884727358479358527921431 4327091037719037791882147)
        ·
          refine ⟨6490636556578556687823221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4327091037719037791882147 6490636556578556687823221)
          ·
            refine ⟨608497177179239689483427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6490636556578556687823221 608497177179239689483427)
            ·
              refine ⟨912745765768859534225141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 608497177179239689483427 912745765768859534225141)
              ·
                refine ⟨85569915540830581333607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 912745765768859534225141 85569915540830581333607)
                ·
                  rfl

theorem cell20_562433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 5].length) (baseStart_562433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562433 prefixEnd_562433 := by exact prefixLift 562433
  have htrace : WordTrace (prefixWord ++ tailWord_562433) baseStart_562433 baseEnd_562433 := by
    simpa [prefixWord, tailWord_562433, baseEnd_562433] using wordTrace_append hprefix tailTrace_562433
  have hstable : (prefixWord ++ tailWord_562433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562433).length < 2 ^ (prefixWord ++ tailWord_562433).sum := by decide
  have hdescent : baseEnd_562433 < baseStart_562433 := by decide
  rcases family_descends (prefixWord ++ tailWord_562433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562474 : List Nat := [3, 1, 4, 2, 1, 3, 1, 2, 3]
def baseStart_562474 : Nat := 118140960795 + 562474 * 2 ^ 59
def prefixEnd_562474 : Nat := 4983230072969 + 3 ^ 40 * 562474 * 2
def baseEnd_562474 : Nat := 256728460139677823633987

theorem tailTrace_562474 : CollatzResearch.WordTrace tailWord_562474 prefixEnd_562474 256728460139677823633987 := by
  unfold tailWord_562474
  simp only [CollatzResearch.WordTrace]
  refine ⟨5128778041065058939087619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13676741442840157170900317 5128778041065058939087619)
  ·
    refine ⟨7693167061597588408631429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5128778041065058939087619 7693167061597588408631429)
    ·
      refine ⟨1442468824049547826618393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7693167061597588408631429 1442468824049547826618393)
      ·
        refine ⟨1081851618037160869963795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1442468824049547826618393 1081851618037160869963795)
        ·
          refine ⟨1622777427055741304945693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1081851618037160869963795 1622777427055741304945693)
          ·
            refine ⟨608541535145902989354635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1622777427055741304945693 608541535145902989354635)
            ·
              refine ⟨912812302718854484031953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 608541535145902989354635 912812302718854484031953)
              ·
                refine ⟨684609227039140863023965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 912812302718854484031953 684609227039140863023965)
                ·
                  refine ⟨256728460139677823633987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 684609227039140863023965 256728460139677823633987)
                  ·
                    rfl

theorem cell20_562474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 3].length) (baseStart_562474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562474 prefixEnd_562474 := by exact prefixLift 562474
  have htrace : WordTrace (prefixWord ++ tailWord_562474) baseStart_562474 baseEnd_562474 := by
    simpa [prefixWord, tailWord_562474, baseEnd_562474] using wordTrace_append hprefix tailTrace_562474
  have hstable : (prefixWord ++ tailWord_562474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562474).length < 2 ^ (prefixWord ++ tailWord_562474).sum := by decide
  have hdescent : baseEnd_562474 < baseStart_562474 := by decide
  rcases family_descends (prefixWord ++ tailWord_562474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562485 : List Nat := [1, 3, 3, 1, 2, 2, 1, 3, 4]
def baseStart_562485 : Nat := 118140960795 + 562485 * 2 ^ 59
def prefixEnd_562485 : Nat := 4983230072969 + 3 ^ 40 * 562485 * 2
def baseEnd_562485 : Nat := 256733480839410674267275

theorem tailTrace_562485 : CollatzResearch.WordTrace tailWord_562485 prefixEnd_562485 256733480839410674267275 := by
  unfold tailWord_562485
  simp only [CollatzResearch.WordTrace]
  refine ⟨20515513367220384635000909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13677008911480256423333939 20515513367220384635000909)
  ·
    refine ⟨7693317512707644238125341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20515513367220384635000909 7693317512707644238125341)
    ·
      refine ⟨2884994067265366589297003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7693317512707644238125341 2884994067265366589297003)
      ·
        refine ⟨4327491100898049883945505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2884994067265366589297003 4327491100898049883945505)
        ·
          refine ⟨3245618325673537412959129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4327491100898049883945505 3245618325673537412959129)
          ·
            refine ⟨2434213744255153059719347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3245618325673537412959129 2434213744255153059719347)
            ·
              refine ⟨3651320616382729589579021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2434213744255153059719347 3651320616382729589579021)
              ·
                refine ⟨1369245231143523596092133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3651320616382729589579021 1369245231143523596092133)
                ·
                  refine ⟨256733480839410674267275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1369245231143523596092133 256733480839410674267275)
                  ·
                    rfl

theorem cell20_562485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_562485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562485 prefixEnd_562485 := by exact prefixLift 562485
  have htrace : WordTrace (prefixWord ++ tailWord_562485) baseStart_562485 baseEnd_562485 := by
    simpa [prefixWord, tailWord_562485, baseEnd_562485] using wordTrace_append hprefix tailTrace_562485
  have hstable : (prefixWord ++ tailWord_562485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562485).length < 2 ^ (prefixWord ++ tailWord_562485).sum := by decide
  have hdescent : baseEnd_562485 < baseStart_562485 := by decide
  rcases family_descends (prefixWord ++ tailWord_562485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562495 : List Nat := [1, 1, 2, 2, 4, 3, 3, 1, 3]
def baseStart_562495 : Nat := 118140960795 + 562495 * 2 ^ 59
def prefixEnd_562495 : Nat := 4983230072969 + 3 ^ 40 * 562495 * 2
def baseEnd_562495 : Nat := 256738045111895083933901

theorem tailTrace_562495 : CollatzResearch.WordTrace tailWord_562495 prefixEnd_562495 256738045111895083933901 := by
  unfold tailWord_562495
  simp only [CollatzResearch.WordTrace]
  refine ⟨20515878097184156342864939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13677252064789437561909959 20515878097184156342864939)
  ·
    refine ⟨30773817145776234514297409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20515878097184156342864939 30773817145776234514297409)
    ·
      refine ⟨23080362859332175885723057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30773817145776234514297409 23080362859332175885723057)
      ·
        refine ⟨17310272144499131914292293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23080362859332175885723057 17310272144499131914292293)
        ·
          refine ⟨3245676027093587233929805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17310272144499131914292293 3245676027093587233929805)
          ·
            refine ⟨1217128510160095212723677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3245676027093587233929805 1217128510160095212723677)
            ·
              refine ⟨456423191310035704771379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1217128510160095212723677 456423191310035704771379)
              ·
                refine ⟨684634786965053557157069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 456423191310035704771379 684634786965053557157069)
                ·
                  refine ⟨256738045111895083933901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 684634786965053557157069 256738045111895083933901)
                  ·
                    rfl

theorem cell20_562495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 3].length) (baseStart_562495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562495 prefixEnd_562495 := by exact prefixLift 562495
  have htrace : WordTrace (prefixWord ++ tailWord_562495) baseStart_562495 baseEnd_562495 := by
    simpa [prefixWord, tailWord_562495, baseEnd_562495] using wordTrace_append hprefix tailTrace_562495
  have hstable : (prefixWord ++ tailWord_562495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562495).length < 2 ^ (prefixWord ++ tailWord_562495).sum := by decide
  have hdescent : baseEnd_562495 < baseStart_562495 := by decide
  rcases family_descends (prefixWord ++ tailWord_562495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562519 : List Nat := [1, 1, 3, 2, 3, 4, 1, 3, 2]
def baseStart_562519 : Nat := 118140960795 + 562519 * 2 ^ 59
def prefixEnd_562519 : Nat := 4983230072969 + 3 ^ 40 * 562519 * 2
def baseEnd_562519 : Nat := 256748999365857667133803

theorem tailTrace_562519 : CollatzResearch.WordTrace tailWord_562519 prefixEnd_562519 256748999365857667133803 := by
  unfold tailWord_562519
  simp only [CollatzResearch.WordTrace]
  refine ⟨20516753449097208441738611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13677835632731472294492407 20516753449097208441738611)
  ·
    refine ⟨30775130173645812662607917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20516753449097208441738611 30775130173645812662607917)
    ·
      refine ⟨11540673815117179748477969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30775130173645812662607917 11540673815117179748477969)
      ·
        refine ⟨8655505361337884811358477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11540673815117179748477969 8655505361337884811358477)
        ·
          refine ⟨3245814510501706804259429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8655505361337884811358477 3245814510501706804259429)
          ·
            refine ⟨608590220719070025798643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3245814510501706804259429 608590220719070025798643)
            ·
              refine ⟨912885331078605038697965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 608590220719070025798643 912885331078605038697965)
              ·
                refine ⟨342331999154476889511737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 912885331078605038697965 342331999154476889511737)
                ·
                  refine ⟨256748999365857667133803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 342331999154476889511737 256748999365857667133803)
                  ·
                    rfl

theorem cell20_562519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 3, 2].length) (baseStart_562519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562519 prefixEnd_562519 := by exact prefixLift 562519
  have htrace : WordTrace (prefixWord ++ tailWord_562519) baseStart_562519 baseEnd_562519 := by
    simpa [prefixWord, tailWord_562519, baseEnd_562519] using wordTrace_append hprefix tailTrace_562519
  have hstable : (prefixWord ++ tailWord_562519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562519).length < 2 ^ (prefixWord ++ tailWord_562519).sum := by decide
  have hdescent : baseEnd_562519 < baseStart_562519 := by decide
  rcases family_descends (prefixWord ++ tailWord_562519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562536 : List Nat := [2, 1, 4, 2, 3, 1, 3, 2, 2]
def baseStart_562536 : Nat := 118140960795 + 562536 * 2 ^ 59
def prefixEnd_562536 : Nat := 4983230072969 + 3 ^ 40 * 562536 * 2
def baseEnd_562536 : Nat := 256756758629081163567067

theorem tailTrace_562536 : CollatzResearch.WordTrace tailWord_562536 prefixEnd_562536 256756758629081163567067 := by
  unfold tailWord_562536
  simp only [CollatzResearch.WordTrace]
  refine ⟨10258686745017810172553731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13678248993357080230071641 10258686745017810172553731)
  ·
    refine ⟨15388030117526715258830597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10258686745017810172553731 15388030117526715258830597)
    ·
      refine ⟨2885255647036259111030737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15388030117526715258830597 2885255647036259111030737)
      ·
        refine ⟨2163941735277194333273053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2885255647036259111030737 2163941735277194333273053)
        ·
          refine ⟨811478150728947874977395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2163941735277194333273053 811478150728947874977395)
          ·
            refine ⟨1217217226093421812466093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 811478150728947874977395 1217217226093421812466093)
            ·
              refine ⟨456456459785033179674785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1217217226093421812466093 456456459785033179674785)
              ·
                refine ⟨342342344838774884756089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 456456459785033179674785 342342344838774884756089)
                ·
                  refine ⟨256756758629081163567067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 342342344838774884756089 256756758629081163567067)
                  ·
                    rfl

theorem cell20_562536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 2, 2].length) (baseStart_562536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562536 prefixEnd_562536 := by exact prefixLift 562536
  have htrace : WordTrace (prefixWord ++ tailWord_562536) baseStart_562536 baseEnd_562536 := by
    simpa [prefixWord, tailWord_562536, baseEnd_562536] using wordTrace_append hprefix tailTrace_562536
  have hstable : (prefixWord ++ tailWord_562536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562536).length < 2 ^ (prefixWord ++ tailWord_562536).sum := by decide
  have hdescent : baseEnd_562536 < baseStart_562536 := by decide
  rcases family_descends (prefixWord ++ tailWord_562536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562540 : List Nat := [2, 2, 1, 1, 5, 3, 1, 1, 4]
def baseStart_562540 : Nat := 118140960795 + 562540 * 2 ^ 59
def prefixEnd_562540 : Nat := 4983230072969 + 3 ^ 40 * 562540 * 2
def baseEnd_562540 : Nat := 256758584338074927433717

theorem tailTrace_562540 : CollatzResearch.WordTrace tailWord_562540 prefixEnd_562540 256758584338074927433717 := by
  unfold tailWord_562540
  simp only [CollatzResearch.WordTrace]
  refine ⟨10258759691010564514126537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13678346254680752685502049 10258759691010564514126537)
  ·
    refine ⟨7694069768257923385594903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10258759691010564514126537 7694069768257923385594903)
    ·
      refine ⟨11541104652386885078392355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7694069768257923385594903 11541104652386885078392355)
      ·
        refine ⟨17311656978580327617588533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11541104652386885078392355 17311656978580327617588533)
        ·
          refine ⟨1622967841741905714148925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17311656978580327617588533 1622967841741905714148925)
          ·
            refine ⟨608612940653214642805847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1622967841741905714148925 608612940653214642805847)
            ·
              refine ⟨912919410979821964208771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 608612940653214642805847 912919410979821964208771)
              ·
                refine ⟨1369379116469732946313157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 912919410979821964208771 1369379116469732946313157)
                ·
                  refine ⟨256758584338074927433717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1369379116469732946313157 256758584338074927433717)
                  ·
                    rfl

theorem cell20_562540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 4].length) (baseStart_562540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562540 prefixEnd_562540 := by exact prefixLift 562540
  have htrace : WordTrace (prefixWord ++ tailWord_562540) baseStart_562540 baseEnd_562540 := by
    simpa [prefixWord, tailWord_562540, baseEnd_562540] using wordTrace_append hprefix tailTrace_562540
  have hstable : (prefixWord ++ tailWord_562540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562540).length < 2 ^ (prefixWord ++ tailWord_562540).sum := by decide
  have hdescent : baseEnd_562540 < baseStart_562540 := by decide
  rcases family_descends (prefixWord ++ tailWord_562540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562568 : List Nat := [2, 1, 3, 3, 1, 2, 2, 6]
def baseStart_562568 : Nat := 118140960795 + 562568 * 2 ^ 59
def prefixEnd_562568 : Nat := 4983230072969 + 3 ^ 40 * 562568 * 2
def baseEnd_562568 : Nat := 85590454767010424833423

theorem tailTrace_562568 : CollatzResearch.WordTrace tailWord_562568 prefixEnd_562568 85590454767010424833423 := by
  unfold tailWord_562568
  simp only [CollatzResearch.WordTrace]
  refine ⟨10259270312959844905136179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13679027083946459873514905 10259270312959844905136179)
  ·
    refine ⟨15388905469439767357704269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10259270312959844905136179 15388905469439767357704269)
    ·
      refine ⟨5770839551039912759139101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15388905469439767357704269 5770839551039912759139101)
      ·
        refine ⟨2164064831639967284677163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5770839551039912759139101 2164064831639967284677163)
        ·
          refine ⟨3246097247459950927015745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2164064831639967284677163 3246097247459950927015745)
          ·
            refine ⟨2434572935594963195261809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3246097247459950927015745 2434572935594963195261809)
            ·
              refine ⟨1825929701696222396446357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2434572935594963195261809 1825929701696222396446357)
              ·
                refine ⟨85590454767010424833423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1825929701696222396446357 85590454767010424833423)
                ·
                  rfl

theorem cell20_562568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 6].length) (baseStart_562568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562568 prefixEnd_562568 := by exact prefixLift 562568
  have htrace : WordTrace (prefixWord ++ tailWord_562568) baseStart_562568 baseEnd_562568 := by
    simpa [prefixWord, tailWord_562568, baseEnd_562568] using wordTrace_append hprefix tailTrace_562568
  have hstable : (prefixWord ++ tailWord_562568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562568).length < 2 ^ (prefixWord ++ tailWord_562568).sum := by decide
  have hdescent : baseEnd_562568 < baseStart_562568 := by decide
  rcases family_descends (prefixWord ++ tailWord_562568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562588 : List Nat := [2, 2, 3, 4, 1, 1, 2, 2, 3]
def baseStart_562588 : Nat := 118140960795 + 562588 * 2 ^ 59
def prefixEnd_562588 : Nat := 4983230072969 + 3 ^ 40 * 562588 * 2
def baseEnd_562588 : Nat := 256780492846000093833521

theorem tailTrace_562588 : CollatzResearch.WordTrace tailWord_562588 prefixEnd_562588 256780492846000093833521 := by
  unfold tailWord_562588
  simp only [CollatzResearch.WordTrace]
  refine ⟨10259635042923616613000209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13679513390564822150666945 10259635042923616613000209)
  ·
    refine ⟨7694726282192712459750157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10259635042923616613000209 7694726282192712459750157)
    ·
      refine ⟨2885522355822267172406309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7694726282192712459750157 2885522355822267172406309)
      ·
        refine ⟨541035441716675094826183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2885522355822267172406309 541035441716675094826183)
        ·
          refine ⟨811553162575012642239275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 541035441716675094826183 811553162575012642239275)
          ·
            refine ⟨1217329743862518963358913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 811553162575012642239275 1217329743862518963358913)
            ·
              refine ⟨912997307896889222519185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1217329743862518963358913 912997307896889222519185)
              ·
                refine ⟨684747980922666916889389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 912997307896889222519185 684747980922666916889389)
                ·
                  refine ⟨256780492846000093833521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 684747980922666916889389 256780492846000093833521)
                  ·
                    rfl

theorem cell20_562588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 3].length) (baseStart_562588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562588 prefixEnd_562588 := by exact prefixLift 562588
  have htrace : WordTrace (prefixWord ++ tailWord_562588) baseStart_562588 baseEnd_562588 := by
    simpa [prefixWord, tailWord_562588, baseEnd_562588] using wordTrace_append hprefix tailTrace_562588
  have hstable : (prefixWord ++ tailWord_562588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562588).length < 2 ^ (prefixWord ++ tailWord_562588).sum := by decide
  have hdescent : baseEnd_562588 < baseStart_562588 := by decide
  rcases family_descends (prefixWord ++ tailWord_562588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562592 : List Nat := [2, 1, 1, 4, 1, 2, 4, 2, 3]
def baseStart_562592 : Nat := 118140960795 + 562592 * 2 ^ 59
def prefixEnd_562592 : Nat := 4983230072969 + 3 ^ 40 * 562592 * 2
def baseEnd_562592 : Nat := 256782318554993857700171

theorem tailTrace_562592 : CollatzResearch.WordTrace tailWord_562592 prefixEnd_562592 256782318554993857700171 := by
  unfold tailWord_562592
  simp only [CollatzResearch.WordTrace]
  refine ⟨10259707988916370954573015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13679610651888494606097353 10259707988916370954573015)
  ·
    refine ⟨15389561983374556431859523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10259707988916370954573015 15389561983374556431859523)
    ·
      refine ⟨23084342975061834647789285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15389561983374556431859523 23084342975061834647789285)
      ·
        refine ⟨4328314307824093996460491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23084342975061834647789285 4328314307824093996460491)
        ·
          refine ⟨6492471461736140994690737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4328314307824093996460491 6492471461736140994690737)
          ·
            refine ⟨4869353596302105746018053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6492471461736140994690737 4869353596302105746018053)
            ·
              refine ⟨913003799306644827378385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4869353596302105746018053 913003799306644827378385)
              ·
                refine ⟨684752849479983620533789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 913003799306644827378385 684752849479983620533789)
                ·
                  refine ⟨256782318554993857700171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 684752849479983620533789 256782318554993857700171)
                  ·
                    rfl

theorem cell20_562592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 3].length) (baseStart_562592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562592 prefixEnd_562592 := by exact prefixLift 562592
  have htrace : WordTrace (prefixWord ++ tailWord_562592) baseStart_562592 baseEnd_562592 := by
    simpa [prefixWord, tailWord_562592, baseEnd_562592] using wordTrace_append hprefix tailTrace_562592
  have hstable : (prefixWord ++ tailWord_562592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562592).length < 2 ^ (prefixWord ++ tailWord_562592).sum := by decide
  have hdescent : baseEnd_562592 < baseStart_562592 := by decide
  rcases family_descends (prefixWord ++ tailWord_562592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562599 : List Nat := [1, 1, 6, 1, 1, 1, 2, 3, 4]
def baseStart_562599 : Nat := 118140960795 + 562599 * 2 ^ 59
def prefixEnd_562599 : Nat := 4983230072969 + 3 ^ 40 * 562599 * 2
def baseEnd_562599 : Nat := 256785513545732944466809

theorem tailTrace_562599 : CollatzResearch.WordTrace tailWord_562599 prefixEnd_562599 256785513545732944466809 := by
  unfold tailWord_562599
  simp only [CollatzResearch.WordTrace]
  refine ⟨20519671288807382104650851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13679780859204921403100567 20519671288807382104650851)
  ·
    refine ⟨30779506933211073156976277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20519671288807382104650851 30779506933211073156976277)
    ·
      refine ⟨1442789387494269054233263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30779506933211073156976277 1442789387494269054233263)
      ·
        refine ⟨2164184081241403581349895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1442789387494269054233263 2164184081241403581349895)
        ·
          refine ⟨3246276121862105372024843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2164184081241403581349895 3246276121862105372024843)
          ·
            refine ⟨4869414182793158058037265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3246276121862105372024843 4869414182793158058037265)
            ·
              refine ⟨3652060637094868543527949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4869414182793158058037265 3652060637094868543527949)
              ·
                refine ⟨1369522738910575703822981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3652060637094868543527949 1369522738910575703822981)
                ·
                  refine ⟨256785513545732944466809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1369522738910575703822981 256785513545732944466809)
                  ·
                    rfl

theorem cell20_562599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 4].length) (baseStart_562599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562599 prefixEnd_562599 := by exact prefixLift 562599
  have htrace : WordTrace (prefixWord ++ tailWord_562599) baseStart_562599 baseEnd_562599 := by
    simpa [prefixWord, tailWord_562599, baseEnd_562599] using wordTrace_append hprefix tailTrace_562599
  have hstable : (prefixWord ++ tailWord_562599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562599).length < 2 ^ (prefixWord ++ tailWord_562599).sum := by decide
  have hdescent : baseEnd_562599 < baseStart_562599 := by decide
  rcases family_descends (prefixWord ++ tailWord_562599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562627 : List Nat := [1, 1, 1, 3, 1, 1, 4, 8]
def baseStart_562627 : Nat := 118140960795 + 562627 * 2 ^ 59
def prefixEnd_562627 : Nat := 4983230072969 + 3 ^ 40 * 562627 * 2
def baseEnd_562627 : Nat := 85599431169563097177787

theorem tailTrace_562627 : CollatzResearch.WordTrace tailWord_562627 prefixEnd_562627 85599431169563097177787 := by
  unfold tailWord_562627
  simp only [CollatzResearch.WordTrace]
  refine ⟨20520692532705942886670135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13680461688470628591113423 20520692532705942886670135)
  ·
    refine ⟨30781038799058914330005203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20520692532705942886670135 30781038799058914330005203)
    ·
      refine ⟨46171558198588371495007805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30781038799058914330005203 46171558198588371495007805)
      ·
        refine ⟨17314334324470639310627927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46171558198588371495007805 17314334324470639310627927)
        ·
          refine ⟨25971501486705958965941891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17314334324470639310627927 25971501486705958965941891)
          ·
            refine ⟨38957252230058938448912837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25971501486705958965941891 38957252230058938448912837)
            ·
              refine ⟨7304484793136050959171157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38957252230058938448912837 7304484793136050959171157)
              ·
                refine ⟨85599431169563097177787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7304484793136050959171157 85599431169563097177787)
                ·
                  rfl

theorem cell20_562627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 8].length) (baseStart_562627 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562627 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562627 prefixEnd_562627 := by exact prefixLift 562627
  have htrace : WordTrace (prefixWord ++ tailWord_562627) baseStart_562627 baseEnd_562627 := by
    simpa [prefixWord, tailWord_562627, baseEnd_562627] using wordTrace_append hprefix tailTrace_562627
  have hstable : (prefixWord ++ tailWord_562627).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562627).length < 2 ^ (prefixWord ++ tailWord_562627).sum := by decide
  have hdescent : baseEnd_562627 < baseStart_562627 := by decide
  rcases family_descends (prefixWord ++ tailWord_562627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562678 : List Nat := [5, 1, 1, 1, 2, 4, 2, 4]
def baseStart_562678 : Nat := 118140960795 + 562678 * 2 ^ 59
def prefixEnd_562678 : Nat := 4983230072969 + 3 ^ 40 * 562678 * 2
def baseEnd_562678 : Nat := 85607190432786593611051

theorem tailTrace_562678 : CollatzResearch.WordTrace tailWord_562678 prefixEnd_562678 85607190432786593611051 := by
  unfold tailWord_562678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1282659540970073662298543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13681701770347452397851125 1282659540970073662298543)
  ·
    refine ⟨1923989311455110493447815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1282659540970073662298543 1923989311455110493447815)
    ·
      refine ⟨2885983967182665740171723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1923989311455110493447815 2885983967182665740171723)
      ·
        refine ⟨4328975950773998610257585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2885983967182665740171723 4328975950773998610257585)
        ·
          refine ⟨3246731963080498957693189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4328975950773998610257585 3246731963080498957693189)
          ·
            refine ⟨608762243077593554567473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3246731963080498957693189 608762243077593554567473)
            ·
              refine ⟨456571682308195165925605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 608762243077593554567473 456571682308195165925605)
              ·
                refine ⟨85607190432786593611051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 456571682308195165925605 85607190432786593611051)
                ·
                  rfl

theorem cell20_562678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_562678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562678 prefixEnd_562678 := by exact prefixLift 562678
  have htrace : WordTrace (prefixWord ++ tailWord_562678) baseStart_562678 baseEnd_562678 := by
    simpa [prefixWord, tailWord_562678, baseEnd_562678] using wordTrace_append hprefix tailTrace_562678
  have hstable : (prefixWord ++ tailWord_562678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562678).length < 2 ^ (prefixWord ++ tailWord_562678).sum := by decide
  have hdescent : baseEnd_562678 < baseStart_562678 := by decide
  rcases family_descends (prefixWord ++ tailWord_562678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562696 : List Nat := [2, 1, 3, 2, 1, 1, 2, 2, 6]
def baseStart_562696 : Nat := 118140960795 + 562696 * 2 ^ 59
def prefixEnd_562696 : Nat := 4983230072969 + 3 ^ 40 * 562696 * 2
def baseEnd_562696 : Nat := 256829786988831718233079

theorem tailTrace_562696 : CollatzResearch.WordTrace tailWord_562696 prefixEnd_562696 256829786988831718233079 := by
  unfold tailWord_562696
  simp only [CollatzResearch.WordTrace]
  refine ⟨10261604584727983835465971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13682139446303978447287961 10261604584727983835465971)
  ·
    refine ⟨15392406877091975753198957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10261604584727983835465971 15392406877091975753198957)
    ·
      refine ⟨5772152578909490907449609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15392406877091975753198957 5772152578909490907449609)
      ·
        refine ⟨4329114434182118180587207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5772152578909490907449609 4329114434182118180587207)
        ·
          refine ⟨6493671651273177270880811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4329114434182118180587207 6493671651273177270880811)
          ·
            refine ⟨9740507476909765906321217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6493671651273177270880811 9740507476909765906321217)
            ·
              refine ⟨7305380607682324429740913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9740507476909765906321217 7305380607682324429740913)
              ·
                refine ⟨5479035455761743322305685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7305380607682324429740913 5479035455761743322305685)
                ·
                  refine ⟨256829786988831718233079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5479035455761743322305685 256829786988831718233079)
                  ·
                    rfl

theorem cell20_562696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_562696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562696 prefixEnd_562696 := by exact prefixLift 562696
  have htrace : WordTrace (prefixWord ++ tailWord_562696) baseStart_562696 baseEnd_562696 := by
    simpa [prefixWord, tailWord_562696, baseEnd_562696] using wordTrace_append hprefix tailTrace_562696
  have hstable : (prefixWord ++ tailWord_562696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562696).length < 2 ^ (prefixWord ++ tailWord_562696).sum := by decide
  have hdescent : baseEnd_562696 < baseStart_562696 := by decide
  rcases family_descends (prefixWord ++ tailWord_562696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562699 : List Nat := [1, 1, 1, 1, 9, 1, 6]
def baseStart_562699 : Nat := 118140960795 + 562699 * 2 ^ 59
def prefixEnd_562699 : Nat := 4983230072969 + 3 ^ 40 * 562699 * 2
def baseEnd_562699 : Nat := 28536795141175226792563

theorem tailTrace_562699 : CollatzResearch.WordTrace tailWord_562699 prefixEnd_562699 28536795141175226792563 := by
  unfold tailWord_562699
  simp only [CollatzResearch.WordTrace]
  refine ⟨20523318588445099183291151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13682212392296732788860767 20523318588445099183291151)
  ·
    refine ⟨30784977882667648774936727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20523318588445099183291151 30784977882667648774936727)
    ·
      refine ⟨46177466824001473162405091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30784977882667648774936727 46177466824001473162405091)
      ·
        refine ⟨69266200236002209743607637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46177466824001473162405091 69266200236002209743607637)
        ·
          refine ⟨405856642007825447716451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 69266200236002209743607637 405856642007825447716451)
          ·
            refine ⟨608784963011738171574677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405856642007825447716451 608784963011738171574677)
            ·
              refine ⟨28536795141175226792563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 608784963011738171574677 28536795141175226792563)
              ·
                rfl

theorem cell20_562699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 6].length) (baseStart_562699 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562699 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562699 prefixEnd_562699 := by exact prefixLift 562699
  have htrace : WordTrace (prefixWord ++ tailWord_562699) baseStart_562699 baseEnd_562699 := by
    simpa [prefixWord, tailWord_562699, baseEnd_562699] using wordTrace_append hprefix tailTrace_562699
  have hstable : (prefixWord ++ tailWord_562699).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562699).length < 2 ^ (prefixWord ++ tailWord_562699).sum := by decide
  have hdescent : baseEnd_562699 < baseStart_562699 := by decide
  rcases family_descends (prefixWord ++ tailWord_562699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562709 : List Nat := [1, 3, 2, 1, 3, 3, 3, 2, 2]
def baseStart_562709 : Nat := 118140960795 + 562709 * 2 ^ 59
def prefixEnd_562709 : Nat := 4983230072969 + 3 ^ 40 * 562709 * 2
def baseEnd_562709 : Nat := 256835720543061450799693

theorem tailTrace_562709 : CollatzResearch.WordTrace tailWord_562709 prefixEnd_562709 256835720543061450799693 := by
  unfold tailWord_562709
  simp only [CollatzResearch.WordTrace]
  refine ⟨20523683318408870891155181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13682455545605913927436787 20523683318408870891155181)
  ·
    refine ⟨7696381244403326584183193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20523683318408870891155181 7696381244403326584183193)
    ·
      refine ⟨5772285933302494938137395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7696381244403326584183193 5772285933302494938137395)
      ·
        refine ⟨8658428899953742407206093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5772285933302494938137395 8658428899953742407206093)
        ·
          refine ⟨3246910837482653402702285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8658428899953742407206093 3246910837482653402702285)
          ·
            refine ⟨1217591564055995026013357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3246910837482653402702285 1217591564055995026013357)
            ·
              refine ⟨456596836520998134755009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1217591564055995026013357 456596836520998134755009)
              ·
                refine ⟨342447627390748601066257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 456596836520998134755009 342447627390748601066257)
                ·
                  refine ⟨256835720543061450799693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 342447627390748601066257 256835720543061450799693)
                  ·
                    rfl

theorem cell20_562709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 2, 2].length) (baseStart_562709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562709 prefixEnd_562709 := by exact prefixLift 562709
  have htrace : WordTrace (prefixWord ++ tailWord_562709) baseStart_562709 baseEnd_562709 := by
    simpa [prefixWord, tailWord_562709, baseEnd_562709] using wordTrace_append hprefix tailTrace_562709
  have hstable : (prefixWord ++ tailWord_562709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562709).length < 2 ^ (prefixWord ++ tailWord_562709).sum := by decide
  have hdescent : baseEnd_562709 < baseStart_562709 := by decide
  rcases family_descends (prefixWord ++ tailWord_562709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562720 : List Nat := [2, 1, 1, 6, 1, 1, 1, 7]
def baseStart_562720 : Nat := 118140960795 + 562720 * 2 ^ 59
def prefixEnd_562720 : Nat := 4983230072969 + 3 ^ 40 * 562720 * 2
def baseEnd_562720 : Nat := 85613580414264767144327

theorem tailTrace_562720 : CollatzResearch.WordTrace tailWord_562720 prefixEnd_562720 85613580414264767144327 := by
  unfold tailWord_562720
  simp only [CollatzResearch.WordTrace]
  refine ⟨10262042260684509884902807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13682723014246013179870409 10262042260684509884902807)
  ·
    refine ⟨15393063391026764827354211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10262042260684509884902807 15393063391026764827354211)
    ·
      refine ⟨23089595086540147241031317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15393063391026764827354211 23089595086540147241031317)
      ·
        refine ⟨1082324769681569401923343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 23089595086540147241031317 1082324769681569401923343)
        ·
          refine ⟨1623487154522354102885015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1082324769681569401923343 1623487154522354102885015)
          ·
            refine ⟨2435230731783531154327523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1623487154522354102885015 2435230731783531154327523)
            ·
              refine ⟨3652846097675296731491285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2435230731783531154327523 3652846097675296731491285)
              ·
                refine ⟨85613580414264767144327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3652846097675296731491285 85613580414264767144327)
                ·
                  rfl

theorem cell20_562720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 7].length) (baseStart_562720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562720 prefixEnd_562720 := by exact prefixLift 562720
  have htrace : WordTrace (prefixWord ++ tailWord_562720) baseStart_562720 baseEnd_562720 := by
    simpa [prefixWord, tailWord_562720, baseEnd_562720] using wordTrace_append hprefix tailTrace_562720
  have hstable : (prefixWord ++ tailWord_562720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562720).length < 2 ^ (prefixWord ++ tailWord_562720).sum := by decide
  have hdescent : baseEnd_562720 < baseStart_562720 := by decide
  rcases family_descends (prefixWord ++ tailWord_562720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562789 : List Nat := [1, 3, 1, 3, 3, 2, 1, 2, 4]
def baseStart_562789 : Nat := 118140960795 + 562789 * 2 ^ 59
def prefixEnd_562789 : Nat := 4983230072969 + 3 ^ 40 * 562789 * 2
def baseEnd_562789 : Nat := 256872234722936728132699

theorem tailTrace_562789 : CollatzResearch.WordTrace tailWord_562789 prefixEnd_562789 256872234722936728132699 := by
  unfold tailWord_562789
  simp only [CollatzResearch.WordTrace]
  refine ⟨20526601158119044554067421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13684400772079363036044947 20526601158119044554067421)
  ·
    refine ⟨7697475434294641707775283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20526601158119044554067421 7697475434294641707775283)
    ·
      refine ⟨11546213151441962561662925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7697475434294641707775283 11546213151441962561662925)
      ·
        refine ⟨4329829931790735960623597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11546213151441962561662925 4329829931790735960623597)
        ·
          refine ⟨1623686224421525985233849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4329829931790735960623597 1623686224421525985233849)
          ·
            refine ⟨1217764668316144488925387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1623686224421525985233849 1217764668316144488925387)
            ·
              refine ⟨1826647002474216733388081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1217764668316144488925387 1826647002474216733388081)
              ·
                refine ⟨1369985251855662550041061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1826647002474216733388081 1369985251855662550041061)
                ·
                  refine ⟨256872234722936728132699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1369985251855662550041061 256872234722936728132699)
                  ·
                    rfl

theorem cell20_562789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_562789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562789 prefixEnd_562789 := by exact prefixLift 562789
  have htrace : WordTrace (prefixWord ++ tailWord_562789) baseStart_562789 baseEnd_562789 := by
    simpa [prefixWord, tailWord_562789, baseEnd_562789] using wordTrace_append hprefix tailTrace_562789
  have hstable : (prefixWord ++ tailWord_562789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562789).length < 2 ^ (prefixWord ++ tailWord_562789).sum := by decide
  have hdescent : baseEnd_562789 < baseStart_562789 := by decide
  rcases family_descends (prefixWord ++ tailWord_562789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562820 : List Nat := [2, 3, 2, 1, 4, 1, 1, 1, 5]
def baseStart_562820 : Nat := 118140960795 + 562820 * 2 ^ 59
def prefixEnd_562820 : Nat := 4983230072969 + 3 ^ 40 * 562820 * 2
def baseEnd_562820 : Nat := 256886383967638398099239

theorem tailTrace_562820 : CollatzResearch.WordTrace tailWord_562820 prefixEnd_562820 256886383967638398099239 := by
  unfold tailWord_562820
  simp only [CollatzResearch.WordTrace]
  refine ⟨10263865910503368424222957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13685154547337824565630609 10263865910503368424222957)
  ·
    refine ⟨3848949716438763159083609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10263865910503368424222957 3848949716438763159083609)
    ·
      refine ⟨2886712287329072369312707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3848949716438763159083609 2886712287329072369312707)
      ·
        refine ⟨4330068430993608553969061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2886712287329072369312707 4330068430993608553969061)
        ·
          refine ⟨811887830811301603869199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4330068430993608553969061 811887830811301603869199)
          ·
            refine ⟨1217831746216952405803799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 811887830811301603869199 1217831746216952405803799)
            ·
              refine ⟨1826747619325428608705699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1217831746216952405803799 1826747619325428608705699)
              ·
                refine ⟨2740121428988142913058549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1826747619325428608705699 2740121428988142913058549)
                ·
                  refine ⟨256886383967638398099239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2740121428988142913058549 256886383967638398099239)
                  ·
                    rfl

theorem cell20_562820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_562820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562820 prefixEnd_562820 := by exact prefixLift 562820
  have htrace : WordTrace (prefixWord ++ tailWord_562820) baseStart_562820 baseEnd_562820 := by
    simpa [prefixWord, tailWord_562820, baseEnd_562820] using wordTrace_append hprefix tailTrace_562820
  have hstable : (prefixWord ++ tailWord_562820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562820).length < 2 ^ (prefixWord ++ tailWord_562820).sum := by decide
  have hdescent : baseEnd_562820 < baseStart_562820 := by decide
  rcases family_descends (prefixWord ++ tailWord_562820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562827 : List Nat := [1, 1, 1, 1, 4, 1, 3, 6, 2]
def baseStart_562827 : Nat := 118140960795 + 562827 * 2 ^ 59
def prefixEnd_562827 : Nat := 4983230072969 + 3 ^ 40 * 562827 * 2
def baseEnd_562827 : Nat := 256889578958377484865877

theorem tailTrace_562827 : CollatzResearch.WordTrace tailWord_562827 prefixEnd_562827 256889578958377484865877 := by
  unfold tailWord_562827
  simp only [CollatzResearch.WordTrace]
  refine ⟨20527987131981377043950735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13685324754654251362633823 20527987131981377043950735)
  ·
    refine ⟨30791980697972065565926103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20527987131981377043950735 30791980697972065565926103)
    ·
      refine ⟨46187971046958098348889155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30791980697972065565926103 46187971046958098348889155)
      ·
        refine ⟨69281956570437147523333733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46187971046958098348889155 69281956570437147523333733)
        ·
          refine ⟨12990366856956965160625075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69281956570437147523333733 12990366856956965160625075)
          ·
            refine ⟨19485550285435447740937613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12990366856956965160625075 19485550285435447740937613)
            ·
              refine ⟨7307081357038292902851605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19485550285435447740937613 7307081357038292902851605)
              ·
                refine ⟨342519438611169979821169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7307081357038292902851605 342519438611169979821169)
                ·
                  refine ⟨256889578958377484865877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 342519438611169979821169 256889578958377484865877)
                  ·
                    rfl

theorem cell20_562827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 6, 2].length) (baseStart_562827 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562827 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562827 prefixEnd_562827 := by exact prefixLift 562827
  have htrace : WordTrace (prefixWord ++ tailWord_562827) baseStart_562827 baseEnd_562827 := by
    simpa [prefixWord, tailWord_562827, baseEnd_562827] using wordTrace_append hprefix tailTrace_562827
  have hstable : (prefixWord ++ tailWord_562827).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562827).length < 2 ^ (prefixWord ++ tailWord_562827).sum := by decide
  have hdescent : baseEnd_562827 < baseStart_562827 := by decide
  rcases family_descends (prefixWord ++ tailWord_562827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562847 : List Nat := [1, 1, 2, 7, 2, 1, 2, 4]
def baseStart_562847 : Nat := 118140960795 + 562847 * 2 ^ 59
def prefixEnd_562847 : Nat := 4983230072969 + 3 ^ 40 * 562847 * 2
def baseEnd_562847 : Nat := 85632902501115434733043

theorem tailTrace_562847 : CollatzResearch.WordTrace tailWord_562847 prefixEnd_562847 85632902501115434733043 := by
  unfold tailWord_562847
  simp only [CollatzResearch.WordTrace]
  refine ⟨20528716591908920459678795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13685811061272613639785863 20528716591908920459678795)
  ·
    refine ⟨30793074887863380689518193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20528716591908920459678795 30793074887863380689518193)
    ·
      refine ⟨23094806165897535517138645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30793074887863380689518193 23094806165897535517138645)
      ·
        refine ⟨541284519513223488682937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 23094806165897535517138645 541284519513223488682937)
        ·
          refine ⟨405963389634917616512203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 541284519513223488682937 405963389634917616512203)
          ·
            refine ⟨608945084452376424768305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405963389634917616512203 608945084452376424768305)
            ·
              refine ⟨456708813339282318576229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 608945084452376424768305 456708813339282318576229)
              ·
                refine ⟨85632902501115434733043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 456708813339282318576229 85632902501115434733043)
                ·
                  rfl

theorem cell20_562847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 4].length) (baseStart_562847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562847 prefixEnd_562847 := by exact prefixLift 562847
  have htrace : WordTrace (prefixWord ++ tailWord_562847) baseStart_562847 baseEnd_562847 := by
    simpa [prefixWord, tailWord_562847, baseEnd_562847] using wordTrace_append hprefix tailTrace_562847
  have hstable : (prefixWord ++ tailWord_562847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562847).length < 2 ^ (prefixWord ++ tailWord_562847).sum := by decide
  have hdescent : baseEnd_562847 < baseStart_562847 := by decide
  rcases family_descends (prefixWord ++ tailWord_562847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562879 : List Nat := [1, 1, 2, 2, 2, 3, 2, 4, 3]
def baseStart_562879 : Nat := 118140960795 + 562879 * 2 ^ 59
def prefixEnd_562879 : Nat := 4983230072969 + 3 ^ 40 * 562879 * 2
def baseEnd_562879 : Nat := 256913313175296415132331

theorem tailTrace_562879 : CollatzResearch.WordTrace tailWord_562879 prefixEnd_562879 256913313175296415132331 := by
  unfold tailWord_562879
  simp only [CollatzResearch.WordTrace]
  refine ⟨20529883727792989924843691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13686589151861993283229127 20529883727792989924843691)
  ·
    refine ⟨30794825591689484887265537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20529883727792989924843691 30794825591689484887265537)
    ·
      refine ⟨23096119193767113665449153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30794825591689484887265537 23096119193767113665449153)
      ·
        refine ⟨17322089395325335249086865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23096119193767113665449153 17322089395325335249086865)
        ·
          refine ⟨12991567046494001436815149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17322089395325335249086865 12991567046494001436815149)
          ·
            refine ⟨4871837642435250538805681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12991567046494001436815149 4871837642435250538805681)
            ·
              refine ⟨3653878231826437904104261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4871837642435250538805681 3653878231826437904104261)
              ·
                refine ⟨685102168467457107019549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3653878231826437904104261 685102168467457107019549)
                ·
                  refine ⟨256913313175296415132331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 685102168467457107019549 256913313175296415132331)
                  ·
                    rfl

theorem cell20_562879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 3].length) (baseStart_562879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562879 prefixEnd_562879 := by exact prefixLift 562879
  have htrace : WordTrace (prefixWord ++ tailWord_562879) baseStart_562879 baseEnd_562879 := by
    simpa [prefixWord, tailWord_562879, baseEnd_562879] using wordTrace_append hprefix tailTrace_562879
  have hstable : (prefixWord ++ tailWord_562879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562879).length < 2 ^ (prefixWord ++ tailWord_562879).sum := by decide
  have hdescent : baseEnd_562879 < baseStart_562879 := by decide
  rcases family_descends (prefixWord ++ tailWord_562879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562892 : List Nat := [2, 2, 1, 5, 2, 2, 2, 1, 3]
def baseStart_562892 : Nat := 118140960795 + 562892 * 2 ^ 59
def prefixEnd_562892 : Nat := 4983230072969 + 3 ^ 40 * 562892 * 2
def baseEnd_562892 : Nat := 256919246729526147698945

theorem tailTrace_562892 : CollatzResearch.WordTrace tailWord_562892 prefixEnd_562892 256919246729526147698945 := by
  unfold tailWord_562892
  simp only [CollatzResearch.WordTrace]
  refine ⟨10265178938372946572533465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13686905251163928763377953 10265178938372946572533465)
  ·
    refine ⟨7698884203779709929400099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10265178938372946572533465 7698884203779709929400099)
    ·
      refine ⟨11548326305669564894100149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7698884203779709929400099 11548326305669564894100149)
      ·
        refine ⟨1082655591156521708821889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11548326305669564894100149 1082655591156521708821889)
        ·
          refine ⟨811991693367391281616417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1082655591156521708821889 811991693367391281616417)
          ·
            refine ⟨608993770025543461212313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 811991693367391281616417 608993770025543461212313)
            ·
              refine ⟨456745327519157595909235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 608993770025543461212313 456745327519157595909235)
              ·
                refine ⟨685117991278736393863853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 456745327519157595909235 685117991278736393863853)
                ·
                  refine ⟨256919246729526147698945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 685117991278736393863853 256919246729526147698945)
                  ·
                    rfl

theorem cell20_562892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 3].length) (baseStart_562892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562892 prefixEnd_562892 := by exact prefixLift 562892
  have htrace : WordTrace (prefixWord ++ tailWord_562892) baseStart_562892 baseEnd_562892 := by
    simpa [prefixWord, tailWord_562892, baseEnd_562892] using wordTrace_append hprefix tailTrace_562892
  have hstable : (prefixWord ++ tailWord_562892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562892).length < 2 ^ (prefixWord ++ tailWord_562892).sum := by decide
  have hdescent : baseEnd_562892 < baseStart_562892 := by decide
  rcases family_descends (prefixWord ++ tailWord_562892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562934 : List Nat := [5, 1, 1, 1, 1, 3, 1, 4, 3]
def baseStart_562934 : Nat := 118140960795 + 562934 * 2 ^ 59
def prefixEnd_562934 : Nat := 4983230072969 + 3 ^ 40 * 562934 * 2
def baseEnd_562934 : Nat := 256938416673960668298773

theorem tailTrace_562934 : CollatzResearch.WordTrace tailWord_562934 prefixEnd_562934 256938416673960668298773 := by
  unfold tailWord_562934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1283243108912108394880991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13687926495062489545397237 1283243108912108394880991)
  ·
    refine ⟨1924864663368162592321487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1283243108912108394880991 1924864663368162592321487)
    ·
      refine ⟨2887296995052243888482231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1924864663368162592321487 2887296995052243888482231)
      ·
        refine ⟨4330945492578365832723347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2887296995052243888482231 4330945492578365832723347)
        ·
          refine ⟨6496418238867548749085021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4330945492578365832723347 6496418238867548749085021)
          ·
            refine ⟨2436156839575330780906883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6496418238867548749085021 2436156839575330780906883)
            ·
              refine ⟨3654235259362996171360325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2436156839575330780906883 3654235259362996171360325)
              ·
                refine ⟨685169111130561782130061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3654235259362996171360325 685169111130561782130061)
                ·
                  refine ⟨256938416673960668298773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 685169111130561782130061 256938416673960668298773)
                  ·
                    rfl

theorem cell20_562934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_562934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562934 prefixEnd_562934 := by exact prefixLift 562934
  have htrace : WordTrace (prefixWord ++ tailWord_562934) baseStart_562934 baseEnd_562934 := by
    simpa [prefixWord, tailWord_562934, baseEnd_562934] using wordTrace_append hprefix tailTrace_562934
  have hstable : (prefixWord ++ tailWord_562934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562934).length < 2 ^ (prefixWord ++ tailWord_562934).sum := by decide
  have hdescent : baseEnd_562934 < baseStart_562934 := by decide
  rcases family_descends (prefixWord ++ tailWord_562934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562948 : List Nat := [2, 3, 2, 2, 1, 2, 3, 5]
def baseStart_562948 : Nat := 118140960795 + 562948 * 2 ^ 59
def prefixEnd_562948 : Nat := 4983230072969 + 3 ^ 40 * 562948 * 2
def baseEnd_562948 : Nat := 85648268885146280610683

theorem tailTrace_562948 : CollatzResearch.WordTrace tailWord_562948 prefixEnd_562948 85648268885146280610683 := by
  unfold tailWord_562948
  simp only [CollatzResearch.WordTrace]
  refine ⟨10266200182271507354552749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13688266909695343139403665 10266200182271507354552749)
  ·
    refine ⟨3849825068351815257957281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10266200182271507354552749 3849825068351815257957281)
    ·
      refine ⟨2887368801263861443467961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3849825068351815257957281 2887368801263861443467961)
      ·
        refine ⟨2165526600947896082600971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2887368801263861443467961 2165526600947896082600971)
        ·
          refine ⟨3248289901421844123901457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2165526600947896082600971 3248289901421844123901457)
          ·
            refine ⟨2436217426066383092926093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3248289901421844123901457 2436217426066383092926093)
            ·
              refine ⟨913581534774893659847285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2436217426066383092926093 913581534774893659847285)
              ·
                refine ⟨85648268885146280610683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 913581534774893659847285 85648268885146280610683)
                ·
                  rfl

theorem cell20_562948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 5].length) (baseStart_562948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562948 prefixEnd_562948 := by exact prefixLift 562948
  have htrace : WordTrace (prefixWord ++ tailWord_562948) baseStart_562948 baseEnd_562948 := by
    simpa [prefixWord, tailWord_562948, baseEnd_562948] using wordTrace_append hprefix tailTrace_562948
  have hstable : (prefixWord ++ tailWord_562948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562948).length < 2 ^ (prefixWord ++ tailWord_562948).sum := by decide
  have hdescent : baseEnd_562948 < baseStart_562948 := by decide
  rcases family_descends (prefixWord ++ tailWord_562948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562955 : List Nat := [1, 1, 1, 1, 5, 1, 4, 3, 3]
def baseStart_562955 : Nat := 118140960795 + 562955 * 2 ^ 59
def prefixEnd_562955 : Nat := 4983230072969 + 3 ^ 40 * 562955 * 2
def baseEnd_562955 : Nat := 256948001646177928598687

theorem tailTrace_562955 : CollatzResearch.WordTrace tailWord_562955 prefixEnd_562955 256948001646177928598687 := by
  unfold tailWord_562955
  simp only [CollatzResearch.WordTrace]
  refine ⟨20532655675517654904610319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13688437117011769936406879 20532655675517654904610319)
  ·
    refine ⟨30798983513276482356915479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20532655675517654904610319 30798983513276482356915479)
    ·
      refine ⟨46198475269914723535373219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30798983513276482356915479 46198475269914723535373219)
      ·
        refine ⟨69297712904872085303059829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46198475269914723535373219 69297712904872085303059829)
        ·
          refine ⟨6496660584831757997161859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69297712904872085303059829 6496660584831757997161859)
          ·
            refine ⟨9744990877247636995742789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6496660584831757997161859 9744990877247636995742789)
            ·
              refine ⟨1827185789483931936701773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9744990877247636995742789 1827185789483931936701773)
              ·
                refine ⟨685194671056474476263165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1827185789483931936701773 685194671056474476263165)
                ·
                  refine ⟨256948001646177928598687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 685194671056474476263165 256948001646177928598687)
                  ·
                    rfl

theorem cell20_562955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 3].length) (baseStart_562955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562955 prefixEnd_562955 := by exact prefixLift 562955
  have htrace : WordTrace (prefixWord ++ tailWord_562955) baseStart_562955 baseEnd_562955 := by
    simpa [prefixWord, tailWord_562955, baseEnd_562955] using wordTrace_append hprefix tailTrace_562955
  have hstable : (prefixWord ++ tailWord_562955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562955).length < 2 ^ (prefixWord ++ tailWord_562955).sum := by decide
  have hdescent : baseEnd_562955 < baseStart_562955 := by decide
  rcases family_descends (prefixWord ++ tailWord_562955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562979 : List Nat := [1, 1, 1, 4, 2, 1, 3, 5, 2]
def baseStart_562979 : Nat := 118140960795 + 562979 * 2 ^ 59
def prefixEnd_562979 : Nat := 4983230072969 + 3 ^ 40 * 562979 * 2
def baseEnd_562979 : Nat := 256958955900140511798589

theorem tailTrace_562979 : CollatzResearch.WordTrace tailWord_562979 prefixEnd_562979 256958955900140511798589 := by
  unfold tailWord_562979
  simp only [CollatzResearch.WordTrace]
  refine ⟨20533531027430707003483991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13689020684953804668989327 20533531027430707003483991)
  ·
    refine ⟨30800296541146060505225987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20533531027430707003483991 30800296541146060505225987)
    ·
      refine ⟨46200444811719090757838981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30800296541146060505225987 46200444811719090757838981)
      ·
        refine ⟨8662583402197329517094809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46200444811719090757838981 8662583402197329517094809)
        ·
          refine ⟨6496937551647997137821107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8662583402197329517094809 6496937551647997137821107)
          ·
            refine ⟨9745406327471995706731661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6496937551647997137821107 9745406327471995706731661)
            ·
              refine ⟨3654527372801998390024373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9745406327471995706731661 3654527372801998390024373)
              ·
                refine ⟨342611941200187349064785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3654527372801998390024373 342611941200187349064785)
                ·
                  refine ⟨256958955900140511798589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 342611941200187349064785 256958955900140511798589)
                  ·
                    rfl

theorem cell20_562979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 5, 2].length) (baseStart_562979 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562979 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562979 prefixEnd_562979 := by exact prefixLift 562979
  have htrace : WordTrace (prefixWord ++ tailWord_562979) baseStart_562979 baseEnd_562979 := by
    simpa [prefixWord, tailWord_562979, baseEnd_562979] using wordTrace_append hprefix tailTrace_562979
  have hstable : (prefixWord ++ tailWord_562979).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562979).length < 2 ^ (prefixWord ++ tailWord_562979).sum := by decide
  have hdescent : baseEnd_562979 < baseStart_562979 := by decide
  rcases family_descends (prefixWord ++ tailWord_562979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562993 : List Nat := [1, 2, 2, 3, 2, 3, 1, 1, 5]
def baseStart_562993 : Nat := 118140960795 + 562993 * 2 ^ 59
def prefixEnd_562993 : Nat := 4983230072969 + 3 ^ 40 * 562993 * 2
def baseEnd_562993 : Nat := 256965345881618685331865

theorem tailTrace_562993 : CollatzResearch.WordTrace tailWord_562993 prefixEnd_562993 256965345881618685331865 := by
  unfold tailWord_562993
  simp only [CollatzResearch.WordTrace]
  refine ⟨20534041649379987394493633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13689361099586658262995755 20534041649379987394493633)
  ·
    refine ⟨15400531237034990545870225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20534041649379987394493633 15400531237034990545870225)
    ·
      refine ⟨11550398427776242909402669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15400531237034990545870225 11550398427776242909402669)
      ·
        refine ⟨4331399410416091091026001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11550398427776242909402669 4331399410416091091026001)
        ·
          refine ⟨3248549557812068318269501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4331399410416091091026001 3248549557812068318269501)
          ·
            refine ⟨1218206084179525619351063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3248549557812068318269501 1218206084179525619351063)
            ·
              refine ⟨1827309126269288429026595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1218206084179525619351063 1827309126269288429026595)
              ·
                refine ⟨2740963689403932643539893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1827309126269288429026595 2740963689403932643539893)
                ·
                  refine ⟨256965345881618685331865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2740963689403932643539893 256965345881618685331865)
                  ·
                    rfl

theorem cell20_562993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 5].length) (baseStart_562993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562993 prefixEnd_562993 := by exact prefixLift 562993
  have htrace : WordTrace (prefixWord ++ tailWord_562993) baseStart_562993 baseEnd_562993 := by
    simpa [prefixWord, tailWord_562993, baseEnd_562993] using wordTrace_append hprefix tailTrace_562993
  have hstable : (prefixWord ++ tailWord_562993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562993).length < 2 ^ (prefixWord ++ tailWord_562993).sum := by decide
  have hdescent : baseEnd_562993 < baseStart_562993 := by decide
  rcases family_descends (prefixWord ++ tailWord_562993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_562996 : List Nat := [2, 5, 1, 1, 2, 2, 2, 1, 4]
def baseStart_562996 : Nat := 118140960795 + 562996 * 2 ^ 59
def prefixEnd_562996 : Nat := 4983230072969 + 3 ^ 40 * 562996 * 2
def baseEnd_562996 : Nat := 256966715163364008231853

theorem tailTrace_562996 : CollatzResearch.WordTrace tailWord_562996 prefixEnd_562996 256966715163364008231853 := by
  unfold tailWord_562996
  simp only [CollatzResearch.WordTrace]
  refine ⟨10267075534184559453426421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13689434045579412604568561 10267075534184559453426421)
  ·
    refine ⟨962538331329802448758727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10267075534184559453426421 962538331329802448758727)
    ·
      refine ⟨1443807496994703673138091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 962538331329802448758727 1443807496994703673138091)
      ·
        refine ⟨2165711245492055509707137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1443807496994703673138091 2165711245492055509707137)
        ·
          refine ⟨1624283434119041632280353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2165711245492055509707137 1624283434119041632280353)
          ·
            refine ⟨1218212575589281224210265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1624283434119041632280353 1218212575589281224210265)
            ·
              refine ⟨913659431691960918157699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1218212575589281224210265 913659431691960918157699)
              ·
                refine ⟨1370489147537941377236549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 913659431691960918157699 1370489147537941377236549)
                ·
                  refine ⟨256966715163364008231853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1370489147537941377236549 256966715163364008231853)
                  ·
                    rfl

theorem cell20_562996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_562996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_562996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_562996 prefixEnd_562996 := by exact prefixLift 562996
  have htrace : WordTrace (prefixWord ++ tailWord_562996) baseStart_562996 baseEnd_562996 := by
    simpa [prefixWord, tailWord_562996, baseEnd_562996] using wordTrace_append hprefix tailTrace_562996
  have hstable : (prefixWord ++ tailWord_562996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_562996).length < 2 ^ (prefixWord ++ tailWord_562996).sum := by decide
  have hdescent : baseEnd_562996 < baseStart_562996 := by decide
  rcases family_descends (prefixWord ++ tailWord_562996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563000 : List Nat := [2, 1, 2, 1, 3, 3, 1, 3, 4]
def baseStart_563000 : Nat := 118140960795 + 563000 * 2 ^ 59
def prefixEnd_563000 : Nat := 4983230072969 + 3 ^ 40 * 563000 * 2
def baseEnd_563000 : Nat := 256968540872357772098503

theorem tailTrace_563000 : CollatzResearch.WordTrace tailWord_563000 prefixEnd_563000 256968540872357772098503 := by
  unfold tailWord_563000
  simp only [CollatzResearch.WordTrace]
  refine ⟨10267148480177313794999227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13689531306903085059998969 10267148480177313794999227)
  ·
    refine ⟨15400722720265970692498841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10267148480177313794999227 15400722720265970692498841)
    ·
      refine ⟨11550542040199478019374131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15400722720265970692498841 11550542040199478019374131)
      ·
        refine ⟨17325813060299217029061197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11550542040199478019374131 17325813060299217029061197)
        ·
          refine ⟨6497179897612206385897949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17325813060299217029061197 6497179897612206385897949)
          ·
            refine ⟨2436442461604577394711731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6497179897612206385897949 2436442461604577394711731)
            ·
              refine ⟨3654663692406866092067597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2436442461604577394711731 3654663692406866092067597)
              ·
                refine ⟨1370498884652574784525349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3654663692406866092067597 1370498884652574784525349)
                ·
                  refine ⟨256968540872357772098503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1370498884652574784525349 256968540872357772098503)
                  ·
                    rfl

theorem cell20_563000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_563000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563000 prefixEnd_563000 := by exact prefixLift 563000
  have htrace : WordTrace (prefixWord ++ tailWord_563000) baseStart_563000 baseEnd_563000 := by
    simpa [prefixWord, tailWord_563000, baseEnd_563000] using wordTrace_append hprefix tailTrace_563000
  have hstable : (prefixWord ++ tailWord_563000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563000).length < 2 ^ (prefixWord ++ tailWord_563000).sum := by decide
  have hdescent : baseEnd_563000 < baseStart_563000 := by decide
  rcases family_descends (prefixWord ++ tailWord_563000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563020 : List Nat := [2, 2, 1, 3, 5, 1, 2, 4]
def baseStart_563020 : Nat := 118140960795 + 563020 * 2 ^ 59
def prefixEnd_563020 : Nat := 4983230072969 + 3 ^ 40 * 563020 * 2
def baseEnd_563020 : Nat := 85659223139108863810585

theorem tailTrace_563020 : CollatzResearch.WordTrace tailWord_563020 prefixEnd_563020 85659223139108863810585 := by
  unfold tailWord_563020
  simp only [CollatzResearch.WordTrace]
  refine ⟨10267513210141085502863257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13690017613521447337151009 10267513210141085502863257)
  ·
    refine ⟨7700634907605814127147443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10267513210141085502863257 7700634907605814127147443)
    ·
      refine ⟨11550952361408721190721165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7700634907605814127147443 11550952361408721190721165)
      ·
        refine ⟨4331607135528270446520437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11550952361408721190721165 4331607135528270446520437)
        ·
          refine ⟨406088168955775354361291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4331607135528270446520437 406088168955775354361291)
          ·
            refine ⟨609132253433663031541937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406088168955775354361291 609132253433663031541937)
            ·
              refine ⟨456849190075247273656453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 609132253433663031541937 456849190075247273656453)
              ·
                refine ⟨85659223139108863810585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 456849190075247273656453 85659223139108863810585)
                ·
                  rfl

theorem cell20_563020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 4].length) (baseStart_563020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563020 prefixEnd_563020 := by exact prefixLift 563020
  have htrace : WordTrace (prefixWord ++ tailWord_563020) baseStart_563020 baseEnd_563020 := by
    simpa [prefixWord, tailWord_563020, baseEnd_563020] using wordTrace_append hprefix tailTrace_563020
  have hstable : (prefixWord ++ tailWord_563020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563020).length < 2 ^ (prefixWord ++ tailWord_563020).sum := by decide
  have hdescent : baseEnd_563020 < baseStart_563020 := by decide
  rcases family_descends (prefixWord ++ tailWord_563020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563076 : List Nat := [2, 3, 2, 1, 1, 1, 2, 4, 4]
def baseStart_563076 : Nat := 118140960795 + 563076 * 2 ^ 59
def prefixEnd_563076 : Nat := 4983230072969 + 3 ^ 40 * 563076 * 2
def baseEnd_563076 : Nat := 257003229343239285564859

theorem tailTrace_563076 : CollatzResearch.WordTrace tailWord_563076 prefixEnd_563076 257003229343239285564859 := by
  unfold tailWord_563076
  simp only [CollatzResearch.WordTrace]
  refine ⟨10268534454039646284882541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13691379272052861713176721 10268534454039646284882541)
  ·
    refine ⟨3850700420264867356830953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10268534454039646284882541 3850700420264867356830953)
    ·
      refine ⟨2888025315198650517623215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3850700420264867356830953 2888025315198650517623215)
      ·
        refine ⟨4332037972797975776434823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2888025315198650517623215 4332037972797975776434823)
        ·
          refine ⟨6498056959196963664652235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4332037972797975776434823 6498056959196963664652235)
          ·
            refine ⟨9747085438795445496978353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6498056959196963664652235 9747085438795445496978353)
            ·
              refine ⟨7310314079096584122733765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9747085438795445496978353 7310314079096584122733765)
              ·
                refine ⟨1370683889830609523012581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7310314079096584122733765 1370683889830609523012581)
                ·
                  refine ⟨257003229343239285564859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1370683889830609523012581 257003229343239285564859)
                  ·
                    rfl

theorem cell20_563076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_563076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563076 prefixEnd_563076 := by exact prefixLift 563076
  have htrace : WordTrace (prefixWord ++ tailWord_563076) baseStart_563076 baseEnd_563076 := by
    simpa [prefixWord, tailWord_563076, baseEnd_563076] using wordTrace_append hprefix tailTrace_563076
  have hstable : (prefixWord ++ tailWord_563076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563076).length < 2 ^ (prefixWord ++ tailWord_563076).sum := by decide
  have hdescent : baseEnd_563076 < baseStart_563076 := by decide
  rcases family_descends (prefixWord ++ tailWord_563076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563093 : List Nat := [1, 3, 2, 1, 1, 3, 2, 5, 2]
def baseStart_563093 : Nat := 118140960795 + 563093 * 2 ^ 59
def prefixEnd_563093 : Nat := 4983230072969 + 3 ^ 40 * 563093 * 2
def baseEnd_563093 : Nat := 257010988606462781998123

theorem tailTrace_563093 : CollatzResearch.WordTrace tailWord_563093 prefixEnd_563093 257010988606462781998123 := by
  unfold tailWord_563093
  simp only [CollatzResearch.WordTrace]
  refine ⟨20537688949017704473133933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13691792632678469648755955 20537688949017704473133933)
  ·
    refine ⟨7701633355881639177425225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20537688949017704473133933 7701633355881639177425225)
    ·
      refine ⟨5776225016911229383068919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7701633355881639177425225 5776225016911229383068919)
      ·
        refine ⟨8664337525366844074603379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5776225016911229383068919 8664337525366844074603379)
        ·
          refine ⟨12996506288050266111905069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8664337525366844074603379 12996506288050266111905069)
          ·
            refine ⟨4873689858018849791964401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12996506288050266111905069 4873689858018849791964401)
            ·
              refine ⟨3655267393514137343973301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4873689858018849791964401 3655267393514137343973301)
              ·
                refine ⟨342681318141950375997497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3655267393514137343973301 342681318141950375997497)
                ·
                  refine ⟨257010988606462781998123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 342681318141950375997497 257010988606462781998123)
                  ·
                    rfl

theorem cell20_563093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 5, 2].length) (baseStart_563093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563093 prefixEnd_563093 := by exact prefixLift 563093
  have htrace : WordTrace (prefixWord ++ tailWord_563093) baseStart_563093 baseEnd_563093 := by
    simpa [prefixWord, tailWord_563093, baseEnd_563093] using wordTrace_append hprefix tailTrace_563093
  have hstable : (prefixWord ++ tailWord_563093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563093).length < 2 ^ (prefixWord ++ tailWord_563093).sum := by decide
  have hdescent : baseEnd_563093 < baseStart_563093 := by decide
  rcases family_descends (prefixWord ++ tailWord_563093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563102 : List Nat := [4, 3, 1, 3, 2, 1, 2, 2, 2]
def baseStart_563102 : Nat := 118140960795 + 563102 * 2 ^ 59
def prefixEnd_563102 : Nat := 4983230072969 + 3 ^ 40 * 563102 * 2
def baseEnd_563102 : Nat := 257015096451698750698087

theorem tailTrace_563102 : CollatzResearch.WordTrace tailWord_563102 prefixEnd_563102 257015096451698750698087 := by
  unfold tailWord_563102
  simp only [CollatzResearch.WordTrace]
  refine ⟨2567252150748137376276445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13692011470656732673474373 2567252150748137376276445)
  ·
    refine ⟨962719556530551516103667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2567252150748137376276445 962719556530551516103667)
    ·
      refine ⟨1444079334795827274155501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 962719556530551516103667 1444079334795827274155501)
      ·
        refine ⟨541529750548435227808313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1444079334795827274155501 541529750548435227808313)
        ·
          refine ⟨406147312911326420856235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 541529750548435227808313 406147312911326420856235)
          ·
            refine ⟨609220969366989631284353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406147312911326420856235 609220969366989631284353)
            ·
              refine ⟨456915727025242223463265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 609220969366989631284353 456915727025242223463265)
              ·
                refine ⟨342686795268931667597449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 456915727025242223463265 342686795268931667597449)
                ·
                  refine ⟨257015096451698750698087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 342686795268931667597449 257015096451698750698087)
                  ·
                    rfl

theorem cell20_563102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_563102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563102 prefixEnd_563102 := by exact prefixLift 563102
  have htrace : WordTrace (prefixWord ++ tailWord_563102) baseStart_563102 baseEnd_563102 := by
    simpa [prefixWord, tailWord_563102, baseEnd_563102] using wordTrace_append hprefix tailTrace_563102
  have hstable : (prefixWord ++ tailWord_563102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563102).length < 2 ^ (prefixWord ++ tailWord_563102).sum := by decide
  have hdescent : baseEnd_563102 < baseStart_563102 := by decide
  rcases family_descends (prefixWord ++ tailWord_563102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563106 : List Nat := [3, 3, 1, 2, 3, 2, 2, 2, 2]
def baseStart_563106 : Nat := 118140960795 + 563106 * 2 ^ 59
def prefixEnd_563106 : Nat := 4983230072969 + 3 ^ 40 * 563106 * 2
def baseEnd_563106 : Nat := 257016922160692514564737

theorem tailTrace_563106 : CollatzResearch.WordTrace tailWord_563106 prefixEnd_563106 257016922160692514564737 := by
  unfold tailWord_563106
  simp only [CollatzResearch.WordTrace]
  refine ⟨5134540774492651923339293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13692108731980405128904781 5134540774492651923339293)
  ·
    refine ⟨1925452790434744471252235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5134540774492651923339293 1925452790434744471252235)
    ·
      refine ⟨2888179185652116706878353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1925452790434744471252235 2888179185652116706878353)
      ·
        refine ⟨2166134389239087530158765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2888179185652116706878353 2166134389239087530158765)
        ·
          refine ⟨812300395964657823809537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2166134389239087530158765 812300395964657823809537)
          ·
            refine ⟨609225296973493367857153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 812300395964657823809537 609225296973493367857153)
            ·
              refine ⟨456918972730120025892865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 609225296973493367857153 456918972730120025892865)
              ·
                refine ⟨342689229547590019419649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 456918972730120025892865 342689229547590019419649)
                ·
                  refine ⟨257016922160692514564737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 342689229547590019419649 257016922160692514564737)
                  ·
                    rfl

theorem cell20_563106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_563106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563106 prefixEnd_563106 := by exact prefixLift 563106
  have htrace : WordTrace (prefixWord ++ tailWord_563106) baseStart_563106 baseEnd_563106 := by
    simpa [prefixWord, tailWord_563106, baseEnd_563106] using wordTrace_append hprefix tailTrace_563106
  have hstable : (prefixWord ++ tailWord_563106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563106).length < 2 ^ (prefixWord ++ tailWord_563106).sum := by decide
  have hdescent : baseEnd_563106 < baseStart_563106 := by decide
  rcases family_descends (prefixWord ++ tailWord_563106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563148 : List Nat := [2, 2, 1, 4, 1, 3, 2, 3, 2]
def baseStart_563148 : Nat := 118140960795 + 563148 * 2 ^ 59
def prefixEnd_563148 : Nat := 4983230072969 + 3 ^ 40 * 563148 * 2
def baseEnd_563148 : Nat := 257036092105127035164565

theorem tailTrace_563148 : CollatzResearch.WordTrace tailWord_563148 prefixEnd_563148 257036092105127035164565 := by
  unfold tailWord_563148
  simp only [CollatzResearch.WordTrace]
  refine ⟨10269847481909224433193049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13693129975878965910924065 10269847481909224433193049)
  ·
    refine ⟨7702385611431918324894787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10269847481909224433193049 7702385611431918324894787)
    ·
      refine ⟨11553578417147877487342181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7702385611431918324894787 11553578417147877487342181)
      ·
        refine ⟨2166295953215227028876659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11553578417147877487342181 2166295953215227028876659)
        ·
          refine ⟨3249443929822840543314989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2166295953215227028876659 3249443929822840543314989)
          ·
            refine ⟨1218541473683565203743121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3249443929822840543314989 1218541473683565203743121)
            ·
              refine ⟨913906105262673902807341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1218541473683565203743121 913906105262673902807341)
              ·
                refine ⟨342714789473502713552753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 913906105262673902807341 342714789473502713552753)
                ·
                  refine ⟨257036092105127035164565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 342714789473502713552753 257036092105127035164565)
                  ·
                    rfl

theorem cell20_563148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 3, 2].length) (baseStart_563148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563148 prefixEnd_563148 := by exact prefixLift 563148
  have htrace : WordTrace (prefixWord ++ tailWord_563148) baseStart_563148 baseEnd_563148 := by
    simpa [prefixWord, tailWord_563148, baseEnd_563148] using wordTrace_append hprefix tailTrace_563148
  have hstable : (prefixWord ++ tailWord_563148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563148).length < 2 ^ (prefixWord ++ tailWord_563148).sum := by decide
  have hdescent : baseEnd_563148 < baseStart_563148 := by decide
  rcases family_descends (prefixWord ++ tailWord_563148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563158 : List Nat := [5, 2, 1, 1, 3, 2, 1, 2, 3]
def baseStart_563158 : Nat := 118140960795 + 563158 * 2 ^ 59
def prefixEnd_563158 : Nat := 4983230072969 + 3 ^ 40 * 563158 * 2
def baseEnd_563158 : Nat := 257040656377611444831191

theorem tailTrace_563158 : CollatzResearch.WordTrace tailWord_563158 prefixEnd_563158 257040656377611444831191 := by
  unfold tailWord_563158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1283753730861388785890633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13693373129188147049500085 1283753730861388785890633)
  ·
    refine ⟨962815298146041589417975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1283753730861388785890633 962815298146041589417975)
    ·
      refine ⟨1444222947219062384126963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 962815298146041589417975 1444222947219062384126963)
      ·
        refine ⟨2166334420828593576190445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1444222947219062384126963 2166334420828593576190445)
        ·
          refine ⟨812375407810722591071417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2166334420828593576190445 812375407810722591071417)
          ·
            refine ⟨609281555858041943303563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 812375407810722591071417 609281555858041943303563)
            ·
              refine ⟨913922333787062914955345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 609281555858041943303563 913922333787062914955345)
              ·
                refine ⟨685441750340297186216509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 913922333787062914955345 685441750340297186216509)
                ·
                  refine ⟨257040656377611444831191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 685441750340297186216509 257040656377611444831191)
                  ·
                    rfl

theorem cell20_563158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_563158 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563158 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563158 prefixEnd_563158 := by exact prefixLift 563158
  have htrace : WordTrace (prefixWord ++ tailWord_563158) baseStart_563158 baseEnd_563158 := by
    simpa [prefixWord, tailWord_563158, baseEnd_563158] using wordTrace_append hprefix tailTrace_563158
  have hstable : (prefixWord ++ tailWord_563158).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563158).length < 2 ^ (prefixWord ++ tailWord_563158).sum := by decide
  have hdescent : baseEnd_563158 < baseStart_563158 := by decide
  rcases family_descends (prefixWord ++ tailWord_563158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563169 : List Nat := [1, 2, 3, 1, 2, 1, 4, 4, 2]
def baseStart_563169 : Nat := 118140960795 + 563169 * 2 ^ 59
def prefixEnd_563169 : Nat := 4983230072969 + 3 ^ 40 * 563169 * 2
def baseEnd_563169 : Nat := 257045677077344295464479

theorem tailTrace_563169 : CollatzResearch.WordTrace tailWord_563169 prefixEnd_563169 257045677077344295464479 := by
  unfold tailWord_563169
  simp only [CollatzResearch.WordTrace]
  refine ⟨20540460896742369452900561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13693640597828246301933707 20540460896742369452900561)
  ·
    refine ⟨15405345672556777089675421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20540460896742369452900561 15405345672556777089675421)
    ·
      refine ⟨5777004627208791408628283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15405345672556777089675421 5777004627208791408628283)
      ·
        refine ⟨8665506940813187112942425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5777004627208791408628283 8665506940813187112942425)
        ·
          refine ⟨6499130205609890334706819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8665506940813187112942425 6499130205609890334706819)
          ·
            refine ⟨9748695308414835502060229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6499130205609890334706819 9748695308414835502060229)
            ·
              refine ⟨1827880370327781656636293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9748695308414835502060229 1827880370327781656636293)
              ·
                refine ⟨342727569436459060619305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1827880370327781656636293 342727569436459060619305)
                ·
                  refine ⟨257045677077344295464479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 342727569436459060619305 257045677077344295464479)
                  ·
                    rfl

theorem cell20_563169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 4, 2].length) (baseStart_563169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563169 prefixEnd_563169 := by exact prefixLift 563169
  have htrace : WordTrace (prefixWord ++ tailWord_563169) baseStart_563169 baseEnd_563169 := by
    simpa [prefixWord, tailWord_563169, baseEnd_563169] using wordTrace_append hprefix tailTrace_563169
  have hstable : (prefixWord ++ tailWord_563169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563169).length < 2 ^ (prefixWord ++ tailWord_563169).sum := by decide
  have hdescent : baseEnd_563169 < baseStart_563169 := by decide
  rcases family_descends (prefixWord ++ tailWord_563169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563206 : List Nat := [6, 2, 1, 2, 2, 1, 6]
def baseStart_563206 : Nat := 118140960795 + 563206 * 2 ^ 59
def prefixEnd_563206 : Nat := 4983230072969 + 3 ^ 40 * 563206 * 2
def baseEnd_563206 : Nat := 28562507209504067914555

theorem tailTrace_563206 : CollatzResearch.WordTrace tailWord_563206 prefixEnd_563206 28562507209504067914555 := by
  unfold tailWord_563206
  simp only [CollatzResearch.WordTrace]
  refine ⟨641931574925260149124921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13694540265072216514664981 641931574925260149124921)
  ·
    refine ⟨481448681193945111843691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 641931574925260149124921 481448681193945111843691)
    ·
      refine ⟨722173021790917667765537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 481448681193945111843691 722173021790917667765537)
      ·
        refine ⟨541629766343188250824153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 722173021790917667765537 541629766343188250824153)
        ·
          refine ⟨406222324757391188118115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 541629766343188250824153 406222324757391188118115)
          ·
            refine ⟨609333487136086782177173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406222324757391188118115 609333487136086782177173)
            ·
              refine ⟨28562507209504067914555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 609333487136086782177173 28562507209504067914555)
              ·
                rfl

theorem cell20_563206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 6].length) (baseStart_563206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563206 prefixEnd_563206 := by exact prefixLift 563206
  have htrace : WordTrace (prefixWord ++ tailWord_563206) baseStart_563206 baseEnd_563206 := by
    simpa [prefixWord, tailWord_563206, baseEnd_563206] using wordTrace_append hprefix tailTrace_563206
  have hstable : (prefixWord ++ tailWord_563206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563206).length < 2 ^ (prefixWord ++ tailWord_563206).sum := by decide
  have hdescent : baseEnd_563206 < baseStart_563206 := by decide
  rcases family_descends (prefixWord ++ tailWord_563206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563220 : List Nat := [2, 4, 3, 2, 2, 1, 1, 1, 4]
def baseStart_563220 : Nat := 118140960795 + 563220 * 2 ^ 59
def prefixEnd_563220 : Nat := 4983230072969 + 3 ^ 40 * 563220 * 2
def baseEnd_563220 : Nat := 257068954867014784764271

theorem tailTrace_563220 : CollatzResearch.WordTrace tailWord_563220 prefixEnd_563220 257068954867014784764271 := by
  unfold tailWord_563220
  simp only [CollatzResearch.WordTrace]
  refine ⟨10271160509778802581503557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13694880679705070108671409 10271160509778802581503557)
  ·
    refine ⟨1925842595583525484031917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10271160509778802581503557 1925842595583525484031917)
    ·
      refine ⟨722190973343822056511969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1925842595583525484031917 722190973343822056511969)
      ·
        refine ⟨541643230007866542383977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 722190973343822056511969 541643230007866542383977)
        ·
          refine ⟨406232422505899906787983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 541643230007866542383977 406232422505899906787983)
          ·
            refine ⟨609348633758849860181975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406232422505899906787983 609348633758849860181975)
            ·
              refine ⟨914022950638274790272963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 609348633758849860181975 914022950638274790272963)
              ·
                refine ⟨1371034425957412185409445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 914022950638274790272963 1371034425957412185409445)
                ·
                  refine ⟨257068954867014784764271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1371034425957412185409445 257068954867014784764271)
                  ·
                    rfl

theorem cell20_563220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_563220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563220 prefixEnd_563220 := by exact prefixLift 563220
  have htrace : WordTrace (prefixWord ++ tailWord_563220) baseStart_563220 baseEnd_563220 := by
    simpa [prefixWord, tailWord_563220, baseEnd_563220] using wordTrace_append hprefix tailTrace_563220
  have hstable : (prefixWord ++ tailWord_563220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563220).length < 2 ^ (prefixWord ++ tailWord_563220).sum := by decide
  have hdescent : baseEnd_563220 < baseStart_563220 := by decide
  rcases family_descends (prefixWord ++ tailWord_563220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563224 : List Nat := [2, 1, 2, 3, 2, 1, 5, 2, 2]
def baseStart_563224 : Nat := 118140960795 + 563224 * 2 ^ 59
def prefixEnd_563224 : Nat := 4983230072969 + 3 ^ 40 * 563224 * 2
def baseEnd_563224 : Nat := 257070780576008548630921

theorem tailTrace_563224 : CollatzResearch.WordTrace tailWord_563224 prefixEnd_563224 257070780576008548630921 := by
  unfold tailWord_563224
  simp only [CollatzResearch.WordTrace]
  refine ⟨10271233455771556923076363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13694977941028742564101817 10271233455771556923076363)
  ·
    refine ⟨15406850183657335384614545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10271233455771556923076363 15406850183657335384614545)
    ·
      refine ⟨11555137637743001538460909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15406850183657335384614545 11555137637743001538460909)
      ·
        refine ⟨4333176614153625576922841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11555137637743001538460909 4333176614153625576922841)
        ·
          refine ⟨3249882460615219182692131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4333176614153625576922841 3249882460615219182692131)
          ·
            refine ⟨4874823690922828774038197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3249882460615219182692131 4874823690922828774038197)
            ·
              refine ⟨457014721024015197566081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4874823690922828774038197 457014721024015197566081)
              ·
                refine ⟨342761040768011398174561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 457014721024015197566081 342761040768011398174561)
                ·
                  refine ⟨257070780576008548630921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 342761040768011398174561 257070780576008548630921)
                  ·
                    rfl

theorem cell20_563224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 2, 2].length) (baseStart_563224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563224 prefixEnd_563224 := by exact prefixLift 563224
  have htrace : WordTrace (prefixWord ++ tailWord_563224) baseStart_563224 baseEnd_563224 := by
    simpa [prefixWord, tailWord_563224, baseEnd_563224] using wordTrace_append hprefix tailTrace_563224
  have hstable : (prefixWord ++ tailWord_563224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563224).length < 2 ^ (prefixWord ++ tailWord_563224).sum := by decide
  have hdescent : baseEnd_563224 < baseStart_563224 := by decide
  rcases family_descends (prefixWord ++ tailWord_563224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563235 : List Nat := [1, 1, 1, 4, 3, 1, 4, 5]
def baseStart_563235 : Nat := 118140960795 + 563235 * 2 ^ 59
def prefixEnd_563235 : Nat := 4983230072969 + 3 ^ 40 * 563235 * 2
def baseEnd_563235 : Nat := 85691933758580466421403

theorem tailTrace_563235 : CollatzResearch.WordTrace tailWord_563235 prefixEnd_563235 85691933758580466421403 := by
  unfold tailWord_563235
  simp only [CollatzResearch.WordTrace]
  refine ⟨20542868114503262724803159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13695245409668841816535439 20542868114503262724803159)
  ·
    refine ⟨30814302171754894087204739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20542868114503262724803159 30814302171754894087204739)
    ·
      refine ⟨46221453257632341130807109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30814302171754894087204739 46221453257632341130807109)
      ·
        refine ⟨8666522485806063962026333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46221453257632341130807109 8666522485806063962026333)
        ·
          refine ⟨3249945932177273985759875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8666522485806063962026333 3249945932177273985759875)
          ·
            refine ⟨4874918898265910978639813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3249945932177273985759875 4874918898265910978639813)
            ·
              refine ⟨914047293424858308494965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4874918898265910978639813 914047293424858308494965)
              ·
                refine ⟨85691933758580466421403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 914047293424858308494965 85691933758580466421403)
                ·
                  rfl

theorem cell20_563235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 5].length) (baseStart_563235 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563235 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563235 prefixEnd_563235 := by exact prefixLift 563235
  have htrace : WordTrace (prefixWord ++ tailWord_563235) baseStart_563235 baseEnd_563235 := by
    simpa [prefixWord, tailWord_563235, baseEnd_563235] using wordTrace_append hprefix tailTrace_563235
  have hstable : (prefixWord ++ tailWord_563235).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563235).length < 2 ^ (prefixWord ++ tailWord_563235).sum := by decide
  have hdescent : baseEnd_563235 < baseStart_563235 := by decide
  rcases family_descends (prefixWord ++ tailWord_563235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563286 : List Nat := [5, 2, 2, 1, 1, 3, 1, 5]
def baseStart_563286 : Nat := 118140960795 + 563286 * 2 ^ 59
def prefixEnd_563286 : Nat := 4983230072969 + 3 ^ 40 * 563286 * 2
def baseEnd_563286 : Nat := 85699693021803962854667

theorem tailTrace_563286 : CollatzResearch.WordTrace tailWord_563286 prefixEnd_563286 85699693021803962854667 := by
  unfold tailWord_563286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1284045514832406152181857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13696485491545665623273141 1284045514832406152181857)
  ·
    refine ⟨963034136124304614136393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1284045514832406152181857 963034136124304614136393)
    ·
      refine ⟨722275602093228460602295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 963034136124304614136393 722275602093228460602295)
      ·
        refine ⟨1083413403139842690903443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 722275602093228460602295 1083413403139842690903443)
        ·
          refine ⟨1625120104709764036355165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1083413403139842690903443 1625120104709764036355165)
          ·
            refine ⟨609420039266161513633187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1625120104709764036355165 609420039266161513633187)
            ·
              refine ⟨914130058899242270449781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 609420039266161513633187 914130058899242270449781)
              ·
                refine ⟨85699693021803962854667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 914130058899242270449781 85699693021803962854667)
                ·
                  rfl

theorem cell20_563286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_563286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563286 prefixEnd_563286 := by exact prefixLift 563286
  have htrace : WordTrace (prefixWord ++ tailWord_563286) baseStart_563286 baseEnd_563286 := by
    simpa [prefixWord, tailWord_563286, baseEnd_563286] using wordTrace_append hprefix tailTrace_563286
  have hstable : (prefixWord ++ tailWord_563286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563286).length < 2 ^ (prefixWord ++ tailWord_563286).sum := by decide
  have hdescent : baseEnd_563286 < baseStart_563286 := by decide
  rcases family_descends (prefixWord ++ tailWord_563286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563321 : List Nat := [1, 2, 1, 3, 4, 1, 1, 5, 2]
def baseStart_563321 : Nat := 118140960795 + 563321 * 2 ^ 59
def prefixEnd_563321 : Nat := 4983230072969 + 3 ^ 40 * 563321 * 2
def baseEnd_563321 : Nat := 257115054019107322397191

theorem tailTrace_563321 : CollatzResearch.WordTrace tailWord_563321 prefixEnd_563321 257115054019107322397191 := by
  unfold tailWord_563321
  simp only [CollatzResearch.WordTrace]
  refine ⟨20546004792191699412433817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13697336528127799608289211 20546004792191699412433817)
  ·
    refine ⟨15409503594143774559325363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20546004792191699412433817 15409503594143774559325363)
    ·
      refine ⟨23114255391215661838988045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15409503594143774559325363 23114255391215661838988045)
      ·
        refine ⟨8667845771705873189620517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23114255391215661838988045 8667845771705873189620517)
        ·
          refine ⟨1625221082194851223053847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8667845771705873189620517 1625221082194851223053847)
          ·
            refine ⟨2437831623292276834580771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1625221082194851223053847 2437831623292276834580771)
            ·
              refine ⟨3656747434938415251871157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2437831623292276834580771 3656747434938415251871157)
              ·
                refine ⟨342820072025476429862921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3656747434938415251871157 342820072025476429862921)
                ·
                  refine ⟨257115054019107322397191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 342820072025476429862921 257115054019107322397191)
                  ·
                    rfl

theorem cell20_563321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 5, 2].length) (baseStart_563321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563321 prefixEnd_563321 := by exact prefixLift 563321
  have htrace : WordTrace (prefixWord ++ tailWord_563321) baseStart_563321 baseEnd_563321 := by
    simpa [prefixWord, tailWord_563321, baseEnd_563321] using wordTrace_append hprefix tailTrace_563321
  have hstable : (prefixWord ++ tailWord_563321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563321).length < 2 ^ (prefixWord ++ tailWord_563321).sum := by decide
  have hdescent : baseEnd_563321 < baseStart_563321 := by decide
  rcases family_descends (prefixWord ++ tailWord_563321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563335 : List Nat := [1, 1, 4, 2, 1, 1, 5, 2, 3]
def baseStart_563335 : Nat := 118140960795 + 563335 * 2 ^ 59
def prefixEnd_563335 : Nat := 4983230072969 + 3 ^ 40 * 563335 * 2
def baseEnd_563335 : Nat := 257121444000585495930467

theorem tailTrace_563335 : CollatzResearch.WordTrace tailWord_563335 prefixEnd_563335 257121444000585495930467 := by
  unfold tailWord_563335
  simp only [CollatzResearch.WordTrace]
  refine ⟨20546515414140979803443459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13697676942760653202295639 20546515414140979803443459)
  ·
    refine ⟨30819773121211469705165189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20546515414140979803443459 30819773121211469705165189)
    ·
      refine ⟨5778707460227150569718473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30819773121211469705165189 5778707460227150569718473)
      ·
        refine ⟨4334030595170362927288855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5778707460227150569718473 4334030595170362927288855)
        ·
          refine ⟨6501045892755544390933283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4334030595170362927288855 6501045892755544390933283)
          ·
            refine ⟨9751568839133316586399925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6501045892755544390933283 9751568839133316586399925)
            ·
              refine ⟨914209578668748429974993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9751568839133316586399925 914209578668748429974993)
              ·
                refine ⟨685657184001561322481245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 914209578668748429974993 685657184001561322481245)
                ·
                  refine ⟨257121444000585495930467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 685657184001561322481245 257121444000585495930467)
                  ·
                    rfl

theorem cell20_563335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 3].length) (baseStart_563335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563335 prefixEnd_563335 := by exact prefixLift 563335
  have htrace : WordTrace (prefixWord ++ tailWord_563335) baseStart_563335 baseEnd_563335 := by
    simpa [prefixWord, tailWord_563335, baseEnd_563335] using wordTrace_append hprefix tailTrace_563335
  have hstable : (prefixWord ++ tailWord_563335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563335).length < 2 ^ (prefixWord ++ tailWord_563335).sum := by decide
  have hdescent : baseEnd_563335 < baseStart_563335 := by decide
  rcases family_descends (prefixWord ++ tailWord_563335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563348 : List Nat := [2, 4, 2, 3, 1, 1, 3, 1, 3]
def baseStart_563348 : Nat := 118140960795 + 563348 * 2 ^ 59
def prefixEnd_563348 : Nat := 4983230072969 + 3 ^ 40 * 563348 * 2
def baseEnd_563348 : Nat := 257127377554815228497081

theorem tailTrace_563348 : CollatzResearch.WordTrace tailWord_563348 prefixEnd_563348 257127377554815228497081 := by
  unfold tailWord_563348
  simp only [CollatzResearch.WordTrace]
  refine ⟨10273494781546941511833349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13697993042062588682444465 10273494781546941511833349)
  ·
    refine ⟨1926280271540051533468753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10273494781546941511833349 1926280271540051533468753)
    ·
      refine ⟨1444710203655038650101565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1926280271540051533468753 1444710203655038650101565)
      ·
        refine ⟨541766326370639493788087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1444710203655038650101565 541766326370639493788087)
        ·
          refine ⟨812649489555959240682131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 541766326370639493788087 812649489555959240682131)
          ·
            refine ⟨1218974234333938861023197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 812649489555959240682131 1218974234333938861023197)
            ·
              refine ⟨457115337875227072883699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1218974234333938861023197 457115337875227072883699)
              ·
                refine ⟨685673006812840609325549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 457115337875227072883699 685673006812840609325549)
                ·
                  refine ⟨257127377554815228497081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 685673006812840609325549 257127377554815228497081)
                  ·
                    rfl

theorem cell20_563348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_563348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563348 prefixEnd_563348 := by exact prefixLift 563348
  have htrace : WordTrace (prefixWord ++ tailWord_563348) baseStart_563348 baseEnd_563348 := by
    simpa [prefixWord, tailWord_563348, baseEnd_563348] using wordTrace_append hprefix tailTrace_563348
  have hstable : (prefixWord ++ tailWord_563348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563348).length < 2 ^ (prefixWord ++ tailWord_563348).sum := by decide
  have hdescent : baseEnd_563348 < baseStart_563348 := by decide
  rcases family_descends (prefixWord ++ tailWord_563348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563373 : List Nat := [1, 5, 2, 1, 2, 1, 1, 2, 5]
def baseStart_563373 : Nat := 118140960795 + 563373 * 2 ^ 59
def prefixEnd_563373 : Nat := 4983230072969 + 3 ^ 40 * 563373 * 2
def baseEnd_563373 : Nat := 257138788236026252663645

theorem tailTrace_563373 : CollatzResearch.WordTrace tailWord_563373 prefixEnd_563373 257138788236026252663645 := by
  unfold tailWord_563373
  simp only [CollatzResearch.WordTrace]
  refine ⟨20547901388003312293326773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13698600925335541528884515 20547901388003312293326773)
  ·
    refine ⟨1926365755125310527499385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20547901388003312293326773 1926365755125310527499385)
    ·
      refine ⟨1444774316343982895624539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1926365755125310527499385 1444774316343982895624539)
      ·
        refine ⟨2167161474515974343436809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1444774316343982895624539 2167161474515974343436809)
        ·
          refine ⟨1625371105886980757577607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2167161474515974343436809 1625371105886980757577607)
          ·
            refine ⟨2438056658830471136366411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1625371105886980757577607 2438056658830471136366411)
            ·
              refine ⟨3657084988245706704549617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2438056658830471136366411 3657084988245706704549617)
              ·
                refine ⟨2742813741184280028412213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3657084988245706704549617 2742813741184280028412213)
                ·
                  refine ⟨257138788236026252663645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2742813741184280028412213 257138788236026252663645)
                  ·
                    rfl

theorem cell20_563373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_563373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563373 prefixEnd_563373 := by exact prefixLift 563373
  have htrace : WordTrace (prefixWord ++ tailWord_563373) baseStart_563373 baseEnd_563373 := by
    simpa [prefixWord, tailWord_563373, baseEnd_563373] using wordTrace_append hprefix tailTrace_563373
  have hstable : (prefixWord ++ tailWord_563373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563373).length < 2 ^ (prefixWord ++ tailWord_563373).sum := by decide
  have hdescent : baseEnd_563373 < baseStart_563373 := by decide
  rcases family_descends (prefixWord ++ tailWord_563373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563393 : List Nat := [1, 2, 6, 1, 3, 1, 1, 1, 4]
def baseStart_563393 : Nat := 118140960795 + 563393 * 2 ^ 59
def prefixEnd_563393 : Nat := 4983230072969 + 3 ^ 40 * 563393 * 2
def baseEnd_563393 : Nat := 257147916780995071996897

theorem tailTrace_563393 : CollatzResearch.WordTrace tailWord_563393 prefixEnd_563393 257147916780995071996897 := by
  unfold tailWord_563393
  simp only [CollatzResearch.WordTrace]
  refine ⟨20548630847930855709054833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13699087231953903806036555 20548630847930855709054833)
  ·
    refine ⟨15411473135948141781791125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20548630847930855709054833 15411473135948141781791125)
    ·
      refine ⟨722412803247569146021459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15411473135948141781791125 722412803247569146021459)
      ·
        refine ⟨1083619204871353719032189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 722412803247569146021459 1083619204871353719032189)
        ·
          refine ⟨406357201826757644637071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1083619204871353719032189 406357201826757644637071)
          ·
            refine ⟨609535802740136466955607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406357201826757644637071 609535802740136466955607)
            ·
              refine ⟨914303704110204700433411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 609535802740136466955607 914303704110204700433411)
              ·
                refine ⟨1371455556165307050650117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 914303704110204700433411 1371455556165307050650117)
                ·
                  refine ⟨257147916780995071996897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1371455556165307050650117 257147916780995071996897)
                  ·
                    rfl

theorem cell20_563393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 4].length) (baseStart_563393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563393 prefixEnd_563393 := by exact prefixLift 563393
  have htrace : WordTrace (prefixWord ++ tailWord_563393) baseStart_563393 baseEnd_563393 := by
    simpa [prefixWord, tailWord_563393, baseEnd_563393] using wordTrace_append hprefix tailTrace_563393
  have hstable : (prefixWord ++ tailWord_563393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563393).length < 2 ^ (prefixWord ++ tailWord_563393).sum := by decide
  have hdescent : baseEnd_563393 < baseStart_563393 := by decide
  rcases family_descends (prefixWord ++ tailWord_563393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563401 : List Nat := [1, 2, 1, 1, 2, 1, 1, 7, 4]
def baseStart_563401 : Nat := 118140960795 + 563401 * 2 ^ 59
def prefixEnd_563401 : Nat := 4983230072969 + 3 ^ 40 * 563401 * 2
def baseEnd_563401 : Nat := 257151568198982599730197

theorem tailTrace_563401 : CollatzResearch.WordTrace tailWord_563401 prefixEnd_563401 257151568198982599730197 := by
  unfold tailWord_563401
  simp only [CollatzResearch.WordTrace]
  refine ⟨20548922631901873075346057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13699281754601248716897371 20548922631901873075346057)
  ·
    refine ⟨15411691973926404806509543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20548922631901873075346057 15411691973926404806509543)
    ·
      refine ⟨23117537960889607209764315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15411691973926404806509543 23117537960889607209764315)
      ·
        refine ⟨34676306941334410814646473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23117537960889607209764315 34676306941334410814646473)
        ·
          refine ⟨26007230206000808110984855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34676306941334410814646473 26007230206000808110984855)
          ·
            refine ⟨39010845309001212166477283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26007230206000808110984855 39010845309001212166477283)
            ·
              refine ⟨58516267963501818249715925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39010845309001212166477283 58516267963501818249715925)
              ·
                refine ⟨1371475030394573865227717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 58516267963501818249715925 1371475030394573865227717)
                ·
                  refine ⟨257151568198982599730197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1371475030394573865227717 257151568198982599730197)
                  ·
                    rfl

theorem cell20_563401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_563401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563401 prefixEnd_563401 := by exact prefixLift 563401
  have htrace : WordTrace (prefixWord ++ tailWord_563401) baseStart_563401 baseEnd_563401 := by
    simpa [prefixWord, tailWord_563401, baseEnd_563401] using wordTrace_append hprefix tailTrace_563401
  have hstable : (prefixWord ++ tailWord_563401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563401).length < 2 ^ (prefixWord ++ tailWord_563401).sum := by decide
  have hdescent : baseEnd_563401 < baseStart_563401 := by decide
  rcases family_descends (prefixWord ++ tailWord_563401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563452 : List Nat := [2, 2, 2, 1, 4, 1, 4, 2, 2]
def baseStart_563452 : Nat := 118140960795 + 563452 * 2 ^ 59
def prefixEnd_563452 : Nat := 4983230072969 + 3 ^ 40 * 563452 * 2
def baseEnd_563452 : Nat := 257174845988653089029989

theorem tailTrace_563452 : CollatzResearch.WordTrace tailWord_563452 prefixEnd_563452 257174845988653089029989 := by
  unfold tailWord_563452
  simp only [CollatzResearch.WordTrace]
  refine ⟨10275391377358554392726305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13700521836478072523635073 10275391377358554392726305)
  ·
    refine ⟨7706543533018915794544729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10275391377358554392726305 7706543533018915794544729)
    ·
      refine ⟨5779907649764186845908547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7706543533018915794544729 5779907649764186845908547)
      ·
        refine ⟨8669861474646280268862821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5779907649764186845908547 8669861474646280268862821)
        ·
          refine ⟨1625599026496177550411779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8669861474646280268862821 1625599026496177550411779)
          ·
            refine ⟨2438398539744266325617669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1625599026496177550411779 2438398539744266325617669)
            ·
              refine ⟨457199726202049936053313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2438398539744266325617669 457199726202049936053313)
              ·
                refine ⟨342899794651537452039985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 457199726202049936053313 342899794651537452039985)
                ·
                  refine ⟨257174845988653089029989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 342899794651537452039985 257174845988653089029989)
                  ·
                    rfl

theorem cell20_563452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 2, 2].length) (baseStart_563452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563452 prefixEnd_563452 := by exact prefixLift 563452
  have htrace : WordTrace (prefixWord ++ tailWord_563452) baseStart_563452 baseEnd_563452 := by
    simpa [prefixWord, tailWord_563452, baseEnd_563452] using wordTrace_append hprefix tailTrace_563452
  have hstable : (prefixWord ++ tailWord_563452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563452).length < 2 ^ (prefixWord ++ tailWord_563452).sum := by decide
  have hdescent : baseEnd_563452 < baseStart_563452 := by decide
  rcases family_descends (prefixWord ++ tailWord_563452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563477 : List Nat := [1, 3, 2, 1, 2, 1, 3, 1, 6]
def baseStart_563477 : Nat := 118140960795 + 563477 * 2 ^ 59
def prefixEnd_563477 : Nat := 4983230072969 + 3 ^ 40 * 563477 * 2
def baseEnd_563477 : Nat := 257186256669864113196553

theorem tailTrace_563477 : CollatzResearch.WordTrace tailWord_563477 prefixEnd_563477 257186256669864113196553 := by
  unfold tailWord_563477
  simp only [CollatzResearch.WordTrace]
  refine ⟨20551694579626538055112685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13701129719751025370075123 20551694579626538055112685)
  ·
    refine ⟨7706885467359951770667257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20551694579626538055112685 7706885467359951770667257)
    ·
      refine ⟨5780164100519963828000443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7706885467359951770667257 5780164100519963828000443)
      ·
        refine ⟨8670246150779945742000665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5780164100519963828000443 8670246150779945742000665)
        ·
          refine ⟨6502684613084959306500499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8670246150779945742000665 6502684613084959306500499)
          ·
            refine ⟨9754026919627438959750749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6502684613084959306500499 9754026919627438959750749)
            ·
              refine ⟨3657760094860289609906531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9754026919627438959750749 3657760094860289609906531)
              ·
                refine ⟨5486640142290434414859797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3657760094860289609906531 5486640142290434414859797)
                ·
                  refine ⟨257186256669864113196553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5486640142290434414859797 257186256669864113196553)
                  ·
                    rfl

theorem cell20_563477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_563477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563477 prefixEnd_563477 := by exact prefixLift 563477
  have htrace : WordTrace (prefixWord ++ tailWord_563477) baseStart_563477 baseEnd_563477 := by
    simpa [prefixWord, tailWord_563477, baseEnd_563477] using wordTrace_append hprefix tailTrace_563477
  have hstable : (prefixWord ++ tailWord_563477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563477).length < 2 ^ (prefixWord ++ tailWord_563477).sum := by decide
  have hdescent : baseEnd_563477 < baseStart_563477 := by decide
  rcases family_descends (prefixWord ++ tailWord_563477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563490 : List Nat := [3, 3, 1, 1, 3, 2, 2, 3, 2]
def baseStart_563490 : Nat := 118140960795 + 563490 * 2 ^ 59
def prefixEnd_563490 : Nat := 4983230072969 + 3 ^ 40 * 563490 * 2
def baseEnd_563490 : Nat := 257192190224093845763167

theorem tailTrace_563490 : CollatzResearch.WordTrace tailWord_563490 prefixEnd_563490 257192190224093845763167 := by
  unfold tailWord_563490
  simp only [CollatzResearch.WordTrace]
  refine ⟨5138042182144860318833981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13701445819052960850223949 5138042182144860318833981)
  ·
    refine ⟨1926765818304322619562743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5138042182144860318833981 1926765818304322619562743)
    ·
      refine ⟨2890148727456483929344115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1926765818304322619562743 2890148727456483929344115)
      ·
        refine ⟨4335223091184725894016173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2890148727456483929344115 4335223091184725894016173)
        ·
          refine ⟨1625708659194272210256065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4335223091184725894016173 1625708659194272210256065)
          ·
            refine ⟨1219281494395704157692049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1625708659194272210256065 1219281494395704157692049)
            ·
              refine ⟨914461120796778118269037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1219281494395704157692049 914461120796778118269037)
              ·
                refine ⟨342922920298791794350889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 914461120796778118269037 342922920298791794350889)
                ·
                  refine ⟨257192190224093845763167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 342922920298791794350889 257192190224093845763167)
                  ·
                    rfl

theorem cell20_563490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_563490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563490 prefixEnd_563490 := by exact prefixLift 563490
  have htrace : WordTrace (prefixWord ++ tailWord_563490) baseStart_563490 baseEnd_563490 := by
    simpa [prefixWord, tailWord_563490, baseEnd_563490] using wordTrace_append hprefix tailTrace_563490
  have hstable : (prefixWord ++ tailWord_563490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563490).length < 2 ^ (prefixWord ++ tailWord_563490).sum := by decide
  have hdescent : baseEnd_563490 < baseStart_563490 := by decide
  rcases family_descends (prefixWord ++ tailWord_563490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563521 : List Nat := [1, 2, 5, 2, 2, 1, 3, 1, 3]
def baseStart_563521 : Nat := 118140960795 + 563521 * 2 ^ 59
def prefixEnd_563521 : Nat := 4983230072969 + 3 ^ 40 * 563521 * 2
def baseEnd_563521 : Nat := 257206339468795515729707

theorem tailTrace_563521 : CollatzResearch.WordTrace tailWord_563521 prefixEnd_563521 257206339468795515729707 := by
  unfold tailWord_563521
  simp only [CollatzResearch.WordTrace]
  refine ⟨20553299391467133569714417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13702199594311422379809611 20553299391467133569714417)
  ·
    refine ⟨15414974543600350177285813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20553299391467133569714417 15414974543600350177285813)
    ·
      refine ⟨1445153863462532829120545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15414974543600350177285813 1445153863462532829120545)
      ·
        refine ⟨1083865397596899621840409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1445153863462532829120545 1083865397596899621840409)
        ·
          refine ⟨812899048197674716380307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1083865397596899621840409 812899048197674716380307)
          ·
            refine ⟨1219348572296512074570461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 812899048197674716380307 1219348572296512074570461)
            ·
              refine ⟨457255714611192027963923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1219348572296512074570461 457255714611192027963923)
              ·
                refine ⟨685883571916788041945885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 457255714611192027963923 685883571916788041945885)
                ·
                  refine ⟨257206339468795515729707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 685883571916788041945885 257206339468795515729707)
                  ·
                    rfl

theorem cell20_563521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 3].length) (baseStart_563521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563521 prefixEnd_563521 := by exact prefixLift 563521
  have htrace : WordTrace (prefixWord ++ tailWord_563521) baseStart_563521 baseEnd_563521 := by
    simpa [prefixWord, tailWord_563521, baseEnd_563521] using wordTrace_append hprefix tailTrace_563521
  have hstable : (prefixWord ++ tailWord_563521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563521).length < 2 ^ (prefixWord ++ tailWord_563521).sum := by decide
  have hdescent : baseEnd_563521 < baseStart_563521 := by decide
  rcases family_descends (prefixWord ++ tailWord_563521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563570 : List Nat := [3, 2, 1, 2, 1, 3, 3, 1, 4]
def baseStart_563570 : Nat := 118140960795 + 563570 * 2 ^ 59
def prefixEnd_563570 : Nat := 4983230072969 + 3 ^ 40 * 563570 * 2
def baseEnd_563570 : Nat := 257228704403969123096173

theorem tailTrace_563570 : CollatzResearch.WordTrace tailWord_563570 prefixEnd_563570 257228704403969123096173 := by
  unfold tailWord_563570
  simp only [CollatzResearch.WordTrace]
  refine ⟨5138771642072403734562041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13703391045526409958832109 5138771642072403734562041)
  ·
    refine ⟨3854078731554302800921531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5138771642072403734562041 3854078731554302800921531)
    ·
      refine ⟨5781118097331454201382297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3854078731554302800921531 5781118097331454201382297)
      ·
        refine ⟨4335838572998590651036723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5781118097331454201382297 4335838572998590651036723)
        ·
          refine ⟨6503757859497885976555085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4335838572998590651036723 6503757859497885976555085)
          ·
            refine ⟨2438909197311707241208157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6503757859497885976555085 2438909197311707241208157)
            ·
              refine ⟨914590948991890215453059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2438909197311707241208157 914590948991890215453059)
              ·
                refine ⟨1371886423487835323179589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 914590948991890215453059 1371886423487835323179589)
                ·
                  refine ⟨257228704403969123096173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1371886423487835323179589 257228704403969123096173)
                  ·
                    rfl

theorem cell20_563570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_563570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563570 prefixEnd_563570 := by exact prefixLift 563570
  have htrace : WordTrace (prefixWord ++ tailWord_563570) baseStart_563570 baseEnd_563570 := by
    simpa [prefixWord, tailWord_563570, baseEnd_563570] using wordTrace_append hprefix tailTrace_563570
  have hstable : (prefixWord ++ tailWord_563570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563570).length < 2 ^ (prefixWord ++ tailWord_563570).sum := by decide
  have hdescent : baseEnd_563570 < baseStart_563570 := by decide
  rcases family_descends (prefixWord ++ tailWord_563570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563591 : List Nat := [1, 1, 4, 2, 2, 1, 2, 1, 6]
def baseStart_563591 : Nat := 118140960795 + 563591 * 2 ^ 59
def prefixEnd_563591 : Nat := 4983230072969 + 3 ^ 40 * 563591 * 2
def baseEnd_563591 : Nat := 257238289376186383396087

theorem tailTrace_563591 : CollatzResearch.WordTrace tailWord_563591 prefixEnd_563591 257238289376186383396087 := by
  unfold tailWord_563591
  simp only [CollatzResearch.WordTrace]
  refine ⟨20555852501213535524762627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13703901667475690349841751 20555852501213535524762627)
  ·
    refine ⟨30833778751820303287143941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20555852501213535524762627 30833778751820303287143941)
    ·
      refine ⟨5781333515966306866339489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30833778751820303287143941 5781333515966306866339489)
      ·
        refine ⟨4336000136974730149754617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5781333515966306866339489 4336000136974730149754617)
        ·
          refine ⟨3252000102731047612315963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4336000136974730149754617 3252000102731047612315963)
          ·
            refine ⟨4878000154096571418473945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3252000102731047612315963 4878000154096571418473945)
            ·
              refine ⟨3658500115572428563855459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4878000154096571418473945 3658500115572428563855459)
              ·
                refine ⟨5487750173358642845783189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3658500115572428563855459 5487750173358642845783189)
                ·
                  refine ⟨257238289376186383396087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5487750173358642845783189 257238289376186383396087)
                  ·
                    rfl

theorem cell20_563591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 6].length) (baseStart_563591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563591 prefixEnd_563591 := by exact prefixLift 563591
  have htrace : WordTrace (prefixWord ++ tailWord_563591) baseStart_563591 baseEnd_563591 := by
    simpa [prefixWord, tailWord_563591, baseEnd_563591] using wordTrace_append hprefix tailTrace_563591
  have hstable : (prefixWord ++ tailWord_563591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563591).length < 2 ^ (prefixWord ++ tailWord_563591).sum := by decide
  have hdescent : baseEnd_563591 < baseStart_563591 := by decide
  rcases family_descends (prefixWord ++ tailWord_563591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563674 : List Nat := [3, 1, 1, 2, 3, 1, 9]
def baseStart_563674 : Nat := 118140960795 + 563674 * 2 ^ 59
def prefixEnd_563674 : Nat := 4983230072969 + 3 ^ 40 * 563674 * 2
def baseEnd_563674 : Nat := 28586241426422998181009

theorem tailTrace_563674 : CollatzResearch.WordTrace tailWord_563674 prefixEnd_563674 28586241426422998181009 := by
  unfold tailWord_563674
  simp only [CollatzResearch.WordTrace]
  refine ⟨5139719939978210175008519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13705919839941893800022717 5139719939978210175008519)
  ·
    refine ⟨7709579909967315262512779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5139719939978210175008519 7709579909967315262512779)
    ·
      refine ⟨11564369864950972893769169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7709579909967315262512779 11564369864950972893769169)
      ·
        refine ⟨8673277398713229670326877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11564369864950972893769169 8673277398713229670326877)
        ·
          refine ⟨3252479024517461126372579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8673277398713229670326877 3252479024517461126372579)
          ·
            refine ⟨4878718536776191689558869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3252479024517461126372579 4878718536776191689558869)
            ·
              refine ⟨28586241426422998181009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4878718536776191689558869 28586241426422998181009)
              ·
                rfl

theorem cell20_563674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 9].length) (baseStart_563674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563674 prefixEnd_563674 := by exact prefixLift 563674
  have htrace : WordTrace (prefixWord ++ tailWord_563674) baseStart_563674 baseEnd_563674 := by
    simpa [prefixWord, tailWord_563674, baseEnd_563674] using wordTrace_append hprefix tailTrace_563674
  have hstable : (prefixWord ++ tailWord_563674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563674).length < 2 ^ (prefixWord ++ tailWord_563674).sum := by decide
  have hdescent : baseEnd_563674 < baseStart_563674 := by decide
  rcases family_descends (prefixWord ++ tailWord_563674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563694 : List Nat := [4, 1, 2, 1, 2, 3, 3, 1, 3]
def baseStart_563694 : Nat := 118140960795 + 563694 * 2 ^ 59
def prefixEnd_563694 : Nat := 4983230072969 + 3 ^ 40 * 563694 * 2
def baseEnd_563694 : Nat := 257285301382775802962333

theorem tailTrace_563694 : CollatzResearch.WordTrace tailWord_563694 prefixEnd_563694 257285301382775802962333 := by
  unfold tailWord_563694
  simp only [CollatzResearch.WordTrace]
  refine ⟨2569951152480048014470267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13706406146560256077174757 2569951152480048014470267)
  ·
    refine ⟨3854926728720072021705401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2569951152480048014470267 3854926728720072021705401)
    ·
      refine ⟨2891195046540054016279051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3854926728720072021705401 2891195046540054016279051)
      ·
        refine ⟨4336792569810081024418577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2891195046540054016279051 4336792569810081024418577)
        ·
          refine ⟨3252594427357560768313933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4336792569810081024418577 3252594427357560768313933)
          ·
            refine ⟨1219722910259085288117725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3252594427357560768313933 1219722910259085288117725)
            ·
              refine ⟨457396091347156983044147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1219722910259085288117725 457396091347156983044147)
              ·
                refine ⟨686094137020735474566221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 457396091347156983044147 686094137020735474566221)
                ·
                  refine ⟨257285301382775802962333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 686094137020735474566221 257285301382775802962333)
                  ·
                    rfl

theorem cell20_563694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_563694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563694 prefixEnd_563694 := by exact prefixLift 563694
  have htrace : WordTrace (prefixWord ++ tailWord_563694) baseStart_563694 baseEnd_563694 := by
    simpa [prefixWord, tailWord_563694, baseEnd_563694] using wordTrace_append hprefix tailTrace_563694
  have hstable : (prefixWord ++ tailWord_563694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563694).length < 2 ^ (prefixWord ++ tailWord_563694).sum := by decide
  have hdescent : baseEnd_563694 < baseStart_563694 := by decide
  rcases family_descends (prefixWord ++ tailWord_563694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563705 : List Nat := [1, 2, 1, 3, 1, 2, 4, 2, 4]
def baseStart_563705 : Nat := 118140960795 + 563705 * 2 ^ 59
def prefixEnd_563705 : Nat := 4983230072969 + 3 ^ 40 * 563705 * 2
def baseEnd_563705 : Nat := 257290322082508653595621

theorem tailTrace_563705 : CollatzResearch.WordTrace tailWord_563705 prefixEnd_563705 257290322082508653595621 := by
  unfold tailWord_563705
  simp only [CollatzResearch.WordTrace]
  refine ⟨20560010422800532994412569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13706673615200355329608379 20560010422800532994412569)
  ·
    refine ⟨15420007817100399745809427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20560010422800532994412569 15420007817100399745809427)
    ·
      refine ⟨23130011725650599618714141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15420007817100399745809427 23130011725650599618714141)
      ·
        refine ⟨8673754397118974857017803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23130011725650599618714141 8673754397118974857017803)
        ·
          refine ⟨13010631595678462285526705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8673754397118974857017803 13010631595678462285526705)
          ·
            refine ⟨9757973696758846714145029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13010631595678462285526705 9757973696758846714145029)
            ·
              refine ⟨1829620068142283758902193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9757973696758846714145029 1829620068142283758902193)
              ·
                refine ⟨1372215051106712819176645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1829620068142283758902193 1372215051106712819176645)
                ·
                  refine ⟨257290322082508653595621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1372215051106712819176645 257290322082508653595621)
                  ·
                    rfl

theorem cell20_563705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_563705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563705 prefixEnd_563705 := by exact prefixLift 563705
  have htrace : WordTrace (prefixWord ++ tailWord_563705) baseStart_563705 baseEnd_563705 := by
    simpa [prefixWord, tailWord_563705, baseEnd_563705] using wordTrace_append hprefix tailTrace_563705
  have hstable : (prefixWord ++ tailWord_563705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563705).length < 2 ^ (prefixWord ++ tailWord_563705).sum := by decide
  have hdescent : baseEnd_563705 < baseStart_563705 := by decide
  rcases family_descends (prefixWord ++ tailWord_563705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563714 : List Nat := [3, 4, 1, 2, 3, 1, 1, 3, 2]
def baseStart_563714 : Nat := 118140960795 + 563714 * 2 ^ 59
def prefixEnd_563714 : Nat := 4983230072969 + 3 ^ 40 * 563714 * 2
def baseEnd_563714 : Nat := 257294429927744622295585

theorem tailTrace_563714 : CollatzResearch.WordTrace tailWord_563714 prefixEnd_563714 257294429927744622295585 := by
  unfold tailWord_563714
  simp only [CollatzResearch.WordTrace]
  refine ⟨5140084669941981882872549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13706892453178618354326797 5140084669941981882872549)
  ·
    refine ⟨963765875614121603038603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5140084669941981882872549 963765875614121603038603)
    ·
      refine ⟨1445648813421182404557905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 963765875614121603038603 1445648813421182404557905)
      ·
        refine ⟨1084236610065886803418429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1445648813421182404557905 1084236610065886803418429)
        ·
          refine ⟨406588728774707551281911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1084236610065886803418429 406588728774707551281911)
          ·
            refine ⟨609883093162061326922867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406588728774707551281911 609883093162061326922867)
            ·
              refine ⟨914824639743091990384301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 609883093162061326922867 914824639743091990384301)
              ·
                refine ⟨343059239903659496394113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 914824639743091990384301 343059239903659496394113)
                ·
                  refine ⟨257294429927744622295585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 343059239903659496394113 257294429927744622295585)
                  ·
                    rfl

theorem cell20_563714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_563714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563714 prefixEnd_563714 := by exact prefixLift 563714
  have htrace : WordTrace (prefixWord ++ tailWord_563714) baseStart_563714 baseEnd_563714 := by
    simpa [prefixWord, tailWord_563714, baseEnd_563714] using wordTrace_append hprefix tailTrace_563714
  have hstable : (prefixWord ++ tailWord_563714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563714).length < 2 ^ (prefixWord ++ tailWord_563714).sum := by decide
  have hdescent : baseEnd_563714 < baseStart_563714 := by decide
  rcases family_descends (prefixWord ++ tailWord_563714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563725 : List Nat := [1, 7, 1, 1, 1, 3, 6]
def baseStart_563725 : Nat := 118140960795 + 563725 * 2 ^ 59
def prefixEnd_563725 : Nat := 4983230072969 + 3 ^ 40 * 563725 * 2
def baseEnd_563725 : Nat := 28588827847497496992097

theorem tailTrace_563725 : CollatzResearch.WordTrace tailWord_563725 prefixEnd_563725 28588827847497496992097 := by
  unfold tailWord_563725
  simp only [CollatzResearch.WordTrace]
  refine ⟨20560739882728076410140629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13707159921818717606760419 20560739882728076410140629)
  ·
    refine ⟨481892341001439290862671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 20560739882728076410140629 481892341001439290862671)
    ·
      refine ⟨722838511502158936294007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 481892341001439290862671 722838511502158936294007)
      ·
        refine ⟨1084257767253238404441011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 722838511502158936294007 1084257767253238404441011)
        ·
          refine ⟨1626386650879857606661517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1084257767253238404441011 1626386650879857606661517)
          ·
            refine ⟨609894994079946602498069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1626386650879857606661517 609894994079946602498069)
            ·
              refine ⟨28588827847497496992097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 609894994079946602498069 28588827847497496992097)
              ·
                rfl

theorem cell20_563725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 6].length) (baseStart_563725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563725 prefixEnd_563725 := by exact prefixLift 563725
  have htrace : WordTrace (prefixWord ++ tailWord_563725) baseStart_563725 baseEnd_563725 := by
    simpa [prefixWord, tailWord_563725, baseEnd_563725] using wordTrace_append hprefix tailTrace_563725
  have hstable : (prefixWord ++ tailWord_563725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563725).length < 2 ^ (prefixWord ++ tailWord_563725).sum := by decide
  have hdescent : baseEnd_563725 < baseStart_563725 := by decide
  rcases family_descends (prefixWord ++ tailWord_563725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563735 : List Nat := [1, 1, 3, 6, 1, 1, 3, 2, 2]
def baseStart_563735 : Nat := 118140960795 + 563735 * 2 ^ 59
def prefixEnd_563735 : Nat := 4983230072969 + 3 ^ 40 * 563735 * 2
def baseEnd_563735 : Nat := 257304014899961882595499

theorem tailTrace_563735 : CollatzResearch.WordTrace tailWord_563735 prefixEnd_563735 257304014899961882595499 := by
  unfold tailWord_563735
  simp only [CollatzResearch.WordTrace]
  refine ⟨20561104612691848118004659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13707403075127898745336439 20561104612691848118004659)
  ·
    refine ⟨30841656919037772177006989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20561104612691848118004659 30841656919037772177006989)
    ·
      refine ⟨11565621344639164566377621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30841656919037772177006989 11565621344639164566377621)
      ·
        refine ⟨542138500529960839048951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11565621344639164566377621 542138500529960839048951)
        ·
          refine ⟨813207750794941258573427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 542138500529960839048951 813207750794941258573427)
          ·
            refine ⟨1219811626192411887860141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 813207750794941258573427 1219811626192411887860141)
            ·
              refine ⟨457429359822154457947553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1219811626192411887860141 457429359822154457947553)
              ·
                refine ⟨343072019866615843460665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 457429359822154457947553 343072019866615843460665)
                ·
                  refine ⟨257304014899961882595499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 343072019866615843460665 257304014899961882595499)
                  ·
                    rfl

theorem cell20_563735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 2, 2].length) (baseStart_563735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563735 prefixEnd_563735 := by exact prefixLift 563735
  have htrace : WordTrace (prefixWord ++ tailWord_563735) baseStart_563735 baseEnd_563735 := by
    simpa [prefixWord, tailWord_563735, baseEnd_563735] using wordTrace_append hprefix tailTrace_563735
  have hstable : (prefixWord ++ tailWord_563735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563735).length < 2 ^ (prefixWord ++ tailWord_563735).sum := by decide
  have hdescent : baseEnd_563735 < baseStart_563735 := by decide
  rcases family_descends (prefixWord ++ tailWord_563735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563736 : List Nat := [2, 1, 2, 3, 3, 1, 2, 1, 5]
def baseStart_563736 : Nat := 118140960795 + 563736 * 2 ^ 59
def prefixEnd_563736 : Nat := 4983230072969 + 3 ^ 40 * 563736 * 2
def baseEnd_563736 : Nat := 257304471327210323562161

theorem tailTrace_563736 : CollatzResearch.WordTrace tailWord_563736 prefixEnd_563736 257304471327210323562161 := by
  unfold tailWord_563736
  simp only [CollatzResearch.WordTrace]
  refine ⟨10280570542844112644395531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13707427390458816859194041 10280570542844112644395531)
  ·
    refine ⟨15420855814266168966593297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10280570542844112644395531 15420855814266168966593297)
    ·
      refine ⟨11565641860699626724944973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15420855814266168966593297 11565641860699626724944973)
      ·
        refine ⟨4337115697762360021854365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11565641860699626724944973 4337115697762360021854365)
        ·
          refine ⟨1626418386660885008195387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4337115697762360021854365 1626418386660885008195387)
          ·
            refine ⟨2439627579991327512293081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1626418386660885008195387 2439627579991327512293081)
            ·
              refine ⟨1829720684993495634219811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2439627579991327512293081 1829720684993495634219811)
              ·
                refine ⟨2744581027490243451329717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1829720684993495634219811 2744581027490243451329717)
                ·
                  refine ⟨257304471327210323562161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2744581027490243451329717 257304471327210323562161)
                  ·
                    rfl

theorem cell20_563736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_563736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563736 prefixEnd_563736 := by exact prefixLift 563736
  have htrace : WordTrace (prefixWord ++ tailWord_563736) baseStart_563736 baseEnd_563736 := by
    simpa [prefixWord, tailWord_563736, baseEnd_563736] using wordTrace_append hprefix tailTrace_563736
  have hstable : (prefixWord ++ tailWord_563736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563736).length < 2 ^ (prefixWord ++ tailWord_563736).sum := by decide
  have hdescent : baseEnd_563736 < baseStart_563736 := by decide
  rcases family_descends (prefixWord ++ tailWord_563736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563812 : List Nat := [2, 3, 1, 1, 2, 2, 1, 5, 3]
def baseStart_563812 : Nat := 118140960795 + 563812 * 2 ^ 59
def prefixEnd_563812 : Nat := 4983230072969 + 3 ^ 40 * 563812 * 2
def baseEnd_563812 : Nat := 257339159798091837028517

theorem tailTrace_563812 : CollatzResearch.WordTrace tailWord_563812 prefixEnd_563812 257339159798091837028517 := by
  unfold tailWord_563812
  simp only [CollatzResearch.WordTrace]
  refine ⟨10281956516706445134278845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13709275355608593512371793 10281956516706445134278845)
  ·
    refine ⟨3855733693764916925354567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10281956516706445134278845 3855733693764916925354567)
    ·
      refine ⟨5783600540647375388031851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3855733693764916925354567 5783600540647375388031851)
      ·
        refine ⟨8675400810971063082047777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5783600540647375388031851 8675400810971063082047777)
        ·
          refine ⟨6506550608228297311535833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8675400810971063082047777 6506550608228297311535833)
          ·
            refine ⟨4879912956171222983651875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6506550608228297311535833 4879912956171222983651875)
            ·
              refine ⟨7319869434256834475477813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4879912956171222983651875 7319869434256834475477813)
              ·
                refine ⟨686237759461578232076045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7319869434256834475477813 686237759461578232076045)
                ·
                  refine ⟨257339159798091837028517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 686237759461578232076045 257339159798091837028517)
                  ·
                    rfl

theorem cell20_563812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_563812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563812 prefixEnd_563812 := by exact prefixLift 563812
  have htrace : WordTrace (prefixWord ++ tailWord_563812) baseStart_563812 baseEnd_563812 := by
    simpa [prefixWord, tailWord_563812, baseEnd_563812] using wordTrace_append hprefix tailTrace_563812
  have hstable : (prefixWord ++ tailWord_563812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563812).length < 2 ^ (prefixWord ++ tailWord_563812).sum := by decide
  have hdescent : baseEnd_563812 < baseStart_563812 := by decide
  rcases family_descends (prefixWord ++ tailWord_563812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563822 : List Nat := [4, 1, 2, 2, 2, 2, 3, 4]
def baseStart_563822 : Nat := 118140960795 + 563822 * 2 ^ 59
def prefixEnd_563822 : Nat := 4983230072969 + 3 ^ 40 * 563822 * 2
def baseEnd_563822 : Nat := 85781241356858748898381

theorem tailTrace_563822 : CollatzResearch.WordTrace tailWord_563822 prefixEnd_563822 85781241356858748898381 := by
  unfold tailWord_563822
  simp only [CollatzResearch.WordTrace]
  refine ⟨2570534720422082747052715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13709518508917774650947813 2570534720422082747052715)
  ·
    refine ⟨3855802080633124120579073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2570534720422082747052715 3855802080633124120579073)
    ·
      refine ⟨2891851560474843090434305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3855802080633124120579073 2891851560474843090434305)
      ·
        refine ⟨2168888670356132317825729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2891851560474843090434305 2168888670356132317825729)
        ·
          refine ⟨1626666502767099238369297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2168888670356132317825729 1626666502767099238369297)
          ·
            refine ⟨1219999877075324428776973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1626666502767099238369297 1219999877075324428776973)
            ·
              refine ⟨457499953903246660791365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1219999877075324428776973 457499953903246660791365)
              ·
                refine ⟨85781241356858748898381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 457499953903246660791365 85781241356858748898381)
                ·
                  rfl

theorem cell20_563822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_563822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563822 prefixEnd_563822 := by exact prefixLift 563822
  have htrace : WordTrace (prefixWord ++ tailWord_563822) baseStart_563822 baseEnd_563822 := by
    simpa [prefixWord, tailWord_563822, baseEnd_563822] using wordTrace_append hprefix tailTrace_563822
  have hstable : (prefixWord ++ tailWord_563822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563822).length < 2 ^ (prefixWord ++ tailWord_563822).sum := by decide
  have hdescent : baseEnd_563822 < baseStart_563822 := by decide
  rcases family_descends (prefixWord ++ tailWord_563822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563836 : List Nat := [2, 2, 2, 1, 1, 2, 3, 5, 2]
def baseStart_563836 : Nat := 118140960795 + 563836 * 2 ^ 59
def prefixEnd_563836 : Nat := 4983230072969 + 3 ^ 40 * 563836 * 2
def baseEnd_563836 : Nat := 257350114052054420228419

theorem tailTrace_563836 : CollatzResearch.WordTrace tailWord_563836 prefixEnd_563836 257350114052054420228419 := by
  unfold tailWord_563836
  simp only [CollatzResearch.WordTrace]
  refine ⟨10282394192662971183715681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13709858923550628244954241 10282394192662971183715681)
  ·
    refine ⟨7711795644497228387786761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10282394192662971183715681 7711795644497228387786761)
    ·
      refine ⟨5783846733372921290840071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7711795644497228387786761 5783846733372921290840071)
      ·
        refine ⟨8675770100059381936260107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5783846733372921290840071 8675770100059381936260107)
        ·
          refine ⟨13013655150089072904390161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8675770100059381936260107 13013655150089072904390161)
          ·
            refine ⟨9760241362566804678292621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13013655150089072904390161 9760241362566804678292621)
            ·
              refine ⟨3660090510962551754359733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9760241362566804678292621 3660090510962551754359733)
              ·
                refine ⟨343133485402739226971225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3660090510962551754359733 343133485402739226971225)
                ·
                  refine ⟨257350114052054420228419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 343133485402739226971225 257350114052054420228419)
                  ·
                    rfl

theorem cell20_563836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 5, 2].length) (baseStart_563836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563836 prefixEnd_563836 := by exact prefixLift 563836
  have htrace : WordTrace (prefixWord ++ tailWord_563836) baseStart_563836 baseEnd_563836 := by
    simpa [prefixWord, tailWord_563836, baseEnd_563836] using wordTrace_append hprefix tailTrace_563836
  have hstable : (prefixWord ++ tailWord_563836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563836).length < 2 ^ (prefixWord ++ tailWord_563836).sum := by decide
  have hdescent : baseEnd_563836 < baseStart_563836 := by decide
  rcases family_descends (prefixWord ++ tailWord_563836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563864 : List Nat := [2, 1, 2, 4, 1, 1, 2, 7]
def baseStart_563864 : Nat := 118140960795 + 563864 * 2 ^ 59
def prefixEnd_563864 : Nat := 4983230072969 + 3 ^ 40 * 563864 * 2
def baseEnd_563864 : Nat := 85787631338336922431657

theorem tailTrace_563864 : CollatzResearch.WordTrace tailWord_563864 prefixEnd_563864 85787631338336922431657 := by
  unfold tailWord_563864
  simp only [CollatzResearch.WordTrace]
  refine ⟨10282904814612251574725323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13710539752816335432967097 10282904814612251574725323)
  ·
    refine ⟨15424357221918377362087985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10282904814612251574725323 15424357221918377362087985)
    ·
      refine ⟨11568267916438783021565989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15424357221918377362087985 11568267916438783021565989)
      ·
        refine ⟨2169050234332271816543623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11568267916438783021565989 2169050234332271816543623)
        ·
          refine ⟨3253575351498407724815435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2169050234332271816543623 3253575351498407724815435)
          ·
            refine ⟨4880363027247611587223153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3253575351498407724815435 4880363027247611587223153)
            ·
              refine ⟨3660272270435708690417365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4880363027247611587223153 3660272270435708690417365)
              ·
                refine ⟨85787631338336922431657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3660272270435708690417365 85787631338336922431657)
                ·
                  rfl

theorem cell20_563864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 7].length) (baseStart_563864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563864 prefixEnd_563864 := by exact prefixLift 563864
  have htrace : WordTrace (prefixWord ++ tailWord_563864) baseStart_563864 baseEnd_563864 := by
    simpa [prefixWord, tailWord_563864, baseEnd_563864] using wordTrace_append hprefix tailTrace_563864
  have hstable : (prefixWord ++ tailWord_563864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563864).length < 2 ^ (prefixWord ++ tailWord_563864).sum := by decide
  have hdescent : baseEnd_563864 < baseStart_563864 := by decide
  rcases family_descends (prefixWord ++ tailWord_563864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563891 : List Nat := [1, 1, 1, 2, 3, 6, 1, 3, 2]
def baseStart_563891 : Nat := 118140960795 + 563891 * 2 ^ 59
def prefixEnd_563891 : Nat := 4983230072969 + 3 ^ 40 * 563891 * 2
def baseEnd_563891 : Nat := 257375217550718673394861

theorem tailTrace_563891 : CollatzResearch.WordTrace tailWord_563891 prefixEnd_563891 257375217550718673394861 := by
  unfold tailWord_563891
  simp only [CollatzResearch.WordTrace]
  refine ⟨20566794400126686760683527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13711196266751124507122351 20566794400126686760683527)
  ·
    refine ⟨30850191600190030141025291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20566794400126686760683527 30850191600190030141025291)
    ·
      refine ⟨46275287400285045211537937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30850191600190030141025291 46275287400285045211537937)
      ·
        refine ⟨34706465550213783908653453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46275287400285045211537937 34706465550213783908653453)
        ·
          refine ⟨13014924581330168965745045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34706465550213783908653453 13014924581330168965745045)
          ·
            refine ⟨610074589749851670269299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13014924581330168965745045 610074589749851670269299)
            ·
              refine ⟨915111884624777505403949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 610074589749851670269299 915111884624777505403949)
              ·
                refine ⟨343166956734291564526481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 915111884624777505403949 343166956734291564526481)
                ·
                  refine ⟨257375217550718673394861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 343166956734291564526481 257375217550718673394861)
                  ·
                    rfl

theorem cell20_563891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 3, 2].length) (baseStart_563891 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563891 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563891 prefixEnd_563891 := by exact prefixLift 563891
  have htrace : WordTrace (prefixWord ++ tailWord_563891) baseStart_563891 baseEnd_563891 := by
    simpa [prefixWord, tailWord_563891, baseEnd_563891] using wordTrace_append hprefix tailTrace_563891
  have hstable : (prefixWord ++ tailWord_563891).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563891).length < 2 ^ (prefixWord ++ tailWord_563891).sum := by decide
  have hdescent : baseEnd_563891 < baseStart_563891 := by decide
  rcases family_descends (prefixWord ++ tailWord_563891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563908 : List Nat := [2, 3, 3, 1, 1, 3, 3, 2, 2]
def baseStart_563908 : Nat := 118140960795 + 563908 * 2 ^ 59
def prefixEnd_563908 : Nat := 4983230072969 + 3 ^ 40 * 563908 * 2
def baseEnd_563908 : Nat := 257382976813942169828125

theorem tailTrace_563908 : CollatzResearch.WordTrace tailWord_563908 prefixEnd_563908 257382976813942169828125 := by
  unfold tailWord_563908
  simp only [CollatzResearch.WordTrace]
  refine ⟨10283707220532549332026189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13711609627376732442701585 10283707220532549332026189)
  ·
    refine ⟨3856390207699705999509821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10283707220532549332026189 3856390207699705999509821)
    ·
      refine ⟨1446146327887389749816183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3856390207699705999509821 1446146327887389749816183)
      ·
        refine ⟨2169219491831084624724275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1446146327887389749816183 2169219491831084624724275)
        ·
          refine ⟨3253829237746626937086413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2169219491831084624724275 3253829237746626937086413)
          ·
            refine ⟨1220185964154985101407405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3253829237746626937086413 1220185964154985101407405)
            ·
              refine ⟨457569736558119413027777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1220185964154985101407405 457569736558119413027777)
              ·
                refine ⟨343177302418589559770833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 457569736558119413027777 343177302418589559770833)
                ·
                  refine ⟨257382976813942169828125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 343177302418589559770833 257382976813942169828125)
                  ·
                    rfl

theorem cell20_563908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_563908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563908 prefixEnd_563908 := by exact prefixLift 563908
  have htrace : WordTrace (prefixWord ++ tailWord_563908) baseStart_563908 baseEnd_563908 := by
    simpa [prefixWord, tailWord_563908, baseEnd_563908] using wordTrace_append hprefix tailTrace_563908
  have hstable : (prefixWord ++ tailWord_563908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563908).length < 2 ^ (prefixWord ++ tailWord_563908).sum := by decide
  have hdescent : baseEnd_563908 < baseStart_563908 := by decide
  rcases family_descends (prefixWord ++ tailWord_563908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563912 : List Nat := [2, 1, 3, 1, 2, 5, 1, 1, 4]
def baseStart_563912 : Nat := 118140960795 + 563912 * 2 ^ 59
def prefixEnd_563912 : Nat := 4983230072969 + 3 ^ 40 * 563912 * 2
def baseEnd_563912 : Nat := 257384802522935933694775

theorem tailTrace_563912 : CollatzResearch.WordTrace tailWord_563912 prefixEnd_563912 257384802522935933694775 := by
  unfold tailWord_563912
  simp only [CollatzResearch.WordTrace]
  refine ⟨10283780166525303673598995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13711706888700404898131993 10283780166525303673598995)
  ·
    refine ⟨15425670249787955510398493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10283780166525303673598995 15425670249787955510398493)
    ·
      refine ⟨5784626343670483316399435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15425670249787955510398493 5784626343670483316399435)
      ·
        refine ⟨8676939515505724974599153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5784626343670483316399435 8676939515505724974599153)
        ·
          refine ⟨6507704636629293730949365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8676939515505724974599153 6507704636629293730949365)
          ·
            refine ⟨610097309683996287276503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6507704636629293730949365 610097309683996287276503)
            ·
              refine ⟨915145964525994430914755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 610097309683996287276503 915145964525994430914755)
              ·
                refine ⟨1372718946788991646372133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 915145964525994430914755 1372718946788991646372133)
                ·
                  refine ⟨257384802522935933694775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1372718946788991646372133 257384802522935933694775)
                  ·
                    rfl

theorem cell20_563912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 4].length) (baseStart_563912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563912 prefixEnd_563912 := by exact prefixLift 563912
  have htrace : WordTrace (prefixWord ++ tailWord_563912) baseStart_563912 baseEnd_563912 := by
    simpa [prefixWord, tailWord_563912, baseEnd_563912] using wordTrace_append hprefix tailTrace_563912
  have hstable : (prefixWord ++ tailWord_563912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563912).length < 2 ^ (prefixWord ++ tailWord_563912).sum := by decide
  have hdescent : baseEnd_563912 < baseStart_563912 := by decide
  rcases family_descends (prefixWord ++ tailWord_563912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563940 : List Nat := [2, 3, 1, 1, 1, 4, 2, 6]
def baseStart_563940 : Nat := 118140960795 + 563940 * 2 ^ 59
def prefixEnd_563940 : Nat := 4983230072969 + 3 ^ 40 * 563940 * 2
def baseEnd_563940 : Nat := 85799194161964093587109

theorem tailTrace_563940 : CollatzResearch.WordTrace tailWord_563940 prefixEnd_563940 85799194161964093587109 := by
  unfold tailWord_563940
  simp only [CollatzResearch.WordTrace]
  refine ⟨10284290788474584064608637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13712387717966112086144849 10284290788474584064608637)
  ·
    refine ⟨3856609045677969024228239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10284290788474584064608637 3856609045677969024228239)
    ·
      refine ⟨5784913568516953536342359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3856609045677969024228239 5784913568516953536342359)
      ·
        refine ⟨8677370352775430304513539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5784913568516953536342359 8677370352775430304513539)
        ·
          refine ⟨13016055529163145456770309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8677370352775430304513539 13016055529163145456770309)
          ·
            refine ⟨2440510411718089773144433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13016055529163145456770309 2440510411718089773144433)
            ·
              refine ⟨1830382808788567329858325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2440510411718089773144433 1830382808788567329858325)
              ·
                refine ⟨85799194161964093587109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1830382808788567329858325 85799194161964093587109)
                ·
                  rfl

theorem cell20_563940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 6].length) (baseStart_563940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563940 prefixEnd_563940 := by exact prefixLift 563940
  have htrace : WordTrace (prefixWord ++ tailWord_563940) baseStart_563940 baseEnd_563940 := by
    simpa [prefixWord, tailWord_563940, baseEnd_563940] using wordTrace_append hprefix tailTrace_563940
  have hstable : (prefixWord ++ tailWord_563940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563940).length < 2 ^ (prefixWord ++ tailWord_563940).sum := by decide
  have hdescent : baseEnd_563940 < baseStart_563940 := by decide
  rcases family_descends (prefixWord ++ tailWord_563940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563964 : List Nat := [2, 2, 2, 1, 3, 2, 1, 4, 3]
def baseStart_563964 : Nat := 118140960795 + 563964 * 2 ^ 59
def prefixEnd_563964 : Nat := 4983230072969 + 3 ^ 40 * 563964 * 2
def baseEnd_563964 : Nat := 257408536739854863961229

theorem tailTrace_563964 : CollatzResearch.WordTrace tailWord_563964 prefixEnd_563964 257408536739854863961229 := by
  unfold tailWord_563964
  simp only [CollatzResearch.WordTrace]
  refine ⟨10284728464431110114045473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13712971285908146818727297 10284728464431110114045473)
  ·
    refine ⟨7713546348323332585534105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10284728464431110114045473 7713546348323332585534105)
    ·
      refine ⟨5785159761242499439150579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7713546348323332585534105 5785159761242499439150579)
      ·
        refine ⟨8677739641863749158725869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5785159761242499439150579 8677739641863749158725869)
        ·
          refine ⟨3254152365698905934522201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8677739641863749158725869 3254152365698905934522201)
          ·
            refine ⟨2440614274274179450891651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3254152365698905934522201 2440614274274179450891651)
            ·
              refine ⟨3660921411411269176337477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2440614274274179450891651 3660921411411269176337477)
              ·
                refine ⟨686422764639612970563277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3660921411411269176337477 686422764639612970563277)
                ·
                  refine ⟨257408536739854863961229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 686422764639612970563277 257408536739854863961229)
                  ·
                    rfl

theorem cell20_563964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_563964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_563964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_563964 prefixEnd_563964 := by exact prefixLift 563964
  have htrace : WordTrace (prefixWord ++ tailWord_563964) baseStart_563964 baseEnd_563964 := by
    simpa [prefixWord, tailWord_563964, baseEnd_563964] using wordTrace_append hprefix tailTrace_563964
  have hstable : (prefixWord ++ tailWord_563964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563964).length < 2 ^ (prefixWord ++ tailWord_563964).sum := by decide
  have hdescent : baseEnd_563964 < baseStart_563964 := by decide
  rcases family_descends (prefixWord ++ tailWord_563964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564019 : List Nat := [1, 1, 1, 2, 6, 3, 1, 2, 3]
def baseStart_564019 : Nat := 118140960795 + 564019 * 2 ^ 59
def prefixEnd_564019 : Nat := 4983230072969 + 3 ^ 40 * 564019 * 2
def baseEnd_564019 : Nat := 257433640238519117127671

theorem tailTrace_564019 : CollatzResearch.WordTrace tailWord_564019 prefixEnd_564019 257433640238519117127671 := by
  unfold tailWord_564019
  simp only [CollatzResearch.WordTrace]
  refine ⟨20571462943662964621343111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13714308629108643080895407 20571462943662964621343111)
  ·
    refine ⟨30857194415494446932014667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20571462943662964621343111 30857194415494446932014667)
    ·
      refine ⟨46285791623241670398022001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30857194415494446932014667 46285791623241670398022001)
      ·
        refine ⟨34714343717431252798516501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46285791623241670398022001 34714343717431252798516501)
        ·
          refine ⟨1627234861754589974930461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34714343717431252798516501 1627234861754589974930461)
          ·
            refine ⟨610213073157971240598923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1627234861754589974930461 610213073157971240598923)
            ·
              refine ⟨915319609736956860898385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 610213073157971240598923 915319609736956860898385)
              ·
                refine ⟨686489707302717645673789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 915319609736956860898385 686489707302717645673789)
                ·
                  refine ⟨257433640238519117127671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 686489707302717645673789 257433640238519117127671)
                  ·
                    rfl

theorem cell20_564019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 3].length) (baseStart_564019 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_564019 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_564019 prefixEnd_564019 := by exact prefixLift 564019
  have htrace : WordTrace (prefixWord ++ tailWord_564019) baseStart_564019 baseEnd_564019 := by
    simpa [prefixWord, tailWord_564019, baseEnd_564019] using wordTrace_append hprefix tailTrace_564019
  have hstable : (prefixWord ++ tailWord_564019).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564019).length < 2 ^ (prefixWord ++ tailWord_564019).sum := by decide
  have hdescent : baseEnd_564019 < baseStart_564019 := by decide
  rcases family_descends (prefixWord ++ tailWord_564019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564023 : List Nat := [1, 1, 3, 1, 2, 1, 5, 1, 5]
def baseStart_564023 : Nat := 118140960795 + 564023 * 2 ^ 59
def prefixEnd_564023 : Nat := 4983230072969 + 3 ^ 40 * 564023 * 2
def baseEnd_564023 : Nat := 257435465947512880994321

theorem tailTrace_564023 : CollatzResearch.WordTrace tailWord_564023 prefixEnd_564023 257435465947512880994321 := by
  unfold tailWord_564023
  simp only [CollatzResearch.WordTrace]
  refine ⟨20571608835648473304488723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13714405890432315536325815 20571608835648473304488723)
  ·
    refine ⟨30857413253472709956733085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20571608835648473304488723 30857413253472709956733085)
    ·
      refine ⟨11571529970052266233774907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30857413253472709956733085 11571529970052266233774907)
      ·
        refine ⟨17357294955078399350662361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11571529970052266233774907 17357294955078399350662361)
        ·
          refine ⟨13017971216308799512996771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17357294955078399350662361 13017971216308799512996771)
          ·
            refine ⟨19526956824463199269495157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13017971216308799512996771 19526956824463199269495157)
            ·
              refine ⟨1830652202293424931515171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19526956824463199269495157 1830652202293424931515171)
              ·
                refine ⟨2745978303440137397272757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1830652202293424931515171 2745978303440137397272757)
                ·
                  refine ⟨257435465947512880994321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2745978303440137397272757 257435465947512880994321)
                  ·
                    rfl

theorem cell20_564023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 5].length) (baseStart_564023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_564023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_564023 prefixEnd_564023 := by exact prefixLift 564023
  have htrace : WordTrace (prefixWord ++ tailWord_564023) baseStart_564023 baseEnd_564023 := by
    simpa [prefixWord, tailWord_564023, baseEnd_564023] using wordTrace_append hprefix tailTrace_564023
  have hstable : (prefixWord ++ tailWord_564023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564023).length < 2 ^ (prefixWord ++ tailWord_564023).sum := by decide
  have hdescent : baseEnd_564023 < baseStart_564023 := by decide
  rcases family_descends (prefixWord ++ tailWord_564023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564026 : List Nat := [3, 1, 1, 1, 6, 1, 2, 1, 4]
def baseStart_564026 : Nat := 118140960795 + 564026 * 2 ^ 59
def prefixEnd_564026 : Nat := 4983230072969 + 3 ^ 40 * 564026 * 2
def baseEnd_564026 : Nat := 257436835229258203894309

theorem tailTrace_564026 : CollatzResearch.WordTrace tailWord_564026 prefixEnd_564026 257436835229258203894309 := by
  unfold tailWord_564026
  simp only [CollatzResearch.WordTrace]
  refine ⟨5142929563659401204211983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13714478836425069877898621 5142929563659401204211983)
  ·
    refine ⟨7714394345489101806317975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5142929563659401204211983 7714394345489101806317975)
    ·
      refine ⟨11571591518233652709476963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7714394345489101806317975 11571591518233652709476963)
      ·
        refine ⟨17357387277350479064215445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11571591518233652709476963 17357387277350479064215445)
        ·
          refine ⟨813627528625803706135099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17357387277350479064215445 813627528625803706135099)
          ·
            refine ⟨1220441292938705559202649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 813627528625803706135099 1220441292938705559202649)
            ·
              refine ⟨915330969704029169401987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1220441292938705559202649 915330969704029169401987)
              ·
                refine ⟨1372996454556043754102981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 915330969704029169401987 1372996454556043754102981)
                ·
                  refine ⟨257436835229258203894309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1372996454556043754102981 257436835229258203894309)
                  ·
                    rfl

theorem cell20_564026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_564026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_564026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_564026 prefixEnd_564026 := by exact prefixLift 564026
  have htrace : WordTrace (prefixWord ++ tailWord_564026) baseStart_564026 baseEnd_564026 := by
    simpa [prefixWord, tailWord_564026, baseEnd_564026] using wordTrace_append hprefix tailTrace_564026
  have hstable : (prefixWord ++ tailWord_564026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564026).length < 2 ^ (prefixWord ++ tailWord_564026).sum := by decide
  have hdescent : baseEnd_564026 < baseStart_564026 := by decide
  rcases family_descends (prefixWord ++ tailWord_564026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564060 : List Nat := [2, 2, 4, 2, 1, 3, 1, 3, 2]
def baseStart_564060 : Nat := 118140960795 + 564060 * 2 ^ 59
def prefixEnd_564060 : Nat := 4983230072969 + 3 ^ 40 * 564060 * 2
def baseEnd_564060 : Nat := 257452353755705196760837

theorem tailTrace_564060 : CollatzResearch.WordTrace tailWord_564060 prefixEnd_564060 257452353755705196760837 := by
  unfold tailWord_564060
  simp only [CollatzResearch.WordTrace]
  refine ⟨10286479168257214311792817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13715305557676285749057089 10286479168257214311792817)
  ·
    refine ⟨7714859376192910733844613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10286479168257214311792817 7714859376192910733844613)
    ·
      refine ⟨1446536133036170762595865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7714859376192910733844613 1446536133036170762595865)
      ·
        refine ⟨1084902099777128071946899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1446536133036170762595865 1084902099777128071946899)
        ·
          refine ⟨1627353149665692107920349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1084902099777128071946899 1627353149665692107920349)
          ·
            refine ⟨610257431124634540470131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1627353149665692107920349 610257431124634540470131)
            ·
              refine ⟨915386146686951810705197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 610257431124634540470131 915386146686951810705197)
              ·
                refine ⟨343269805007606929014449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 915386146686951810705197 343269805007606929014449)
                ·
                  refine ⟨257452353755705196760837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 343269805007606929014449 257452353755705196760837)
                  ·
                    rfl

theorem cell20_564060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 3, 2].length) (baseStart_564060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_564060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_564060 prefixEnd_564060 := by exact prefixLift 564060
  have htrace : WordTrace (prefixWord ++ tailWord_564060) baseStart_564060 baseEnd_564060 := by
    simpa [prefixWord, tailWord_564060, baseEnd_564060] using wordTrace_append hprefix tailTrace_564060
  have hstable : (prefixWord ++ tailWord_564060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564060).length < 2 ^ (prefixWord ++ tailWord_564060).sum := by decide
  have hdescent : baseEnd_564060 < baseStart_564060 := by decide
  rcases family_descends (prefixWord ++ tailWord_564060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564075 : List Nat := [1, 1, 1, 1, 2, 2, 12]
def baseStart_564075 : Nat := 118140960795 + 564075 * 2 ^ 59
def prefixEnd_564075 : Nat := 4983230072969 + 3 ^ 40 * 564075 * 2
def baseEnd_564075 : Nat := 28606577796047979028975

theorem tailTrace_564075 : CollatzResearch.WordTrace tailWord_564075 prefixEnd_564075 28606577796047979028975 := by
  unfold tailWord_564075
  simp only [CollatzResearch.WordTrace]
  refine ⟨20573505431460086185381679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13715670287640057456921119 20573505431460086185381679)
  ·
    refine ⟨30860258147190129278072519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20573505431460086185381679 30860258147190129278072519)
    ·
      refine ⟨46290387220785193917108779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30860258147190129278072519 46290387220785193917108779)
      ·
        refine ⟨69435580831177790875663169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46290387220785193917108779 69435580831177790875663169)
        ·
          refine ⟨52076685623383343156747377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69435580831177790875663169 52076685623383343156747377)
          ·
            refine ⟨39057514217537507367560533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52076685623383343156747377 39057514217537507367560533)
            ·
              refine ⟨28606577796047979028975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 39057514217537507367560533 28606577796047979028975)
              ·
                rfl

theorem cell20_564075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 12].length) (baseStart_564075 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_564075 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_564075 prefixEnd_564075 := by exact prefixLift 564075
  have htrace : WordTrace (prefixWord ++ tailWord_564075) baseStart_564075 baseEnd_564075 := by
    simpa [prefixWord, tailWord_564075, baseEnd_564075] using wordTrace_append hprefix tailTrace_564075
  have hstable : (prefixWord ++ tailWord_564075).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564075).length < 2 ^ (prefixWord ++ tailWord_564075).sum := by decide
  have hdescent : baseEnd_564075 < baseStart_564075 := by decide
  rcases family_descends (prefixWord ++ tailWord_564075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564081 : List Nat := [1, 2, 2, 2, 1, 5, 3, 2, 2]
def baseStart_564081 : Nat := 118140960795 + 564081 * 2 ^ 59
def prefixEnd_564081 : Nat := 4983230072969 + 3 ^ 40 * 564081 * 2
def baseEnd_564081 : Nat := 257461938727922457060751

theorem tailTrace_564081 : CollatzResearch.WordTrace tailWord_564081 prefixEnd_564081 257461938727922457060751 := by
  unfold tailWord_564081
  simp only [CollatzResearch.WordTrace]
  refine ⟨20573724269438349210100097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13715816179625566140066731 20573724269438349210100097)
  ·
    refine ⟨15430293202078761907575073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20573724269438349210100097 15430293202078761907575073)
    ·
      refine ⟨11572719901559071430681305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15430293202078761907575073 11572719901559071430681305)
      ·
        refine ⟨8679539926169303573010979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11572719901559071430681305 8679539926169303573010979)
        ·
          refine ⟨13019309889253955359516469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8679539926169303573010979 13019309889253955359516469)
          ·
            refine ⟨1220560302117558314954669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13019309889253955359516469 1220560302117558314954669)
            ·
              refine ⟨457710113294084368108001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1220560302117558314954669 457710113294084368108001)
              ·
                refine ⟨343282584970563276081001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 457710113294084368108001 343282584970563276081001)
                ·
                  refine ⟨257461938727922457060751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 343282584970563276081001 257461938727922457060751)
                  ·
                    rfl

theorem cell20_564081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 2, 2].length) (baseStart_564081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_564081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_564081 prefixEnd_564081 := by exact prefixLift 564081
  have htrace : WordTrace (prefixWord ++ tailWord_564081) baseStart_564081 baseEnd_564081 := by
    simpa [prefixWord, tailWord_564081, baseEnd_564081] using wordTrace_append hprefix tailTrace_564081
  have hstable : (prefixWord ++ tailWord_564081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564081).length < 2 ^ (prefixWord ++ tailWord_564081).sum := by decide
  have hdescent : baseEnd_564081 < baseStart_564081 := by decide
  rcases family_descends (prefixWord ++ tailWord_564081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564130 : List Nat := [3, 3, 1, 2, 2, 9]
def baseStart_564130 : Nat := 118140960795 + 564130 * 2 ^ 59
def prefixEnd_564130 : Nat := 4983230072969 + 3 ^ 40 * 564130 * 2
def baseEnd_564130 : Nat := 9536455691225780163971

theorem tailTrace_564130 : CollatzResearch.WordTrace tailWord_564130 prefixEnd_564130 9536455691225780163971 := by
  unfold tailWord_564130
  simp only [CollatzResearch.WordTrace]
  refine ⟨5143877861565207644658461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13717007630840553719089229 5143877861565207644658461)
  ·
    refine ⟨1928954198086952866746923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5143877861565207644658461 1928954198086952866746923)
    ·
      refine ⟨2893431297130429300120385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1928954198086952866746923 2893431297130429300120385)
      ·
        refine ⟨2170073472847821975090289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2893431297130429300120385 2170073472847821975090289)
        ·
          refine ⟨1627555104635866481317717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2170073472847821975090289 1627555104635866481317717)
          ·
            refine ⟨9536455691225780163971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1627555104635866481317717 9536455691225780163971)
            ·
              rfl

theorem cell20_564130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 9].length) (baseStart_564130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_564130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_564130 prefixEnd_564130 := by exact prefixLift 564130
  have htrace : WordTrace (prefixWord ++ tailWord_564130) baseStart_564130 baseEnd_564130 := by
    simpa [prefixWord, tailWord_564130, baseEnd_564130] using wordTrace_append hprefix tailTrace_564130
  have hstable : (prefixWord ++ tailWord_564130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564130).length < 2 ^ (prefixWord ++ tailWord_564130).sum := by decide
  have hdescent : baseEnd_564130 < baseStart_564130 := by decide
  rcases family_descends (prefixWord ++ tailWord_564130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564199 : List Nat := [1, 1, 5, 2, 2, 1, 1, 3, 4]
def baseStart_564199 : Nat := 118140960795 + 564199 * 2 ^ 59
def prefixEnd_564199 : Nat := 4983230072969 + 3 ^ 40 * 564199 * 2
def baseEnd_564199 : Nat := 257515797143238491126935

theorem tailTrace_564199 : CollatzResearch.WordTrace tailWord_564199 prefixEnd_564199 257515797143238491126935 := by
  unfold tailWord_564199
  simp only [CollatzResearch.WordTrace]
  refine ⟨20578028083010855362895651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13718685388673903575263767 20578028083010855362895651)
  ·
    refine ⟨30867042124516283044343477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20578028083010855362895651 30867042124516283044343477)
    ·
      refine ⟨2893785199173401535407201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30867042124516283044343477 2893785199173401535407201)
      ·
        refine ⟨2170338899380051151555401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2893785199173401535407201 2170338899380051151555401)
        ·
          refine ⟨1627754174535038363666551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2170338899380051151555401 1627754174535038363666551)
          ·
            refine ⟨2441631261802557545499827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1627754174535038363666551 2441631261802557545499827)
            ·
              refine ⟨3662446892703836318249741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2441631261802557545499827 3662446892703836318249741)
              ·
                refine ⟨1373417584763938619343653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3662446892703836318249741 1373417584763938619343653)
                ·
                  refine ⟨257515797143238491126935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1373417584763938619343653 257515797143238491126935)
                  ·
                    rfl

theorem cell20_564199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 4].length) (baseStart_564199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_564199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_564199 prefixEnd_564199 := by exact prefixLift 564199
  have htrace : WordTrace (prefixWord ++ tailWord_564199) baseStart_564199 baseEnd_564199 := by
    simpa [prefixWord, tailWord_564199, baseEnd_564199] using wordTrace_append hprefix tailTrace_564199
  have hstable : (prefixWord ++ tailWord_564199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564199).length < 2 ^ (prefixWord ++ tailWord_564199).sum := by decide
  have hdescent : baseEnd_564199 < baseStart_564199 := by decide
  rcases family_descends (prefixWord ++ tailWord_564199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564209 : List Nat := [1, 2, 2, 2, 4, 2, 3, 1, 3]
def baseStart_564209 : Nat := 118140960795 + 564209 * 2 ^ 59
def prefixEnd_564209 : Nat := 4983230072969 + 3 ^ 40 * 564209 * 2
def baseEnd_564209 : Nat := 257520361415722900793561

theorem tailTrace_564209 : CollatzResearch.WordTrace tailWord_564209 prefixEnd_564209 257520361415722900793561 := by
  unfold tailWord_564209
  simp only [CollatzResearch.WordTrace]
  refine ⟨20578392812974627070759681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13718928541983084713839787 20578392812974627070759681)
  ·
    refine ⟨15433794609730970303069761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20578392812974627070759681 15433794609730970303069761)
    ·
      refine ⟨11575345957298227727302321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15433794609730970303069761 11575345957298227727302321)
      ·
        refine ⟨8681509467973670795476741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11575345957298227727302321 8681509467973670795476741)
        ·
          refine ⟨1627783025245063274151889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8681509467973670795476741 1627783025245063274151889)
          ·
            refine ⟨1220837268933797455613917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1627783025245063274151889 1220837268933797455613917)
            ·
              refine ⟨457813975850174045855219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1220837268933797455613917 457813975850174045855219)
              ·
                refine ⟨686720963775261068782829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 457813975850174045855219 686720963775261068782829)
                ·
                  refine ⟨257520361415722900793561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 686720963775261068782829 257520361415722900793561)
                  ·
                    rfl

theorem cell20_564209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 3].length) (baseStart_564209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_564209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_564209 prefixEnd_564209 := by exact prefixLift 564209
  have htrace : WordTrace (prefixWord ++ tailWord_564209) baseStart_564209 baseEnd_564209 := by
    simpa [prefixWord, tailWord_564209, baseEnd_564209] using wordTrace_append hprefix tailTrace_564209
  have hstable : (prefixWord ++ tailWord_564209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564209).length < 2 ^ (prefixWord ++ tailWord_564209).sum := by decide
  have hdescent : baseEnd_564209 < baseStart_564209 := by decide
  rcases family_descends (prefixWord ++ tailWord_564209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564306 : List Nat := [3, 2, 2, 1, 3, 1, 1, 4, 3]
def baseStart_564306 : Nat := 118140960795 + 564306 * 2 ^ 59
def prefixEnd_564306 : Nat := 4983230072969 + 3 ^ 40 * 564306 * 2
def baseEnd_564306 : Nat := 257564634858821674559831

theorem tailTrace_564306 : CollatzResearch.WordTrace tailWord_564306 prefixEnd_564306 257564634858821674559831 := by
  unfold tailWord_564306
  simp only [CollatzResearch.WordTrace]
  refine ⟨5145482673405803159260193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13721287129082141758027181 5145482673405803159260193)
  ·
    refine ⟨3859112005054352369445145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5145482673405803159260193 3859112005054352369445145)
    ·
      refine ⟨2894334003790764277083859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3859112005054352369445145 2894334003790764277083859)
      ·
        refine ⟨4341501005686146415625789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2894334003790764277083859 4341501005686146415625789)
        ·
          refine ⟨1628062877132304905859671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4341501005686146415625789 1628062877132304905859671)
          ·
            refine ⟨2442094315698457358789507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1628062877132304905859671 2442094315698457358789507)
            ·
              refine ⟨3663141473547686038184261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2442094315698457358789507 3663141473547686038184261)
              ·
                refine ⟨686839026290191132159549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3663141473547686038184261 686839026290191132159549)
                ·
                  refine ⟨257564634858821674559831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 686839026290191132159549 257564634858821674559831)
                  ·
                    rfl

theorem cell20_564306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_564306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_564306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_564306 prefixEnd_564306 := by exact prefixLift 564306
  have htrace : WordTrace (prefixWord ++ tailWord_564306) baseStart_564306 baseEnd_564306 := by
    simpa [prefixWord, tailWord_564306, baseEnd_564306] using wordTrace_append hprefix tailTrace_564306
  have hstable : (prefixWord ++ tailWord_564306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564306).length < 2 ^ (prefixWord ++ tailWord_564306).sum := by decide
  have hdescent : baseEnd_564306 < baseStart_564306 := by decide
  rcases family_descends (prefixWord ++ tailWord_564306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564434 : List Nat := [3, 2, 2, 2, 1, 1, 4, 5]
def baseStart_564434 : Nat := 118140960795 + 564434 * 2 ^ 59
def prefixEnd_564434 : Nat := 4983230072969 + 3 ^ 40 * 564434 * 2
def baseEnd_564434 : Nat := 85874352515540706097547

theorem tailTrace_564434 : CollatzResearch.WordTrace tailWord_564434 prefixEnd_564434 85874352515540706097547 := by
  unfold tailWord_564434
  simp only [CollatzResearch.WordTrace]
  refine ⟨5146649809289872624425089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13724399491439660331800237 5146649809289872624425089)
  ·
    refine ⟨3859987356967404468318817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5146649809289872624425089 3859987356967404468318817)
    ·
      refine ⟨2894990517725553351239113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3859987356967404468318817 2894990517725553351239113)
      ·
        refine ⟨2171242888294165013429335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2894990517725553351239113 2171242888294165013429335)
        ·
          refine ⟨3256864332441247520144003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2171242888294165013429335 3256864332441247520144003)
          ·
            refine ⟨4885296498661871280216005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3256864332441247520144003 4885296498661871280216005)
            ·
              refine ⟨915993093499100865040501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4885296498661871280216005 915993093499100865040501)
              ·
                refine ⟨85874352515540706097547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 915993093499100865040501 85874352515540706097547)
                ·
                  rfl

theorem cell20_564434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_564434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_564434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_564434 prefixEnd_564434 := by exact prefixLift 564434
  have htrace : WordTrace (prefixWord ++ tailWord_564434) baseStart_564434 baseEnd_564434 := by
    simpa [prefixWord, tailWord_564434, baseEnd_564434] using wordTrace_append hprefix tailTrace_564434
  have hstable : (prefixWord ++ tailWord_564434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564434).length < 2 ^ (prefixWord ++ tailWord_564434).sum := by decide
  have hdescent : baseEnd_564434 < baseStart_564434 := by decide
  rcases family_descends (prefixWord ++ tailWord_564434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564437 : List Nat := [1, 3, 2, 4, 1, 1, 4, 1, 3]
def baseStart_564437 : Nat := 118140960795 + 564437 * 2 ^ 59
def prefixEnd_564437 : Nat := 4983230072969 + 3 ^ 40 * 564437 * 2
def baseEnd_564437 : Nat := 257624426828367441192629

theorem tailTrace_564437 : CollatzResearch.WordTrace tailWord_564437 prefixEnd_564437 257624426828367441192629 := by
  unfold tailWord_564437
  simp only [CollatzResearch.WordTrace]
  refine ⟨20586708656148622010059565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13724472437432414673373043 20586708656148622010059565)
  ·
    refine ⟨7720015746055733253772337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20586708656148622010059565 7720015746055733253772337)
    ·
      refine ⟨5790011809541799940329253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7720015746055733253772337 5790011809541799940329253)
      ·
        refine ⟨1085627214289087488811735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5790011809541799940329253 1085627214289087488811735)
        ·
          refine ⟨1628440821433631233217603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1085627214289087488811735 1628440821433631233217603)
          ·
            refine ⟨2442661232150446849826405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1628440821433631233217603 2442661232150446849826405)
            ·
              refine ⟨457998981028208784342451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2442661232150446849826405 457998981028208784342451)
              ·
                refine ⟨686998471542313176513677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 457998981028208784342451 686998471542313176513677)
                ·
                  refine ⟨257624426828367441192629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 686998471542313176513677 257624426828367441192629)
                  ·
                    rfl

theorem cell20_564437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 3].length) (baseStart_564437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_564437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_564437 prefixEnd_564437 := by exact prefixLift 564437
  have htrace : WordTrace (prefixWord ++ tailWord_564437) baseStart_564437 baseEnd_564437 := by
    simpa [prefixWord, tailWord_564437, baseEnd_564437] using wordTrace_append hprefix tailTrace_564437
  have hstable : (prefixWord ++ tailWord_564437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564437).length < 2 ^ (prefixWord ++ tailWord_564437).sum := by decide
  have hdescent : baseEnd_564437 < baseStart_564437 := by decide
  rcases family_descends (prefixWord ++ tailWord_564437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564465 : List Nat := [1, 2, 2, 2, 2, 1, 1, 7, 2]
def baseStart_564465 : Nat := 118140960795 + 564465 * 2 ^ 59
def prefixEnd_564465 : Nat := 4983230072969 + 3 ^ 40 * 564465 * 2
def baseEnd_564465 : Nat := 257637206791323788259181

theorem tailTrace_564465 : CollatzResearch.WordTrace tailWord_564465 prefixEnd_564465 257637206791323788259181 := by
  unfold tailWord_564465
  simp only [CollatzResearch.WordTrace]
  refine ⟨20587729900047182792078849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13725153266698121861385899 20587729900047182792078849)
  ·
    refine ⟨15440797425035387094059137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20587729900047182792078849 15440797425035387094059137)
    ·
      refine ⟨11580598068776540320544353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15440797425035387094059137 11580598068776540320544353)
      ·
        refine ⟨8685448551582405240408265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11580598068776540320544353 8685448551582405240408265)
        ·
          refine ⟨6514086413686803930306199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8685448551582405240408265 6514086413686803930306199)
          ·
            refine ⟨9771129620530205895459299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6514086413686803930306199 9771129620530205895459299)
            ·
              refine ⟨14656694430795308843188949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9771129620530205895459299 14656694430795308843188949)
              ·
                refine ⟨343516275721765051012241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 14656694430795308843188949 343516275721765051012241)
                ·
                  refine ⟨257637206791323788259181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 343516275721765051012241 257637206791323788259181)
                  ·
                    rfl

theorem cell20_564465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 7, 2].length) (baseStart_564465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_564465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_564465 prefixEnd_564465 := by exact prefixLift 564465
  have htrace : WordTrace (prefixWord ++ tailWord_564465) baseStart_564465 baseEnd_564465 := by
    simpa [prefixWord, tailWord_564465, baseEnd_564465] using wordTrace_append hprefix tailTrace_564465
  have hstable : (prefixWord ++ tailWord_564465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564465).length < 2 ^ (prefixWord ++ tailWord_564465).sum := by decide
  have hdescent : baseEnd_564465 < baseStart_564465 := by decide
  rcases family_descends (prefixWord ++ tailWord_564465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564468 : List Nat := [2, 6, 1, 2, 1, 8]
def baseStart_564468 : Nat := 118140960795 + 564468 * 2 ^ 59
def prefixEnd_564468 : Nat := 4983230072969 + 3 ^ 40 * 564468 * 2
def baseEnd_564468 : Nat := 9542169484187744857747

theorem tailTrace_564468 : CollatzResearch.WordTrace tailWord_564468 prefixEnd_564468 9542169484187744857747 := by
  unfold tailWord_564468
  simp only [CollatzResearch.WordTrace]
  refine ⟨10293919659518157152219029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13725226212690876202958705 10293919659518157152219029)
  ·
    refine ⟨482527484039913616510267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10293919659518157152219029 482527484039913616510267)
    ·
      refine ⟨723791226059870424765401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 482527484039913616510267 723791226059870424765401)
      ·
        refine ⟨542843419544902818574051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 723791226059870424765401 542843419544902818574051)
        ·
          refine ⟨814265129317354227861077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 542843419544902818574051 814265129317354227861077)
          ·
            refine ⟨9542169484187744857747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 814265129317354227861077 9542169484187744857747)
            ·
              rfl

theorem cell20_564468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 8].length) (baseStart_564468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_564468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_564468 prefixEnd_564468 := by exact prefixLift 564468
  have htrace : WordTrace (prefixWord ++ tailWord_564468) baseStart_564468 baseEnd_564468 := by
    simpa [prefixWord, tailWord_564468, baseEnd_564468] using wordTrace_append hprefix tailTrace_564468
  have hstable : (prefixWord ++ tailWord_564468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564468).length < 2 ^ (prefixWord ++ tailWord_564468).sum := by decide
  have hdescent : baseEnd_564468 < baseStart_564468 := by decide
  rcases family_descends (prefixWord ++ tailWord_564468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564478 : List Nat := [4, 2, 2, 1, 1, 4, 2, 2, 2]
def baseStart_564478 : Nat := 118140960795 + 564478 * 2 ^ 59
def prefixEnd_564478 : Nat := 4983230072969 + 3 ^ 40 * 564478 * 2
def baseEnd_564478 : Nat := 257643140345553520825795

theorem tailTrace_564478 : CollatzResearch.WordTrace tailWord_564478 prefixEnd_564478 257643140345553520825795 := by
  unfold tailWord_564478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2573525506125010751537761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13725469366000057341534725 2573525506125010751537761)
  ·
    refine ⟨1930144129593758063653321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2573525506125010751537761 1930144129593758063653321)
    ·
      refine ⟨1447608097195318547739991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1930144129593758063653321 1447608097195318547739991)
      ·
        refine ⟨2171412145792977821609987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1447608097195318547739991 2171412145792977821609987)
        ·
          refine ⟨3257118218689466732414981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2171412145792977821609987 3257118218689466732414981)
          ·
            refine ⟨610709666004275012327809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3257118218689466732414981 610709666004275012327809)
            ·
              refine ⟨458032249503206259245857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 610709666004275012327809 458032249503206259245857)
              ·
                refine ⟨343524187127404694434393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 458032249503206259245857 343524187127404694434393)
                ·
                  refine ⟨257643140345553520825795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 343524187127404694434393 257643140345553520825795)
                  ·
                    rfl

theorem cell20_564478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_564478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_564478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_564478 prefixEnd_564478 := by exact prefixLift 564478
  have htrace : WordTrace (prefixWord ++ tailWord_564478) baseStart_564478 baseEnd_564478 := by
    simpa [prefixWord, tailWord_564478, baseEnd_564478] using wordTrace_append hprefix tailTrace_564478
  have hstable : (prefixWord ++ tailWord_564478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564478).length < 2 ^ (prefixWord ++ tailWord_564478).sum := by decide
  have hdescent : baseEnd_564478 < baseStart_564478 := by decide
  rcases family_descends (prefixWord ++ tailWord_564478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564479 : List Nat := [1, 1, 2, 2, 1, 5, 1, 4, 3]
def baseStart_564479 : Nat := 118140960795 + 564479 * 2 ^ 59
def prefixEnd_564479 : Nat := 4983230072969 + 3 ^ 40 * 564479 * 2
def baseEnd_564479 : Nat := 257643596772801961792457

theorem tailTrace_564479 : CollatzResearch.WordTrace tailWord_564479 prefixEnd_564479 257643596772801961792457 := by
  unfold tailWord_564479
  simp only [CollatzResearch.WordTrace]
  refine ⟨20588240521996463183088491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13725493681330975455392327 20588240521996463183088491)
  ·
    refine ⟨30882360782994694774632737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20588240521996463183088491 30882360782994694774632737)
    ·
      refine ⟨23161770587246021080974553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30882360782994694774632737 23161770587246021080974553)
      ·
        refine ⟨17371327940434515810730915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23161770587246021080974553 17371327940434515810730915)
        ·
          refine ⟨26056991910651773716096373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17371327940434515810730915 26056991910651773716096373)
          ·
            refine ⟨2442842991623603785884035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26056991910651773716096373 2442842991623603785884035)
            ·
              refine ⟨3664264487435405678826053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2442842991623603785884035 3664264487435405678826053)
              ·
                refine ⟨687049591394138564779885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3664264487435405678826053 687049591394138564779885)
                ·
                  refine ⟨257643596772801961792457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 687049591394138564779885 257643596772801961792457)
                  ·
                    rfl

theorem cell20_564479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 3].length) (baseStart_564479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_564479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_564479 prefixEnd_564479 := by exact prefixLift 564479
  have htrace : WordTrace (prefixWord ++ tailWord_564479) baseStart_564479 baseEnd_564479 := by
    simpa [prefixWord, tailWord_564479, baseEnd_564479] using wordTrace_append hprefix tailTrace_564479
  have hstable : (prefixWord ++ tailWord_564479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564479).length < 2 ^ (prefixWord ++ tailWord_564479).sum := by decide
  have hdescent : baseEnd_564479 < baseStart_564479 := by decide
  rcases family_descends (prefixWord ++ tailWord_564479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564520 : List Nat := [2, 1, 5, 1, 2, 1, 1, 5, 2]
def baseStart_564520 : Nat := 118140960795 + 564520 * 2 ^ 59
def prefixEnd_564520 : Nat := 4983230072969 + 3 ^ 40 * 564520 * 2
def baseEnd_564520 : Nat := 257662310289988041425623

theorem tailTrace_564520 : CollatzResearch.WordTrace tailWord_564520 prefixEnd_564520 257662310289988041425623 := by
  unfold tailWord_564520
  simp only [CollatzResearch.WordTrace]
  refine ⟨10294867957423963592665507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13726490609898618123554009 10294867957423963592665507)
  ·
    refine ⟨15442301936135945388998261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10294867957423963592665507 15442301936135945388998261)
    ·
      refine ⟨1447715806512744880218587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15442301936135945388998261 1447715806512744880218587)
      ·
        refine ⟨2171573709769117320327881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1447715806512744880218587 2171573709769117320327881)
        ·
          refine ⟨1628680282326837990245911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2171573709769117320327881 1628680282326837990245911)
          ·
            refine ⟨2443020423490256985368867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1628680282326837990245911 2443020423490256985368867)
            ·
              refine ⟨3664530635235385478053301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2443020423490256985368867 3664530635235385478053301)
              ·
                refine ⟨343549747053317388567497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3664530635235385478053301 343549747053317388567497)
                ·
                  refine ⟨257662310289988041425623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 343549747053317388567497 257662310289988041425623)
                  ·
                    rfl

theorem cell20_564520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 5, 2].length) (baseStart_564520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_564520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_564520 prefixEnd_564520 := by exact prefixLift 564520
  have htrace : WordTrace (prefixWord ++ tailWord_564520) baseStart_564520 baseEnd_564520 := by
    simpa [prefixWord, tailWord_564520, baseEnd_564520] using wordTrace_append hprefix tailTrace_564520
  have hstable : (prefixWord ++ tailWord_564520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564520).length < 2 ^ (prefixWord ++ tailWord_564520).sum := by decide
  have hdescent : baseEnd_564520 < baseStart_564520 := by decide
  rcases family_descends (prefixWord ++ tailWord_564520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564531 : List Nat := [1, 1, 1, 2, 5, 3, 7]
def baseStart_564531 : Nat := 118140960795 + 564531 * 2 ^ 59
def prefixEnd_564531 : Nat := 4983230072969 + 3 ^ 40 * 564531 * 2
def baseEnd_564531 : Nat := 28629703443302321339879

theorem tailTrace_564531 : CollatzResearch.WordTrace tailWord_564531 prefixEnd_564531 28629703443302321339879 := by
  unfold tailWord_564531
  simp only [CollatzResearch.WordTrace]
  refine ⟨20590137117808076063981447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13726758078538717375987631 20590137117808076063981447)
  ·
    refine ⟨30885205676712114095972171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20590137117808076063981447 30885205676712114095972171)
    ·
      refine ⟨46327808515068171143958257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30885205676712114095972171 46327808515068171143958257)
      ·
        refine ⟨34745856386301128357968693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46327808515068171143958257 34745856386301128357968693)
        ·
          refine ⟨3257424036215730783559565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34745856386301128357968693 3257424036215730783559565)
          ·
            refine ⟨1221534013580899043834837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3257424036215730783559565 1221534013580899043834837)
            ·
              refine ⟨28629703443302321339879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1221534013580899043834837 28629703443302321339879)
              ·
                rfl

theorem cell20_564531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 7].length) (baseStart_564531 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_564531 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_564531 prefixEnd_564531 := by exact prefixLift 564531
  have htrace : WordTrace (prefixWord ++ tailWord_564531) baseStart_564531 baseEnd_564531 := by
    simpa [prefixWord, tailWord_564531, baseEnd_564531] using wordTrace_append hprefix tailTrace_564531
  have hstable : (prefixWord ++ tailWord_564531).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564531).length < 2 ^ (prefixWord ++ tailWord_564531).sum := by decide
  have hdescent : baseEnd_564531 < baseStart_564531 := by decide
  rcases family_descends (prefixWord ++ tailWord_564531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564565 : List Nat := [1, 3, 2, 2, 3, 3, 2, 4]
def baseStart_564565 : Nat := 118140960795 + 564565 * 2 ^ 59
def prefixEnd_564565 : Nat := 4983230072969 + 3 ^ 40 * 564565 * 2
def baseEnd_564565 : Nat := 85894283172055961641813

theorem tailTrace_564565 : CollatzResearch.WordTrace tailWord_564565 prefixEnd_564565 85894283172055961641813 := by
  unfold tailWord_564565
  simp only [CollatzResearch.WordTrace]
  refine ⟨20591377199684899870719149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13727584799789933247146099 20591377199684899870719149)
  ·
    refine ⟨7721766449881837451519681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20591377199684899870719149 7721766449881837451519681)
    ·
      refine ⟨5791324837411378088639761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7721766449881837451519681 5791324837411378088639761)
      ·
        refine ⟨4343493628058533566479821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5791324837411378088639761 4343493628058533566479821)
        ·
          refine ⟨1628810110521950087429933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4343493628058533566479821 1628810110521950087429933)
          ·
            refine ⟨610803791445731282786225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1628810110521950087429933 610803791445731282786225)
            ·
              refine ⟨458102843584298462089669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 610803791445731282786225 458102843584298462089669)
              ·
                refine ⟨85894283172055961641813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 458102843584298462089669 85894283172055961641813)
                ·
                  rfl

theorem cell20_564565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 4].length) (baseStart_564565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_564565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_564565 prefixEnd_564565 := by exact prefixLift 564565
  have htrace : WordTrace (prefixWord ++ tailWord_564565) baseStart_564565 baseEnd_564565 := by
    simpa [prefixWord, tailWord_564565, baseEnd_564565] using wordTrace_append hprefix tailTrace_564565
  have hstable : (prefixWord ++ tailWord_564565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564565).length < 2 ^ (prefixWord ++ tailWord_564565).sum := by decide
  have hdescent : baseEnd_564565 < baseStart_564565 := by decide
  rcases family_descends (prefixWord ++ tailWord_564565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564606 : List Nat := [4, 2, 3, 2, 1, 1, 1, 3, 3]
def baseStart_564606 : Nat := 118140960795 + 564606 * 2 ^ 59
def prefixEnd_564606 : Nat := 4983230072969 + 3 ^ 40 * 564606 * 2
def baseEnd_564606 : Nat := 257701563033353964558605

theorem tailTrace_564606 : CollatzResearch.WordTrace tailWord_564606 prefixEnd_564606 257701563033353964558605 := by
  unfold tailWord_564606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2574109074067045484120209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13728581728357575915307781 2574109074067045484120209)
  ·
    refine ⟨1930581805550284113090157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2574109074067045484120209 1930581805550284113090157)
    ·
      refine ⟨723968177081356542408809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1930581805550284113090157 723968177081356542408809)
      ·
        refine ⟨542976132811017406806607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 723968177081356542408809 542976132811017406806607)
        ·
          refine ⟨814464199216526110209911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 542976132811017406806607 814464199216526110209911)
          ·
            refine ⟨1221696298824789165314867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 814464199216526110209911 1221696298824789165314867)
            ·
              refine ⟨1832544448237183747972301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1221696298824789165314867 1832544448237183747972301)
              ·
                refine ⟨687204168088943905489613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1832544448237183747972301 687204168088943905489613)
                ·
                  refine ⟨257701563033353964558605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 687204168088943905489613 257701563033353964558605)
                  ·
                    rfl

theorem cell20_564606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_564606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_564606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_564606 prefixEnd_564606 := by exact prefixLift 564606
  have htrace : WordTrace (prefixWord ++ tailWord_564606) baseStart_564606 baseEnd_564606 := by
    simpa [prefixWord, tailWord_564606, baseEnd_564606] using wordTrace_append hprefix tailTrace_564606
  have hstable : (prefixWord ++ tailWord_564606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564606).length < 2 ^ (prefixWord ++ tailWord_564606).sum := by decide
  have hdescent : baseEnd_564606 < baseStart_564606 := by decide
  rcases family_descends (prefixWord ++ tailWord_564606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564652 : List Nat := [2, 2, 1, 1, 1, 1, 4, 3, 5]
def baseStart_564652 : Nat := 118140960795 + 564652 * 2 ^ 59
def prefixEnd_564652 : Nat := 4983230072969 + 3 ^ 40 * 564652 * 2
def baseEnd_564652 : Nat := 257722558686782249025083

theorem tailTrace_564652 : CollatzResearch.WordTrace tailWord_564652 prefixEnd_564652 257722558686782249025083 := by
  unfold tailWord_564652
  simp only [CollatzResearch.WordTrace]
  refine ⟨10297275175184856864568105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13729700233579809152757473 10297275175184856864568105)
  ·
    refine ⟨7722956381388642648426079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10297275175184856864568105 7722956381388642648426079)
    ·
      refine ⟨11584434572082963972639119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7722956381388642648426079 11584434572082963972639119)
      ·
        refine ⟨17376651858124445958958679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11584434572082963972639119 17376651858124445958958679)
        ·
          refine ⟨26064977787186668938438019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17376651858124445958958679 26064977787186668938438019)
          ·
            refine ⟨39097466680780003407657029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26064977787186668938438019 39097466680780003407657029)
            ·
              refine ⟨7330775002646250638935693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39097466680780003407657029 7330775002646250638935693)
              ·
                refine ⟨2749040625992343989600885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7330775002646250638935693 2749040625992343989600885)
                ·
                  refine ⟨257722558686782249025083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2749040625992343989600885 257722558686782249025083)
                  ·
                    rfl

theorem cell20_564652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_564652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_564652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_564652 prefixEnd_564652 := by exact prefixLift 564652
  have htrace : WordTrace (prefixWord ++ tailWord_564652) baseStart_564652 baseEnd_564652 := by
    simpa [prefixWord, tailWord_564652, baseEnd_564652] using wordTrace_append hprefix tailTrace_564652
  have hstable : (prefixWord ++ tailWord_564652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564652).length < 2 ^ (prefixWord ++ tailWord_564652).sum := by decide
  have hdescent : baseEnd_564652 < baseStart_564652 := by decide
  rcases family_descends (prefixWord ++ tailWord_564652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564659 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 8]
def baseStart_564659 : Nat := 118140960795 + 564659 * 2 ^ 59
def prefixEnd_564659 : Nat := 4983230072969 + 3 ^ 40 * 564659 * 2
def baseEnd_564659 : Nat := 257725753677521335791721

theorem tailTrace_564659 : CollatzResearch.WordTrace tailWord_564659 prefixEnd_564659 257725753677521335791721 := by
  unfold tailWord_564659
  simp only [CollatzResearch.WordTrace]
  refine ⟨20594805661344353924641031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13729870440896235949760687 20594805661344353924641031)
  ·
    refine ⟨30892208492016530886961547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20594805661344353924641031 30892208492016530886961547)
    ·
      refine ⟨46338312738024796330442321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30892208492016530886961547 46338312738024796330442321)
      ·
        refine ⟨34753734553518597247831741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46338312738024796330442321 34753734553518597247831741)
        ·
          refine ⟨13032650457569473967936903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34753734553518597247831741 13032650457569473967936903)
          ·
            refine ⟨19548975686354210951905355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13032650457569473967936903 19548975686354210951905355)
            ·
              refine ⟨29323463529531316427858033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19548975686354210951905355 29323463529531316427858033)
              ·
                refine ⟨21992597647148487320893525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29323463529531316427858033 21992597647148487320893525)
                ·
                  refine ⟨257725753677521335791721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21992597647148487320893525 257725753677521335791721)
                  ·
                    rfl

theorem cell20_564659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 8].length) (baseStart_564659 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_564659 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_564659 prefixEnd_564659 := by exact prefixLift 564659
  have htrace : WordTrace (prefixWord ++ tailWord_564659) baseStart_564659 baseEnd_564659 := by
    simpa [prefixWord, tailWord_564659, baseEnd_564659] using wordTrace_append hprefix tailTrace_564659
  have hstable : (prefixWord ++ tailWord_564659).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564659).length < 2 ^ (prefixWord ++ tailWord_564659).sum := by decide
  have hdescent : baseEnd_564659 < baseStart_564659 := by decide
  rcases family_descends (prefixWord ++ tailWord_564659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564669 : List Nat := [1, 4, 1, 2, 2, 1, 1, 5, 3]
def baseStart_564669 : Nat := 118140960795 + 564669 * 2 ^ 59
def prefixEnd_564669 : Nat := 4983230072969 + 3 ^ 40 * 564669 * 2
def baseEnd_564669 : Nat := 257730317950005745458347

theorem tailTrace_564669 : CollatzResearch.WordTrace tailWord_564669 prefixEnd_564669 257730317950005745458347 := by
  unfold tailWord_564669
  simp only [CollatzResearch.WordTrace]
  refine ⟨20595170391308125632505061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13730113594205417088336707 20595170391308125632505061)
  ·
    refine ⟨3861594448370273556094699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20595170391308125632505061 3861594448370273556094699)
    ·
      refine ⟨5792391672555410334142049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3861594448370273556094699 5792391672555410334142049)
      ·
        refine ⟨4344293754416557750606537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5792391672555410334142049 4344293754416557750606537)
        ·
          refine ⟨3258220315812418312954903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4344293754416557750606537 3258220315812418312954903)
          ·
            refine ⟨4887330473718627469432355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3258220315812418312954903 4887330473718627469432355)
            ·
              refine ⟨7330995710577941204148533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4887330473718627469432355 7330995710577941204148533)
              ·
                refine ⟨687280847866681987888925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7330995710577941204148533 687280847866681987888925)
                ·
                  refine ⟨257730317950005745458347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 687280847866681987888925 257730317950005745458347)
                  ·
                    rfl

theorem cell20_564669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_564669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_564669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_564669 prefixEnd_564669 := by exact prefixLift 564669
  have htrace : WordTrace (prefixWord ++ tailWord_564669) baseStart_564669 baseEnd_564669 := by
    simpa [prefixWord, tailWord_564669, baseEnd_564669] using wordTrace_append hprefix tailTrace_564669
  have hstable : (prefixWord ++ tailWord_564669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564669).length < 2 ^ (prefixWord ++ tailWord_564669).sum := by decide
  have hdescent : baseEnd_564669 < baseStart_564669 := by decide
  rcases family_descends (prefixWord ++ tailWord_564669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564707 : List Nat := [1, 1, 1, 6, 2, 2, 1, 1, 5]
def baseStart_564707 : Nat := 118140960795 + 564707 * 2 ^ 59
def prefixEnd_564707 : Nat := 4983230072969 + 3 ^ 40 * 564707 * 2
def baseEnd_564707 : Nat := 257747662185446502191525

theorem tailTrace_564707 : CollatzResearch.WordTrace tailWord_564707 prefixEnd_564707 257747662185446502191525 := by
  unfold tailWord_564707
  simp only [CollatzResearch.WordTrace]
  refine ⟨20596556365170458122388375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13731037576780305414925583 20596556365170458122388375)
  ·
    refine ⟨30894834547755687183582563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20596556365170458122388375 30894834547755687183582563)
    ·
      refine ⟨46342251821633530775373845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30894834547755687183582563 46342251821633530775373845)
      ·
        refine ⟨2172293054139071755095649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 46342251821633530775373845 2172293054139071755095649)
        ·
          refine ⟨1629219790604303816321737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2172293054139071755095649 1629219790604303816321737)
          ·
            refine ⟨1221914842953227862241303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1629219790604303816321737 1221914842953227862241303)
            ·
              refine ⟨1832872264429841793361955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1221914842953227862241303 1832872264429841793361955)
              ·
                refine ⟨2749308396644762690042933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1832872264429841793361955 2749308396644762690042933)
                ·
                  refine ⟨257747662185446502191525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2749308396644762690042933 257747662185446502191525)
                  ·
                    rfl

theorem cell20_564707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 5].length) (baseStart_564707 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_564707 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_564707 prefixEnd_564707 := by exact prefixLift 564707
  have htrace : WordTrace (prefixWord ++ tailWord_564707) baseStart_564707 baseEnd_564707 := by
    simpa [prefixWord, tailWord_564707, baseEnd_564707] using wordTrace_append hprefix tailTrace_564707
  have hstable : (prefixWord ++ tailWord_564707).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564707).length < 2 ^ (prefixWord ++ tailWord_564707).sum := by decide
  have hdescent : baseEnd_564707 < baseStart_564707 := by decide
  rcases family_descends (prefixWord ++ tailWord_564707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564735 : List Nat := [1, 1, 2, 2, 1, 2, 2, 3, 6]
def baseStart_564735 : Nat := 118140960795 + 564735 * 2 ^ 59
def prefixEnd_564735 : Nat := 4983230072969 + 3 ^ 40 * 564735 * 2
def baseEnd_564735 : Nat := 257760442148402849258077

theorem tailTrace_564735 : CollatzResearch.WordTrace tailWord_564735 prefixEnd_564735 257760442148402849258077 := by
  unfold tailWord_564735
  simp only [CollatzResearch.WordTrace]
  refine ⟨20597577609069018904407659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13731718406046012602938439 20597577609069018904407659)
  ·
    refine ⟨30896366413603528356611489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20597577609069018904407659 30896366413603528356611489)
    ·
      refine ⟨23172274810202646267458617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30896366413603528356611489 23172274810202646267458617)
      ·
        refine ⟨17379206107651984700593963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23172274810202646267458617 17379206107651984700593963)
        ·
          refine ⟨26068809161477977050890945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17379206107651984700593963 26068809161477977050890945)
          ·
            refine ⟨19551606871108482788168209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26068809161477977050890945 19551606871108482788168209)
            ·
              refine ⟨14663705153331362091126157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19551606871108482788168209 14663705153331362091126157)
              ·
                refine ⟨5498889432499260784172309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14663705153331362091126157 5498889432499260784172309)
                ·
                  refine ⟨257760442148402849258077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5498889432499260784172309 257760442148402849258077)
                  ·
                    rfl

theorem cell20_564735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 6].length) (baseStart_564735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_564735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_564735 prefixEnd_564735 := by exact prefixLift 564735
  have htrace : WordTrace (prefixWord ++ tailWord_564735) baseStart_564735 baseEnd_564735 := by
    simpa [prefixWord, tailWord_564735, baseEnd_564735] using wordTrace_append hprefix tailTrace_564735
  have hstable : (prefixWord ++ tailWord_564735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564735).length < 2 ^ (prefixWord ++ tailWord_564735).sum := by decide
  have hdescent : baseEnd_564735 < baseStart_564735 := by decide
  rcases family_descends (prefixWord ++ tailWord_564735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564769 : List Nat := [1, 2, 3, 2, 2, 4, 1, 1, 4]
def baseStart_564769 : Nat := 118140960795 + 564769 * 2 ^ 59
def prefixEnd_564769 : Nat := 4983230072969 + 3 ^ 40 * 564769 * 2
def baseEnd_564769 : Nat := 257775960674849842124605

theorem tailTrace_564769 : CollatzResearch.WordTrace tailWord_564769 prefixEnd_564769 257775960674849842124605 := by
  unfold tailWord_564769
  simp only [CollatzResearch.WordTrace]
  refine ⟨20598817690945842711145361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13732545127297228474096907 20598817690945842711145361)
  ·
    refine ⟨15449113268209382033359021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20598817690945842711145361 15449113268209382033359021)
    ·
      refine ⟨5793417475578518262509633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15449113268209382033359021 5793417475578518262509633)
      ·
        refine ⟨4345063106683888696882225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5793417475578518262509633 4345063106683888696882225)
        ·
          refine ⟨3258797330012916522661669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4345063106683888696882225 3258797330012916522661669)
          ·
            refine ⟨611024499377421847999063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3258797330012916522661669 611024499377421847999063)
            ·
              refine ⟨916536749066132771998595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 611024499377421847999063 916536749066132771998595)
              ·
                refine ⟨1374805123599199157997893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 916536749066132771998595 1374805123599199157997893)
                ·
                  refine ⟨257775960674849842124605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1374805123599199157997893 257775960674849842124605)
                  ·
                    rfl

theorem cell20_564769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 4].length) (baseStart_564769 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_564769 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_564769 prefixEnd_564769 := by exact prefixLift 564769
  have htrace : WordTrace (prefixWord ++ tailWord_564769) baseStart_564769 baseEnd_564769 := by
    simpa [prefixWord, tailWord_564769, baseEnd_564769] using wordTrace_append hprefix tailTrace_564769
  have hstable : (prefixWord ++ tailWord_564769).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564769).length < 2 ^ (prefixWord ++ tailWord_564769).sum := by decide
  have hdescent : baseEnd_564769 < baseStart_564769 := by decide
  rcases family_descends (prefixWord ++ tailWord_564769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564835 : List Nat := [1, 1, 1, 5, 1, 3, 3, 5]
def baseStart_564835 : Nat := 118140960795 + 564835 * 2 ^ 59
def prefixEnd_564835 : Nat := 4983230072969 + 3 ^ 40 * 564835 * 2
def baseEnd_564835 : Nat := 85935361624415648641445

theorem tailTrace_564835 : CollatzResearch.WordTrace tailWord_564835 prefixEnd_564835 85935361624415648641445 := by
  unfold tailWord_564835
  simp only [CollatzResearch.WordTrace]
  refine ⟨20601224908706735983047959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13734149939137823988698639 20601224908706735983047959)
  ·
    refine ⟨30901837363060103974571939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20601224908706735983047959 30901837363060103974571939)
    ·
      refine ⟨46352756044590155961857909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30901837363060103974571939 46352756044590155961857909)
      ·
        refine ⟨4345570879180327121424179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46352756044590155961857909 4345570879180327121424179)
        ·
          refine ⟨6518356318770490682136269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4345570879180327121424179 6518356318770490682136269)
          ·
            refine ⟨2444383619538934005801101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6518356318770490682136269 2444383619538934005801101)
            ·
              refine ⟨916643857327100252175413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2444383619538934005801101 916643857327100252175413)
              ·
                refine ⟨85935361624415648641445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 916643857327100252175413 85935361624415648641445)
                ·
                  rfl

theorem cell20_564835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 5].length) (baseStart_564835 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_564835 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_564835 prefixEnd_564835 := by exact prefixLift 564835
  have htrace : WordTrace (prefixWord ++ tailWord_564835) baseStart_564835 baseEnd_564835 := by
    simpa [prefixWord, tailWord_564835, baseEnd_564835] using wordTrace_append hprefix tailTrace_564835
  have hstable : (prefixWord ++ tailWord_564835).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564835).length < 2 ^ (prefixWord ++ tailWord_564835).sum := by decide
  have hdescent : baseEnd_564835 < baseStart_564835 := by decide
  rcases family_descends (prefixWord ++ tailWord_564835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564845 : List Nat := [1, 5, 1, 1, 4, 1, 1, 2, 4]
def baseStart_564845 : Nat := 118140960795 + 564845 * 2 ^ 59
def prefixEnd_564845 : Nat := 4983230072969 + 3 ^ 40 * 564845 * 2
def baseEnd_564845 : Nat := 257810649145731355590961

theorem tailTrace_564845 : CollatzResearch.WordTrace tailWord_564845 prefixEnd_564845 257810649145731355590961 := by
  unfold tailWord_564845
  simp only [CollatzResearch.WordTrace]
  refine ⟨20601589638670507690911989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13734393092447005127274659 20601589638670507690911989)
  ·
    refine ⟨1931399028625360096022999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20601589638670507690911989 1931399028625360096022999)
    ·
      refine ⟨2897098542938040144034499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1931399028625360096022999 2897098542938040144034499)
      ·
        refine ⟨4345647814407060216051749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2897098542938040144034499 4345647814407060216051749)
        ·
          refine ⟨814808965201323790509703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4345647814407060216051749 814808965201323790509703)
          ·
            refine ⟨1222213447801985685764555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 814808965201323790509703 1222213447801985685764555)
            ·
              refine ⟨1833320171702978528646833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1222213447801985685764555 1833320171702978528646833)
              ·
                refine ⟨1374990128777233896485125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1833320171702978528646833 1374990128777233896485125)
                ·
                  refine ⟨257810649145731355590961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1374990128777233896485125 257810649145731355590961)
                  ·
                    rfl

theorem cell20_564845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_564845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_564845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_564845 prefixEnd_564845 := by exact prefixLift 564845
  have htrace : WordTrace (prefixWord ++ tailWord_564845) baseStart_564845 baseEnd_564845 := by
    simpa [prefixWord, tailWord_564845, baseEnd_564845] using wordTrace_append hprefix tailTrace_564845
  have hstable : (prefixWord ++ tailWord_564845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564845).length < 2 ^ (prefixWord ++ tailWord_564845).sum := by decide
  have hdescent : baseEnd_564845 < baseStart_564845 := by decide
  rcases family_descends (prefixWord ++ tailWord_564845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564872 : List Nat := [2, 1, 3, 5, 2, 1, 1, 2, 3]
def baseStart_564872 : Nat := 118140960795 + 564872 * 2 ^ 59
def prefixEnd_564872 : Nat := 4983230072969 + 3 ^ 40 * 564872 * 2
def baseEnd_564872 : Nat := 257822972681439261690851

theorem tailTrace_564872 : CollatzResearch.WordTrace tailWord_564872 prefixEnd_564872 257822972681439261690851 := by
  unfold tailWord_564872
  simp only [CollatzResearch.WordTrace]
  refine ⟨10301287204786345651072435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13735049606381794201429913 10301287204786345651072435)
  ·
    refine ⟨15451930807179518476608653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10301287204786345651072435 15451930807179518476608653)
    ·
      refine ⟨5794474052692319428728245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15451930807179518476608653 5794474052692319428728245)
      ·
        refine ⟨543231942439904946443273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5794474052692319428728245 543231942439904946443273)
        ·
          refine ⟨407423956829928709832455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 543231942439904946443273 407423956829928709832455)
          ·
            refine ⟨611135935244893064748683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407423956829928709832455 611135935244893064748683)
            ·
              refine ⟨916703902867339597123025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 611135935244893064748683 916703902867339597123025)
              ·
                refine ⟨687527927150504697842269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 916703902867339597123025 687527927150504697842269)
                ·
                  refine ⟨257822972681439261690851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 687527927150504697842269 257822972681439261690851)
                  ·
                    rfl

theorem cell20_564872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 3].length) (baseStart_564872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_564872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_564872 prefixEnd_564872 := by exact prefixLift 564872
  have htrace : WordTrace (prefixWord ++ tailWord_564872) baseStart_564872 baseEnd_564872 := by
    simpa [prefixWord, tailWord_564872, baseEnd_564872] using wordTrace_append hprefix tailTrace_564872
  have hstable : (prefixWord ++ tailWord_564872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564872).length < 2 ^ (prefixWord ++ tailWord_564872).sum := by decide
  have hdescent : baseEnd_564872 < baseStart_564872 := by decide
  rcases family_descends (prefixWord ++ tailWord_564872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564917 : List Nat := [1, 3, 3, 3, 2, 2, 1, 3, 2]
def baseStart_564917 : Nat := 118140960795 + 564917 * 2 ^ 59
def prefixEnd_564917 : Nat := 4983230072969 + 3 ^ 40 * 564917 * 2
def baseEnd_564917 : Nat := 257843511907619105190667

theorem tailTrace_564917 : CollatzResearch.WordTrace tailWord_564917 prefixEnd_564917 257843511907619105190667 := by
  unfold tailWord_564917
  simp only [CollatzResearch.WordTrace]
  refine ⟨20604215694409663987533005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13736143796273109325022003 20604215694409663987533005)
  ·
    refine ⟨7726580885403623995324877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20604215694409663987533005 7726580885403623995324877)
    ·
      refine ⟨2897467832026358998246829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7726580885403623995324877 2897467832026358998246829)
      ·
        refine ⟨1086550437009884624342561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2897467832026358998246829 1086550437009884624342561)
        ·
          refine ⟨814912827757413468256921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1086550437009884624342561 814912827757413468256921)
          ·
            refine ⟨611184620818060101192691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 814912827757413468256921 611184620818060101192691)
            ·
              refine ⟨916776931227090151789037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 611184620818060101192691 916776931227090151789037)
              ·
                refine ⟨343791349210158806920889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 916776931227090151789037 343791349210158806920889)
                ·
                  refine ⟨257843511907619105190667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 343791349210158806920889 257843511907619105190667)
                  ·
                    rfl

theorem cell20_564917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 3, 2].length) (baseStart_564917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_564917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_564917 prefixEnd_564917 := by exact prefixLift 564917
  have htrace : WordTrace (prefixWord ++ tailWord_564917) baseStart_564917 baseEnd_564917 := by
    simpa [prefixWord, tailWord_564917, baseEnd_564917] using wordTrace_append hprefix tailTrace_564917
  have hstable : (prefixWord ++ tailWord_564917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564917).length < 2 ^ (prefixWord ++ tailWord_564917).sum := by decide
  have hdescent : baseEnd_564917 < baseStart_564917 := by decide
  rcases family_descends (prefixWord ++ tailWord_564917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564921 : List Nat := [1, 2, 1, 4, 1, 1, 5, 3, 2]
def baseStart_564921 : Nat := 118140960795 + 564921 * 2 ^ 59
def prefixEnd_564921 : Nat := 4983230072969 + 3 ^ 40 * 564921 * 2
def baseEnd_564921 : Nat := 257845337616612869057317

theorem tailTrace_564921 : CollatzResearch.WordTrace tailWord_564921 prefixEnd_564921 257845337616612869057317 := by
  unfold tailWord_564921
  simp only [CollatzResearch.WordTrace]
  refine ⟨20604361586395172670678617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13736241057596781780452411 20604361586395172670678617)
  ·
    refine ⟨15453271189796379503008963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20604361586395172670678617 15453271189796379503008963)
    ·
      refine ⟨23179906784694569254513445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15453271189796379503008963 23179906784694569254513445)
      ·
        refine ⟨4346232522130231735221271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23179906784694569254513445 4346232522130231735221271)
        ·
          refine ⟨6519348783195347602831907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4346232522130231735221271 6519348783195347602831907)
          ·
            refine ⟨9779023174793021404247861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6519348783195347602831907 9779023174793021404247861)
            ·
              refine ⟨916783422636845756648237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9779023174793021404247861 916783422636845756648237)
              ·
                refine ⟨343793783488817158743089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 916783422636845756648237 343793783488817158743089)
                ·
                  refine ⟨257845337616612869057317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 343793783488817158743089 257845337616612869057317)
                  ·
                    rfl

theorem cell20_564921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 3, 2].length) (baseStart_564921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_564921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_564921 prefixEnd_564921 := by exact prefixLift 564921
  have htrace : WordTrace (prefixWord ++ tailWord_564921) baseStart_564921 baseEnd_564921 := by
    simpa [prefixWord, tailWord_564921, baseEnd_564921] using wordTrace_append hprefix tailTrace_564921
  have hstable : (prefixWord ++ tailWord_564921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564921).length < 2 ^ (prefixWord ++ tailWord_564921).sum := by decide
  have hdescent : baseEnd_564921 < baseStart_564921 := by decide
  rcases family_descends (prefixWord ++ tailWord_564921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564938 : List Nat := [3, 1, 2, 1, 6, 1, 1, 1, 4]
def baseStart_564938 : Nat := 118140960795 + 564938 * 2 ^ 59
def prefixEnd_564938 : Nat := 4983230072969 + 3 ^ 40 * 564938 * 2
def baseEnd_564938 : Nat := 257853096879836365490581

theorem tailTrace_564938 : CollatzResearch.WordTrace tailWord_564938 prefixEnd_564938 257853096879836365490581 := by
  unfold tailWord_564938
  simp only [CollatzResearch.WordTrace]
  refine ⟨5151245406833396143511867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13736654418222389716031645 5151245406833396143511867)
  ·
    refine ⟨7726868110250094215267801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5151245406833396143511867 7726868110250094215267801)
    ·
      refine ⟨5795151082687570661450851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7726868110250094215267801 5795151082687570661450851)
      ·
        refine ⟨8692726624031355992176277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5795151082687570661450851 8692726624031355992176277)
        ·
          refine ⟨407471560501469812133263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8692726624031355992176277 407471560501469812133263)
          ·
            refine ⟨611207340752204718199895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407471560501469812133263 611207340752204718199895)
            ·
              refine ⟨916811011128307077299843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 611207340752204718199895 916811011128307077299843)
              ·
                refine ⟨1375216516692460615949765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 916811011128307077299843 1375216516692460615949765)
                ·
                  refine ⟨257853096879836365490581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1375216516692460615949765 257853096879836365490581)
                  ·
                    rfl

theorem cell20_564938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 4].length) (baseStart_564938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_564938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_564938 prefixEnd_564938 := by exact prefixLift 564938
  have htrace : WordTrace (prefixWord ++ tailWord_564938) baseStart_564938 baseEnd_564938 := by
    simpa [prefixWord, tailWord_564938, baseEnd_564938] using wordTrace_append hprefix tailTrace_564938
  have hstable : (prefixWord ++ tailWord_564938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564938).length < 2 ^ (prefixWord ++ tailWord_564938).sum := by decide
  have hdescent : baseEnd_564938 < baseStart_564938 := by decide
  rcases family_descends (prefixWord ++ tailWord_564938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565001 : List Nat := [1, 2, 1, 1, 3, 2, 1, 5, 4]
def baseStart_565001 : Nat := 118140960795 + 565001 * 2 ^ 59
def prefixEnd_565001 : Nat := 4983230072969 + 3 ^ 40 * 565001 * 2
def baseEnd_565001 : Nat := 257881851796488146390323

theorem tailTrace_565001 : CollatzResearch.WordTrace tailWord_565001 prefixEnd_565001 257881851796488146390323 := by
  unfold tailWord_565001
  simp only [CollatzResearch.WordTrace]
  refine ⟨20607279426105346333590857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13738186284070230889060571 20607279426105346333590857)
  ·
    refine ⟨15455459569579009750193143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20607279426105346333590857 15455459569579009750193143)
    ·
      refine ⟨23183189354368514625289715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15455459569579009750193143 23183189354368514625289715)
      ·
        refine ⟨34774784031552771937934573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23183189354368514625289715 34774784031552771937934573)
        ·
          refine ⟨13040544011832289476725465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34774784031552771937934573 13040544011832289476725465)
          ·
            refine ⟨9780408008874217107544099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13040544011832289476725465 9780408008874217107544099)
            ·
              refine ⟨14670612013311325661316149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9780408008874217107544099 14670612013311325661316149)
              ·
                refine ⟨1375369876247936780748389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14670612013311325661316149 1375369876247936780748389)
                ·
                  refine ⟨257881851796488146390323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1375369876247936780748389 257881851796488146390323)
                  ·
                    rfl

theorem cell20_565001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_565001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565001 prefixEnd_565001 := by exact prefixLift 565001
  have htrace : WordTrace (prefixWord ++ tailWord_565001) baseStart_565001 baseEnd_565001 := by
    simpa [prefixWord, tailWord_565001, baseEnd_565001] using wordTrace_append hprefix tailTrace_565001
  have hstable : (prefixWord ++ tailWord_565001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565001).length < 2 ^ (prefixWord ++ tailWord_565001).sum := by decide
  have hdescent : baseEnd_565001 < baseStart_565001 := by decide
  rcases family_descends (prefixWord ++ tailWord_565001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565018 : List Nat := [3, 1, 1, 3, 2, 3, 1, 2, 4]
def baseStart_565018 : Nat := 118140960795 + 565018 * 2 ^ 59
def prefixEnd_565018 : Nat := 4983230072969 + 3 ^ 40 * 565018 * 2
def baseEnd_565018 : Nat := 257889611059711642823587

theorem tailTrace_565018 : CollatzResearch.WordTrace tailWord_565018 prefixEnd_565018 257889611059711642823587 := by
  unfold tailWord_565018
  simp only [CollatzResearch.WordTrace]
  refine ⟨5151974866760939559239927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13738599644695838824639805 5151974866760939559239927)
  ·
    refine ⟨7727962300141409338859891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5151974866760939559239927 7727962300141409338859891)
    ·
      refine ⟨11591943450212114008289837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7727962300141409338859891 11591943450212114008289837)
      ·
        refine ⟨4346978793829542753108689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11591943450212114008289837 4346978793829542753108689)
        ·
          refine ⟨3260234095372157064831517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4346978793829542753108689 3260234095372157064831517)
          ·
            refine ⟨1222587785764558899311819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3260234095372157064831517 1222587785764558899311819)
            ·
              refine ⟨1833881678646838348967729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1222587785764558899311819 1833881678646838348967729)
              ·
                refine ⟨1375411258985128761725797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1833881678646838348967729 1375411258985128761725797)
                ·
                  refine ⟨257889611059711642823587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1375411258985128761725797 257889611059711642823587)
                  ·
                    rfl

theorem cell20_565018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_565018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565018 prefixEnd_565018 := by exact prefixLift 565018
  have htrace : WordTrace (prefixWord ++ tailWord_565018) baseStart_565018 baseEnd_565018 := by
    simpa [prefixWord, tailWord_565018, baseEnd_565018] using wordTrace_append hprefix tailTrace_565018
  have hstable : (prefixWord ++ tailWord_565018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565018).length < 2 ^ (prefixWord ++ tailWord_565018).sum := by decide
  have hdescent : baseEnd_565018 < baseStart_565018 := by decide
  rcases family_descends (prefixWord ++ tailWord_565018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565045 : List Nat := [1, 3, 3, 1, 5, 1, 1, 2, 3]
def baseStart_565045 : Nat := 118140960795 + 565045 * 2 ^ 59
def prefixEnd_565045 : Nat := 4983230072969 + 3 ^ 40 * 565045 * 2
def baseEnd_565045 : Nat := 257901934595419548923477

theorem tailTrace_565045 : CollatzResearch.WordTrace tailWord_565045 prefixEnd_565045 257901934595419548923477 := by
  unfold tailWord_565045
  simp only [CollatzResearch.WordTrace]
  refine ⟨20608884237945941848192589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13739256158630627898795059 20608884237945941848192589)
  ·
    refine ⟨7728331589229728193072221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20608884237945941848192589 7728331589229728193072221)
    ·
      refine ⟨2898124345961148072402083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7728331589229728193072221 2898124345961148072402083)
      ·
        refine ⟨4347186518941722108603125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2898124345961148072402083 4347186518941722108603125)
        ·
          refine ⟨407548736150786447681543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4347186518941722108603125 407548736150786447681543)
          ·
            refine ⟨611323104226179671522315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407548736150786447681543 611323104226179671522315)
            ·
              refine ⟨916984656339269507283473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 611323104226179671522315 916984656339269507283473)
              ·
                refine ⟨687738492254452130462605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 916984656339269507283473 687738492254452130462605)
                ·
                  refine ⟨257901934595419548923477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 687738492254452130462605 257901934595419548923477)
                  ·
                    rfl

theorem cell20_565045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 3].length) (baseStart_565045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565045 prefixEnd_565045 := by exact prefixLift 565045
  have htrace : WordTrace (prefixWord ++ tailWord_565045) baseStart_565045 baseEnd_565045 := by
    simpa [prefixWord, tailWord_565045, baseEnd_565045] using wordTrace_append hprefix tailTrace_565045
  have hstable : (prefixWord ++ tailWord_565045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565045).length < 2 ^ (prefixWord ++ tailWord_565045).sum := by decide
  have hdescent : baseEnd_565045 < baseStart_565045 := by decide
  rcases family_descends (prefixWord ++ tailWord_565045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565062 : List Nat := [6, 1, 1, 2, 1, 2, 3, 1, 3]
def baseStart_565062 : Nat := 118140960795 + 565062 * 2 ^ 59
def prefixEnd_565062 : Nat := 4983230072969 + 3 ^ 40 * 565062 * 2
def baseEnd_565062 : Nat := 257909693858643045356741

theorem tailTrace_565062 : CollatzResearch.WordTrace tailWord_565062 prefixEnd_565062 257909693858643045356741 := by
  unfold tailWord_565062
  simp only [CollatzResearch.WordTrace]
  refine ⟨644047008715136054736295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13739669519256235834374293 644047008715136054736295)
  ·
    refine ⟨966070513072704082104443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 644047008715136054736295 966070513072704082104443)
    ·
      refine ⟨1449105769609056123156665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 966070513072704082104443 1449105769609056123156665)
      ·
        refine ⟨1086829327206792092367499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1449105769609056123156665 1086829327206792092367499)
        ·
          refine ⟨1630243990810188138551249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1086829327206792092367499 1630243990810188138551249)
          ·
            refine ⟨1222682993107641103913437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1630243990810188138551249 1222682993107641103913437)
            ·
              refine ⟨458506122415365413967539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1222682993107641103913437 458506122415365413967539)
              ·
                refine ⟨687759183623048120951309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 458506122415365413967539 687759183623048120951309)
                ·
                  refine ⟨257909693858643045356741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 687759183623048120951309 257909693858643045356741)
                  ·
                    rfl

theorem cell20_565062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_565062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565062 prefixEnd_565062 := by exact prefixLift 565062
  have htrace : WordTrace (prefixWord ++ tailWord_565062) baseStart_565062 baseEnd_565062 := by
    simpa [prefixWord, tailWord_565062, baseEnd_565062] using wordTrace_append hprefix tailTrace_565062
  have hstable : (prefixWord ++ tailWord_565062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565062).length < 2 ^ (prefixWord ++ tailWord_565062).sum := by decide
  have hdescent : baseEnd_565062 < baseStart_565062 := by decide
  rcases family_descends (prefixWord ++ tailWord_565062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565090 : List Nat := [3, 3, 2, 1, 2, 1, 3, 3, 2]
def baseStart_565090 : Nat := 118140960795 + 565090 * 2 ^ 59
def prefixEnd_565090 : Nat := 4983230072969 + 3 ^ 40 * 565090 * 2
def baseEnd_565090 : Nat := 257922473821599392423293

theorem tailTrace_565090 : CollatzResearch.WordTrace tailWord_565090 prefixEnd_565090 257922473821599392423293 := by
  unfold tailWord_565090
  simp only [CollatzResearch.WordTrace]
  refine ⟨5152631380695728633395181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13740350348521943022387149 5152631380695728633395181)
  ·
    refine ⟨1932236767760898237523193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5152631380695728633395181 1932236767760898237523193)
    ·
      refine ⟨1449177575820673678142395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1932236767760898237523193 1449177575820673678142395)
      ·
        refine ⟨2173766363731010517213593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1449177575820673678142395 2173766363731010517213593)
        ·
          refine ⟨1630324772798257887910195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2173766363731010517213593 1630324772798257887910195)
          ·
            refine ⟨2445487159197386831865293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1630324772798257887910195 2445487159197386831865293)
            ·
              refine ⟨917057684699020061949485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2445487159197386831865293 917057684699020061949485)
              ·
                refine ⟨343896631762132523231057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 917057684699020061949485 343896631762132523231057)
                ·
                  refine ⟨257922473821599392423293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 343896631762132523231057 257922473821599392423293)
                  ·
                    rfl

theorem cell20_565090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_565090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565090 prefixEnd_565090 := by exact prefixLift 565090
  have htrace : WordTrace (prefixWord ++ tailWord_565090) baseStart_565090 baseEnd_565090 := by
    simpa [prefixWord, tailWord_565090, baseEnd_565090] using wordTrace_append hprefix tailTrace_565090
  have hstable : (prefixWord ++ tailWord_565090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565090).length < 2 ^ (prefixWord ++ tailWord_565090).sum := by decide
  have hdescent : baseEnd_565090 < baseStart_565090 := by decide
  rcases family_descends (prefixWord ++ tailWord_565090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565118 : List Nat := [4, 2, 3, 1, 1, 1, 1, 7]
def baseStart_565118 : Nat := 118140960795 + 565118 * 2 ^ 59
def prefixEnd_565118 : Nat := 4983230072969 + 3 ^ 40 * 565118 * 2
def baseEnd_565118 : Nat := 85978417928185246496615

theorem tailTrace_565118 : CollatzResearch.WordTrace tailWord_565118 prefixEnd_565118 85978417928185246496615 := by
  unfold tailWord_565118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2576443345835184414450001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13741031177787650210400005 2576443345835184414450001)
  ·
    refine ⟨1932332509376388310837501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2576443345835184414450001 1932332509376388310837501)
    ·
      refine ⟨724624691016145616564063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1932332509376388310837501 724624691016145616564063)
      ·
        refine ⟨1086937036524218424846095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 724624691016145616564063 1086937036524218424846095)
        ·
          refine ⟨1630405554786327637269143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1086937036524218424846095 1630405554786327637269143)
          ·
            refine ⟨2445608332179491455903715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1630405554786327637269143 2445608332179491455903715)
            ·
              refine ⟨3668412498269237183855573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2445608332179491455903715 3668412498269237183855573)
              ·
                refine ⟨85978417928185246496615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3668412498269237183855573 85978417928185246496615)
                ·
                  rfl

theorem cell20_565118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_565118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565118 prefixEnd_565118 := by exact prefixLift 565118
  have htrace : WordTrace (prefixWord ++ tailWord_565118) baseStart_565118 baseEnd_565118 := by
    simpa [prefixWord, tailWord_565118, baseEnd_565118] using wordTrace_append hprefix tailTrace_565118
  have hstable : (prefixWord ++ tailWord_565118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565118).length < 2 ^ (prefixWord ++ tailWord_565118).sum := by decide
  have hdescent : baseEnd_565118 < baseStart_565118 := by decide
  rcases family_descends (prefixWord ++ tailWord_565118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565184 : List Nat := [2, 1, 1, 2, 3, 2, 1, 5, 3]
def baseStart_565184 : Nat := 118140960795 + 565184 * 2 ^ 59
def prefixEnd_565184 : Nat := 4983230072969 + 3 ^ 40 * 565184 * 2
def baseEnd_565184 : Nat := 257965377982952843289575

theorem tailTrace_565184 : CollatzResearch.WordTrace tailWord_565184 prefixEnd_565184 257965377982952843289575 := by
  unfold tailWord_565184
  simp only [CollatzResearch.WordTrace]
  refine ⟨10306976992221184293751303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13742635989628245725001737 10306976992221184293751303)
  ·
    refine ⟨15460465488331776440626955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10306976992221184293751303 15460465488331776440626955)
    ·
      refine ⟨23190698232497664660940433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15460465488331776440626955 23190698232497664660940433)
      ·
        refine ⟨17393023674373248495705325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23190698232497664660940433 17393023674373248495705325)
        ·
          refine ⟨6522383877889968185889497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17393023674373248495705325 6522383877889968185889497)
          ·
            refine ⟨4891787908417476139417123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6522383877889968185889497 4891787908417476139417123)
            ·
              refine ⟨7337681862626214209125685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4891787908417476139417123 7337681862626214209125685)
              ·
                refine ⟨687907674621207582105533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7337681862626214209125685 687907674621207582105533)
                ·
                  refine ⟨257965377982952843289575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 687907674621207582105533 257965377982952843289575)
                  ·
                    rfl

theorem cell20_565184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 3].length) (baseStart_565184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565184 prefixEnd_565184 := by exact prefixLift 565184
  have htrace : WordTrace (prefixWord ++ tailWord_565184) baseStart_565184 baseEnd_565184 := by
    simpa [prefixWord, tailWord_565184, baseEnd_565184] using wordTrace_append hprefix tailTrace_565184
  have hstable : (prefixWord ++ tailWord_565184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565184).length < 2 ^ (prefixWord ++ tailWord_565184).sum := by decide
  have hdescent : baseEnd_565184 < baseStart_565184 := by decide
  rcases family_descends (prefixWord ++ tailWord_565184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565218 : List Nat := [3, 3, 3, 1, 2, 1, 1, 1, 5]
def baseStart_565218 : Nat := 118140960795 + 565218 * 2 ^ 59
def prefixEnd_565218 : Nat := 4983230072969 + 3 ^ 40 * 565218 * 2
def baseEnd_565218 : Nat := 257980896509399836156103

theorem tailTrace_565218 : CollatzResearch.WordTrace tailWord_565218 prefixEnd_565218 257980896509399836156103 := by
  unfold tailWord_565218
  simp only [CollatzResearch.WordTrace]
  refine ⟨5153798516579798098560077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13743462710879461596160205 5153798516579798098560077)
  ·
    refine ⟨1932674443717424286960029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5153798516579798098560077 1932674443717424286960029)
    ·
      refine ⟨724752916394034107610011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1932674443717424286960029 724752916394034107610011)
      ·
        refine ⟨1087129374591051161415017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 724752916394034107610011 1087129374591051161415017)
        ·
          refine ⟨815347030943288371061263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1087129374591051161415017 815347030943288371061263)
          ·
            refine ⟨1223020546414932556591895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 815347030943288371061263 1223020546414932556591895)
            ·
              refine ⟨1834530819622398834887843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1223020546414932556591895 1834530819622398834887843)
              ·
                refine ⟨2751796229433598252331765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1834530819622398834887843 2751796229433598252331765)
                ·
                  refine ⟨257980896509399836156103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2751796229433598252331765 257980896509399836156103)
                  ·
                    rfl

theorem cell20_565218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_565218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565218 prefixEnd_565218 := by exact prefixLift 565218
  have htrace : WordTrace (prefixWord ++ tailWord_565218) baseStart_565218 baseEnd_565218 := by
    simpa [prefixWord, tailWord_565218, baseEnd_565218] using wordTrace_append hprefix tailTrace_565218
  have hstable : (prefixWord ++ tailWord_565218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565218).length < 2 ^ (prefixWord ++ tailWord_565218).sum := by decide
  have hdescent : baseEnd_565218 < baseStart_565218 := by decide
  rcases family_descends (prefixWord ++ tailWord_565218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565253 : List Nat := [1, 3, 1, 1, 2, 4, 4, 4]
def baseStart_565253 : Nat := 118140960795 + 565253 * 2 ^ 59
def prefixEnd_565253 : Nat := 4983230072969 + 3 ^ 40 * 565253 * 2
def baseEnd_565253 : Nat := 85998957154365089996431

theorem tailTrace_565253 : CollatzResearch.WordTrace tailWord_565253 prefixEnd_565253 85998957154365089996431 := by
  unfold tailWord_565253
  simp only [CollatzResearch.WordTrace]
  refine ⟨20616470621192393371764413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13744313747461595581176275 20616470621192393371764413)
  ·
    refine ⟨7731176482947147514411655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20616470621192393371764413 7731176482947147514411655)
    ·
      refine ⟨11596764724420721271617483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7731176482947147514411655 11596764724420721271617483)
      ·
        refine ⟨17395147086631081907426225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11596764724420721271617483 17395147086631081907426225)
        ·
          refine ⟨13046360314973311430569669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17395147086631081907426225 13046360314973311430569669)
          ·
            refine ⟨2446192559057495893231813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13046360314973311430569669 2446192559057495893231813)
            ·
              refine ⟨458661104823280479980965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2446192559057495893231813 458661104823280479980965)
              ·
                refine ⟨85998957154365089996431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 458661104823280479980965 85998957154365089996431)
                ·
                  rfl

theorem cell20_565253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 4].length) (baseStart_565253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565253 prefixEnd_565253 := by exact prefixLift 565253
  have htrace : WordTrace (prefixWord ++ tailWord_565253) baseStart_565253 baseEnd_565253 := by
    simpa [prefixWord, tailWord_565253, baseEnd_565253] using wordTrace_append hprefix tailTrace_565253
  have hstable : (prefixWord ++ tailWord_565253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565253).length < 2 ^ (prefixWord ++ tailWord_565253).sum := by decide
  have hdescent : baseEnd_565253 < baseStart_565253 := by decide
  rcases family_descends (prefixWord ++ tailWord_565253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565274 : List Nat := [3, 1, 1, 3, 1, 3, 8]
def baseStart_565274 : Nat := 118140960795 + 565274 * 2 ^ 59
def prefixEnd_565274 : Nat := 4983230072969 + 3 ^ 40 * 565274 * 2
def baseEnd_565274 : Nat := 28667384048368058921023

theorem tailTrace_565274 : CollatzResearch.WordTrace tailWord_565274 prefixEnd_565274 28667384048368058921023 := by
  unfold tailWord_565274
  simp only [CollatzResearch.WordTrace]
  refine ⟨5154309138529078489569719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13744824369410875972185917 5154309138529078489569719)
  ·
    refine ⟨7731463707793617734354579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5154309138529078489569719 7731463707793617734354579)
    ·
      refine ⟨11597195561690426601531869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7731463707793617734354579 11597195561690426601531869)
      ·
        refine ⟨4348948335633909975574451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11597195561690426601531869 4348948335633909975574451)
        ·
          refine ⟨6523422503450864963361677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4348948335633909975574451 6523422503450864963361677)
          ·
            refine ⟨2446283438794074361260629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6523422503450864963361677 2446283438794074361260629)
            ·
              refine ⟨28667384048368058921023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2446283438794074361260629 28667384048368058921023)
              ·
                rfl

theorem cell20_565274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 8].length) (baseStart_565274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565274 prefixEnd_565274 := by exact prefixLift 565274
  have htrace : WordTrace (prefixWord ++ tailWord_565274) baseStart_565274 baseEnd_565274 := by
    simpa [prefixWord, tailWord_565274, baseEnd_565274] using wordTrace_append hprefix tailTrace_565274
  have hstable : (prefixWord ++ tailWord_565274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565274).length < 2 ^ (prefixWord ++ tailWord_565274).sum := by decide
  have hdescent : baseEnd_565274 < baseStart_565274 := by decide
  rcases family_descends (prefixWord ++ tailWord_565274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565294 : List Nat := [4, 1, 3, 1, 1, 2, 4, 1, 3]
def baseStart_565294 : Nat := 118140960795 + 565294 * 2 ^ 59
def prefixEnd_565294 : Nat := 4983230072969 + 3 ^ 40 * 565294 * 2
def baseEnd_565294 : Nat := 258015584980281349622459

theorem tailTrace_565294 : CollatzResearch.WordTrace tailWord_565294 prefixEnd_565294 258015584980281349622459 := by
  unfold tailWord_565294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2577245751755482171750867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13745310676029238249337957 2577245751755482171750867)
  ·
    refine ⟨3865868627633223257626301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2577245751755482171750867 3865868627633223257626301)
    ·
      refine ⟨1449700735362458721609863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3865868627633223257626301 1449700735362458721609863)
      ·
        refine ⟨2174551103043688082414795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1449700735362458721609863 2174551103043688082414795)
        ·
          refine ⟨3261826654565532123622193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2174551103043688082414795 3261826654565532123622193)
          ·
            refine ⟨2446369990924149092716645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3261826654565532123622193 2446369990924149092716645)
            ·
              refine ⟨458694373298277954884371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2446369990924149092716645 458694373298277954884371)
              ·
                refine ⟨688041559947416932326557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 458694373298277954884371 688041559947416932326557)
                ·
                  refine ⟨258015584980281349622459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 688041559947416932326557 258015584980281349622459)
                  ·
                    rfl

theorem cell20_565294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_565294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565294 prefixEnd_565294 := by exact prefixLift 565294
  have htrace : WordTrace (prefixWord ++ tailWord_565294) baseStart_565294 baseEnd_565294 := by
    simpa [prefixWord, tailWord_565294, baseEnd_565294] using wordTrace_append hprefix tailTrace_565294
  have hstable : (prefixWord ++ tailWord_565294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565294).length < 2 ^ (prefixWord ++ tailWord_565294).sum := by decide
  have hdescent : baseEnd_565294 < baseStart_565294 := by decide
  rcases family_descends (prefixWord ++ tailWord_565294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565312 : List Nat := [2, 1, 1, 2, 2, 4, 2, 6]
def baseStart_565312 : Nat := 118140960795 + 565312 * 2 ^ 59
def prefixEnd_565312 : Nat := 4983230072969 + 3 ^ 40 * 565312 * 2
def baseEnd_565312 : Nat := 86007933556917762340795

theorem tailTrace_565312 : CollatzResearch.WordTrace tailWord_565312 prefixEnd_565312 86007933556917762340795 := by
  unfold tailWord_565312
  simp only [CollatzResearch.WordTrace]
  refine ⟨10309311263989323224081095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13745748351985764298774793 10309311263989323224081095)
  ·
    refine ⟨15463966895983984836121643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10309311263989323224081095 15463966895983984836121643)
    ·
      refine ⟨23195950343975977254182465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15463966895983984836121643 23195950343975977254182465)
      ·
        refine ⟨17396962757981982940636849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23195950343975977254182465 17396962757981982940636849)
        ·
          refine ⟨13047722068486487205477637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17396962757981982940636849 13047722068486487205477637)
          ·
            refine ⟨2446447887841216351027057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13047722068486487205477637 2446447887841216351027057)
            ·
              refine ⟨1834835915880912263270293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2446447887841216351027057 1834835915880912263270293)
              ·
                refine ⟨86007933556917762340795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1834835915880912263270293 86007933556917762340795)
                ·
                  rfl

theorem cell20_565312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 6].length) (baseStart_565312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565312 prefixEnd_565312 := by exact prefixLift 565312
  have htrace : WordTrace (prefixWord ++ tailWord_565312) baseStart_565312 baseEnd_565312 := by
    simpa [prefixWord, tailWord_565312, baseEnd_565312] using wordTrace_append hprefix tailTrace_565312
  have hstable : (prefixWord ++ tailWord_565312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565312).length < 2 ^ (prefixWord ++ tailWord_565312).sum := by decide
  have hdescent : baseEnd_565312 < baseStart_565312 := by decide
  rcases family_descends (prefixWord ++ tailWord_565312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565318 : List Nat := [6, 1, 1, 1, 1, 1, 2, 5, 2]
def baseStart_565318 : Nat := 118140960795 + 565318 * 2 ^ 59
def prefixEnd_565318 : Nat := 4983230072969 + 3 ^ 40 * 565318 * 2
def baseEnd_565318 : Nat := 258026539234243932822361

theorem tailTrace_565318 : CollatzResearch.WordTrace tailWord_565318 prefixEnd_565318 258026539234243932822361 := by
  unfold tailWord_565318
  simp only [CollatzResearch.WordTrace]
  refine ⟨644338792686153421027519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13745894243971272981920405 644338792686153421027519)
  ·
    refine ⟨966508189029230131541279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 644338792686153421027519 966508189029230131541279)
    ·
      refine ⟨1449762283543845197311919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 966508189029230131541279 1449762283543845197311919)
      ·
        refine ⟨2174643425315767795967879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1449762283543845197311919 2174643425315767795967879)
        ·
          refine ⟨3261965137973651693951819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2174643425315767795967879 3261965137973651693951819)
          ·
            refine ⟨4892947706960477540927729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3261965137973651693951819 4892947706960477540927729)
            ·
              refine ⟨3669710780220358155695797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4892947706960477540927729 3669710780220358155695797)
              ·
                refine ⟨344035385645658577096481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3669710780220358155695797 344035385645658577096481)
                ·
                  refine ⟨258026539234243932822361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 344035385645658577096481 258026539234243932822361)
                  ·
                    rfl

theorem cell20_565318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_565318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565318 prefixEnd_565318 := by exact prefixLift 565318
  have htrace : WordTrace (prefixWord ++ tailWord_565318) baseStart_565318 baseEnd_565318 := by
    simpa [prefixWord, tailWord_565318, baseEnd_565318] using wordTrace_append hprefix tailTrace_565318
  have hstable : (prefixWord ++ tailWord_565318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565318).length < 2 ^ (prefixWord ++ tailWord_565318).sum := by decide
  have hdescent : baseEnd_565318 < baseStart_565318 := by decide
  rcases family_descends (prefixWord ++ tailWord_565318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565322 : List Nat := [3, 1, 2, 1, 1, 2, 1, 7, 2]
def baseStart_565322 : Nat := 118140960795 + 565322 * 2 ^ 59
def prefixEnd_565322 : Nat := 4983230072969 + 3 ^ 40 * 565322 * 2
def baseEnd_565322 : Nat := 258028364943237696689011

theorem tailTrace_565322 : CollatzResearch.WordTrace tailWord_565322 prefixEnd_565322 258028364943237696689011 := by
  unfold tailWord_565322
  simp only [CollatzResearch.WordTrace]
  refine ⟨5154746814485604539006555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13745991505294945437350813 5154746814485604539006555)
  ·
    refine ⟨7732120221728406808509833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5154746814485604539006555 7732120221728406808509833)
    ·
      refine ⟨5799090166296305106382375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7732120221728406808509833 5799090166296305106382375)
      ·
        refine ⟨8698635249444457659573563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5799090166296305106382375 8698635249444457659573563)
        ·
          refine ⟨13047952874166686489360345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8698635249444457659573563 13047952874166686489360345)
          ·
            refine ⟨9785964655625014867020259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13047952874166686489360345 9785964655625014867020259)
            ·
              refine ⟨14678946983437522300530389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9785964655625014867020259 14678946983437522300530389)
              ·
                refine ⟨344037819924316928918681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 14678946983437522300530389 344037819924316928918681)
                ·
                  refine ⟨258028364943237696689011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 344037819924316928918681 258028364943237696689011)
                  ·
                    rfl

theorem cell20_565322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 7, 2].length) (baseStart_565322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565322 prefixEnd_565322 := by exact prefixLift 565322
  have htrace : WordTrace (prefixWord ++ tailWord_565322) baseStart_565322 baseEnd_565322 := by
    simpa [prefixWord, tailWord_565322, baseEnd_565322] using wordTrace_append hprefix tailTrace_565322
  have hstable : (prefixWord ++ tailWord_565322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565322).length < 2 ^ (prefixWord ++ tailWord_565322).sum := by decide
  have hdescent : baseEnd_565322 < baseStart_565322 := by decide
  rcases family_descends (prefixWord ++ tailWord_565322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565336 : List Nat := [2, 1, 2, 2, 1, 4, 1, 4, 3]
def baseStart_565336 : Nat := 118140960795 + 565336 * 2 ^ 59
def prefixEnd_565336 : Nat := 4983230072969 + 3 ^ 40 * 565336 * 2
def baseEnd_565336 : Nat := 258034754924715870222287

theorem tailTrace_565336 : CollatzResearch.WordTrace tailWord_565336 prefixEnd_565336 258034754924715870222287 := by
  unfold tailWord_565336
  simp only [CollatzResearch.WordTrace]
  refine ⟨10309748939945849273517931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13746331919927799031357241 10309748939945849273517931)
  ·
    refine ⟨15464623409918773910276897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10309748939945849273517931 15464623409918773910276897)
    ·
      refine ⟨11598467557439080432707673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15464623409918773910276897 11598467557439080432707673)
      ·
        refine ⟨8698850668079310324530755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11598467557439080432707673 8698850668079310324530755)
        ·
          refine ⟨13048276002118965486796133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8698850668079310324530755 13048276002118965486796133)
          ·
            refine ⟨2446551750397306028774275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13048276002118965486796133 2446551750397306028774275)
            ·
              refine ⟨3669827625595959043161413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2446551750397306028774275 3669827625595959043161413)
              ·
                refine ⟨688092679799242320592765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3669827625595959043161413 688092679799242320592765)
                ·
                  refine ⟨258034754924715870222287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 688092679799242320592765 258034754924715870222287)
                  ·
                    rfl

theorem cell20_565336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 3].length) (baseStart_565336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565336 prefixEnd_565336 := by exact prefixLift 565336
  have htrace : WordTrace (prefixWord ++ tailWord_565336) baseStart_565336 baseEnd_565336 := by
    simpa [prefixWord, tailWord_565336, baseEnd_565336] using wordTrace_append hprefix tailTrace_565336
  have hstable : (prefixWord ++ tailWord_565336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565336).length < 2 ^ (prefixWord ++ tailWord_565336).sum := by decide
  have hdescent : baseEnd_565336 < baseStart_565336 := by decide
  rcases family_descends (prefixWord ++ tailWord_565336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565342 : List Nat := [4, 4, 1, 1, 2, 2, 1, 5]
def baseStart_565342 : Nat := 118140960795 + 565342 * 2 ^ 59
def prefixEnd_565342 : Nat := 4983230072969 + 3 ^ 40 * 565342 * 2
def baseEnd_565342 : Nat := 86012497829402172007421

theorem tailTrace_565342 : CollatzResearch.WordTrace tailWord_565342 prefixEnd_565342 86012497829402172007421 := by
  unfold tailWord_565342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2577464589733745196469285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13746477811913307714502853 2577464589733745196469285)
  ·
    refine ⟨483274610575077224337991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2577464589733745196469285 483274610575077224337991)
    ·
      refine ⟨724911915862615836506987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 483274610575077224337991 724911915862615836506987)
      ·
        refine ⟨1087367873793923754760481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 724911915862615836506987 1087367873793923754760481)
        ·
          refine ⟨815525905345442816070361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1087367873793923754760481 815525905345442816070361)
          ·
            refine ⟨611644429009082112052771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 815525905345442816070361 611644429009082112052771)
            ·
              refine ⟨917466643513623168079157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 611644429009082112052771 917466643513623168079157)
              ·
                refine ⟨86012497829402172007421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 917466643513623168079157 86012497829402172007421)
                ·
                  rfl

theorem cell20_565342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_565342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565342 prefixEnd_565342 := by exact prefixLift 565342
  have htrace : WordTrace (prefixWord ++ tailWord_565342) baseStart_565342 baseEnd_565342 := by
    simpa [prefixWord, tailWord_565342, baseEnd_565342] using wordTrace_append hprefix tailTrace_565342
  have hstable : (prefixWord ++ tailWord_565342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565342).length < 2 ^ (prefixWord ++ tailWord_565342).sum := by decide
  have hdescent : baseEnd_565342 < baseStart_565342 := by decide
  rcases family_descends (prefixWord ++ tailWord_565342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565367 : List Nat := [1, 1, 3, 1, 1, 6, 3, 4]
def baseStart_565367 : Nat := 118140960795 + 565367 * 2 ^ 59
def prefixEnd_565367 : Nat := 4983230072969 + 3 ^ 40 * 565367 * 2
def baseEnd_565367 : Nat := 86016301389805846729609

theorem tailTrace_565367 : CollatzResearch.WordTrace tailWord_565367 prefixEnd_565367 86016301389805846729609 := by
  unfold tailWord_565367
  simp only [CollatzResearch.WordTrace]
  refine ⟨20620628542779390841414355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13747085695186260560942903 20620628542779390841414355)
  ·
    refine ⟨30930942814169086262121533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20620628542779390841414355 30930942814169086262121533)
    ·
      refine ⟨11599103555313407348295575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30930942814169086262121533 11599103555313407348295575)
      ·
        refine ⟨17398655332970111022443363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11599103555313407348295575 17398655332970111022443363)
        ·
          refine ⟨26097982999455166533665045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17398655332970111022443363 26097982999455166533665045)
          ·
            refine ⟨1223342953099460931265549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 26097982999455166533665045 1223342953099460931265549)
            ·
              refine ⟨458753607412297849224581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1223342953099460931265549 458753607412297849224581)
              ·
                refine ⟨86016301389805846729609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 458753607412297849224581 86016301389805846729609)
                ·
                  rfl

theorem cell20_565367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 4].length) (baseStart_565367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565367 prefixEnd_565367 := by exact prefixLift 565367
  have htrace : WordTrace (prefixWord ++ tailWord_565367) baseStart_565367 baseEnd_565367 := by
    simpa [prefixWord, tailWord_565367, baseEnd_565367] using wordTrace_append hprefix tailTrace_565367
  have hstable : (prefixWord ++ tailWord_565367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565367).length < 2 ^ (prefixWord ++ tailWord_565367).sum := by decide
  have hdescent : baseEnd_565367 < baseStart_565367 := by decide
  rcases family_descends (prefixWord ++ tailWord_565367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565418 : List Nat := [3, 1, 5, 1, 3, 1, 2, 4]
def baseStart_565418 : Nat := 118140960795 + 565418 * 2 ^ 59
def prefixEnd_565418 : Nat := 4983230072969 + 3 ^ 40 * 565418 * 2
def baseEnd_565418 : Nat := 86024060653029343162873

theorem tailTrace_565418 : CollatzResearch.WordTrace tailWord_565418 prefixEnd_565418 86024060653029343162873 := by
  unfold tailWord_565418
  simp only [CollatzResearch.WordTrace]
  refine ⟨5155622166398656637880227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13748325777063084367680605 5155622166398656637880227)
  ·
    refine ⟨7733433249597984956820341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5155622166398656637880227 7733433249597984956820341)
    ·
      refine ⟨725009367149811089701907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7733433249597984956820341 725009367149811089701907)
      ·
        refine ⟨1087514050724716634552861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 725009367149811089701907 1087514050724716634552861)
        ·
          refine ⟨407817769021768737957323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1087514050724716634552861 407817769021768737957323)
          ·
            refine ⟨611726653532653106935985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407817769021768737957323 611726653532653106935985)
            ·
              refine ⟨458794990149489830201989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 611726653532653106935985 458794990149489830201989)
              ·
                refine ⟨86024060653029343162873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 458794990149489830201989 86024060653029343162873)
                ·
                  rfl

theorem cell20_565418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 4].length) (baseStart_565418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565418 prefixEnd_565418 := by exact prefixLift 565418
  have htrace : WordTrace (prefixWord ++ tailWord_565418) baseStart_565418 baseEnd_565418 := by
    simpa [prefixWord, tailWord_565418, baseEnd_565418] using wordTrace_append hprefix tailTrace_565418
  have hstable : (prefixWord ++ tailWord_565418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565418).length < 2 ^ (prefixWord ++ tailWord_565418).sum := by decide
  have hdescent : baseEnd_565418 < baseStart_565418 := by decide
  rcases family_descends (prefixWord ++ tailWord_565418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565426 : List Nat := [3, 2, 1, 1, 1, 3, 3, 6]
def baseStart_565426 : Nat := 118140960795 + 565426 * 2 ^ 59
def prefixEnd_565426 : Nat := 4983230072969 + 3 ^ 40 * 565426 * 2
def baseEnd_565426 : Nat := 86025277792358519073973

theorem tailTrace_565426 : CollatzResearch.WordTrace tailWord_565426 prefixEnd_565426 86025277792358519073973 := by
  unfold tailWord_565426
  simp only [CollatzResearch.WordTrace]
  refine ⟨5155695112391410979453033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13748520299710429278541421 5155695112391410979453033)
  ·
    refine ⟨3866771334293558234589775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5155695112391410979453033 3866771334293558234589775)
    ·
      refine ⟨5800157001440337351884663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3866771334293558234589775 5800157001440337351884663)
      ·
        refine ⟨8700235502160506027826995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5800157001440337351884663 8700235502160506027826995)
        ·
          refine ⟨13050353253240759041740493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8700235502160506027826995 13050353253240759041740493)
          ·
            refine ⟨4893882469965284640652685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13050353253240759041740493 4893882469965284640652685)
            ·
              refine ⟨1835205926236981740244757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4893882469965284640652685 1835205926236981740244757)
              ·
                refine ⟨86025277792358519073973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1835205926236981740244757 86025277792358519073973)
                ·
                  rfl

theorem cell20_565426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_565426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565426 prefixEnd_565426 := by exact prefixLift 565426
  have htrace : WordTrace (prefixWord ++ tailWord_565426) baseStart_565426 baseEnd_565426 := by
    simpa [prefixWord, tailWord_565426, baseEnd_565426] using wordTrace_append hprefix tailTrace_565426
  have hstable : (prefixWord ++ tailWord_565426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565426).length < 2 ^ (prefixWord ++ tailWord_565426).sum := by decide
  have hdescent : baseEnd_565426 < baseStart_565426 := by decide
  rcases family_descends (prefixWord ++ tailWord_565426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565433 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 7]
def baseStart_565433 : Nat := 118140960795 + 565433 * 2 ^ 59
def prefixEnd_565433 : Nat := 4983230072969 + 3 ^ 40 * 565433 * 2
def baseEnd_565433 : Nat := 258079028367814643988557

theorem tailTrace_565433 : CollatzResearch.WordTrace tailWord_565433 prefixEnd_565433 258079028367814643988557 := by
  unfold tailWord_565433
  simp only [CollatzResearch.WordTrace]
  refine ⟨20623035760540284113316953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13748690507026856075544635 20623035760540284113316953)
  ·
    refine ⟨15467276820405213084987715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20623035760540284113316953 15467276820405213084987715)
    ·
      refine ⟨23200915230607819627481573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15467276820405213084987715 23200915230607819627481573)
      ·
        refine ⟨4350171605738966180152795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23200915230607819627481573 4350171605738966180152795)
        ·
          refine ⟨6525257408608449270229193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4350171605738966180152795 6525257408608449270229193)
          ·
            refine ⟨4893943056456336952671895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6525257408608449270229193 4893943056456336952671895)
            ·
              refine ⟨7340914584684505429007843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4893943056456336952671895 7340914584684505429007843)
              ·
                refine ⟨11011371877026758143511765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7340914584684505429007843 11011371877026758143511765)
                ·
                  refine ⟨258079028367814643988557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11011371877026758143511765 258079028367814643988557)
                  ·
                    rfl

theorem cell20_565433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_565433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565433 prefixEnd_565433 := by exact prefixLift 565433
  have htrace : WordTrace (prefixWord ++ tailWord_565433) baseStart_565433 baseEnd_565433 := by
    simpa [prefixWord, tailWord_565433, baseEnd_565433] using wordTrace_append hprefix tailTrace_565433
  have hstable : (prefixWord ++ tailWord_565433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565433).length < 2 ^ (prefixWord ++ tailWord_565433).sum := by decide
  have hdescent : baseEnd_565433 < baseStart_565433 := by decide
  rcases family_descends (prefixWord ++ tailWord_565433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565450 : List Nat := [3, 1, 2, 1, 3, 1, 2, 4, 3]
def baseStart_565450 : Nat := 118140960795 + 565450 * 2 ^ 59
def prefixEnd_565450 : Nat := 4983230072969 + 3 ^ 40 * 565450 * 2
def baseEnd_565450 : Nat := 258086787631038140421821

theorem tailTrace_565450 : CollatzResearch.WordTrace tailWord_565450 prefixEnd_565450 258086787631038140421821 := by
  unfold tailWord_565450
  simp only [CollatzResearch.WordTrace]
  refine ⟨5155913950369674004171451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13749103867652464011123869 5155913950369674004171451)
  ·
    refine ⟨7733870925554511006257177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5155913950369674004171451 7733870925554511006257177)
    ·
      refine ⟨5800403194165883254692883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7733870925554511006257177 5800403194165883254692883)
      ·
        refine ⟨8700604791248824882039325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5800403194165883254692883 8700604791248824882039325)
        ·
          refine ⟨3262726796718309330764747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8700604791248824882039325 3262726796718309330764747)
          ·
            refine ⟨4894090195077463996147121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3262726796718309330764747 4894090195077463996147121)
            ·
              refine ⟨3670567646308097997110341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4894090195077463996147121 3670567646308097997110341)
              ·
                refine ⟨688231433682768374458189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3670567646308097997110341 688231433682768374458189)
                ·
                  refine ⟨258086787631038140421821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 688231433682768374458189 258086787631038140421821)
                  ·
                    rfl

theorem cell20_565450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_565450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565450 prefixEnd_565450 := by exact prefixLift 565450
  have htrace : WordTrace (prefixWord ++ tailWord_565450) baseStart_565450 baseEnd_565450 := by
    simpa [prefixWord, tailWord_565450, baseEnd_565450] using wordTrace_append hprefix tailTrace_565450
  have hstable : (prefixWord ++ tailWord_565450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565450).length < 2 ^ (prefixWord ++ tailWord_565450).sum := by decide
  have hdescent : baseEnd_565450 < baseStart_565450 := by decide
  rcases family_descends (prefixWord ++ tailWord_565450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565457 : List Nat := [1, 2, 2, 1, 2, 2, 5, 1, 4]
def baseStart_565457 : Nat := 118140960795 + 565457 * 2 ^ 59
def prefixEnd_565457 : Nat := 4983230072969 + 3 ^ 40 * 565457 * 2
def baseEnd_565457 : Nat := 258089982621777227188459

theorem tailTrace_565457 : CollatzResearch.WordTrace tailWord_565457 prefixEnd_565457 258089982621777227188459 := by
  unfold tailWord_565457
  simp only [CollatzResearch.WordTrace]
  refine ⟨20623911112453336212190625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13749274074968890808127083 20623911112453336212190625)
  ·
    refine ⟨15467933334340002159142969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20623911112453336212190625 15467933334340002159142969)
    ·
      refine ⟨11600950000755001619357227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15467933334340002159142969 11600950000755001619357227)
      ·
        refine ⟨17401425001132502429035841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11600950000755001619357227 17401425001132502429035841)
        ·
          refine ⟨13051068750849376821776881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17401425001132502429035841 13051068750849376821776881)
          ·
            refine ⟨9788301563137032616332661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13051068750849376821776881 9788301563137032616332661)
            ·
              refine ⟨917653271544096807781187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9788301563137032616332661 917653271544096807781187)
              ·
                refine ⟨1376479907316145211671781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 917653271544096807781187 1376479907316145211671781)
                ·
                  refine ⟨258089982621777227188459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1376479907316145211671781 258089982621777227188459)
                  ·
                    rfl

theorem cell20_565457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 4].length) (baseStart_565457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565457 prefixEnd_565457 := by exact prefixLift 565457
  have htrace : WordTrace (prefixWord ++ tailWord_565457) baseStart_565457 baseEnd_565457 := by
    simpa [prefixWord, tailWord_565457, baseEnd_565457] using wordTrace_append hprefix tailTrace_565457
  have hstable : (prefixWord ++ tailWord_565457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565457).length < 2 ^ (prefixWord ++ tailWord_565457).sum := by decide
  have hdescent : baseEnd_565457 < baseStart_565457 := by decide
  rcases family_descends (prefixWord ++ tailWord_565457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565464 : List Nat := [2, 1, 2, 2, 4, 1, 1, 7]
def baseStart_565464 : Nat := 118140960795 + 565464 * 2 ^ 59
def prefixEnd_565464 : Nat := 4983230072969 + 3 ^ 40 * 565464 * 2
def baseEnd_565464 : Nat := 86031059204172104651699

theorem tailTrace_565464 : CollatzResearch.WordTrace tailWord_565464 prefixEnd_565464 86031059204172104651699 := by
  unfold tailWord_565464
  simp only [CollatzResearch.WordTrace]
  refine ⟨10312083211713988203847723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13749444282285317605130297 10312083211713988203847723)
  ·
    refine ⟨15468124817570982305771585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10312083211713988203847723 15468124817570982305771585)
    ·
      refine ⟨11601093613178236729328689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15468124817570982305771585 11601093613178236729328689)
      ·
        refine ⟨8700820209883677546996517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11601093613178236729328689 8700820209883677546996517)
        ·
          refine ⟨1631403789353189540061847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8700820209883677546996517 1631403789353189540061847)
          ·
            refine ⟨2447105684029784310092771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1631403789353189540061847 2447105684029784310092771)
            ·
              refine ⟨3670658526044676465139157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2447105684029784310092771 3670658526044676465139157)
              ·
                refine ⟨86031059204172104651699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3670658526044676465139157 86031059204172104651699)
                ·
                  rfl

theorem cell20_565464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 7].length) (baseStart_565464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565464 prefixEnd_565464 := by exact prefixLift 565464
  have htrace : WordTrace (prefixWord ++ tailWord_565464) baseStart_565464 baseEnd_565464 := by
    simpa [prefixWord, tailWord_565464, baseEnd_565464] using wordTrace_append hprefix tailTrace_565464
  have hstable : (prefixWord ++ tailWord_565464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565464).length < 2 ^ (prefixWord ++ tailWord_565464).sum := by decide
  have hdescent : baseEnd_565464 < baseStart_565464 := by decide
  rcases family_descends (prefixWord ++ tailWord_565464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565546 : List Nat := [3, 1, 4, 2, 2, 1, 2, 3, 2]
def baseStart_565546 : Nat := 118140960795 + 565546 * 2 ^ 59
def prefixEnd_565546 : Nat := 4983230072969 + 3 ^ 40 * 565546 * 2
def baseEnd_565546 : Nat := 258130604646888473221429

theorem tailTrace_565546 : CollatzResearch.WordTrace tailWord_565546 prefixEnd_565546 258130604646888473221429 := by
  unfold tailWord_565546
  simp only [CollatzResearch.WordTrace]
  refine ⟨5156789302282726103045123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13751438139420602941453661 5156789302282726103045123)
  ·
    refine ⟨7735183953424089154567685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5156789302282726103045123 7735183953424089154567685)
    ·
      refine ⟨1450346991267016716481441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7735183953424089154567685 1450346991267016716481441)
      ·
        refine ⟨1087760243450262537361081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1450346991267016716481441 1087760243450262537361081)
        ·
          refine ⟨815820182587696903020811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1087760243450262537361081 815820182587696903020811)
          ·
            refine ⟨1223730273881545354531217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 815820182587696903020811 1223730273881545354531217)
            ·
              refine ⟨917797705411159015898413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1223730273881545354531217 917797705411159015898413)
              ·
                refine ⟨344174139529184630961905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 917797705411159015898413 344174139529184630961905)
                ·
                  refine ⟨258130604646888473221429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 344174139529184630961905 258130604646888473221429)
                  ·
                    rfl

theorem cell20_565546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 3, 2].length) (baseStart_565546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565546 prefixEnd_565546 := by exact prefixLift 565546
  have htrace : WordTrace (prefixWord ++ tailWord_565546) baseStart_565546 baseEnd_565546 := by
    simpa [prefixWord, tailWord_565546, baseEnd_565546] using wordTrace_append hprefix tailTrace_565546
  have hstable : (prefixWord ++ tailWord_565546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565546).length < 2 ^ (prefixWord ++ tailWord_565546).sum := by decide
  have hdescent : baseEnd_565546 < baseStart_565546 := by decide
  rcases family_descends (prefixWord ++ tailWord_565546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565592 : List Nat := [2, 1, 2, 2, 1, 1, 2, 3, 6]
def baseStart_565592 : Nat := 118140960795 + 565592 * 2 ^ 59
def prefixEnd_565592 : Nat := 4983230072969 + 3 ^ 40 * 565592 * 2
def baseEnd_565592 : Nat := 258151600300316757687907

theorem tailTrace_565592 : CollatzResearch.WordTrace tailWord_565592 prefixEnd_565592 258151600300316757687907 := by
  unfold tailWord_565592
  simp only [CollatzResearch.WordTrace]
  refine ⟨10314417483482127134177515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13752556644642836178903353 10314417483482127134177515)
  ·
    refine ⟨15471626225223190701266273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10314417483482127134177515 15471626225223190701266273)
    ·
      refine ⟨11603719668917393025949705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15471626225223190701266273 11603719668917393025949705)
      ·
        refine ⟨8702789751688044769462279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11603719668917393025949705 8702789751688044769462279)
        ·
          refine ⟨13054184627532067154193419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8702789751688044769462279 13054184627532067154193419)
          ·
            refine ⟨19581276941298100731290129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13054184627532067154193419 19581276941298100731290129)
            ·
              refine ⟨14685957705973575548467597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19581276941298100731290129 14685957705973575548467597)
              ·
                refine ⟨5507234139740090830675349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14685957705973575548467597 5507234139740090830675349)
                ·
                  refine ⟨258151600300316757687907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5507234139740090830675349 258151600300316757687907)
                  ·
                    rfl

theorem cell20_565592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_565592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565592 prefixEnd_565592 := by exact prefixLift 565592
  have htrace : WordTrace (prefixWord ++ tailWord_565592) baseStart_565592 baseEnd_565592 := by
    simpa [prefixWord, tailWord_565592, baseEnd_565592] using wordTrace_append hprefix tailTrace_565592
  have hstable : (prefixWord ++ tailWord_565592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565592).length < 2 ^ (prefixWord ++ tailWord_565592).sum := by decide
  have hdescent : baseEnd_565592 < baseStart_565592 := by decide
  rcases family_descends (prefixWord ++ tailWord_565592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565602 : List Nat := [3, 3, 2, 1, 1, 2, 1, 2, 5]
def baseStart_565602 : Nat := 118140960795 + 565602 * 2 ^ 59
def prefixEnd_565602 : Nat := 4983230072969 + 3 ^ 40 * 565602 * 2
def baseEnd_565602 : Nat := 258156164572801167354533

theorem tailTrace_565602 : CollatzResearch.WordTrace tailWord_565602 prefixEnd_565602 258156164572801167354533 := by
  unfold tailWord_565602
  simp only [CollatzResearch.WordTrace]
  refine ⟨5157299924232006494054765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13752799797952017317479373 5157299924232006494054765)
  ·
    refine ⟨1933987471587002435270537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5157299924232006494054765 1933987471587002435270537)
    ·
      refine ⟨1450490603690251826452903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1933987471587002435270537 1450490603690251826452903)
      ·
        refine ⟨2175735905535377739679355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1450490603690251826452903 2175735905535377739679355)
        ·
          refine ⟨3263603858303066609519033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2175735905535377739679355 3263603858303066609519033)
          ·
            refine ⟨2447702893727299957139275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3263603858303066609519033 2447702893727299957139275)
            ·
              refine ⟨3671554340590949935708913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2447702893727299957139275 3671554340590949935708913)
              ·
                refine ⟨2753665755443212451781685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3671554340590949935708913 2753665755443212451781685)
                ·
                  refine ⟨258156164572801167354533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2753665755443212451781685 258156164572801167354533)
                  ·
                    rfl

theorem cell20_565602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_565602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565602 prefixEnd_565602 := by exact prefixLift 565602
  have htrace : WordTrace (prefixWord ++ tailWord_565602) baseStart_565602 baseEnd_565602 := by
    simpa [prefixWord, tailWord_565602, baseEnd_565602] using wordTrace_append hprefix tailTrace_565602
  have hstable : (prefixWord ++ tailWord_565602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565602).length < 2 ^ (prefixWord ++ tailWord_565602).sum := by decide
  have hdescent : baseEnd_565602 < baseStart_565602 := by decide
  rcases family_descends (prefixWord ++ tailWord_565602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565605 : List Nat := [1, 3, 1, 3, 1, 5, 1, 3, 2]
def baseStart_565605 : Nat := 118140960795 + 565605 * 2 ^ 59
def prefixEnd_565605 : Nat := 4983230072969 + 3 ^ 40 * 565605 * 2
def baseEnd_565605 : Nat := 258157533854546490254521

theorem tailTrace_565605 : CollatzResearch.WordTrace tailWord_565605 prefixEnd_565605 258157533854546490254521 := by
  unfold tailWord_565605
  simp only [CollatzResearch.WordTrace]
  refine ⟨20629309115917157488578269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13752872743944771659052179 20629309115917157488578269)
  ·
    refine ⟨7735990918468934058216851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20629309115917157488578269 7735990918468934058216851)
    ·
      refine ⟨11603986377703401087325277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7735990918468934058216851 11603986377703401087325277)
      ·
        refine ⟨4351494891638775407746979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11603986377703401087325277 4351494891638775407746979)
        ·
          refine ⟨6527242337458163111620469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4351494891638775407746979 6527242337458163111620469)
          ·
            refine ⟨611928969136702791714419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6527242337458163111620469 611928969136702791714419)
            ·
              refine ⟨917893453705054187571629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 611928969136702791714419 917893453705054187571629)
              ·
                refine ⟨344210045139395320339361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 917893453705054187571629 344210045139395320339361)
                ·
                  refine ⟨258157533854546490254521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 344210045139395320339361 258157533854546490254521)
                  ·
                    rfl

theorem cell20_565605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 3, 2].length) (baseStart_565605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565605 prefixEnd_565605 := by exact prefixLift 565605
  have htrace : WordTrace (prefixWord ++ tailWord_565605) baseStart_565605 baseEnd_565605 := by
    simpa [prefixWord, tailWord_565605, baseEnd_565605] using wordTrace_append hprefix tailTrace_565605
  have hstable : (prefixWord ++ tailWord_565605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565605).length < 2 ^ (prefixWord ++ tailWord_565605).sum := by decide
  have hdescent : baseEnd_565605 < baseStart_565605 := by decide
  rcases family_descends (prefixWord ++ tailWord_565605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565616 : List Nat := [2, 1, 1, 1, 4, 5, 6]
def baseStart_565616 : Nat := 118140960795 + 565616 * 2 ^ 59
def prefixEnd_565616 : Nat := 4983230072969 + 3 ^ 40 * 565616 * 2
def baseEnd_565616 : Nat := 28684728283808815654201

theorem tailTrace_565616 : CollatzResearch.WordTrace tailWord_565616 prefixEnd_565616 28684728283808815654201 := by
  unfold tailWord_565616
  simp only [CollatzResearch.WordTrace]
  refine ⟨10314855159438653183614351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13753140212584870911485801 10314855159438653183614351)
  ·
    refine ⟨15472282739157979775421527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10314855159438653183614351 15472282739157979775421527)
    ·
      refine ⟨23208424108736969663132291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15472282739157979775421527 23208424108736969663132291)
      ·
        refine ⟨34812636163105454494698437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23208424108736969663132291 34812636163105454494698437)
        ·
          refine ⟨6527369280582272717755957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34812636163105454494698437 6527369280582272717755957)
          ·
            refine ⟨611940870054588067289621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6527369280582272717755957 611940870054588067289621)
            ·
              refine ⟨28684728283808815654201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 611940870054588067289621 28684728283808815654201)
              ·
                rfl

theorem cell20_565616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 6].length) (baseStart_565616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565616 prefixEnd_565616 := by exact prefixLift 565616
  have htrace : WordTrace (prefixWord ++ tailWord_565616) baseStart_565616 baseEnd_565616 := by
    simpa [prefixWord, tailWord_565616, baseEnd_565616] using wordTrace_append hprefix tailTrace_565616
  have hstable : (prefixWord ++ tailWord_565616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565616).length < 2 ^ (prefixWord ++ tailWord_565616).sum := by decide
  have hdescent : baseEnd_565616 < baseStart_565616 := by decide
  rcases family_descends (prefixWord ++ tailWord_565616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565622 : List Nat := [5, 1, 1, 4, 1, 2, 1, 1, 4]
def baseStart_565622 : Nat := 118140960795 + 565622 * 2 ^ 59
def prefixEnd_565622 : Nat := 4983230072969 + 3 ^ 40 * 565622 * 2
def baseEnd_565622 : Nat := 258165293117769986687785

theorem tailTrace_565622 : CollatzResearch.WordTrace tailWord_565622 prefixEnd_565622 258165293117769986687785 := by
  unfold tailWord_565622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1289370572303473086996695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13753286104570379594631413 1289370572303473086996695)
  ·
    refine ⟨1934055858455209630495043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1289370572303473086996695 1934055858455209630495043)
    ·
      refine ⟨2901083787682814445742565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1934055858455209630495043 2901083787682814445742565)
      ·
        refine ⟨543953210190527708576731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2901083787682814445742565 543953210190527708576731)
        ·
          refine ⟨815929815285791562865097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 543953210190527708576731 815929815285791562865097)
          ·
            refine ⟨611947361464343672148823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 815929815285791562865097 611947361464343672148823)
            ·
              refine ⟨917921042196515508223235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 611947361464343672148823 917921042196515508223235)
              ·
                refine ⟨1376881563294773262334853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 917921042196515508223235 1376881563294773262334853)
                ·
                  refine ⟨258165293117769986687785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1376881563294773262334853 258165293117769986687785)
                  ·
                    rfl

theorem cell20_565622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_565622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565622 prefixEnd_565622 := by exact prefixLift 565622
  have htrace : WordTrace (prefixWord ++ tailWord_565622) baseStart_565622 baseEnd_565622 := by
    simpa [prefixWord, tailWord_565622, baseEnd_565622] using wordTrace_append hprefix tailTrace_565622
  have hstable : (prefixWord ++ tailWord_565622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565622).length < 2 ^ (prefixWord ++ tailWord_565622).sum := by decide
  have hdescent : baseEnd_565622 < baseStart_565622 := by decide
  rcases family_descends (prefixWord ++ tailWord_565622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565633 : List Nat := [1, 2, 4, 3, 1, 2, 2, 5]
def baseStart_565633 : Nat := 118140960795 + 565633 * 2 ^ 59
def prefixEnd_565633 : Nat := 4983230072969 + 3 ^ 40 * 565633 * 2
def baseEnd_565633 : Nat := 86056771272500945773691

theorem tailTrace_565633 : CollatzResearch.WordTrace tailWord_565633 prefixEnd_565633 86056771272500945773691 := by
  unfold tailWord_565633
  simp only [CollatzResearch.WordTrace]
  refine ⟨20630330359815718270597553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13753553573210478847065035 20630330359815718270597553)
  ·
    refine ⟨15472747769861788702948165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20630330359815718270597553 15472747769861788702948165)
    ·
      refine ⟨2901140206849085381802781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15472747769861788702948165 2901140206849085381802781)
      ·
        refine ⟨1087927577568407018176043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2901140206849085381802781 1087927577568407018176043)
        ·
          refine ⟨1631891366352610527264065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1087927577568407018176043 1631891366352610527264065)
          ·
            refine ⟨1223918524764457895448049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1631891366352610527264065 1223918524764457895448049)
            ·
              refine ⟨917938893573343421586037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1223918524764457895448049 917938893573343421586037)
              ·
                refine ⟨86056771272500945773691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 917938893573343421586037 86056771272500945773691)
                ·
                  rfl

theorem cell20_565633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 5].length) (baseStart_565633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565633 prefixEnd_565633 := by exact prefixLift 565633
  have htrace : WordTrace (prefixWord ++ tailWord_565633) baseStart_565633 baseEnd_565633 := by
    simpa [prefixWord, tailWord_565633, baseEnd_565633] using wordTrace_append hprefix tailTrace_565633
  have hstable : (prefixWord ++ tailWord_565633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565633).length < 2 ^ (prefixWord ++ tailWord_565633).sum := by decide
  have hdescent : baseEnd_565633 < baseStart_565633 := by decide
  rcases family_descends (prefixWord ++ tailWord_565633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565640 : List Nat := [2, 1, 3, 3, 1, 1, 3, 3, 3]
def baseStart_565640 : Nat := 118140960795 + 565640 * 2 ^ 59
def prefixEnd_565640 : Nat := 4983230072969 + 3 ^ 40 * 565640 * 2
def baseEnd_565640 : Nat := 258173508808241924087711

theorem tailTrace_565640 : CollatzResearch.WordTrace tailWord_565640 prefixEnd_565640 258173508808241924087711 := by
  unfold tailWord_565640
  simp only [CollatzResearch.WordTrace]
  refine ⟨10315292835395179233051187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13753723780526905644068249 10315292835395179233051187)
  ·
    refine ⟨15472939253092768849576781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10315292835395179233051187 15472939253092768849576781)
    ·
      refine ⟨5802352219909788318591293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15472939253092768849576781 5802352219909788318591293)
      ·
        refine ⟨2175882082466170619471735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5802352219909788318591293 2175882082466170619471735)
        ·
          refine ⟨3263823123699255929207603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2175882082466170619471735 3263823123699255929207603)
          ·
            refine ⟨4895734685548883893811405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3263823123699255929207603 4895734685548883893811405)
            ·
              refine ⟨1835900507080831460179277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4895734685548883893811405 1835900507080831460179277)
              ·
                refine ⟨688462690155311797567229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1835900507080831460179277 688462690155311797567229)
                ·
                  refine ⟨258173508808241924087711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 688462690155311797567229 258173508808241924087711)
                  ·
                    rfl

theorem cell20_565640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 3].length) (baseStart_565640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565640 prefixEnd_565640 := by exact prefixLift 565640
  have htrace : WordTrace (prefixWord ++ tailWord_565640) baseStart_565640 baseEnd_565640 := by
    simpa [prefixWord, tailWord_565640, baseEnd_565640] using wordTrace_append hprefix tailTrace_565640
  have hstable : (prefixWord ++ tailWord_565640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565640).length < 2 ^ (prefixWord ++ tailWord_565640).sum := by decide
  have hdescent : baseEnd_565640 < baseStart_565640 := by decide
  rcases family_descends (prefixWord ++ tailWord_565640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565677 : List Nat := [1, 5, 2, 2, 2, 2, 2, 2, 2]
def baseStart_565677 : Nat := 118140960795 + 565677 * 2 ^ 59
def prefixEnd_565677 : Nat := 4983230072969 + 3 ^ 40 * 565677 * 2
def baseEnd_565677 : Nat := 258190396616434239854227

theorem tailTrace_565677 : CollatzResearch.WordTrace tailWord_565677 prefixEnd_565677 258190396616434239854227 := by
  unfold tailWord_565677
  simp only [CollatzResearch.WordTrace]
  refine ⟨20631935171656313785199285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13754623447770875856799523 20631935171656313785199285)
  ·
    refine ⟨1934243922342779417362433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20631935171656313785199285 1934243922342779417362433)
    ·
      refine ⟨1450682941757084563021825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1934243922342779417362433 1450682941757084563021825)
      ·
        refine ⟨1088012206317813422266369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1450682941757084563021825 1088012206317813422266369)
        ·
          refine ⟨816009154738360066699777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1088012206317813422266369 816009154738360066699777)
          ·
            refine ⟨612006866053770050024833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 816009154738360066699777 612006866053770050024833)
            ·
              refine ⟨459005149540327537518625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 612006866053770050024833 459005149540327537518625)
              ·
                refine ⟨344253862155245653138969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 459005149540327537518625 344253862155245653138969)
                ·
                  refine ⟨258190396616434239854227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 344253862155245653138969 258190396616434239854227)
                  ·
                    rfl

theorem cell20_565677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_565677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565677 prefixEnd_565677 := by exact prefixLift 565677
  have htrace : WordTrace (prefixWord ++ tailWord_565677) baseStart_565677 baseEnd_565677 := by
    simpa [prefixWord, tailWord_565677, baseEnd_565677] using wordTrace_append hprefix tailTrace_565677
  have hstable : (prefixWord ++ tailWord_565677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565677).length < 2 ^ (prefixWord ++ tailWord_565677).sum := by decide
  have hdescent : baseEnd_565677 < baseStart_565677 := by decide
  rcases family_descends (prefixWord ++ tailWord_565677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565681 : List Nat := [1, 2, 2, 4, 1, 2, 4, 2, 2]
def baseStart_565681 : Nat := 118140960795 + 565681 * 2 ^ 59
def prefixEnd_565681 : Nat := 4983230072969 + 3 ^ 40 * 565681 * 2
def baseEnd_565681 : Nat := 258192222325428003720877

theorem tailTrace_565681 : CollatzResearch.WordTrace tailWord_565681 prefixEnd_565681 258192222325428003720877 := by
  unfold tailWord_565681
  simp only [CollatzResearch.WordTrace]
  refine ⟨20632081063641822468344897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13754720709094548312229931 20632081063641822468344897)
  ·
    refine ⟨15474060797731366851258673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20632081063641822468344897 15474060797731366851258673)
    ·
      refine ⟨11605545598298525138444005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15474060797731366851258673 11605545598298525138444005)
      ·
        refine ⟨2176039799680973463458251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11605545598298525138444005 2176039799680973463458251)
        ·
          refine ⟨3264059699521460195187377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2176039799680973463458251 3264059699521460195187377)
          ·
            refine ⟨2448044774641095146390533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3264059699521460195187377 2448044774641095146390533)
            ·
              refine ⟨459008395245205339948225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2448044774641095146390533 459008395245205339948225)
              ·
                refine ⟨344256296433904004961169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 459008395245205339948225 344256296433904004961169)
                ·
                  refine ⟨258192222325428003720877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 344256296433904004961169 258192222325428003720877)
                  ·
                    rfl

theorem cell20_565681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 2, 2].length) (baseStart_565681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565681 prefixEnd_565681 := by exact prefixLift 565681
  have htrace : WordTrace (prefixWord ++ tailWord_565681) baseStart_565681 baseEnd_565681 := by
    simpa [prefixWord, tailWord_565681, baseEnd_565681] using wordTrace_append hprefix tailTrace_565681
  have hstable : (prefixWord ++ tailWord_565681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565681).length < 2 ^ (prefixWord ++ tailWord_565681).sum := by decide
  have hdescent : baseEnd_565681 < baseStart_565681 := by decide
  rcases family_descends (prefixWord ++ tailWord_565681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565684 : List Nat := [2, 5, 2, 2, 2, 1, 1, 5]
def baseStart_565684 : Nat := 118140960795 + 565684 * 2 ^ 59
def prefixEnd_565684 : Nat := 4983230072969 + 3 ^ 40 * 565684 * 2
def baseEnd_565684 : Nat := 86064530535724442206955

theorem tailTrace_565684 : CollatzResearch.WordTrace tailWord_565684 prefixEnd_565684 86064530535724442206955 := by
  unfold tailWord_565684
  simp only [CollatzResearch.WordTrace]
  refine ⟨10316095241315476990352053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13754793655087302653802737 10316095241315476990352053)
  ·
    refine ⟨967133928873325967845505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10316095241315476990352053 967133928873325967845505)
    ·
      refine ⟨725350446654994475884129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 967133928873325967845505 725350446654994475884129)
      ·
        refine ⟨544012834991245856913097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 725350446654994475884129 544012834991245856913097)
        ·
          refine ⟨408009626243434392684823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 544012834991245856913097 408009626243434392684823)
          ·
            refine ⟨612014439365151589027235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408009626243434392684823 612014439365151589027235)
            ·
              refine ⟨918021659047727383540853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 612014439365151589027235 918021659047727383540853)
              ·
                refine ⟨86064530535724442206955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 918021659047727383540853 86064530535724442206955)
                ·
                  rfl

theorem cell20_565684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 5].length) (baseStart_565684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565684 prefixEnd_565684 := by exact prefixLift 565684
  have htrace : WordTrace (prefixWord ++ tailWord_565684) baseStart_565684 baseEnd_565684 := by
    simpa [prefixWord, tailWord_565684, baseEnd_565684] using wordTrace_append hprefix tailTrace_565684
  have hstable : (prefixWord ++ tailWord_565684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565684).length < 2 ^ (prefixWord ++ tailWord_565684).sum := by decide
  have hdescent : baseEnd_565684 < baseStart_565684 := by decide
  rcases family_descends (prefixWord ++ tailWord_565684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565713 : List Nat := [1, 2, 2, 1, 2, 1, 1, 10]
def baseStart_565713 : Nat := 118140960795 + 565713 * 2 ^ 59
def prefixEnd_565713 : Nat := 4983230072969 + 3 ^ 40 * 565713 * 2
def baseEnd_565713 : Nat := 86068942665792704884693

theorem tailTrace_565713 : CollatzResearch.WordTrace tailWord_565713 prefixEnd_565713 86068942665792704884693 := by
  unfold tailWord_565713
  simp only [CollatzResearch.WordTrace]
  refine ⟨20633248199525891933509793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13755498799683927955673195 20633248199525891933509793)
  ·
    refine ⟨15474936149644418950132345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20633248199525891933509793 15474936149644418950132345)
    ·
      refine ⟨11606202112233314212599259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15474936149644418950132345 11606202112233314212599259)
      ·
        refine ⟨17409303168349971318898889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11606202112233314212599259 17409303168349971318898889)
        ·
          refine ⟨13056977376262478489174167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17409303168349971318898889 13056977376262478489174167)
          ·
            refine ⟨19585466064393717733761251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13056977376262478489174167 19585466064393717733761251)
            ·
              refine ⟨29378199096590576600641877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19585466064393717733761251 29378199096590576600641877)
              ·
                refine ⟨86068942665792704884693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29378199096590576600641877 86068942665792704884693)
                ·
                  rfl

theorem cell20_565713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 10].length) (baseStart_565713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565713 prefixEnd_565713 := by exact prefixLift 565713
  have htrace : WordTrace (prefixWord ++ tailWord_565713) baseStart_565713 baseEnd_565713 := by
    simpa [prefixWord, tailWord_565713, baseEnd_565713] using wordTrace_append hprefix tailTrace_565713
  have hstable : (prefixWord ++ tailWord_565713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565713).length < 2 ^ (prefixWord ++ tailWord_565713).sum := by decide
  have hdescent : baseEnd_565713 < baseStart_565713 := by decide
  rcases family_descends (prefixWord ++ tailWord_565713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565737 : List Nat := [1, 2, 1, 1, 1, 2, 1, 8, 3]
def baseStart_565737 : Nat := 118140960795 + 565737 * 2 ^ 59
def prefixEnd_565737 : Nat := 4983230072969 + 3 ^ 40 * 565737 * 2
def baseEnd_565737 : Nat := 258217782251340697853981

theorem tailTrace_565737 : CollatzResearch.WordTrace tailWord_565737 prefixEnd_565737 258217782251340697853981 := by
  unfold tailWord_565737
  simp only [CollatzResearch.WordTrace]
  refine ⟨20634123551438944032383465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13756082367625962688255643 20634123551438944032383465)
  ·
    refine ⟨15475592663579208024287599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20634123551438944032383465 15475592663579208024287599)
    ·
      refine ⟨23213388995368812036431399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15475592663579208024287599 23213388995368812036431399)
      ·
        refine ⟨34820083493053218054647099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23213388995368812036431399 34820083493053218054647099)
        ·
          refine ⟨52230125239579827081970649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34820083493053218054647099 52230125239579827081970649)
          ·
            refine ⟨39172593929684870311477987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52230125239579827081970649 39172593929684870311477987)
            ·
              refine ⟨58758890894527305467216981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39172593929684870311477987 58758890894527305467216981)
              ·
                refine ⟨688580752670241860943949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 58758890894527305467216981 688580752670241860943949)
                ·
                  refine ⟨258217782251340697853981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 688580752670241860943949 258217782251340697853981)
                  ·
                    rfl

theorem cell20_565737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 3].length) (baseStart_565737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_565737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_565737 prefixEnd_565737 := by exact prefixLift 565737
  have htrace : WordTrace (prefixWord ++ tailWord_565737) baseStart_565737 baseEnd_565737 := by
    simpa [prefixWord, tailWord_565737, baseEnd_565737] using wordTrace_append hprefix tailTrace_565737
  have hstable : (prefixWord ++ tailWord_565737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565737).length < 2 ^ (prefixWord ++ tailWord_565737).sum := by decide
  have hdescent : baseEnd_565737 < baseStart_565737 := by decide
  rcases family_descends (prefixWord ++ tailWord_565737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
