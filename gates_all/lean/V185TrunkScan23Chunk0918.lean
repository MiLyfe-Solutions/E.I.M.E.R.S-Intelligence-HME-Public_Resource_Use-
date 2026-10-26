import V185TrunkScan23Chunk0917

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5432935 : List Nat := [1, 1, 5, 1, 1, 1, 4, 3, 2, 2, 2]
def baseStart_5432935 : Nat := 118140960795 + 5432935 * 2 ^ 59
def prefixEnd_5432935 : Nat := 4983230072969 + 3 ^ 40 * 5432935 * 2
def baseEnd_5432935 : Nat := 2789707019634806350526893

theorem tailTrace_5432935 : CollatzResearch.WordTrace tailWord_5432935 prefixEnd_5432935 2789707019634806350526893 := by
  unfold tailWord_5432935
  simp only [CollatzResearch.WordTrace]
  refine ⟨198155418572411841271492259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132103612381607894180994839 198155418572411841271492259)
  ·
    refine ⟨297233127858617761907238389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198155418572411841271492259 297233127858617761907238389)
    ·
      refine ⟨27865605736745415178803599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 297233127858617761907238389 27865605736745415178803599)
      ·
        refine ⟨41798408605118122768205399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27865605736745415178803599 41798408605118122768205399)
        ·
          refine ⟨62697612907677184152308099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41798408605118122768205399 62697612907677184152308099)
          ·
            refine ⟨94046419361515776228462149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62697612907677184152308099 94046419361515776228462149)
            ·
              refine ⟨17633703630284208042836653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94046419361515776228462149 17633703630284208042836653)
              ·
                refine ⟨6612638861356578016063745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17633703630284208042836653 6612638861356578016063745)
                ·
                  refine ⟨4959479146017433512047809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6612638861356578016063745 4959479146017433512047809)
                  ·
                    refine ⟨3719609359513075134035857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4959479146017433512047809 3719609359513075134035857)
                    ·
                      refine ⟨2789707019634806350526893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3719609359513075134035857 2789707019634806350526893)
                      ·
                        rfl

theorem cell23_5432935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_5432935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432935 prefixEnd_5432935 := by exact prefixLift 5432935
  have htrace : WordTrace (prefixWord ++ tailWord_5432935) baseStart_5432935 baseEnd_5432935 := by
    simpa [prefixWord, tailWord_5432935, baseEnd_5432935] using wordTrace_append hprefix tailTrace_5432935
  have hstable : (prefixWord ++ tailWord_5432935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432935).length < 2 ^ (prefixWord ++ tailWord_5432935).sum := by decide
  have hdescent : baseEnd_5432935 < baseStart_5432935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433011 : List Nat := [1, 1, 1, 2, 3, 3, 1, 3, 1, 4, 3]
def baseStart_5433011 : Nat := 118140960795 + 5433011 * 2 ^ 59
def prefixEnd_5433011 : Nat := 4983230072969 + 3 ^ 40 * 5433011 * 2
def baseEnd_5433011 : Nat := 2789746044164548053176543

theorem tailTrace_5433011 : CollatzResearch.WordTrace tailWord_5433011 prefixEnd_5433011 2789746044164548053176543 := by
  unfold tailWord_5433011
  simp only [CollatzResearch.WordTrace]
  refine ⟨198158190520136506251258887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132105460346757670834172591 198158190520136506251258887)
  ·
    refine ⟨297237285780204759376888331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198158190520136506251258887 297237285780204759376888331)
    ·
      refine ⟨445855928670307139065332497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297237285780204759376888331 445855928670307139065332497)
      ·
        refine ⟨334391946502730354298999373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 445855928670307139065332497 334391946502730354298999373)
        ·
          refine ⟨125396979938523882862124765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 334391946502730354298999373 125396979938523882862124765)
          ·
            refine ⟨47023867476946456073296787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125396979938523882862124765 47023867476946456073296787)
            ·
              refine ⟨70535801215419684109945181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47023867476946456073296787 70535801215419684109945181)
              ·
                refine ⟨26450925455782381541229443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70535801215419684109945181 26450925455782381541229443)
                ·
                  refine ⟨39676388183673572311844165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26450925455782381541229443 39676388183673572311844165)
                  ·
                    refine ⟨7439322784438794808470781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39676388183673572311844165 7439322784438794808470781)
                    ·
                      refine ⟨2789746044164548053176543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7439322784438794808470781 2789746044164548053176543)
                      ·
                        rfl

theorem cell23_5433011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 4, 3].length) (baseStart_5433011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433011 prefixEnd_5433011 := by exact prefixLift 5433011
  have htrace : WordTrace (prefixWord ++ tailWord_5433011) baseStart_5433011 baseEnd_5433011 := by
    simpa [prefixWord, tailWord_5433011, baseEnd_5433011] using wordTrace_append hprefix tailTrace_5433011
  have hstable : (prefixWord ++ tailWord_5433011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433011).length < 2 ^ (prefixWord ++ tailWord_5433011).sum := by decide
  have hdescent : baseEnd_5433011 < baseStart_5433011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433026 : List Nat := [3, 5, 1, 2, 1, 1, 3, 2, 5]
def baseStart_5433026 : Nat := 118140960795 + 5433026 * 2 ^ 59
def prefixEnd_5433026 : Nat := 4983230072969 + 3 ^ 40 * 5433026 * 2
def baseEnd_5433026 : Nat := 309972638486040610498775

theorem tailTrace_5433026 : CollatzResearch.WordTrace tailWord_5433026 prefixEnd_5433026 309972638486040610498775 := by
  unfold tailWord_5433026
  simp only [CollatzResearch.WordTrace]
  refine ⟨49539684403770540953263733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132105825076721442542036621 49539684403770540953263733)
  ·
    refine ⟨4644345412853488214368475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49539684403770540953263733 4644345412853488214368475)
    ·
      refine ⟨6966518119280232321552713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4644345412853488214368475 6966518119280232321552713)
      ·
        refine ⟨5224888589460174241164535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6966518119280232321552713 5224888589460174241164535)
        ·
          refine ⟨7837332884190261361746803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5224888589460174241164535 7837332884190261361746803)
          ·
            refine ⟨11755999326285392042620205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7837332884190261361746803 11755999326285392042620205)
            ·
              refine ⟨4408499747357022015982577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11755999326285392042620205 4408499747357022015982577)
              ·
                refine ⟨3306374810517766511986933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4408499747357022015982577 3306374810517766511986933)
                ·
                  refine ⟨309972638486040610498775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3306374810517766511986933 309972638486040610498775)
                  ·
                    rfl

theorem cell23_5433026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_5433026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433026 prefixEnd_5433026 := by exact prefixLift 5433026
  have htrace : WordTrace (prefixWord ++ tailWord_5433026) baseStart_5433026 baseEnd_5433026 := by
    simpa [prefixWord, tailWord_5433026, baseEnd_5433026] using wordTrace_append hprefix tailTrace_5433026
  have hstable : (prefixWord ++ tailWord_5433026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433026).length < 2 ^ (prefixWord ++ tailWord_5433026).sum := by decide
  have hdescent : baseEnd_5433026 < baseStart_5433026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433031 : List Nat := [1, 1, 4, 1, 1, 1, 4, 4, 6]
def baseStart_5433031 : Nat := 118140960795 + 5433031 * 2 ^ 59
def prefixEnd_5433031 : Nat := 4983230072969 + 3 ^ 40 * 5433031 * 2
def baseEnd_5433031 : Nat := 309972923753070886102939

theorem tailTrace_5433031 : CollatzResearch.WordTrace tailWord_5433031 prefixEnd_5433031 309972923753070886102939 := by
  unfold tailWord_5433031
  simp only [CollatzResearch.WordTrace]
  refine ⟨198158919980064049666986947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132105946653376033111324631 198158919980064049666986947)
  ·
    refine ⟨297238379970096074500480421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198158919980064049666986947 297238379970096074500480421)
    ·
      refine ⟨55732196244393013968840079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 297238379970096074500480421 55732196244393013968840079)
      ·
        refine ⟨83598294366589520953260119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55732196244393013968840079 83598294366589520953260119)
        ·
          refine ⟨125397441549884281429890179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83598294366589520953260119 125397441549884281429890179)
          ·
            refine ⟨188096162324826422144835269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125397441549884281429890179 188096162324826422144835269)
            ·
              refine ⟨35268030435904954152156613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 188096162324826422144835269 35268030435904954152156613)
              ·
                refine ⟨6612755706732178903529365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35268030435904954152156613 6612755706732178903529365)
                ·
                  refine ⟨309972923753070886102939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6612755706732178903529365 309972923753070886102939)
                  ·
                    rfl

theorem cell23_5433031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 6].length) (baseStart_5433031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433031 prefixEnd_5433031 := by exact prefixLift 5433031
  have htrace : WordTrace (prefixWord ++ tailWord_5433031) baseStart_5433031 baseEnd_5433031 := by
    simpa [prefixWord, tailWord_5433031, baseEnd_5433031] using wordTrace_append hprefix tailTrace_5433031
  have hstable : (prefixWord ++ tailWord_5433031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433031).length < 2 ^ (prefixWord ++ tailWord_5433031).sum := by decide
  have hdescent : baseEnd_5433031 < baseStart_5433031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433068 : List Nat := [2, 2, 1, 1, 2, 2, 2, 3, 1, 5, 2]
def baseStart_5433068 : Nat := 118140960795 + 5433068 * 2 ^ 59
def prefixEnd_5433068 : Nat := 4983230072969 + 3 ^ 40 * 5433068 * 2
def baseEnd_5433068 : Nat := 2789775312561854330163781

theorem tailTrace_5433068 : CollatzResearch.WordTrace tailWord_5433068 prefixEnd_5433068 2789775312561854330163781 := by
  unfold tailWord_5433068
  simp only [CollatzResearch.WordTrace]
  refine ⟨99080134740465002493041929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132106846320620003324055905 99080134740465002493041929)
  ·
    refine ⟨74310101055348751869781447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99080134740465002493041929 74310101055348751869781447)
    ·
      refine ⟨111465151583023127804672171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74310101055348751869781447 111465151583023127804672171)
      ·
        refine ⟨167197727374534691707008257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111465151583023127804672171 167197727374534691707008257)
        ·
          refine ⟨125398295530901018780256193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167197727374534691707008257 125398295530901018780256193)
          ·
            refine ⟨94048721648175764085192145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125398295530901018780256193 94048721648175764085192145)
            ·
              refine ⟨70536541236131823063894109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94048721648175764085192145 70536541236131823063894109)
              ·
                refine ⟨26451202963549433648960291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70536541236131823063894109 26451202963549433648960291)
                ·
                  refine ⟨39676804445324150473440437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26451202963549433648960291 39676804445324150473440437)
                  ·
                    refine ⟨3719700416749139106885041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39676804445324150473440437 3719700416749139106885041)
                    ·
                      refine ⟨2789775312561854330163781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3719700416749139106885041 2789775312561854330163781)
                      ·
                        rfl

theorem cell23_5433068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 5, 2].length) (baseStart_5433068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433068 prefixEnd_5433068 := by exact prefixLift 5433068
  have htrace : WordTrace (prefixWord ++ tailWord_5433068) baseStart_5433068 baseEnd_5433068 := by
    simpa [prefixWord, tailWord_5433068, baseEnd_5433068] using wordTrace_append hprefix tailTrace_5433068
  have hstable : (prefixWord ++ tailWord_5433068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433068).length < 2 ^ (prefixWord ++ tailWord_5433068).sum := by decide
  have hdescent : baseEnd_5433068 < baseStart_5433068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433086 : List Nat := [4, 2, 2, 1, 3, 2, 2, 2, 1, 4]
def baseStart_5433086 : Nat := 118140960795 + 5433086 * 2 ^ 59
def prefixEnd_5433086 : Nat := 4983230072969 + 3 ^ 40 * 5433086 * 2
def baseEnd_5433086 : Nat := 929928185071211753246233

theorem tailTrace_5433086 : CollatzResearch.WordTrace tailWord_5433086 prefixEnd_5433086 929928185071211753246233 := by
  unfold tailWord_5433086
  simp only [CollatzResearch.WordTrace]
  refine ⟨24770115749358099257529889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132107283996576529373492741 24770115749358099257529889)
  ·
    refine ⟨18577586812018574443147417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24770115749358099257529889 18577586812018574443147417)
    ·
      refine ⟨13933190109013930832360563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18577586812018574443147417 13933190109013930832360563)
      ·
        refine ⟨20899785163520896248540845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13933190109013930832360563 20899785163520896248540845)
        ·
          refine ⟨7837419436320336093202817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20899785163520896248540845 7837419436320336093202817)
          ·
            refine ⟨5878064577240252069902113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7837419436320336093202817 5878064577240252069902113)
            ·
              refine ⟨4408548432930189052426585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5878064577240252069902113 4408548432930189052426585)
              ·
                refine ⟨3306411324697641789319939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4408548432930189052426585 3306411324697641789319939)
                ·
                  refine ⟨4959616987046462683979909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3306411324697641789319939 4959616987046462683979909)
                  ·
                    refine ⟨929928185071211753246233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4959616987046462683979909 929928185071211753246233)
                    ·
                      rfl

theorem cell23_5433086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_5433086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433086 prefixEnd_5433086 := by exact prefixLift 5433086
  have htrace : WordTrace (prefixWord ++ tailWord_5433086) baseStart_5433086 baseEnd_5433086 := by
    simpa [prefixWord, tailWord_5433086, baseEnd_5433086] using wordTrace_append hprefix tailTrace_5433086
  have hstable : (prefixWord ++ tailWord_5433086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433086).length < 2 ^ (prefixWord ++ tailWord_5433086).sum := by decide
  have hdescent : baseEnd_5433086 < baseStart_5433086 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433098 : List Nat := [3, 1, 2, 2, 1, 3, 1, 2, 3, 1, 4]
def baseStart_5433098 : Nat := 118140960795 + 5433098 * 2 ^ 59
def prefixEnd_5433098 : Nat := 4983230072969 + 3 ^ 40 * 5433098 * 2
def baseEnd_5433098 : Nat := 2789790716981489212788643

theorem tailTrace_5433098 : CollatzResearch.WordTrace tailWord_5433098 prefixEnd_5433098 2789790716981489212788643 := by
  unfold tailWord_5433098
  simp only [CollatzResearch.WordTrace]
  refine ⟨49540340917705330027418987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132107575780547546739783965 49540340917705330027418987)
  ·
    refine ⟨74310511376557995041128481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49540340917705330027418987 74310511376557995041128481)
    ·
      refine ⟨55732883532418496280846361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74310511376557995041128481 55732883532418496280846361)
      ·
        refine ⟨41799662649313872210634771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55732883532418496280846361 41799662649313872210634771)
        ·
          refine ⟨62699493973970808315952157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41799662649313872210634771 62699493973970808315952157)
          ·
            refine ⟨23512310240239053118482059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62699493973970808315952157 23512310240239053118482059)
            ·
              refine ⟨35268465360358579677723089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23512310240239053118482059 35268465360358579677723089)
              ·
                refine ⟨26451349020268934758292317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35268465360358579677723089 26451349020268934758292317)
                ·
                  refine ⟨9919255882600850534359619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26451349020268934758292317 9919255882600850534359619)
                  ·
                    refine ⟨14878883823901275801539429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9919255882600850534359619 14878883823901275801539429)
                    ·
                      refine ⟨2789790716981489212788643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14878883823901275801539429 2789790716981489212788643)
                      ·
                        rfl

theorem cell23_5433098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_5433098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433098 prefixEnd_5433098 := by exact prefixLift 5433098
  have htrace : WordTrace (prefixWord ++ tailWord_5433098) baseStart_5433098 baseEnd_5433098 := by
    simpa [prefixWord, tailWord_5433098, baseEnd_5433098] using wordTrace_append hprefix tailTrace_5433098
  have hstable : (prefixWord ++ tailWord_5433098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433098).length < 2 ^ (prefixWord ++ tailWord_5433098).sum := by decide
  have hdescent : baseEnd_5433098 < baseStart_5433098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433115 : List Nat := [1, 1, 1, 1, 1, 1, 4, 6, 3, 2, 2]
def baseStart_5433115 : Nat := 118140960795 + 5433115 * 2 ^ 59
def prefixEnd_5433115 : Nat := 4983230072969 + 3 ^ 40 * 5433115 * 2
def baseEnd_5433115 : Nat := 2789799446152615646276065

theorem tailTrace_5433115 : CollatzResearch.WordTrace tailWord_5433115 prefixEnd_5433115 2789799446152615646276065 := by
  unfold tailWord_5433115
  simp only [CollatzResearch.WordTrace]
  refine ⟨198161983711759732013044799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132107989141173154675363199 198161983711759732013044799)
  ·
    refine ⟨297242975567639598019567199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198161983711759732013044799 297242975567639598019567199)
    ·
      refine ⟨445864463351459397029350799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297242975567639598019567199 445864463351459397029350799)
      ·
        refine ⟨668796695027189095544026199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 445864463351459397029350799 668796695027189095544026199)
        ·
          refine ⟨1003195042540783643316039299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 668796695027189095544026199 1003195042540783643316039299)
          ·
            refine ⟨1504792563811175464974058949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1003195042540783643316039299 1504792563811175464974058949)
            ·
              refine ⟨282148605714595399682636053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1504792563811175464974058949 282148605714595399682636053)
              ·
                refine ⟨13225715892871659360123565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 282148605714595399682636053 13225715892871659360123565)
                ·
                  refine ⟨4959643459826872260046337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13225715892871659360123565 4959643459826872260046337)
                  ·
                    refine ⟨3719732594870154195034753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4959643459826872260046337 3719732594870154195034753)
                    ·
                      refine ⟨2789799446152615646276065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3719732594870154195034753 2789799446152615646276065)
                      ·
                        rfl

theorem cell23_5433115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 3, 2, 2].length) (baseStart_5433115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433115 prefixEnd_5433115 := by exact prefixLift 5433115
  have htrace : WordTrace (prefixWord ++ tailWord_5433115) baseStart_5433115 baseEnd_5433115 := by
    simpa [prefixWord, tailWord_5433115, baseEnd_5433115] using wordTrace_append hprefix tailTrace_5433115
  have hstable : (prefixWord ++ tailWord_5433115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433115).length < 2 ^ (prefixWord ++ tailWord_5433115).sum := by decide
  have hdescent : baseEnd_5433115 < baseStart_5433115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433132 : List Nat := [2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 4]
def baseStart_5433132 : Nat := 118140960795 + 5433132 * 2 ^ 59
def prefixEnd_5433132 : Nat := 4983230072969 + 3 ^ 40 * 5433132 * 2
def baseEnd_5433132 : Nat := 2789808175323742079763487

theorem tailTrace_5433132 : CollatzResearch.WordTrace tailWord_5433132 prefixEnd_5433132 2789808175323742079763487 := by
  unfold tailWord_5433132
  simp only [CollatzResearch.WordTrace]
  refine ⟨99081301876349071958206825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132108402501798762610942433 99081301876349071958206825)
  ·
    refine ⟨74310976407261803968655119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99081301876349071958206825 74310976407261803968655119)
    ·
      refine ⟨111466464610892705952982679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74310976407261803968655119 111466464610892705952982679)
      ·
        refine ⟨167199696916339058929474019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111466464610892705952982679 167199696916339058929474019)
        ·
          refine ⟨250799545374508588394211029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167199696916339058929474019 250799545374508588394211029)
          ·
            refine ⟨5878114344715045040489321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 250799545374508588394211029 5878114344715045040489321)
            ·
              refine ⟨4408585758536283780366991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5878114344715045040489321 4408585758536283780366991)
              ·
                refine ⟨6612878637804425670550487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4408585758536283780366991 6612878637804425670550487)
                ·
                  refine ⟨9919317956706638505825731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6612878637804425670550487 9919317956706638505825731)
                  ·
                    refine ⟨14878976935059957758738597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9919317956706638505825731 14878976935059957758738597)
                    ·
                      refine ⟨2789808175323742079763487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14878976935059957758738597 2789808175323742079763487)
                      ·
                        rfl

theorem cell23_5433132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 4].length) (baseStart_5433132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433132 prefixEnd_5433132 := by exact prefixLift 5433132
  have htrace : WordTrace (prefixWord ++ tailWord_5433132) baseStart_5433132 baseEnd_5433132 := by
    simpa [prefixWord, tailWord_5433132, baseEnd_5433132] using wordTrace_append hprefix tailTrace_5433132
  have hstable : (prefixWord ++ tailWord_5433132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433132).length < 2 ^ (prefixWord ++ tailWord_5433132).sum := by decide
  have hdescent : baseEnd_5433132 < baseStart_5433132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433142 : List Nat := [5, 1, 2, 2, 1, 2, 1, 1, 4, 4]
def baseStart_5433142 : Nat := 118140960795 + 5433142 * 2 ^ 59
def prefixEnd_5433142 : Nat := 4983230072969 + 3 ^ 40 * 5433142 * 2
def baseEnd_5433142 : Nat := 929937770043429013546147

theorem tailTrace_5433142 : CollatzResearch.WordTrace tailWord_5433142 prefixEnd_5433142 929937770043429013546147 := by
  unfold tailWord_5433142
  simp only [CollatzResearch.WordTrace]
  refine ⟨12385185530166369726517355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132108645655107943749518453 12385185530166369726517355)
  ·
    refine ⟨18577778295249554589776033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12385185530166369726517355 18577778295249554589776033)
    ·
      refine ⟨13933333721437165942332025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18577778295249554589776033 13933333721437165942332025)
      ·
        refine ⟨10450000291077874456749019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13933333721437165942332025 10450000291077874456749019)
        ·
          refine ⟨15675000436616811685123529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10450000291077874456749019 15675000436616811685123529)
          ·
            refine ⟨11756250327462608763842647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15675000436616811685123529 11756250327462608763842647)
            ·
              refine ⟨17634375491193913145763971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11756250327462608763842647 17634375491193913145763971)
              ·
                refine ⟨26451563236790869718645957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17634375491193913145763971 26451563236790869718645957)
                ·
                  refine ⟨4959668106898288072246117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26451563236790869718645957 4959668106898288072246117)
                  ·
                    refine ⟨929937770043429013546147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4959668106898288072246117 929937770043429013546147)
                    ·
                      rfl

theorem cell23_5433142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_5433142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433142 prefixEnd_5433142 := by exact prefixLift 5433142
  have htrace : WordTrace (prefixWord ++ tailWord_5433142) baseStart_5433142 baseEnd_5433142 := by
    simpa [prefixWord, tailWord_5433142, baseEnd_5433142] using wordTrace_append hprefix tailTrace_5433142
  have hstable : (prefixWord ++ tailWord_5433142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433142).length < 2 ^ (prefixWord ++ tailWord_5433142).sum := by decide
  have hdescent : baseEnd_5433142 < baseStart_5433142 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433148 : List Nat := [2, 2, 2, 2, 1, 1, 2, 2, 3, 3, 3]
def baseStart_5433148 : Nat := 118140960795 + 5433148 * 2 ^ 59
def prefixEnd_5433148 : Nat := 4983230072969 + 3 ^ 40 * 5433148 * 2
def baseEnd_5433148 : Nat := 2789816391014214017163413

theorem tailTrace_5433148 : CollatzResearch.WordTrace tailWord_5433148 prefixEnd_5433148 2789816391014214017163413 := by
  unfold tailWord_5433148
  simp only [CollatzResearch.WordTrace]
  refine ⟨99081593660320089324498049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132108791547093452432664065 99081593660320089324498049)
  ·
    refine ⟨74311195245240066993373537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99081593660320089324498049 74311195245240066993373537)
    ·
      refine ⟨55733396433930050245030153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74311195245240066993373537 55733396433930050245030153)
      ·
        refine ⟨41800047325447537683772615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55733396433930050245030153 41800047325447537683772615)
        ·
          refine ⟨62700070988171306525658923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41800047325447537683772615 62700070988171306525658923)
          ·
            refine ⟨94050106482256959788488385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62700070988171306525658923 94050106482256959788488385)
            ·
              refine ⟨70537579861692719841366289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94050106482256959788488385 70537579861692719841366289)
              ·
                refine ⟨52903184896269539881024717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70537579861692719841366289 52903184896269539881024717)
                ·
                  refine ⟨19838694336101077455384269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52903184896269539881024717 19838694336101077455384269)
                  ·
                    refine ⟨7439510376037904045769101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19838694336101077455384269 7439510376037904045769101)
                    ·
                      refine ⟨2789816391014214017163413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7439510376037904045769101 2789816391014214017163413)
                      ·
                        rfl

theorem cell23_5433148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_5433148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433148 prefixEnd_5433148 := by exact prefixLift 5433148
  have htrace : WordTrace (prefixWord ++ tailWord_5433148) baseStart_5433148 baseEnd_5433148 := by
    simpa [prefixWord, tailWord_5433148, baseEnd_5433148] using wordTrace_append hprefix tailTrace_5433148
  have hstable : (prefixWord ++ tailWord_5433148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433148).length < 2 ^ (prefixWord ++ tailWord_5433148).sum := by decide
  have hdescent : baseEnd_5433148 < baseStart_5433148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433149 : List Nat := [1, 4, 1, 4, 1, 2, 2, 1, 3, 2, 2]
def baseStart_5433149 : Nat := 118140960795 + 5433149 * 2 ^ 59
def prefixEnd_5433149 : Nat := 4983230072969 + 3 ^ 40 * 5433149 * 2
def baseEnd_5433149 : Nat := 2789816904494868513250909

theorem tailTrace_5433149 : CollatzResearch.WordTrace tailWord_5433149 prefixEnd_5433149 2789816904494868513250909 := by
  unfold tailWord_5433149
  simp only [CollatzResearch.WordTrace]
  refine ⟨198163223793636555819782501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132108815862424370546521667 198163223793636555819782501)
  ·
    refine ⟨37155604461306854216209219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198163223793636555819782501 37155604461306854216209219)
    ·
      refine ⟨55733406691960281324313829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37155604461306854216209219 55733406691960281324313829)
      ·
        refine ⟨10450013754742552748308843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55733406691960281324313829 10450013754742552748308843)
        ·
          refine ⟨15675020632113829122463265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10450013754742552748308843 15675020632113829122463265)
          ·
            refine ⟨11756265474085371841847449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15675020632113829122463265 11756265474085371841847449)
            ·
              refine ⟨8817199105564028881385587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11756265474085371841847449 8817199105564028881385587)
              ·
                refine ⟨13225798658346043322078381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8817199105564028881385587 13225798658346043322078381)
                ·
                  refine ⟨4959674496879766245779393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13225798658346043322078381 4959674496879766245779393)
                  ·
                    refine ⟨3719755872659824684334545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4959674496879766245779393 3719755872659824684334545)
                    ·
                      refine ⟨2789816904494868513250909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3719755872659824684334545 2789816904494868513250909)
                      ·
                        rfl

theorem cell23_5433149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_5433149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433149 prefixEnd_5433149 := by exact prefixLift 5433149
  have htrace : WordTrace (prefixWord ++ tailWord_5433149) baseStart_5433149 baseEnd_5433149 := by
    simpa [prefixWord, tailWord_5433149, baseEnd_5433149] using wordTrace_append hprefix tailTrace_5433149
  have hstable : (prefixWord ++ tailWord_5433149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433149).length < 2 ^ (prefixWord ++ tailWord_5433149).sum := by decide
  have hdescent : baseEnd_5433149 < baseStart_5433149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433192 : List Nat := [2, 1, 4, 2, 1, 1, 1, 5, 1, 3, 2]
def baseStart_5433192 : Nat := 118140960795 + 5433192 * 2 ^ 59
def prefixEnd_5433192 : Nat := 4983230072969 + 3 ^ 40 * 5433192 * 2
def baseEnd_5433192 : Nat := 2789838984163011845013211

theorem tailTrace_5433192 : CollatzResearch.WordTrace tailWord_5433192 prefixEnd_5433192 2789838984163011845013211 := by
  unfold tailWord_5433192
  simp only [CollatzResearch.WordTrace]
  refine ⟨99082396066240387081798915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132109861421653849442398553 99082396066240387081798915)
  ·
    refine ⟨148623594099360580622698373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99082396066240387081798915 148623594099360580622698373)
    ·
      refine ⟨27866923893630108866755945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148623594099360580622698373 27866923893630108866755945)
      ·
        refine ⟨20900192920222581650066959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27866923893630108866755945 20900192920222581650066959)
        ·
          refine ⟨31350289380333872475100439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20900192920222581650066959 31350289380333872475100439)
          ·
            refine ⟨47025434070500808712650659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31350289380333872475100439 47025434070500808712650659)
            ·
              refine ⟨70538151105751213068975989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47025434070500808712650659 70538151105751213068975989)
              ·
                refine ⟨6612951666164176225216499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70538151105751213068975989 6612951666164176225216499)
                ·
                  refine ⟨9919427499246264337824749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6612951666164176225216499 9919427499246264337824749)
                  ·
                    refine ⟨3719785312217349126684281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9919427499246264337824749 3719785312217349126684281)
                    ·
                      refine ⟨2789838984163011845013211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3719785312217349126684281 2789838984163011845013211)
                      ·
                        rfl

theorem cell23_5433192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_5433192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433192 prefixEnd_5433192 := by exact prefixLift 5433192
  have htrace : WordTrace (prefixWord ++ tailWord_5433192) baseStart_5433192 baseEnd_5433192 := by
    simpa [prefixWord, tailWord_5433192, baseEnd_5433192] using wordTrace_append hprefix tailTrace_5433192
  have hstable : (prefixWord ++ tailWord_5433192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433192).length < 2 ^ (prefixWord ++ tailWord_5433192).sum := by decide
  have hdescent : baseEnd_5433192 < baseStart_5433192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433226 : List Nat := [3, 1, 2, 4, 2, 2, 1, 2, 1, 3, 2]
def baseStart_5433226 : Nat := 118140960795 + 5433226 * 2 ^ 59
def prefixEnd_5433226 : Nat := 4983230072969 + 3 ^ 40 * 5433226 * 2
def baseEnd_5433226 : Nat := 2789856442505264711988055

theorem tailTrace_5433226 : CollatzResearch.WordTrace tailWord_5433226 prefixEnd_5433226 2789856442505264711988055 := by
  unfold tailWord_5433226
  simp only [CollatzResearch.WordTrace]
  refine ⟨49541508053589399492583883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132110688142905065313557021 49541508053589399492583883)
  ·
    refine ⟨74312262080384099238875825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49541508053589399492583883 74312262080384099238875825)
    ·
      refine ⟨55734196560288074429156869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74312262080384099238875825 55734196560288074429156869)
      ·
        refine ⟨10450161855054013955466913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55734196560288074429156869 10450161855054013955466913)
        ·
          refine ⟨7837621391290510466600185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10450161855054013955466913 7837621391290510466600185)
          ·
            refine ⟨5878216043467882849950139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7837621391290510466600185 5878216043467882849950139)
            ·
              refine ⟨8817324065201824274925209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5878216043467882849950139 8817324065201824274925209)
              ·
                refine ⟨6612993048901368206193907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8817324065201824274925209 6612993048901368206193907)
                ·
                  refine ⟨9919489573352052309290861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6612993048901368206193907 9919489573352052309290861)
                  ·
                    refine ⟨3719808590007019615984073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9919489573352052309290861 3719808590007019615984073)
                    ·
                      refine ⟨2789856442505264711988055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3719808590007019615984073 2789856442505264711988055)
                      ·
                        rfl

theorem cell23_5433226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_5433226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433226 prefixEnd_5433226 := by exact prefixLift 5433226
  have htrace : WordTrace (prefixWord ++ tailWord_5433226) baseStart_5433226 baseEnd_5433226 := by
    simpa [prefixWord, tailWord_5433226, baseEnd_5433226] using wordTrace_append hprefix tailTrace_5433226
  have hstable : (prefixWord ++ tailWord_5433226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433226).length < 2 ^ (prefixWord ++ tailWord_5433226).sum := by decide
  have hdescent : baseEnd_5433226 < baseStart_5433226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433292 : List Nat := [2, 2, 1, 4, 1, 4, 1, 1, 2, 5]
def baseStart_5433292 : Nat := 118140960795 + 5433292 * 2 ^ 59
def prefixEnd_5433292 : Nat := 4983230072969 + 3 ^ 40 * 5433292 * 2
def baseEnd_5433292 : Nat := 929963444076153817920917

theorem tailTrace_5433292 : CollatzResearch.WordTrace tailWord_5433292 prefixEnd_5433292 929963444076153817920917 := by
  unfold tailWord_5433292
  simp only [CollatzResearch.WordTrace]
  refine ⟨99084219716059245621119065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132112292954745660828158753 99084219716059245621119065)
  ·
    refine ⟨74313164787044434215839299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99084219716059245621119065 74313164787044434215839299)
    ·
      refine ⟨111469747180566651323758949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74313164787044434215839299 111469747180566651323758949)
      ·
        refine ⟨20900577596356247123204803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111469747180566651323758949 20900577596356247123204803)
        ·
          refine ⟨31350866394534370684807205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20900577596356247123204803 31350866394534370684807205)
          ·
            refine ⟨5878287448975194503401351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31350866394534370684807205 5878287448975194503401351)
            ·
              refine ⟨8817431173462791755102027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5878287448975194503401351 8817431173462791755102027)
              ·
                refine ⟨13226146760194187632653041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8817431173462791755102027 13226146760194187632653041)
                ·
                  refine ⟨9919610070145640724489781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13226146760194187632653041 9919610070145640724489781)
                  ·
                    refine ⟨929963444076153817920917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9919610070145640724489781 929963444076153817920917)
                    ·
                      rfl

theorem cell23_5433292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 2, 5].length) (baseStart_5433292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433292 prefixEnd_5433292 := by exact prefixLift 5433292
  have htrace : WordTrace (prefixWord ++ tailWord_5433292) baseStart_5433292 baseEnd_5433292 := by
    simpa [prefixWord, tailWord_5433292, baseEnd_5433292] using wordTrace_append hprefix tailTrace_5433292
  have hstable : (prefixWord ++ tailWord_5433292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433292).length < 2 ^ (prefixWord ++ tailWord_5433292).sum := by decide
  have hdescent : baseEnd_5433292 < baseStart_5433292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433295 : List Nat := [1, 1, 2, 1, 1, 5, 1, 2, 1, 6, 2]
def baseStart_5433295 : Nat := 118140960795 + 5433295 * 2 ^ 59
def prefixEnd_5433295 : Nat := 4983230072969 + 3 ^ 40 * 5433295 * 2
def baseEnd_5433295 : Nat := 2789891872670424942025237

theorem tailTrace_5433295 : CollatzResearch.WordTrace tailWord_5433295 prefixEnd_5433295 2789891872670424942025237 := by
  unfold tailWord_5433295
  simp only [CollatzResearch.WordTrace]
  refine ⟨198168548851107622754597339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132112365900738415169731559 198168548851107622754597339)
  ·
    refine ⟨297252823276661434131896009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198168548851107622754597339 297252823276661434131896009)
    ·
      refine ⟨222939617457496075598922007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297252823276661434131896009 222939617457496075598922007)
      ·
        refine ⟨334409426186244113398383011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222939617457496075598922007 334409426186244113398383011)
        ·
          refine ⟨501614139279366170097574517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334409426186244113398383011 501614139279366170097574517)
          ·
            refine ⟨47026325557440578446647611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 501614139279366170097574517 47026325557440578446647611)
            ·
              refine ⟨70539488336160867669971417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47026325557440578446647611 70539488336160867669971417)
              ·
                refine ⟨52904616252120650752478563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70539488336160867669971417 52904616252120650752478563)
                ·
                  refine ⟨79356924378180976128717845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52904616252120650752478563 79356924378180976128717845)
                  ·
                    refine ⟨3719855830227233256033649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79356924378180976128717845 3719855830227233256033649)
                    ·
                      refine ⟨2789891872670424942025237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3719855830227233256033649 2789891872670424942025237)
                      ·
                        rfl

theorem cell23_5433295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 6, 2].length) (baseStart_5433295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433295 prefixEnd_5433295 := by exact prefixLift 5433295
  have htrace : WordTrace (prefixWord ++ tailWord_5433295) baseStart_5433295 baseEnd_5433295 := by
    simpa [prefixWord, tailWord_5433295, baseEnd_5433295] using wordTrace_append hprefix tailTrace_5433295
  have hstable : (prefixWord ++ tailWord_5433295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433295).length < 2 ^ (prefixWord ++ tailWord_5433295).sum := by decide
  have hdescent : baseEnd_5433295 < baseStart_5433295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433322 : List Nat := [3, 1, 3, 1, 2, 1, 4, 1, 3, 4]
def baseStart_5433322 : Nat := 118140960795 + 5433322 * 2 ^ 59
def prefixEnd_5433322 : Nat := 4983230072969 + 3 ^ 40 * 5433322 * 2
def baseEnd_5433322 : Nat := 929968578882698778795871

theorem tailTrace_5433322 : CollatzResearch.WordTrace tailWord_5433322 prefixEnd_5433322 929968578882698778795871 := by
  unfold tailWord_5433322
  simp only [CollatzResearch.WordTrace]
  refine ⟨49542383405502451591457555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132113022414673204243886813 49542383405502451591457555)
  ·
    refine ⟨74313575108253677387186333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49542383405502451591457555 74313575108253677387186333)
    ·
      refine ⟨27867590665595129020194875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74313575108253677387186333 27867590665595129020194875)
      ·
        refine ⟨41801385998392693530292313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27867590665595129020194875 41801385998392693530292313)
        ·
          refine ⟨31351039498794520147719235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41801385998392693530292313 31351039498794520147719235)
          ·
            refine ⟨47026559248191780221578853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31351039498794520147719235 47026559248191780221578853)
            ·
              refine ⟨8817479859035958791546035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47026559248191780221578853 8817479859035958791546035)
              ·
                refine ⟨13226219788553938187319053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8817479859035958791546035 13226219788553938187319053)
                ·
                  refine ⟨4959832420707726820244645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13226219788553938187319053 4959832420707726820244645)
                  ·
                    refine ⟨929968578882698778795871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4959832420707726820244645 929968578882698778795871)
                    ·
                      rfl

theorem cell23_5433322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_5433322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433322 prefixEnd_5433322 := by exact prefixLift 5433322
  have htrace : WordTrace (prefixWord ++ tailWord_5433322) baseStart_5433322 baseEnd_5433322 := by
    simpa [prefixWord, tailWord_5433322, baseEnd_5433322] using wordTrace_append hprefix tailTrace_5433322
  have hstable : (prefixWord ++ tailWord_5433322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433322).length < 2 ^ (prefixWord ++ tailWord_5433322).sum := by decide
  have hdescent : baseEnd_5433322 < baseStart_5433322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433345 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 2, 5, 3]
def baseStart_5433345 : Nat := 118140960795 + 5433345 * 2 ^ 59
def prefixEnd_5433345 : Nat := 4983230072969 + 3 ^ 40 * 5433345 * 2
def baseEnd_5433345 : Nat := 2789917546703149746400007

theorem tailTrace_5433345 : CollatzResearch.WordTrace tailWord_5433345 prefixEnd_5433345 2789917546703149746400007 := by
  unfold tailWord_5433345
  simp only [CollatzResearch.WordTrace]
  refine ⟨198170372500926481293917489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132113581667284320862611659 198170372500926481293917489)
  ·
    refine ⟨148627779375694860970438117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198170372500926481293917489 148627779375694860970438117)
    ·
      refine ⟨27867708632942786431957147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148627779375694860970438117 27867708632942786431957147)
      ·
        refine ⟨41801562949414179647935721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27867708632942786431957147 41801562949414179647935721)
        ·
          refine ⟨31351172212060634735951791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41801562949414179647935721 31351172212060634735951791)
          ·
            refine ⟨47026758318090952103927687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31351172212060634735951791 47026758318090952103927687)
            ·
              refine ⟨70540137477136428155891531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47026758318090952103927687 70540137477136428155891531)
              ·
                refine ⟨105810206215704642233837297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70540137477136428155891531 105810206215704642233837297)
                ·
                  refine ⟨79357654661778481675377973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105810206215704642233837297 79357654661778481675377973)
                  ·
                    refine ⟨7439780124541732657066685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 79357654661778481675377973 7439780124541732657066685)
                    ·
                      refine ⟨2789917546703149746400007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7439780124541732657066685 2789917546703149746400007)
                      ·
                        rfl

theorem cell23_5433345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_5433345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433345 prefixEnd_5433345 := by exact prefixLift 5433345
  have htrace : WordTrace (prefixWord ++ tailWord_5433345) baseStart_5433345 baseEnd_5433345 := by
    simpa [prefixWord, tailWord_5433345, baseEnd_5433345] using wordTrace_append hprefix tailTrace_5433345
  have hstable : (prefixWord ++ tailWord_5433345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433345).length < 2 ^ (prefixWord ++ tailWord_5433345).sum := by decide
  have hdescent : baseEnd_5433345 < baseStart_5433345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433422 : List Nat := [4, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5]
def baseStart_5433422 : Nat := 118140960795 + 5433422 * 2 ^ 59
def prefixEnd_5433422 : Nat := 4983230072969 + 3 ^ 40 * 5433422 * 2
def baseEnd_5433422 : Nat := 2789957084713545945137153

theorem tailTrace_5433422 : CollatzResearch.WordTrace tailWord_5433422 prefixEnd_5433422 2789957084713545945137153 := by
  unfold tailWord_5433422
  simp only [CollatzResearch.WordTrace]
  refine ⟨24771647615205940430558815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132115453947765015629647013 24771647615205940430558815)
  ·
    refine ⟨37157471422808910645838223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24771647615205940430558815 37157471422808910645838223)
    ·
      refine ⟨55736207134213365968757335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37157471422808910645838223 55736207134213365968757335)
      ·
        refine ⟨83604310701320048953136003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55736207134213365968757335 83604310701320048953136003)
        ·
          refine ⟨125406466051980073429704005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83604310701320048953136003 125406466051980073429704005)
          ·
            refine ⟨23513712384746263768069501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125406466051980073429704005 23513712384746263768069501)
            ·
              refine ⟨8817642144279848913026063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23513712384746263768069501 8817642144279848913026063)
              ·
                refine ⟨13226463216419773369539095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8817642144279848913026063 13226463216419773369539095)
                ·
                  refine ⟨19839694824629660054308643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13226463216419773369539095 19839694824629660054308643)
                  ·
                    refine ⟨29759542236944490081462965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19839694824629660054308643 29759542236944490081462965)
                    ·
                      refine ⟨2789957084713545945137153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29759542236944490081462965 2789957084713545945137153)
                      ·
                        rfl

theorem cell23_5433422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_5433422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433422 prefixEnd_5433422 := by exact prefixLift 5433422
  have htrace : WordTrace (prefixWord ++ tailWord_5433422) baseStart_5433422 baseEnd_5433422 := by
    simpa [prefixWord, tailWord_5433422, baseEnd_5433422] using wordTrace_append hprefix tailTrace_5433422
  have hstable : (prefixWord ++ tailWord_5433422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433422).length < 2 ^ (prefixWord ++ tailWord_5433422).sum := by decide
  have hdescent : baseEnd_5433422 < baseStart_5433422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433429 : List Nat := [1, 3, 2, 2, 1, 4, 2, 2, 2, 4]
def baseStart_5433429 : Nat := 118140960795 + 5433429 * 2 ^ 59
def prefixEnd_5433429 : Nat := 4983230072969 + 3 ^ 40 * 5433429 * 2
def baseEnd_5433429 : Nat := 929986893026042472583207

theorem tailTrace_5433429 : CollatzResearch.WordTrace tailWord_5433429 prefixEnd_5433429 929986893026042472583207 := by
  unfold tailWord_5433429
  simp only [CollatzResearch.WordTrace]
  refine ⟨198173436232622163639975341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132115624155081442426650227 198173436232622163639975341)
  ·
    refine ⟨74315038587233311364990753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198173436232622163639975341 74315038587233311364990753)
    ·
      refine ⟨55736278940424983523743065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74315038587233311364990753 55736278940424983523743065)
      ·
        refine ⟨41802209205318737642807299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55736278940424983523743065 41802209205318737642807299)
        ·
          refine ⟨62703313807978106464210949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41802209205318737642807299 62703313807978106464210949)
          ·
            refine ⟨11756871338995894962039553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62703313807978106464210949 11756871338995894962039553)
            ·
              refine ⟨8817653504246921221529665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11756871338995894962039553 8817653504246921221529665)
              ·
                refine ⟨6613240128185190916147249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8817653504246921221529665 6613240128185190916147249)
                ·
                  refine ⟨4959930096138893187110437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6613240128185190916147249 4959930096138893187110437)
                  ·
                    refine ⟨929986893026042472583207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4959930096138893187110437 929986893026042472583207)
                    ·
                      rfl

theorem cell23_5433429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_5433429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433429 prefixEnd_5433429 := by exact prefixLift 5433429
  have htrace : WordTrace (prefixWord ++ tailWord_5433429) baseStart_5433429 baseEnd_5433429 := by
    simpa [prefixWord, tailWord_5433429, baseEnd_5433429] using wordTrace_append hprefix tailTrace_5433429
  have hstable : (prefixWord ++ tailWord_5433429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433429).length < 2 ^ (prefixWord ++ tailWord_5433429).sum := by decide
  have hdescent : baseEnd_5433429 < baseStart_5433429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433430 : List Nat := [5, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3]
def baseStart_5433430 : Nat := 118140960795 + 5433430 * 2 ^ 59
def prefixEnd_5433430 : Nat := 4983230072969 + 3 ^ 40 * 5433430 * 2
def baseEnd_5433430 : Nat := 2789961192558781913837117

theorem tailTrace_5433430 : CollatzResearch.WordTrace tailWord_5433430 prefixEnd_5433430 2789961192558781913837117 := by
  unfold tailWord_5433430
  simp only [CollatzResearch.WordTrace]
  refine ⟨12385842044101158800672609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132115648470412360540507829 12385842044101158800672609)
  ·
    refine ⟨9289381533075869100504457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12385842044101158800672609 9289381533075869100504457)
    ·
      refine ⟨6967036149806901825378343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9289381533075869100504457 6967036149806901825378343)
      ·
        refine ⟨10450554224710352738067515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6967036149806901825378343 10450554224710352738067515)
        ·
          refine ⟨15675831337065529107101273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10450554224710352738067515 15675831337065529107101273)
          ·
            refine ⟨11756873502799146830325955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15675831337065529107101273 11756873502799146830325955)
            ·
              refine ⟨17635310254198720245488933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11756873502799146830325955 17635310254198720245488933)
              ·
                refine ⟨3306620672662260046029175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17635310254198720245488933 3306620672662260046029175)
                ·
                  refine ⟨4959931008993390069043763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3306620672662260046029175 4959931008993390069043763)
                  ·
                    refine ⟨7439896513490085103565645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4959931008993390069043763 7439896513490085103565645)
                    ·
                      refine ⟨2789961192558781913837117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7439896513490085103565645 2789961192558781913837117)
                      ·
                        rfl

theorem cell23_5433430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_5433430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433430 prefixEnd_5433430 := by exact prefixLift 5433430
  have htrace : WordTrace (prefixWord ++ tailWord_5433430) baseStart_5433430 baseEnd_5433430 := by
    simpa [prefixWord, tailWord_5433430, baseEnd_5433430] using wordTrace_append hprefix tailTrace_5433430
  have hstable : (prefixWord ++ tailWord_5433430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433430).length < 2 ^ (prefixWord ++ tailWord_5433430).sum := by decide
  have hdescent : baseEnd_5433430 < baseStart_5433430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433452 : List Nat := [2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 3]
def baseStart_5433452 : Nat := 118140960795 + 5433452 * 2 ^ 59
def prefixEnd_5433452 : Nat := 4983230072969 + 3 ^ 40 * 5433452 * 2
def baseEnd_5433452 : Nat := 2789972489133180827762015

theorem tailTrace_5433452 : CollatzResearch.WordTrace tailWord_5433452 prefixEnd_5433452 2789972489133180827762015 := by
  unfold tailWord_5433452
  simp only [CollatzResearch.WordTrace]
  refine ⟨99087137555769419284031305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132116183407692559045375073 99087137555769419284031305)
  ·
    refine ⟨74315353166827064463023479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99087137555769419284031305 74315353166827064463023479)
    ·
      refine ⟨111473029750240596694535219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74315353166827064463023479 111473029750240596694535219)
      ·
        refine ⟨167209544625360895041802829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111473029750240596694535219 167209544625360895041802829)
        ·
          refine ⟨62703579234510335640676061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167209544625360895041802829 62703579234510335640676061)
          ·
            refine ⟨23513842212941375865253523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62703579234510335640676061 23513842212941375865253523)
            ·
              refine ⟨35270763319412063797880285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23513842212941375865253523 35270763319412063797880285)
              ·
                refine ⟨13226536244779523924205107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35270763319412063797880285 13226536244779523924205107)
                ·
                  refine ⟨19839804367169285886307661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13226536244779523924205107 19839804367169285886307661)
                  ·
                    refine ⟨7439926637688482207365373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19839804367169285886307661 7439926637688482207365373)
                    ·
                      refine ⟨2789972489133180827762015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7439926637688482207365373 2789972489133180827762015)
                      ·
                        rfl

theorem cell23_5433452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 3].length) (baseStart_5433452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433452 prefixEnd_5433452 := by exact prefixLift 5433452
  have htrace : WordTrace (prefixWord ++ tailWord_5433452) baseStart_5433452 baseEnd_5433452 := by
    simpa [prefixWord, tailWord_5433452, baseEnd_5433452] using wordTrace_append hprefix tailTrace_5433452
  have hstable : (prefixWord ++ tailWord_5433452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433452).length < 2 ^ (prefixWord ++ tailWord_5433452).sum := by decide
  have hdescent : baseEnd_5433452 < baseStart_5433452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433473 : List Nat := [1, 2, 4, 2, 3, 2, 2, 1, 1, 2, 3]
def baseStart_5433473 : Nat := 118140960795 + 5433473 * 2 ^ 59
def prefixEnd_5433473 : Nat := 4983230072969 + 3 ^ 40 * 5433473 * 2
def baseEnd_5433473 : Nat := 2789983272226925245599419

theorem tailTrace_5433473 : CollatzResearch.WordTrace tailWord_5433473 prefixEnd_5433473 2789983272226925245599419 := by
  unfold tailWord_5433473
  simp only [CollatzResearch.WordTrace]
  refine ⟨198175041044462759154577073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132116694029641839436384715 198175041044462759154577073)
  ·
    refine ⟨148631280783347069365932805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198175041044462759154577073 148631280783347069365932805)
    ·
      refine ⟨27868365146877575506112401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148631280783347069365932805 27868365146877575506112401)
      ·
        refine ⟨20901273860158181629584301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27868365146877575506112401 20901273860158181629584301)
        ·
          refine ⟨7837977697559318111094113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20901273860158181629584301 7837977697559318111094113)
          ·
            refine ⟨5878483273169488583320585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7837977697559318111094113 5878483273169488583320585)
            ·
              refine ⟨4408862454877116437490439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5878483273169488583320585 4408862454877116437490439)
              ·
                refine ⟨6613293682315674656235659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4408862454877116437490439 6613293682315674656235659)
                ·
                  refine ⟨9919940523473511984353489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6613293682315674656235659 9919940523473511984353489)
                  ·
                    refine ⟨7439955392605133988265117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9919940523473511984353489 7439955392605133988265117)
                    ·
                      refine ⟨2789983272226925245599419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7439955392605133988265117 2789983272226925245599419)
                      ·
                        rfl

theorem cell23_5433473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_5433473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433473 prefixEnd_5433473 := by exact prefixLift 5433473
  have htrace : WordTrace (prefixWord ++ tailWord_5433473) baseStart_5433473 baseEnd_5433473 := by
    simpa [prefixWord, tailWord_5433473, baseEnd_5433473] using wordTrace_append hprefix tailTrace_5433473
  have hstable : (prefixWord ++ tailWord_5433473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433473).length < 2 ^ (prefixWord ++ tailWord_5433473).sum := by decide
  have hdescent : baseEnd_5433473 < baseStart_5433473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433486 : List Nat := [4, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3]
def baseStart_5433486 : Nat := 118140960795 + 5433486 * 2 ^ 59
def prefixEnd_5433486 : Nat := 4983230072969 + 3 ^ 40 * 5433486 * 2
def baseEnd_5433486 : Nat := 2789989947475433694736859

theorem tailTrace_5433486 : CollatzResearch.WordTrace tailWord_5433486 prefixEnd_5433486 2789989947475433694736859 := by
  unfold tailWord_5433486
  simp only [CollatzResearch.WordTrace]
  refine ⟨24771939399176957796850039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132117010128943774916533541 24771939399176957796850039)
  ·
    refine ⟨37157909098765436695275059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24771939399176957796850039 37157909098765436695275059)
    ·
      refine ⟨55736863648148155042912589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37157909098765436695275059 55736863648148155042912589)
      ·
        refine ⟨20901323868055558141092221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55736863648148155042912589 20901323868055558141092221)
        ·
          refine ⟨7837996450520834302909583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20901323868055558141092221 7837996450520834302909583)
          ·
            refine ⟨11756994675781251454364375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7837996450520834302909583 11756994675781251454364375)
            ·
              refine ⟨17635492013671877181546563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11756994675781251454364375 17635492013671877181546563)
              ·
                refine ⟨26453238020507815772319845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17635492013671877181546563 26453238020507815772319845)
                ·
                  refine ⟨4959982128845215457309971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26453238020507815772319845 4959982128845215457309971)
                  ·
                    refine ⟨7439973193267823185964957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4959982128845215457309971 7439973193267823185964957)
                    ·
                      refine ⟨2789989947475433694736859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7439973193267823185964957 2789989947475433694736859)
                      ·
                        rfl

theorem cell23_5433486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_5433486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433486 prefixEnd_5433486 := by exact prefixLift 5433486
  have htrace : WordTrace (prefixWord ++ tailWord_5433486) baseStart_5433486 baseEnd_5433486 := by
    simpa [prefixWord, tailWord_5433486, baseEnd_5433486] using wordTrace_append hprefix tailTrace_5433486
  have hstable : (prefixWord ++ tailWord_5433486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433486).length < 2 ^ (prefixWord ++ tailWord_5433486).sum := by decide
  have hdescent : baseEnd_5433486 < baseStart_5433486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433503 : List Nat := [1, 1, 2, 6, 1, 2, 3, 1, 2, 1, 3]
def baseStart_5433503 : Nat := 118140960795 + 5433503 * 2 ^ 59
def prefixEnd_5433503 : Nat := 4983230072969 + 3 ^ 40 * 5433503 * 2
def baseEnd_5433503 : Nat := 2789998676646560128224281

theorem tailTrace_5433503 : CollatzResearch.WordTrace tailWord_5433503 prefixEnd_5433503 2789998676646560128224281 := by
  unfold tailWord_5433503
  simp only [CollatzResearch.WordTrace]
  refine ⟨198176135234354074278169163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132117423489569382852112775 198176135234354074278169163)
  ·
    refine ⟨297264202851531111417253745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198176135234354074278169163 297264202851531111417253745)
    ·
      refine ⟨222948152138648333562940309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297264202851531111417253745 222948152138648333562940309)
      ·
        refine ⟨10450694631499140635762827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 222948152138648333562940309 10450694631499140635762827)
        ·
          refine ⟨15676041947248710953644241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10450694631499140635762827 15676041947248710953644241)
          ·
            refine ⟨11757031460436533215233181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15676041947248710953644241 11757031460436533215233181)
            ·
              refine ⟨4408886797663699955712443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11757031460436533215233181 4408886797663699955712443)
              ·
                refine ⟨6613330196495549933568665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4408886797663699955712443 6613330196495549933568665)
                ·
                  refine ⟨4959997647371662450176499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6613330196495549933568665 4959997647371662450176499)
                  ·
                    refine ⟨7439996471057493675264749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4959997647371662450176499 7439996471057493675264749)
                    ·
                      refine ⟨2789998676646560128224281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7439996471057493675264749 2789998676646560128224281)
                      ·
                        rfl

theorem cell23_5433503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_5433503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433503 prefixEnd_5433503 := by exact prefixLift 5433503
  have htrace : WordTrace (prefixWord ++ tailWord_5433503) baseStart_5433503 baseEnd_5433503 := by
    simpa [prefixWord, tailWord_5433503, baseEnd_5433503] using wordTrace_append hprefix tailTrace_5433503
  have hstable : (prefixWord ++ tailWord_5433503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433503).length < 2 ^ (prefixWord ++ tailWord_5433503).sum := by decide
  have hdescent : baseEnd_5433503 < baseStart_5433503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433545 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 3, 7]
def baseStart_5433545 : Nat := 118140960795 + 5433545 * 2 ^ 59
def prefixEnd_5433545 : Nat := 4983230072969 + 3 ^ 40 * 5433545 * 2
def baseEnd_5433545 : Nat := 930006747611349654633029

theorem tailTrace_5433545 : CollatzResearch.WordTrace tailWord_5433545 prefixEnd_5433545 930006747611349654633029 := by
  unfold tailWord_5433545
  simp only [CollatzResearch.WordTrace]
  refine ⟨198177667100201915451198089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132118444733467943634132059 198177667100201915451198089)
  ·
    refine ⟨148633250325151436588398567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198177667100201915451198089 148633250325151436588398567)
    ·
      refine ⟨222949875487727154882597851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148633250325151436588398567 222949875487727154882597851)
      ·
        refine ⟨334424813231590732323896777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222949875487727154882597851 334424813231590732323896777)
        ·
          refine ⟨250818609923693049242922583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 334424813231590732323896777 250818609923693049242922583)
          ·
            refine ⟨376227914885539573864383875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250818609923693049242922583 376227914885539573864383875)
            ·
              refine ⟨564341872328309360796575813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376227914885539573864383875 564341872328309360796575813)
              ·
                refine ⟨105814101061558005149357965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 564341872328309360796575813 105814101061558005149357965)
                ·
                  refine ⟨39680287898084251931009237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105814101061558005149357965 39680287898084251931009237)
                  ·
                    refine ⟨930006747611349654633029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39680287898084251931009237 930006747611349654633029)
                    ·
                      rfl

theorem cell23_5433545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 7].length) (baseStart_5433545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433545 prefixEnd_5433545 := by exact prefixLift 5433545
  have htrace : WordTrace (prefixWord ++ tailWord_5433545) baseStart_5433545 baseEnd_5433545 := by
    simpa [prefixWord, tailWord_5433545, baseEnd_5433545] using wordTrace_append hprefix tailTrace_5433545
  have hstable : (prefixWord ++ tailWord_5433545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433545).length < 2 ^ (prefixWord ++ tailWord_5433545).sum := by decide
  have hdescent : baseEnd_5433545 < baseStart_5433545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433560 : List Nat := [2, 1, 2, 2, 4, 3, 2, 1, 2, 2, 2]
def baseStart_5433560 : Nat := 118140960795 + 5433560 * 2 ^ 59
def prefixEnd_5433560 : Nat := 4983230072969 + 3 ^ 40 * 5433560 * 2
def baseEnd_5433560 : Nat := 2790027945043866405211519

theorem tailTrace_5433560 : CollatzResearch.WordTrace tailWord_5433560 prefixEnd_5433560 2790027945043866405211519 := by
  unfold tailWord_5433560
  simp only [CollatzResearch.WordTrace]
  refine ⟨99089107097573786506497067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132118809463431715341996089 99089107097573786506497067)
  ·
    refine ⟨148633660646360679759745601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99089107097573786506497067 148633660646360679759745601)
    ·
      refine ⟨111475245484770509819809201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148633660646360679759745601 111475245484770509819809201)
      ·
        refine ⟨83606434113577882364856901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111475245484770509819809201 83606434113577882364856901)
        ·
          refine ⟨15676206396295852943410669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83606434113577882364856901 15676206396295852943410669)
          ·
            refine ⟨5878577398610944853779001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15676206396295852943410669 5878577398610944853779001)
            ·
              refine ⟨4408933048958208640334251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5878577398610944853779001 4408933048958208640334251)
              ·
                refine ⟨6613399573437312960501377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4408933048958208640334251 6613399573437312960501377)
                ·
                  refine ⟨4960049680077984720376033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6613399573437312960501377 4960049680077984720376033)
                  ·
                    refine ⟨3720037260058488540282025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4960049680077984720376033 3720037260058488540282025)
                    ·
                      refine ⟨2790027945043866405211519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3720037260058488540282025 2790027945043866405211519)
                      ·
                        rfl

theorem cell23_5433560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 2, 2, 2].length) (baseStart_5433560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433560 prefixEnd_5433560 := by exact prefixLift 5433560
  have htrace : WordTrace (prefixWord ++ tailWord_5433560) baseStart_5433560 baseEnd_5433560 := by
    simpa [prefixWord, tailWord_5433560, baseEnd_5433560] using wordTrace_append hprefix tailTrace_5433560
  have hstable : (prefixWord ++ tailWord_5433560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433560).length < 2 ^ (prefixWord ++ tailWord_5433560).sum := by decide
  have hdescent : baseEnd_5433560 < baseStart_5433560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433599 : List Nat := [1, 1, 2, 2, 1, 4, 2, 2, 2, 4, 2]
def baseStart_5433599 : Nat := 118140960795 + 5433599 * 2 ^ 59
def prefixEnd_5433599 : Nat := 4983230072969 + 3 ^ 40 * 5433599 * 2
def baseEnd_5433599 : Nat := 2790047970789391752623839

theorem tailTrace_5433599 : CollatzResearch.WordTrace tailWord_5433599 prefixEnd_5433599 2790047970789391752623839 := by
  unfold tailWord_5433599
  simp only [CollatzResearch.WordTrace]
  refine ⟨198179636642006282673663851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132119757761337521782442567 198179636642006282673663851)
  ·
    refine ⟨297269454963009424010495777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198179636642006282673663851 297269454963009424010495777)
    ·
      refine ⟨222952091222257068007871833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297269454963009424010495777 222952091222257068007871833)
      ·
        refine ⟨167214068416692801005903875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222952091222257068007871833 167214068416692801005903875)
        ·
          refine ⟨250821102625039201508855813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167214068416692801005903875 250821102625039201508855813)
          ·
            refine ⟨47028956742194850282910465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 250821102625039201508855813 47028956742194850282910465)
            ·
              refine ⟨35271717556646137712182849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47028956742194850282910465 35271717556646137712182849)
              ·
                refine ⟨26453788167484603284137137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35271717556646137712182849 26453788167484603284137137)
                ·
                  refine ⟨19840341125613452463102853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26453788167484603284137137 19840341125613452463102853)
                  ·
                    refine ⟨3720063961052522336831785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19840341125613452463102853 3720063961052522336831785)
                    ·
                      refine ⟨2790047970789391752623839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3720063961052522336831785 2790047970789391752623839)
                      ·
                        rfl

theorem cell23_5433599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 4, 2].length) (baseStart_5433599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433599 prefixEnd_5433599 := by exact prefixLift 5433599
  have htrace : WordTrace (prefixWord ++ tailWord_5433599) baseStart_5433599 baseEnd_5433599 := by
    simpa [prefixWord, tailWord_5433599, baseEnd_5433599] using wordTrace_append hprefix tailTrace_5433599
  have hstable : (prefixWord ++ tailWord_5433599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433599).length < 2 ^ (prefixWord ++ tailWord_5433599).sum := by decide
  have hdescent : baseEnd_5433599 < baseStart_5433599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433626 : List Nat := [3, 1, 1, 3, 4, 1, 1, 2, 3, 4]
def baseStart_5433626 : Nat := 118140960795 + 5433626 * 2 ^ 59
def prefixEnd_5433626 : Nat := 4983230072969 + 3 ^ 40 * 5433626 * 2
def baseEnd_5433626 : Nat := 930020611589021048995405

theorem tailTrace_5433626 : CollatzResearch.WordTrace tailWord_5433626 prefixEnd_5433626 930020611589021048995405 := by
  unfold tailWord_5433626
  simp only [CollatzResearch.WordTrace]
  refine ⟨49545155353227116571224183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132120414275272310856597821 49545155353227116571224183)
  ·
    refine ⟨74317733029840674856836275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49545155353227116571224183 74317733029840674856836275)
    ·
      refine ⟨111476599544761012285254413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74317733029840674856836275 111476599544761012285254413)
      ·
        refine ⟨41803724829285379606970405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111476599544761012285254413 41803724829285379606970405)
        ·
          refine ⟨7838198405491008676306951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41803724829285379606970405 7838198405491008676306951)
          ·
            refine ⟨11757297608236513014460427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7838198405491008676306951 11757297608236513014460427)
            ·
              refine ⟨17635946412354769521690641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11757297608236513014460427 17635946412354769521690641)
              ·
                refine ⟨13226959809266077141267981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17635946412354769521690641 13226959809266077141267981)
                ·
                  refine ⟨4960109928474778927975493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13226959809266077141267981 4960109928474778927975493)
                  ·
                    refine ⟨930020611589021048995405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4960109928474778927975493 930020611589021048995405)
                    ·
                      rfl

theorem cell23_5433626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 3, 4].length) (baseStart_5433626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433626 prefixEnd_5433626 := by exact prefixLift 5433626
  have htrace : WordTrace (prefixWord ++ tailWord_5433626) baseStart_5433626 baseEnd_5433626 := by
    simpa [prefixWord, tailWord_5433626, baseEnd_5433626] using wordTrace_append hprefix tailTrace_5433626
  have hstable : (prefixWord ++ tailWord_5433626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433626).length < 2 ^ (prefixWord ++ tailWord_5433626).sum := by decide
  have hdescent : baseEnd_5433626 < baseStart_5433626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433636 : List Nat := [2, 3, 1, 3, 1, 2, 3, 1, 2, 2, 3]
def baseStart_5433636 : Nat := 118140960795 + 5433636 * 2 ^ 59
def prefixEnd_5433636 : Nat := 4983230072969 + 3 ^ 40 * 5433636 * 2
def baseEnd_5433636 : Nat := 2790066969573608107861169

theorem tailTrace_5433636 : CollatzResearch.WordTrace tailWord_5433636 prefixEnd_5433636 2790066969573608107861169 := by
  unfold tailWord_5433636
  simp only [CollatzResearch.WordTrace]
  refine ⟨99090493071436118996380381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132120657428581491995173841 99090493071436118996380381)
  ·
    refine ⟨37158934901788544623642643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99090493071436118996380381 37158934901788544623642643)
    ·
      refine ⟨55738402352682816935463965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37158934901788544623642643 55738402352682816935463965)
      ·
        refine ⟨20901900882256056350798987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55738402352682816935463965 20901900882256056350798987)
        ·
          refine ⟨31352851323384084526198481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20901900882256056350798987 31352851323384084526198481)
          ·
            refine ⟨23514638492538063394648861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31352851323384084526198481 23514638492538063394648861)
            ·
              refine ⟨8817989434701773772993323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23514638492538063394648861 8817989434701773772993323)
              ·
                refine ⟨13226984152052660659489985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8817989434701773772993323 13226984152052660659489985)
                ·
                  refine ⟨9920238114039495494617489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13226984152052660659489985 9920238114039495494617489)
                  ·
                    refine ⟨7440178585529621620963117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9920238114039495494617489 7440178585529621620963117)
                    ·
                      refine ⟨2790066969573608107861169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7440178585529621620963117 2790066969573608107861169)
                      ·
                        rfl

theorem cell23_5433636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_5433636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433636 prefixEnd_5433636 := by exact prefixLift 5433636
  have htrace : WordTrace (prefixWord ++ tailWord_5433636) baseStart_5433636 baseEnd_5433636 := by
    simpa [prefixWord, tailWord_5433636, baseEnd_5433636] using wordTrace_append hprefix tailTrace_5433636
  have hstable : (prefixWord ++ tailWord_5433636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433636).length < 2 ^ (prefixWord ++ tailWord_5433636).sum := by decide
  have hdescent : baseEnd_5433636 < baseStart_5433636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433689 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 1, 8, 2]
def baseStart_5433689 : Nat := 118140960795 + 5433689 * 2 ^ 59
def prefixEnd_5433689 : Nat := 4983230072969 + 3 ^ 40 * 5433689 * 2
def baseEnd_5433689 : Nat := 2790094184048296400498425

theorem tailTrace_5433689 : CollatzResearch.WordTrace tailWord_5433689 prefixEnd_5433689 2790094184048296400498425 := by
  unfold tailWord_5433689
  simp only [CollatzResearch.WordTrace]
  refine ⟨198182919211680228044440121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132121946141120152029626747 198182919211680228044440121)
  ·
    refine ⟨148637189408760171033330091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198182919211680228044440121 148637189408760171033330091)
    ·
      refine ⟨222955784113140256549995137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148637189408760171033330091 222955784113140256549995137)
      ·
        refine ⟨167216838084855192412496353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222955784113140256549995137 167216838084855192412496353)
        ·
          refine ⟨125412628563641394309372265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167216838084855192412496353 125412628563641394309372265)
          ·
            refine ⟨94059471422731045732029199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125412628563641394309372265 94059471422731045732029199)
            ·
              refine ⟨141089207134096568598043799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94059471422731045732029199 141089207134096568598043799)
              ·
                refine ⟨211633810701144852897065699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141089207134096568598043799 211633810701144852897065699)
                ·
                  refine ⟨317450716051717279345598549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 211633810701144852897065699 317450716051717279345598549)
                  ·
                    refine ⟨3720125578731061867331233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 317450716051717279345598549 3720125578731061867331233)
                    ·
                      refine ⟨2790094184048296400498425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3720125578731061867331233 2790094184048296400498425)
                      ·
                        rfl

theorem cell23_5433689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 8, 2].length) (baseStart_5433689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433689 prefixEnd_5433689 := by exact prefixLift 5433689
  have htrace : WordTrace (prefixWord ++ tailWord_5433689) baseStart_5433689 baseEnd_5433689 := by
    simpa [prefixWord, tailWord_5433689, baseEnd_5433689] using wordTrace_append hprefix tailTrace_5433689
  have hstable : (prefixWord ++ tailWord_5433689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433689).length < 2 ^ (prefixWord ++ tailWord_5433689).sum := by decide
  have hdescent : baseEnd_5433689 < baseStart_5433689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433699 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 6, 4]
def baseStart_5433699 : Nat := 118140960795 + 5433699 * 2 ^ 59
def prefixEnd_5433699 : Nat := 4983230072969 + 3 ^ 40 * 5433699 * 2
def baseEnd_5433699 : Nat := 930033106284947120457793

theorem tailTrace_5433699 : CollatzResearch.WordTrace tailWord_5433699 prefixEnd_5433699 930033106284947120457793 := by
  unfold tailWord_5433699
  simp only [CollatzResearch.WordTrace]
  refine ⟨198183283941643999752304151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132122189294429333168202767 198183283941643999752304151)
  ·
    refine ⟨297274925912465999628456227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198183283941643999752304151 297274925912465999628456227)
    ·
      refine ⟨445912388868698999442684341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297274925912465999628456227 445912388868698999442684341)
      ·
        refine ⟨41804286456440531197751657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 445912388868698999442684341 41804286456440531197751657)
        ·
          refine ⟨31353214842330398398313743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41804286456440531197751657 31353214842330398398313743)
          ·
            refine ⟨47029822263495597597470615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31353214842330398398313743 47029822263495597597470615)
            ·
              refine ⟨70544733395243396396205923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47029822263495597597470615 70544733395243396396205923)
              ·
                refine ⟨105817100092865094594308885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70544733395243396396205923 105817100092865094594308885)
                ·
                  refine ⟨4960176566853051309108229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 105817100092865094594308885 4960176566853051309108229)
                  ·
                    refine ⟨930033106284947120457793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4960176566853051309108229 930033106284947120457793)
                    ·
                      rfl

theorem cell23_5433699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 6, 4].length) (baseStart_5433699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433699 prefixEnd_5433699 := by exact prefixLift 5433699
  have htrace : WordTrace (prefixWord ++ tailWord_5433699) baseStart_5433699 baseEnd_5433699 := by
    simpa [prefixWord, tailWord_5433699, baseEnd_5433699] using wordTrace_append hprefix tailTrace_5433699
  have hstable : (prefixWord ++ tailWord_5433699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433699).length < 2 ^ (prefixWord ++ tailWord_5433699).sum := by decide
  have hdescent : baseEnd_5433699 < baseStart_5433699 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433712 : List Nat := [2, 1, 1, 1, 4, 3, 11]
def baseStart_5433712 : Nat := 118140960795 + 5433712 * 2 ^ 59
def prefixEnd_5433712 : Nat := 4983230072969 + 3 ^ 40 * 5433712 * 2
def baseEnd_5433712 : Nat := 34445753013621602598899

theorem tailTrace_5433712 : CollatzResearch.WordTrace tailWord_5433712 prefixEnd_5433712 34445753013621602598899 := by
  unfold tailWord_5433712
  simp only [CollatzResearch.WordTrace]
  refine ⟨99091879045298451486263695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132122505393731268648351593 99091879045298451486263695)
  ·
    refine ⟨148637818567947677229395543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99091879045298451486263695 148637818567947677229395543)
    ·
      refine ⟨222956727851921515844093315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148637818567947677229395543 222956727851921515844093315)
      ·
        refine ⟨334435091777882273766139973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222956727851921515844093315 334435091777882273766139973)
        ·
          refine ⟨62706579708352926331151245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 334435091777882273766139973 62706579708352926331151245)
          ·
            refine ⟨23514967390632347374181717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62706579708352926331151245 23514967390632347374181717)
            ·
              refine ⟨34445753013621602598899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 23514967390632347374181717 34445753013621602598899)
              ·
                rfl

theorem cell23_5433712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 11].length) (baseStart_5433712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433712 prefixEnd_5433712 := by exact prefixLift 5433712
  have htrace : WordTrace (prefixWord ++ tailWord_5433712) baseStart_5433712 baseEnd_5433712 := by
    simpa [prefixWord, tailWord_5433712, baseEnd_5433712] using wordTrace_append hprefix tailTrace_5433712
  have hstable : (prefixWord ++ tailWord_5433712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433712).length < 2 ^ (prefixWord ++ tailWord_5433712).sum := by decide
  have hdescent : baseEnd_5433712 < baseStart_5433712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433717 : List Nat := [1, 3, 4, 1, 2, 2, 3, 2, 1, 1, 3]
def baseStart_5433717 : Nat := 118140960795 + 5433717 * 2 ^ 59
def prefixEnd_5433717 : Nat := 4983230072969 + 3 ^ 40 * 5433717 * 2
def baseEnd_5433717 : Nat := 2790108561506622290948297

theorem tailTrace_5433717 : CollatzResearch.WordTrace tailWord_5433717 prefixEnd_5433717 2790108561506622290948297 := by
  unfold tailWord_5433717
  simp only [CollatzResearch.WordTrace]
  refine ⟨198183940455578788826459405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132122626970385859217639603 198183940455578788826459405)
  ·
    refine ⟨74318977670842045809922277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198183940455578788826459405 74318977670842045809922277)
    ·
      refine ⟨13934808313282883589360427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74318977670842045809922277 13934808313282883589360427)
      ·
        refine ⟨20902212469924325384040641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13934808313282883589360427 20902212469924325384040641)
        ·
          refine ⟨15676659352443244038030481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20902212469924325384040641 15676659352443244038030481)
          ·
            refine ⟨11757494514332433028522861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15676659352443244038030481 11757494514332433028522861)
            ·
              refine ⟨4409060442874662385696073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11757494514332433028522861 4409060442874662385696073)
              ·
                refine ⟨3306795332155996789272055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4409060442874662385696073 3306795332155996789272055)
                ·
                  refine ⟨4960192998233995183908083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3306795332155996789272055 4960192998233995183908083)
                  ·
                    refine ⟨7440289497350992775862125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4960192998233995183908083 7440289497350992775862125)
                    ·
                      refine ⟨2790108561506622290948297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7440289497350992775862125 2790108561506622290948297)
                      ·
                        rfl

theorem cell23_5433717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_5433717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433717 prefixEnd_5433717 := by exact prefixLift 5433717
  have htrace : WordTrace (prefixWord ++ tailWord_5433717) baseStart_5433717 baseEnd_5433717 := by
    simpa [prefixWord, tailWord_5433717, baseEnd_5433717] using wordTrace_append hprefix tailTrace_5433717
  have hstable : (prefixWord ++ tailWord_5433717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433717).length < 2 ^ (prefixWord ++ tailWord_5433717).sum := by decide
  have hdescent : baseEnd_5433717 < baseStart_5433717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433722 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 1, 4, 7]
def baseStart_5433722 : Nat := 118140960795 + 5433722 * 2 ^ 59
def prefixEnd_5433722 : Nat := 4983230072969 + 3 ^ 40 * 5433722 * 2
def baseEnd_5433722 : Nat := 2790111128909894771385773

theorem tailTrace_5433722 : CollatzResearch.WordTrace tailWord_5433722 prefixEnd_5433722 2790111128909894771385773 := by
  unfold tailWord_5433722
  simp only [CollatzResearch.WordTrace]
  refine ⟨49546030705140168670097855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132122748547040449786927613 49546030705140168670097855)
  ·
    refine ⟨74319046057710253005146783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49546030705140168670097855 74319046057710253005146783)
    ·
      refine ⟨111478569086565379507720175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74319046057710253005146783 111478569086565379507720175)
      ·
        refine ⟨167217853629848069261580263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111478569086565379507720175 167217853629848069261580263)
        ·
          refine ⟨250826780444772103892370395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167217853629848069261580263 250826780444772103892370395)
          ·
            refine ⟨376240170667158155838555593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250826780444772103892370395 376240170667158155838555593)
            ·
              refine ⟨282180128000368616878916695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 376240170667158155838555593 282180128000368616878916695)
              ·
                refine ⟨423270192000552925318375043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 282180128000368616878916695 423270192000552925318375043)
                ·
                  refine ⟨634905288000829387977562565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 423270192000552925318375043 634905288000829387977562565)
                  ·
                    refine ⟨119044741500155510245792981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 634905288000829387977562565 119044741500155510245792981)
                    ·
                      refine ⟨2790111128909894771385773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 119044741500155510245792981 2790111128909894771385773)
                      ·
                        rfl

theorem cell23_5433722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_5433722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433722 prefixEnd_5433722 := by exact prefixLift 5433722
  have htrace : WordTrace (prefixWord ++ tailWord_5433722) baseStart_5433722 baseEnd_5433722 := by
    simpa [prefixWord, tailWord_5433722, baseEnd_5433722] using wordTrace_append hprefix tailTrace_5433722
  have hstable : (prefixWord ++ tailWord_5433722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433722).length < 2 ^ (prefixWord ++ tailWord_5433722).sum := by decide
  have hdescent : baseEnd_5433722 < baseStart_5433722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433723 : List Nat := [1, 1, 1, 1, 1, 7, 3, 1, 3, 2, 2]
def baseStart_5433723 : Nat := 118140960795 + 5433723 * 2 ^ 59
def prefixEnd_5433723 : Nat := 4983230072969 + 3 ^ 40 * 5433723 * 2
def baseEnd_5433723 : Nat := 2790111642390549267473269

theorem tailTrace_5433723 : CollatzResearch.WordTrace tailWord_5433723 prefixEnd_5433723 2790111642390549267473269 := by
  unfold tailWord_5433723
  simp only [CollatzResearch.WordTrace]
  refine ⟨198184159293557051851177823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132122772862371367900785215 198184159293557051851177823)
  ·
    refine ⟨297276238940335577776766735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198184159293557051851177823 297276238940335577776766735)
    ·
      refine ⟨445914358410503366665150103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297276238940335577776766735 445914358410503366665150103)
      ·
        refine ⟨668871537615755049997725155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 445914358410503366665150103 668871537615755049997725155)
        ·
          refine ⟨1003307306423632574996587733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 668871537615755049997725155 1003307306423632574996587733)
          ·
            refine ⟨23515014994303888476482525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1003307306423632574996587733 23515014994303888476482525)
            ·
              refine ⟨8818130622863958178680947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23515014994303888476482525 8818130622863958178680947)
              ·
                refine ⟨13227195934295937268021421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8818130622863958178680947 13227195934295937268021421)
                ·
                  refine ⟨4960198475360976475508033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13227195934295937268021421 4960198475360976475508033)
                  ·
                    refine ⟨3720148856520732356631025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4960198475360976475508033 3720148856520732356631025)
                    ·
                      refine ⟨2790111642390549267473269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3720148856520732356631025 2790111642390549267473269)
                      ·
                        rfl

theorem cell23_5433723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 3, 2, 2].length) (baseStart_5433723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433723 prefixEnd_5433723 := by exact prefixLift 5433723
  have htrace : WordTrace (prefixWord ++ tailWord_5433723) baseStart_5433723 baseEnd_5433723 := by
    simpa [prefixWord, tailWord_5433723, baseEnd_5433723] using wordTrace_append hprefix tailTrace_5433723
  have hstable : (prefixWord ++ tailWord_5433723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433723).length < 2 ^ (prefixWord ++ tailWord_5433723).sum := by decide
  have hdescent : baseEnd_5433723 < baseStart_5433723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433729 : List Nat := [1, 2, 4, 3, 1, 1, 1, 10]
def baseStart_5433729 : Nat := 118140960795 + 5433729 * 2 ^ 59
def prefixEnd_5433729 : Nat := 4983230072969 + 3 ^ 40 * 5433729 * 2
def baseEnd_5433729 : Nat := 103337582343499120148083

theorem tailTrace_5433729 : CollatzResearch.WordTrace tailWord_5433729 prefixEnd_5433729 103337582343499120148083 := by
  unfold tailWord_5433729
  simp only [CollatzResearch.WordTrace]
  refine ⟨198184378131535314875896241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132122918754356876583930827 198184378131535314875896241)
  ·
    refine ⟨148638283598651486156922181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198184378131535314875896241 148638283598651486156922181)
    ·
      refine ⟨27869678174747153654422909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148638283598651486156922181 27869678174747153654422909)
      ·
        refine ⟨10451129315530182620408591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27869678174747153654422909 10451129315530182620408591)
        ·
          refine ⟨15676693973295273930612887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10451129315530182620408591 15676693973295273930612887)
          ·
            refine ⟨23515040959942910895919331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15676693973295273930612887 23515040959942910895919331)
            ·
              refine ⟨35272561439914366343878997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23515040959942910895919331 35272561439914366343878997)
              ·
                refine ⟨103337582343499120148083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 35272561439914366343878997 103337582343499120148083)
                ·
                  rfl

theorem cell23_5433729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 10].length) (baseStart_5433729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433729 prefixEnd_5433729 := by exact prefixLift 5433729
  have htrace : WordTrace (prefixWord ++ tailWord_5433729) baseStart_5433729 baseEnd_5433729 := by
    simpa [prefixWord, tailWord_5433729, baseEnd_5433729] using wordTrace_append hprefix tailTrace_5433729
  have hstable : (prefixWord ++ tailWord_5433729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433729).length < 2 ^ (prefixWord ++ tailWord_5433729).sum := by decide
  have hdescent : baseEnd_5433729 < baseStart_5433729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433780 : List Nat := [2, 5, 2, 2, 1, 2, 1, 8]
def baseStart_5433780 : Nat := 118140960795 + 5433780 * 2 ^ 59
def prefixEnd_5433780 : Nat := 4983230072969 + 3 ^ 40 * 5433780 * 2
def baseEnd_5433780 : Nat := 103338552251402057202241

theorem tailTrace_5433780 : CollatzResearch.WordTrace tailWord_5433780 prefixEnd_5433780 103338552251402057202241 := by
  unfold tailWord_5433780
  simp only [CollatzResearch.WordTrace]
  refine ⟨99093119127175275293001397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132124158836233700390668529 99093119127175275293001397)
  ·
    refine ⟨9289979918172682058718881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99093119127175275293001397 9289979918172682058718881)
    ·
      refine ⟨6967484938629511544039161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9289979918172682058718881 6967484938629511544039161)
      ·
        refine ⟨5225613703972133658029371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6967484938629511544039161 5225613703972133658029371)
        ·
          refine ⟨7838420555958200487044057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5225613703972133658029371 7838420555958200487044057)
          ·
            refine ⟨5878815416968650365283043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7838420555958200487044057 5878815416968650365283043)
            ·
              refine ⟨8818223125452975547924565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5878815416968650365283043 8818223125452975547924565)
              ·
                refine ⟨103338552251402057202241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8818223125452975547924565 103338552251402057202241)
                ·
                  rfl

theorem cell23_5433780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 8].length) (baseStart_5433780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433780 prefixEnd_5433780 := by exact prefixLift 5433780
  have htrace : WordTrace (prefixWord ++ tailWord_5433780) baseStart_5433780 baseEnd_5433780 := by
    simpa [prefixWord, tailWord_5433780, baseEnd_5433780] using wordTrace_append hprefix tailTrace_5433780
  have hstable : (prefixWord ++ tailWord_5433780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433780).length < 2 ^ (prefixWord ++ tailWord_5433780).sum := by decide
  have hdescent : baseEnd_5433780 < baseStart_5433780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433789 : List Nat := [1, 4, 1, 2, 2, 2, 1, 1, 1, 8]
def baseStart_5433789 : Nat := 118140960795 + 5433789 * 2 ^ 59
def prefixEnd_5433789 : Nat := 4983230072969 + 3 ^ 40 * 5433789 * 2
def baseEnd_5433789 : Nat := 930048510704582003082655

theorem tailTrace_5433789 : CollatzResearch.WordTrace tailWord_5433789 prefixEnd_5433789 930048510704582003082655 := by
  unfold tailWord_5433789
  simp only [CollatzResearch.WordTrace]
  refine ⟨198186566511317945123080421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132124377674211963415386947 198186566511317945123080421)
  ·
    refine ⟨37159981220872114710577579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198186566511317945123080421 37159981220872114710577579)
    ·
      refine ⟨55739971831308172065866369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37159981220872114710577579 55739971831308172065866369)
      ·
        refine ⟨41804978873481129049399777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55739971831308172065866369 41804978873481129049399777)
        ·
          refine ⟨31353734155110846787049833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41804978873481129049399777 31353734155110846787049833)
          ·
            refine ⟨23515300616333135090287375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31353734155110846787049833 23515300616333135090287375)
            ·
              refine ⟨35272950924499702635431063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23515300616333135090287375 35272950924499702635431063)
              ·
                refine ⟨52909426386749553953146595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35272950924499702635431063 52909426386749553953146595)
                ·
                  refine ⟨79364139580124330929719893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52909426386749553953146595 79364139580124330929719893)
                  ·
                    refine ⟨930048510704582003082655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 79364139580124330929719893 930048510704582003082655)
                    ·
                      rfl

theorem cell23_5433789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_5433789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433789 prefixEnd_5433789 := by exact prefixLift 5433789
  have htrace : WordTrace (prefixWord ++ tailWord_5433789) baseStart_5433789 baseEnd_5433789 := by
    simpa [prefixWord, tailWord_5433789, baseEnd_5433789] using wordTrace_append hprefix tailTrace_5433789
  have hstable : (prefixWord ++ tailWord_5433789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433789).length < 2 ^ (prefixWord ++ tailWord_5433789).sum := by decide
  have hdescent : baseEnd_5433789 < baseStart_5433789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433813 : List Nat := [1, 3, 2, 3, 1, 2, 2, 2, 1, 4, 2]
def baseStart_5433813 : Nat := 118140960795 + 5433813 * 2 ^ 59
def prefixEnd_5433813 : Nat := 4983230072969 + 3 ^ 40 * 5433813 * 2
def baseEnd_5433813 : Nat := 2790157855649453915347855

theorem tailTrace_5433813 : CollatzResearch.WordTrace tailWord_5433813 prefixEnd_5433813 2790157855649453915347855 := by
  unfold tailWord_5433813
  simp only [CollatzResearch.WordTrace]
  refine ⟨198187441863230997221954093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132124961242153998147969395 198187441863230997221954093)
  ·
    refine ⟨74320290698711623958232785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198187441863230997221954093 74320290698711623958232785)
    ·
      refine ⟨55740218024033717968674589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74320290698711623958232785 55740218024033717968674589)
      ·
        refine ⟨20902581759012644238252971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55740218024033717968674589 20902581759012644238252971)
        ·
          refine ⟨31353872638518966357379457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20902581759012644238252971 31353872638518966357379457)
          ·
            refine ⟨23515404478889224768034593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31353872638518966357379457 23515404478889224768034593)
            ·
              refine ⟨17636553359166918576025945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23515404478889224768034593 17636553359166918576025945)
              ·
                refine ⟨13227415019375188932019459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17636553359166918576025945 13227415019375188932019459)
                ·
                  refine ⟨19841122529062783398029189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13227415019375188932019459 19841122529062783398029189)
                  ·
                    refine ⟨3720210474199271887130473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19841122529062783398029189 3720210474199271887130473)
                    ·
                      refine ⟨2790157855649453915347855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3720210474199271887130473 2790157855649453915347855)
                      ·
                        rfl

theorem cell23_5433813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_5433813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433813 prefixEnd_5433813 := by exact prefixLift 5433813
  have htrace : WordTrace (prefixWord ++ tailWord_5433813) baseStart_5433813 baseEnd_5433813 := by
    simpa [prefixWord, tailWord_5433813, baseEnd_5433813] using wordTrace_append hprefix tailTrace_5433813
  have hstable : (prefixWord ++ tailWord_5433813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433813).length < 2 ^ (prefixWord ++ tailWord_5433813).sum := by decide
  have hdescent : baseEnd_5433813 < baseStart_5433813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433836 : List Nat := [2, 2, 1, 1, 2, 1, 3, 6, 5]
def baseStart_5433836 : Nat := 118140960795 + 5433836 * 2 ^ 59
def prefixEnd_5433836 : Nat := 4983230072969 + 3 ^ 40 * 5433836 * 2
def baseEnd_5433836 : Nat := 310018851744945258373361

theorem tailTrace_5433836 : CollatzResearch.WordTrace tailWord_5433836 prefixEnd_5433836 310018851744945258373361 := by
  unfold tailWord_5433836
  simp only [CollatzResearch.WordTrace]
  refine ⟨99094140371073836075020681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132125520494765114766694241 99094140371073836075020681)
  ·
    refine ⟨74320605278305377056265511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99094140371073836075020681 74320605278305377056265511)
    ·
      refine ⟨111480907917458065584398267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74320605278305377056265511 111480907917458065584398267)
      ·
        refine ⟨167221361876187098376597401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111480907917458065584398267 167221361876187098376597401)
        ·
          refine ⟨125416021407140323782448051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167221361876187098376597401 125416021407140323782448051)
          ·
            refine ⟨188124032110710485673672077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125416021407140323782448051 188124032110710485673672077)
            ·
              refine ⟨70546512041516432127627029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 188124032110710485673672077 70546512041516432127627029)
              ·
                refine ⟨3306867751946082755982517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70546512041516432127627029 3306867751946082755982517)
                ·
                  refine ⟨310018851744945258373361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3306867751946082755982517 310018851744945258373361)
                  ·
                    rfl

theorem cell23_5433836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 6, 5].length) (baseStart_5433836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433836 prefixEnd_5433836 := by exact prefixLift 5433836
  have htrace : WordTrace (prefixWord ++ tailWord_5433836) baseStart_5433836 baseEnd_5433836 := by
    simpa [prefixWord, tailWord_5433836, baseEnd_5433836] using wordTrace_append hprefix tailTrace_5433836
  have hstable : (prefixWord ++ tailWord_5433836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433836).length < 2 ^ (prefixWord ++ tailWord_5433836).sum := by decide
  have hdescent : baseEnd_5433836 < baseStart_5433836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433849 : List Nat := [1, 2, 1, 3, 1, 2, 3, 2, 1, 7]
def baseStart_5433849 : Nat := 118140960795 + 5433849 * 2 ^ 59
def prefixEnd_5433849 : Nat := 4983230072969 + 3 ^ 40 * 5433849 * 2
def baseEnd_5433849 : Nat := 930058780317671924832563

theorem tailTrace_5433849 : CollatzResearch.WordTrace tailWord_5433849 prefixEnd_5433849 930058780317671924832563 := by
  unfold tailWord_5433849
  simp only [CollatzResearch.WordTrace]
  refine ⟨198188754891100575370264601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132125836594067050246843067 198188754891100575370264601)
  ·
    refine ⟨148641566168325431527698451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198188754891100575370264601 148641566168325431527698451)
    ·
      refine ⟨222962349252488147291547677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148641566168325431527698451 222962349252488147291547677)
      ·
        refine ⟨83610880969683055234330379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222962349252488147291547677 83610880969683055234330379)
        ·
          refine ⟨125416321454524582851495569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83610880969683055234330379 125416321454524582851495569)
          ·
            refine ⟨94062241090893437138621677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125416321454524582851495569 94062241090893437138621677)
            ·
              refine ⟨35273340409085038926983129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94062241090893437138621677 35273340409085038926983129)
              ·
                refine ⟨26455005306813779195237347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35273340409085038926983129 26455005306813779195237347)
                ·
                  refine ⟨39682507960220668792856021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26455005306813779195237347 39682507960220668792856021)
                  ·
                    refine ⟨930058780317671924832563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39682507960220668792856021 930058780317671924832563)
                    ·
                      rfl

theorem cell23_5433849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 7].length) (baseStart_5433849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433849 prefixEnd_5433849 := by exact prefixLift 5433849
  have htrace : WordTrace (prefixWord ++ tailWord_5433849) baseStart_5433849 baseEnd_5433849 := by
    simpa [prefixWord, tailWord_5433849, baseEnd_5433849] using wordTrace_append hprefix tailTrace_5433849
  have hstable : (prefixWord ++ tailWord_5433849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433849).length < 2 ^ (prefixWord ++ tailWord_5433849).sum := by decide
  have hdescent : baseEnd_5433849 < baseStart_5433849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433866 : List Nat := [3, 1, 2, 2, 2, 1, 2, 3, 2, 5]
def baseStart_5433866 : Nat := 118140960795 + 5433866 * 2 ^ 59
def prefixEnd_5433866 : Nat := 4983230072969 + 3 ^ 40 * 5433866 * 2
def baseEnd_5433866 : Nat := 930061690041380735995037

theorem tailTrace_5433866 : CollatzResearch.WordTrace tailWord_5433866 prefixEnd_5433866 930061690041380735995037 := by
  unfold tailWord_5433866
  simp only [CollatzResearch.WordTrace]
  refine ⟨49547343733009746818408363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132126249954692658182422301 49547343733009746818408363)
  ·
    refine ⟨74321015599514620227612545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49547343733009746818408363 74321015599514620227612545)
    ·
      refine ⟨55740761699635965170709409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74321015599514620227612545 55740761699635965170709409)
      ·
        refine ⟨41805571274726973878032057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55740761699635965170709409 41805571274726973878032057)
        ·
          refine ⟨31354178456045230408524043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41805571274726973878032057 31354178456045230408524043)
          ·
            refine ⟨47031267684067845612786065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31354178456045230408524043 47031267684067845612786065)
            ·
              refine ⟨35273450763050884209589549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47031267684067845612786065 35273450763050884209589549)
              ·
                refine ⟨13227544036144081578596081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35273450763050884209589549 13227544036144081578596081)
                ·
                  refine ⟨9920658027108061183947061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13227544036144081578596081 9920658027108061183947061)
                  ·
                    refine ⟨930061690041380735995037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9920658027108061183947061 930061690041380735995037)
                    ·
                      rfl

theorem cell23_5433866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_5433866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433866 prefixEnd_5433866 := by exact prefixLift 5433866
  have htrace : WordTrace (prefixWord ++ tailWord_5433866) baseStart_5433866 baseEnd_5433866 := by
    simpa [prefixWord, tailWord_5433866, baseEnd_5433866] using wordTrace_append hprefix tailTrace_5433866
  have hstable : (prefixWord ++ tailWord_5433866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433866).length < 2 ^ (prefixWord ++ tailWord_5433866).sum := by decide
  have hdescent : baseEnd_5433866 < baseStart_5433866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433870 : List Nat := [4, 1, 1, 2, 3, 3, 1, 3, 5]
def baseStart_5433870 : Nat := 118140960795 + 5433870 * 2 ^ 59
def prefixEnd_5433870 : Nat := 4983230072969 + 3 ^ 40 * 5433870 * 2
def baseEnd_5433870 : Nat := 310020791560751132481677

theorem tailTrace_5433870 : CollatzResearch.WordTrace tailWord_5433870 prefixEnd_5433870 310020791560751132481677 := by
  unfold tailWord_5433870
  simp only [CollatzResearch.WordTrace]
  refine ⟨24773690103003061994597383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132126347216016330637852709 24773690103003061994597383)
  ·
    refine ⟨37160535154504592991896075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24773690103003061994597383 37160535154504592991896075)
    ·
      refine ⟨55740802731756889487844113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37160535154504592991896075 55740802731756889487844113)
      ·
        refine ⟨41805602048817667115883085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55740802731756889487844113 41805602048817667115883085)
        ·
          refine ⟨15677100768306625168456157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41805602048817667115883085 15677100768306625168456157)
          ·
            refine ⟨5878912788114984438171059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15677100768306625168456157 5878912788114984438171059)
            ·
              refine ⟨8818369182172476657256589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5878912788114984438171059 8818369182172476657256589)
              ·
                refine ⟨3306888443314678746471221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8818369182172476657256589 3306888443314678746471221)
                ·
                  refine ⟨310020791560751132481677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3306888443314678746471221 310020791560751132481677)
                  ·
                    rfl

theorem cell23_5433870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 3, 5].length) (baseStart_5433870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433870 prefixEnd_5433870 := by exact prefixLift 5433870
  have htrace : WordTrace (prefixWord ++ tailWord_5433870) baseStart_5433870 baseEnd_5433870 := by
    simpa [prefixWord, tailWord_5433870, baseEnd_5433870] using wordTrace_append hprefix tailTrace_5433870
  have hstable : (prefixWord ++ tailWord_5433870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433870).length < 2 ^ (prefixWord ++ tailWord_5433870).sum := by decide
  have hdescent : baseEnd_5433870 < baseStart_5433870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433899 : List Nat := [1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 6]
def baseStart_5433899 : Nat := 118140960795 + 5433899 * 2 ^ 59
def prefixEnd_5433899 : Nat := 4983230072969 + 3 ^ 40 * 5433899 * 2
def baseEnd_5433899 : Nat := 2790202014985740578872459

theorem tailTrace_5433899 : CollatzResearch.WordTrace tailWord_5433899 prefixEnd_5433899 2790202014985740578872459 := by
  unfold tailWord_5433899
  simp only [CollatzResearch.WordTrace]
  refine ⟨198190578540919433909584751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132127052360612955939723167 198190578540919433909584751)
  ·
    refine ⟨297285867811379150864377127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198190578540919433909584751 297285867811379150864377127)
    ·
      refine ⟨445928801717068726296565691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297285867811379150864377127 445928801717068726296565691)
      ·
        refine ⟨668893202575603089444848537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 445928801717068726296565691 668893202575603089444848537)
        ·
          refine ⟨501669901931702317083636403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 668893202575603089444848537 501669901931702317083636403)
          ·
            refine ⟨752504852897553475625454605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501669901931702317083636403 752504852897553475625454605)
            ·
              refine ⟨282189319836582553359545477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 752504852897553475625454605 282189319836582553359545477)
              ·
                refine ⟨52910497469359228754914777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 282189319836582553359545477 52910497469359228754914777)
                ·
                  refine ⟨39682873102019421566186083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52910497469359228754914777 39682873102019421566186083)
                  ·
                    refine ⟨59524309653029132349279125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39682873102019421566186083 59524309653029132349279125)
                    ·
                      refine ⟨2790202014985740578872459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59524309653029132349279125 2790202014985740578872459)
                      ·
                        rfl

theorem cell23_5433899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 6].length) (baseStart_5433899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433899 prefixEnd_5433899 := by exact prefixLift 5433899
  have htrace : WordTrace (prefixWord ++ tailWord_5433899) baseStart_5433899 baseEnd_5433899 := by
    simpa [prefixWord, tailWord_5433899, baseEnd_5433899] using wordTrace_append hprefix tailTrace_5433899
  have hstable : (prefixWord ++ tailWord_5433899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433899).length < 2 ^ (prefixWord ++ tailWord_5433899).sum := by decide
  have hdescent : baseEnd_5433899 < baseStart_5433899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433906 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3]
def baseStart_5433906 : Nat := 118140960795 + 5433906 * 2 ^ 59
def prefixEnd_5433906 : Nat := 4983230072969 + 3 ^ 40 * 5433906 * 2
def baseEnd_5433906 : Nat := 2790205609350322051484927

theorem tailTrace_5433906 : CollatzResearch.WordTrace tailWord_5433906 prefixEnd_5433906 2790205609350322051484927 := by
  unfold tailWord_5433906
  simp only [CollatzResearch.WordTrace]
  refine ⟨49547708462973518526272393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132127222567929382736726381 49547708462973518526272393)
  ·
    refine ⟨37160781347230138894704295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49547708462973518526272393 37160781347230138894704295)
    ·
      refine ⟨55741172020845208342056443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37160781347230138894704295 55741172020845208342056443)
      ·
        refine ⟨83611758031267812513084665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55741172020845208342056443 83611758031267812513084665)
        ·
          refine ⟨62708818523450859384813499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83611758031267812513084665 62708818523450859384813499)
          ·
            refine ⟨94063227785176289077220249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62708818523450859384813499 94063227785176289077220249)
            ·
              refine ⟨70547420838882216807915187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94063227785176289077220249 70547420838882216807915187)
              ·
                refine ⟨105821131258323325211872781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70547420838882216807915187 105821131258323325211872781)
                ·
                  refine ⟨39682924221871246954452293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105821131258323325211872781 39682924221871246954452293)
                  ·
                    refine ⟨7440548291600858803959805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39682924221871246954452293 7440548291600858803959805)
                    ·
                      refine ⟨2790205609350322051484927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7440548291600858803959805 2790205609350322051484927)
                      ·
                        rfl

theorem cell23_5433906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_5433906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433906 prefixEnd_5433906 := by exact prefixLift 5433906
  have htrace : WordTrace (prefixWord ++ tailWord_5433906) baseStart_5433906 baseEnd_5433906 := by
    simpa [prefixWord, tailWord_5433906, baseEnd_5433906] using wordTrace_append hprefix tailTrace_5433906
  have hstable : (prefixWord ++ tailWord_5433906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433906).length < 2 ^ (prefixWord ++ tailWord_5433906).sum := by decide
  have hdescent : baseEnd_5433906 < baseStart_5433906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433929 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 3, 1, 8]
def baseStart_5433929 : Nat := 118140960795 + 5433929 * 2 ^ 59
def prefixEnd_5433929 : Nat := 4983230072969 + 3 ^ 40 * 5433929 * 2
def baseEnd_5433929 : Nat := 2790217419405375461497321

theorem tailTrace_5433929 : CollatzResearch.WordTrace tailWord_5433929 prefixEnd_5433929 2790217419405375461497321 := by
  unfold tailWord_5433929
  simp only [CollatzResearch.WordTrace]
  refine ⟨198191672730810749033176841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132127781820540499355451227 198191672730810749033176841)
  ·
    refine ⟨148643754548108061774882631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198191672730810749033176841 148643754548108061774882631)
    ·
      refine ⟨222965631822162092662323947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148643754548108061774882631 222965631822162092662323947)
      ·
        refine ⟨334448447733243138993485921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222965631822162092662323947 334448447733243138993485921)
        ·
          refine ⟨250836335799932354245114441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 334448447733243138993485921 250836335799932354245114441)
          ·
            refine ⟨188127251849949265683835831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250836335799932354245114441 188127251849949265683835831)
            ·
              refine ⟨282190877774923898525753747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188127251849949265683835831 282190877774923898525753747)
              ·
                refine ⟨423286316662385847788630621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 282190877774923898525753747 423286316662385847788630621)
                ·
                  refine ⟨158732368748394692920736483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 423286316662385847788630621 158732368748394692920736483)
                  ·
                    refine ⟨238098553122592039381104725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 158732368748394692920736483 238098553122592039381104725)
                    ·
                      refine ⟨2790217419405375461497321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 238098553122592039381104725 2790217419405375461497321)
                      ·
                        rfl

theorem cell23_5433929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 1, 8].length) (baseStart_5433929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433929 prefixEnd_5433929 := by exact prefixLift 5433929
  have htrace : WordTrace (prefixWord ++ tailWord_5433929) baseStart_5433929 baseEnd_5433929 := by
    simpa [prefixWord, tailWord_5433929, baseEnd_5433929] using wordTrace_append hprefix tailTrace_5433929
  have hstable : (prefixWord ++ tailWord_5433929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433929).length < 2 ^ (prefixWord ++ tailWord_5433929).sum := by decide
  have hdescent : baseEnd_5433929 < baseStart_5433929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433956 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 5, 5]
def baseStart_5433956 : Nat := 118140960795 + 5433956 * 2 ^ 59
def prefixEnd_5433956 : Nat := 4983230072969 + 3 ^ 40 * 5433956 * 2
def baseEnd_5433956 : Nat := 930077094461015618619899

theorem tailTrace_5433956 : CollatzResearch.WordTrace tailWord_5433956 prefixEnd_5433956 930077094461015618619899 := by
  unfold tailWord_5433956
  simp only [CollatzResearch.WordTrace]
  refine ⟨99096328750856466322204861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132128438334475288429606481 99096328750856466322204861)
  ·
    refine ⟨37161123281571174870826823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99096328750856466322204861 37161123281571174870826823)
    ·
      refine ⟨55741684922356762306240235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37161123281571174870826823 55741684922356762306240235)
      ·
        refine ⟨83612527383535143459360353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55741684922356762306240235 83612527383535143459360353)
        ·
          refine ⟨62709395537651357594520265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83612527383535143459360353 62709395537651357594520265)
          ·
            refine ⟨47032046653238518195890199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62709395537651357594520265 47032046653238518195890199)
            ·
              refine ⟨70548069979857777293835299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47032046653238518195890199 70548069979857777293835299)
              ·
                refine ⟨105822104969786665940752949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70548069979857777293835299 105822104969786665940752949)
                ·
                  refine ⟨9920822340917499931945589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105822104969786665940752949 9920822340917499931945589)
                  ·
                    refine ⟨930077094461015618619899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9920822340917499931945589 930077094461015618619899)
                    ·
                      rfl

theorem cell23_5433956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_5433956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433956 prefixEnd_5433956 := by exact prefixLift 5433956
  have htrace : WordTrace (prefixWord ++ tailWord_5433956) baseStart_5433956 baseEnd_5433956 := by
    simpa [prefixWord, tailWord_5433956, baseEnd_5433956] using wordTrace_append hprefix tailTrace_5433956
  have hstable : (prefixWord ++ tailWord_5433956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433956).length < 2 ^ (prefixWord ++ tailWord_5433956).sum := by decide
  have hdescent : baseEnd_5433956 < baseStart_5433956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433974 : List Nat := [5, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3]
def baseStart_5433974 : Nat := 118140960795 + 5433974 * 2 ^ 59
def prefixEnd_5433974 : Nat := 4983230072969 + 3 ^ 40 * 5433974 * 2
def baseEnd_5433974 : Nat := 2790240526034827785434615

theorem tailTrace_5433974 : CollatzResearch.WordTrace tailWord_5433974 prefixEnd_5433974 2790240526034827785434615 := by
  unfold tailWord_5433974
  simp only [CollatzResearch.WordTrace]
  refine ⟨12387082125977982607410311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132128876010431814479043317 12387082125977982607410311)
  ·
    refine ⟨18580623188966973911115467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12387082125977982607410311 18580623188966973911115467)
    ·
      refine ⟨27870934783450460866673201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18580623188966973911115467 27870934783450460866673201)
      ·
        refine ⟨20903201087587845650004901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27870934783450460866673201 20903201087587845650004901)
        ·
          refine ⟨3919350203922721059375919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20903201087587845650004901 3919350203922721059375919)
          ·
            refine ⟨5879025305884081589063879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3919350203922721059375919 5879025305884081589063879)
            ·
              refine ⟨8818537958826122383595819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5879025305884081589063879 8818537958826122383595819)
              ·
                refine ⟨13227806938239183575393729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8818537958826122383595819 13227806938239183575393729)
                ·
                  refine ⟨9920855203679387681545297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13227806938239183575393729 9920855203679387681545297)
                  ·
                    refine ⟨7440641402759540761158973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9920855203679387681545297 7440641402759540761158973)
                    ·
                      refine ⟨2790240526034827785434615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7440641402759540761158973 2790240526034827785434615)
                      ·
                        rfl

theorem cell23_5433974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_5433974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433974 prefixEnd_5433974 := by exact prefixLift 5433974
  have htrace : WordTrace (prefixWord ++ tailWord_5433974) baseStart_5433974 baseEnd_5433974 := by
    simpa [prefixWord, tailWord_5433974, baseEnd_5433974] using wordTrace_append hprefix tailTrace_5433974
  have hstable : (prefixWord ++ tailWord_5433974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433974).length < 2 ^ (prefixWord ++ tailWord_5433974).sum := by decide
  have hdescent : baseEnd_5433974 < baseStart_5433974 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5433980 : List Nat := [2, 2, 2, 1, 1, 2, 5, 1, 2, 3, 2]
def baseStart_5433980 : Nat := 118140960795 + 5433980 * 2 ^ 59
def prefixEnd_5433980 : Nat := 4983230072969 + 3 ^ 40 * 5433980 * 2
def baseEnd_5433980 : Nat := 2790243606918754761959587

theorem tailTrace_5433980 : CollatzResearch.WordTrace tailWord_5433980 prefixEnd_5433980 2790243606918754761959587 := by
  unfold tailWord_5433980
  simp only [CollatzResearch.WordTrace]
  refine ⟨99096766426812992371641697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132129021902417323162188929 99096766426812992371641697)
  ·
    refine ⟨74322574820109744278731273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99096766426812992371641697 74322574820109744278731273)
    ·
      refine ⟨55741931115082308209048455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74322574820109744278731273 55741931115082308209048455)
      ·
        refine ⟨83612896672623462313572683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55741931115082308209048455 83612896672623462313572683)
        ·
          refine ⟨125419345008935193470359025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83612896672623462313572683 125419345008935193470359025)
          ·
            refine ⟨94064508756701395102769269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125419345008935193470359025 94064508756701395102769269)
            ·
              refine ⟨8818547695940755790884619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94064508756701395102769269 8818547695940755790884619)
              ·
                refine ⟨13227821543911133686326929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8818547695940755790884619 13227821543911133686326929)
                ·
                  refine ⟨9920866157933350264745197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13227821543911133686326929 9920866157933350264745197)
                  ·
                    refine ⟨3720324809225006349279449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9920866157933350264745197 3720324809225006349279449)
                    ·
                      refine ⟨2790243606918754761959587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3720324809225006349279449 2790243606918754761959587)
                      ·
                        rfl

theorem cell23_5433980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 2, 3, 2].length) (baseStart_5433980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5433980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5433980 prefixEnd_5433980 := by exact prefixLift 5433980
  have htrace : WordTrace (prefixWord ++ tailWord_5433980) baseStart_5433980 baseEnd_5433980 := by
    simpa [prefixWord, tailWord_5433980, baseEnd_5433980] using wordTrace_append hprefix tailTrace_5433980
  have hstable : (prefixWord ++ tailWord_5433980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5433980).length < 2 ^ (prefixWord ++ tailWord_5433980).sum := by decide
  have hdescent : baseEnd_5433980 < baseStart_5433980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5433980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5434004 : List Nat := [2, 4, 2, 2, 1, 1, 2, 4, 1, 1, 3]
def baseStart_5434004 : Nat := 118140960795 + 5434004 * 2 ^ 59
def prefixEnd_5434004 : Nat := 4983230072969 + 3 ^ 40 * 5434004 * 2
def baseEnd_5434004 : Nat := 2790255930454462668059477

theorem tailTrace_5434004 : CollatzResearch.WordTrace tailWord_5434004 prefixEnd_5434004 2790255930454462668059477 := by
  unfold tailWord_5434004
  simp only [CollatzResearch.WordTrace]
  refine ⟨99097204102769518421078533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132129605470359357894771377 99097204102769518421078533)
  ·
    refine ⟨18580725769269284703952225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99097204102769518421078533 18580725769269284703952225)
    ·
      refine ⟨13935544326951963527964169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18580725769269284703952225 13935544326951963527964169)
      ·
        refine ⟨10451658245213972645973127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13935544326951963527964169 10451658245213972645973127)
        ·
          refine ⟨15677487367820958968959691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10451658245213972645973127 15677487367820958968959691)
          ·
            refine ⟨23516231051731438453439537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15677487367820958968959691 23516231051731438453439537)
            ·
              refine ⟨17637173288798578840079653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23516231051731438453439537 17637173288798578840079653)
              ·
                refine ⟨3306969991649733532514935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17637173288798578840079653 3306969991649733532514935)
                ·
                  refine ⟨4960454987474600298772403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3306969991649733532514935 4960454987474600298772403)
                  ·
                    refine ⟨7440682481211900448158605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4960454987474600298772403 7440682481211900448158605)
                    ·
                      refine ⟨2790255930454462668059477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7440682481211900448158605 2790255930454462668059477)
                      ·
                        rfl

theorem cell23_5434004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_5434004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5434004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5434004 prefixEnd_5434004 := by exact prefixLift 5434004
  have htrace : WordTrace (prefixWord ++ tailWord_5434004) baseStart_5434004 baseEnd_5434004 := by
    simpa [prefixWord, tailWord_5434004, baseEnd_5434004] using wordTrace_append hprefix tailTrace_5434004
  have hstable : (prefixWord ++ tailWord_5434004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5434004).length < 2 ^ (prefixWord ++ tailWord_5434004).sum := by decide
  have hdescent : baseEnd_5434004 < baseStart_5434004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5434004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5434013 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 5, 2, 3]
def baseStart_5434013 : Nat := 118140960795 + 5434013 * 2 ^ 59
def prefixEnd_5434013 : Nat := 4983230072969 + 3 ^ 40 * 5434013 * 2
def baseEnd_5434013 : Nat := 2790260551780353132846935

theorem tailTrace_5434013 : CollatzResearch.WordTrace tailWord_5434013 prefixEnd_5434013 2790260551780353132846935 := by
  unfold tailWord_5434013
  simp only [CollatzResearch.WordTrace]
  refine ⟨198194736462506431379234693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132129824308337620919489795 198194736462506431379234693)
  ·
    refine ⟨37161513086719955883606505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198194736462506431379234693 37161513086719955883606505)
    ·
      refine ⟨27871134815039966912704879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37161513086719955883606505 27871134815039966912704879)
      ·
        refine ⟨41806702222559950369057319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27871134815039966912704879 41806702222559950369057319)
        ·
          refine ⟨62710053333839925553585979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41806702222559950369057319 62710053333839925553585979)
          ·
            refine ⟨94065080000759888330378969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62710053333839925553585979 94065080000759888330378969)
            ·
              refine ⟨70548810000569916247784227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94065080000759888330378969 70548810000569916247784227)
              ·
                refine ⟨105823215000854874371676341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70548810000569916247784227 105823215000854874371676341)
                ·
                  refine ⟨9920926406330144472344657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105823215000854874371676341 9920926406330144472344657)
                  ·
                    refine ⟨7440694804747608354258493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9920926406330144472344657 7440694804747608354258493)
                    ·
                      refine ⟨2790260551780353132846935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7440694804747608354258493 2790260551780353132846935)
                      ·
                        rfl

theorem cell23_5434013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_5434013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5434013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5434013 prefixEnd_5434013 := by exact prefixLift 5434013
  have htrace : WordTrace (prefixWord ++ tailWord_5434013) baseStart_5434013 baseEnd_5434013 := by
    simpa [prefixWord, tailWord_5434013, baseEnd_5434013] using wordTrace_append hprefix tailTrace_5434013
  have hstable : (prefixWord ++ tailWord_5434013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5434013).length < 2 ^ (prefixWord ++ tailWord_5434013).sum := by decide
  have hdescent : baseEnd_5434013 < baseStart_5434013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5434013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5434038 : List Nat := [5, 1, 3, 1, 2, 2, 1, 3, 1, 1, 3]
def baseStart_5434038 : Nat := 118140960795 + 5434038 * 2 ^ 59
def prefixEnd_5434038 : Nat := 4983230072969 + 3 ^ 40 * 5434038 * 2
def baseEnd_5434038 : Nat := 2790273388796715535034321

theorem tailTrace_5434038 : CollatzResearch.WordTrace tailWord_5434038 prefixEnd_5434038 2790273388796715535034321 := by
  unfold tailWord_5434038
  simp only [CollatzResearch.WordTrace]
  refine ⟨12387228017963491290555923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132130432191610573765929845 12387228017963491290555923)
  ·
    refine ⟨18580842026945236935833885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12387228017963491290555923 18580842026945236935833885)
    ·
      refine ⟨6967815760104463850937707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18580842026945236935833885 6967815760104463850937707)
      ·
        refine ⟨10451723640156695776406561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6967815760104463850937707 10451723640156695776406561)
        ·
          refine ⟨7838792730117521832304921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10451723640156695776406561 7838792730117521832304921)
          ·
            refine ⟨5879094547588141374228691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7838792730117521832304921 5879094547588141374228691)
            ·
              refine ⟨8818641821382212061343037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5879094547588141374228691 8818641821382212061343037)
              ·
                refine ⟨3306990683018329523003639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8818641821382212061343037 3306990683018329523003639)
                ·
                  refine ⟨4960486024527494284505459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3306990683018329523003639 4960486024527494284505459)
                  ·
                    refine ⟨7440729036791241426758189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4960486024527494284505459 7440729036791241426758189)
                    ·
                      refine ⟨2790273388796715535034321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7440729036791241426758189 2790273388796715535034321)
                      ·
                        rfl

theorem cell23_5434038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_5434038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5434038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5434038 prefixEnd_5434038 := by exact prefixLift 5434038
  have htrace : WordTrace (prefixWord ++ tailWord_5434038) baseStart_5434038 baseEnd_5434038 := by
    simpa [prefixWord, tailWord_5434038, baseEnd_5434038] using wordTrace_append hprefix tailTrace_5434038
  have hstable : (prefixWord ++ tailWord_5434038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5434038).length < 2 ^ (prefixWord ++ tailWord_5434038).sum := by decide
  have hdescent : baseEnd_5434038 < baseStart_5434038 := by decide
  rcases family_descends (prefixWord ++ tailWord_5434038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5434113 : List Nat := [1, 2, 4, 1, 1, 1, 1, 4, 2, 2, 4]
def baseStart_5434113 : Nat := 118140960795 + 5434113 * 2 ^ 59
def prefixEnd_5434113 : Nat := 4983230072969 + 3 ^ 40 * 5434113 * 2
def baseEnd_5434113 : Nat := 2790311899845802741596475

theorem tailTrace_5434113 : CollatzResearch.WordTrace tailWord_5434113 prefixEnd_5434113 2790311899845802741596475 := by
  unfold tailWord_5434113
  simp only [CollatzResearch.WordTrace]
  refine ⟨198198383762144148457874993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132132255841429432305249995 198198383762144148457874993)
  ·
    refine ⟨148648787821608111343406245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198198383762144148457874993 148648787821608111343406245)
    ·
      refine ⟨27871647716551520876888671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148648787821608111343406245 27871647716551520876888671)
      ·
        refine ⟨41807471574827281315333007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27871647716551520876888671 41807471574827281315333007)
        ·
          refine ⟨62711207362240921972999511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41807471574827281315333007 62711207362240921972999511)
          ·
            refine ⟨94066811043361382959499267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62711207362240921972999511 94066811043361382959499267)
            ·
              refine ⟨141100216565042074439248901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94066811043361382959499267 141100216565042074439248901)
              ·
                refine ⟨26456290605945388957359169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 141100216565042074439248901 26456290605945388957359169)
                ·
                  refine ⟨19842217954459041718019377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26456290605945388957359169 19842217954459041718019377)
                  ·
                    refine ⟨14881663465844281288514533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19842217954459041718019377 14881663465844281288514533)
                    ·
                      refine ⟨2790311899845802741596475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14881663465844281288514533 2790311899845802741596475)
                      ·
                        rfl

theorem cell23_5434113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_5434113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5434113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5434113 prefixEnd_5434113 := by exact prefixLift 5434113
  have htrace : WordTrace (prefixWord ++ tailWord_5434113) baseStart_5434113 baseEnd_5434113 := by
    simpa [prefixWord, tailWord_5434113, baseEnd_5434113] using wordTrace_append hprefix tailTrace_5434113
  have hstable : (prefixWord ++ tailWord_5434113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5434113).length < 2 ^ (prefixWord ++ tailWord_5434113).sum := by decide
  have hdescent : baseEnd_5434113 < baseStart_5434113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5434113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5434213 : List Nat := [1, 3, 1, 3, 1, 1, 3, 2, 8]
def baseStart_5434213 : Nat := 118140960795 + 5434213 * 2 ^ 59
def prefixEnd_5434213 : Nat := 4983230072969 + 3 ^ 40 * 5434213 * 2
def baseEnd_5434213 : Nat := 310040360879028038927335

theorem tailTrace_5434213 : CollatzResearch.WordTrace tailWord_5434213 prefixEnd_5434213 310040360879028038927335 := by
  unfold tailWord_5434213
  simp only [CollatzResearch.WordTrace]
  refine ⟨198202031061781865536515293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132134687374521243691010195 198202031061781865536515293)
  ·
    refine ⟨74325761648168199576193235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198202031061781865536515293 74325761648168199576193235)
    ·
      refine ⟨111488642472252299364289853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74325761648168199576193235 111488642472252299364289853)
      ·
        refine ⟨41808240927094612261608695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111488642472252299364289853 41808240927094612261608695)
        ·
          refine ⟨62712361390641918392413043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41808240927094612261608695 62712361390641918392413043)
          ·
            refine ⟨94068542085962877588619565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62712361390641918392413043 94068542085962877588619565)
            ·
              refine ⟨35275703282236079095732337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94068542085962877588619565 35275703282236079095732337)
              ·
                refine ⟨26456777461677059321799253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35275703282236079095732337 26456777461677059321799253)
                ·
                  refine ⟨310040360879028038927335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26456777461677059321799253 310040360879028038927335)
                  ·
                    rfl

theorem cell23_5434213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 8].length) (baseStart_5434213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5434213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5434213 prefixEnd_5434213 := by exact prefixLift 5434213
  have htrace : WordTrace (prefixWord ++ tailWord_5434213) baseStart_5434213 baseEnd_5434213 := by
    simpa [prefixWord, tailWord_5434213, baseEnd_5434213] using wordTrace_append hprefix tailTrace_5434213
  have hstable : (prefixWord ++ tailWord_5434213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5434213).length < 2 ^ (prefixWord ++ tailWord_5434213).sum := by decide
  have hdescent : baseEnd_5434213 < baseStart_5434213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5434213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5434247 : List Nat := [1, 1, 4, 2, 3, 1, 4, 1, 6]
def baseStart_5434247 : Nat := 118140960795 + 5434247 * 2 ^ 59
def prefixEnd_5434247 : Nat := 4983230072969 + 3 ^ 40 * 5434247 * 2
def baseEnd_5434247 : Nat := 310042300694833913035651

theorem tailTrace_5434247 : CollatzResearch.WordTrace tailWord_5434247 prefixEnd_5434247 310042300694833913035651 := by
  unfold tailWord_5434247
  simp only [CollatzResearch.WordTrace]
  refine ⟨198203271143658689343252995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132135514095772459562168663 198203271143658689343252995)
  ·
    refine ⟨297304906715488034014879493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198203271143658689343252995 297304906715488034014879493)
    ·
      refine ⟨55744670009154006377789905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 297304906715488034014879493 55744670009154006377789905)
      ·
        refine ⟨41808502506865504783342429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55744670009154006377789905 41808502506865504783342429)
        ·
          refine ⟨15678188440074564293753411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41808502506865504783342429 15678188440074564293753411)
          ·
            refine ⟨23517282660111846440630117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15678188440074564293753411 23517282660111846440630117)
            ·
              refine ⟨4409490498770971207618147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23517282660111846440630117 4409490498770971207618147)
              ·
                refine ⟨6614235748156456811427221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4409490498770971207618147 6614235748156456811427221)
                ·
                  refine ⟨310042300694833913035651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6614235748156456811427221 310042300694833913035651)
                  ·
                    rfl

theorem cell23_5434247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 6].length) (baseStart_5434247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5434247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5434247 prefixEnd_5434247 := by exact prefixLift 5434247
  have htrace : WordTrace (prefixWord ++ tailWord_5434247) baseStart_5434247 baseEnd_5434247 := by
    simpa [prefixWord, tailWord_5434247, baseEnd_5434247] using wordTrace_append hprefix tailTrace_5434247
  have hstable : (prefixWord ++ tailWord_5434247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5434247).length < 2 ^ (prefixWord ++ tailWord_5434247).sum := by decide
  have hdescent : baseEnd_5434247 < baseStart_5434247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5434247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5434285 : List Nat := [1, 5, 2, 3, 1, 2, 2, 2, 1, 4]
def baseStart_5434285 : Nat := 118140960795 + 5434285 * 2 ^ 59
def prefixEnd_5434285 : Nat := 4983230072969 + 3 ^ 40 * 5434285 * 2
def baseEnd_5434285 : Nat := 930133406172792022881895

theorem tailTrace_5434285 : CollatzResearch.WordTrace tailWord_5434285 prefixEnd_5434285 930133406172792022881895 := by
  unfold tailWord_5434285
  simp only [CollatzResearch.WordTrace]
  refine ⟨198204657117521021833136309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132136438078347347888757539 198204657117521021833136309)
  ·
    refine ⟨18581686604767595796856529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 198204657117521021833136309 18581686604767595796856529)
    ·
      refine ⟨13936264953575696847642397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18581686604767595796856529 13936264953575696847642397)
      ·
        refine ⟨5226099357590886317865899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13936264953575696847642397 5226099357590886317865899)
        ·
          refine ⟨7839149036386329476798849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5226099357590886317865899 7839149036386329476798849)
          ·
            refine ⟨5879361777289747107599137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7839149036386329476798849 5879361777289747107599137)
            ·
              refine ⟨4409521332967310330699353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5879361777289747107599137 4409521332967310330699353)
              ·
                refine ⟨3307140999725482748024515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4409521332967310330699353 3307140999725482748024515)
                ·
                  refine ⟨4960711499588224122036773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3307140999725482748024515 4960711499588224122036773)
                  ·
                    refine ⟨930133406172792022881895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4960711499588224122036773 930133406172792022881895)
                    ·
                      rfl

theorem cell23_5434285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_5434285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5434285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5434285 prefixEnd_5434285 := by exact prefixLift 5434285
  have htrace : WordTrace (prefixWord ++ tailWord_5434285) baseStart_5434285 baseEnd_5434285 := by
    simpa [prefixWord, tailWord_5434285, baseEnd_5434285] using wordTrace_append hprefix tailTrace_5434285
  have hstable : (prefixWord ++ tailWord_5434285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5434285).length < 2 ^ (prefixWord ++ tailWord_5434285).sum := by decide
  have hdescent : baseEnd_5434285 < baseStart_5434285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5434285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5434303 : List Nat := [1, 1, 2, 2, 2, 1, 2, 12]
def baseStart_5434303 : Nat := 118140960795 + 5434303 * 2 ^ 59
def prefixEnd_5434303 : Nat := 4983230072969 + 3 ^ 40 * 5434303 * 2
def baseEnd_5434303 : Nat := 103348498561857666600763

theorem tailTrace_5434303 : CollatzResearch.WordTrace tailWord_5434303 prefixEnd_5434303 103348498561857666600763 := by
  unfold tailWord_5434303
  simp only [CollatzResearch.WordTrace]
  refine ⟨198205313631455810907291563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132136875754303873938194375 198205313631455810907291563)
  ·
    refine ⟨297307970447183716360937345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198205313631455810907291563 297307970447183716360937345)
    ·
      refine ⟨222980977835387787270703009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297307970447183716360937345 222980977835387787270703009)
      ·
        refine ⟨167235733376540840453027257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222980977835387787270703009 167235733376540840453027257)
        ·
          refine ⟨125426800032405630339770443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167235733376540840453027257 125426800032405630339770443)
          ·
            refine ⟨188140200048608445509655665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125426800032405630339770443 188140200048608445509655665)
            ·
              refine ⟨141105150036456334132241749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188140200048608445509655665 141105150036456334132241749)
              ·
                refine ⟨103348498561857666600763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 141105150036456334132241749 103348498561857666600763)
                ·
                  rfl

theorem cell23_5434303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 12].length) (baseStart_5434303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5434303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5434303 prefixEnd_5434303 := by exact prefixLift 5434303
  have htrace : WordTrace (prefixWord ++ tailWord_5434303) baseStart_5434303 baseEnd_5434303 := by
    simpa [prefixWord, tailWord_5434303, baseEnd_5434303] using wordTrace_append hprefix tailTrace_5434303
  have hstable : (prefixWord ++ tailWord_5434303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5434303).length < 2 ^ (prefixWord ++ tailWord_5434303).sum := by decide
  have hdescent : baseEnd_5434303 < baseStart_5434303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5434303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5434364 : List Nat := [2, 2, 2, 1, 2, 5, 1, 1, 1, 3, 3]
def baseStart_5434364 : Nat := 118140960795 + 5434364 * 2 ^ 59
def prefixEnd_5434364 : Nat := 4983230072969 + 3 ^ 40 * 5434364 * 2
def baseEnd_5434364 : Nat := 2790440783490081259557821

theorem tailTrace_5434364 : CollatzResearch.WordTrace tailWord_5434364 prefixEnd_5434364 2790440783490081259557821 := by
  unfold tailWord_5434364
  simp only [CollatzResearch.WordTrace]
  refine ⟨99103769242117409162631073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132138358989489878883508097 99103769242117409162631073)
  ·
    refine ⟨74327826931588056871973305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99103769242117409162631073 74327826931588056871973305)
    ·
      refine ⟨55745870198691042653979979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74327826931588056871973305 55745870198691042653979979)
      ·
        refine ⟨83618805298036563980969969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55745870198691042653979979 83618805298036563980969969)
        ·
          refine ⟨62714103973527422985727477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83618805298036563980969969 62714103973527422985727477)
          ·
            refine ⟨5879447247518195904911951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62714103973527422985727477 5879447247518195904911951)
            ·
              refine ⟨8819170871277293857367927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5879447247518195904911951 8819170871277293857367927)
              ·
                refine ⟨13228756306915940786051891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8819170871277293857367927 13228756306915940786051891)
                ·
                  refine ⟨19843134460373911179077837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13228756306915940786051891 19843134460373911179077837)
                  ·
                    refine ⟨7441175422640216692154189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19843134460373911179077837 7441175422640216692154189)
                    ·
                      refine ⟨2790440783490081259557821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7441175422640216692154189 2790440783490081259557821)
                      ·
                        rfl

theorem cell23_5434364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 1, 3, 3].length) (baseStart_5434364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5434364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5434364 prefixEnd_5434364 := by exact prefixLift 5434364
  have htrace : WordTrace (prefixWord ++ tailWord_5434364) baseStart_5434364 baseEnd_5434364 := by
    simpa [prefixWord, tailWord_5434364, baseEnd_5434364] using wordTrace_append hprefix tailTrace_5434364
  have hstable : (prefixWord ++ tailWord_5434364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5434364).length < 2 ^ (prefixWord ++ tailWord_5434364).sum := by decide
  have hdescent : baseEnd_5434364 < baseStart_5434364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5434364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5434387 : List Nat := [1, 1, 1, 2, 1, 4, 1, 3, 3, 4, 2]
def baseStart_5434387 : Nat := 118140960795 + 5434387 * 2 ^ 59
def prefixEnd_5434387 : Nat := 4983230072969 + 3 ^ 40 * 5434387 * 2
def baseEnd_5434387 : Nat := 2790452593545134669570215

theorem tailTrace_5434387 : CollatzResearch.WordTrace tailWord_5434387 prefixEnd_5434387 2790452593545134669570215 := by
  unfold tailWord_5434387
  simp only [CollatzResearch.WordTrace]
  refine ⟨198208377363151493253349415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132138918242100995502232943 198208377363151493253349415)
  ·
    refine ⟨297312566044727239880024123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198208377363151493253349415 297312566044727239880024123)
    ·
      refine ⟨445968849067090859820036185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297312566044727239880024123 445968849067090859820036185)
      ·
        refine ⟨334476636800318144865027139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 445968849067090859820036185 334476636800318144865027139)
        ·
          refine ⟨501714955200477217297540709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334476636800318144865027139 501714955200477217297540709)
          ·
            refine ⟨94071554100089478243288883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 501714955200477217297540709 94071554100089478243288883)
            ·
              refine ⟨141107331150134217364933325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94071554100089478243288883 141107331150134217364933325)
              ·
                refine ⟨52915249181300331511849997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141107331150134217364933325 52915249181300331511849997)
                ·
                  refine ⟨19843218442987624316943749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52915249181300331511849997 19843218442987624316943749)
                  ·
                    refine ⟨3720603458060179559426953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19843218442987624316943749 3720603458060179559426953)
                    ·
                      refine ⟨2790452593545134669570215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3720603458060179559426953 2790452593545134669570215)
                      ·
                        rfl

theorem cell23_5434387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 4, 2].length) (baseStart_5434387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5434387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5434387 prefixEnd_5434387 := by exact prefixLift 5434387
  have htrace : WordTrace (prefixWord ++ tailWord_5434387) baseStart_5434387 baseEnd_5434387 := by
    simpa [prefixWord, tailWord_5434387, baseEnd_5434387] using wordTrace_append hprefix tailTrace_5434387
  have hstable : (prefixWord ++ tailWord_5434387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5434387).length < 2 ^ (prefixWord ++ tailWord_5434387).sum := by decide
  have hdescent : baseEnd_5434387 < baseStart_5434387 := by decide
  rcases family_descends (prefixWord ++ tailWord_5434387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5434391 : List Nat := [1, 1, 3, 5, 1, 1, 2, 3, 1, 3, 2]
def baseStart_5434391 : Nat := 118140960795 + 5434391 * 2 ^ 59
def prefixEnd_5434391 : Nat := 4983230072969 + 3 ^ 40 * 5434391 * 2
def baseEnd_5434391 : Nat := 2790454647467752653920197

theorem tailTrace_5434391 : CollatzResearch.WordTrace tailWord_5434391 prefixEnd_5434391 2790454647467752653920197 := by
  unfold tailWord_5434391
  simp only [CollatzResearch.WordTrace]
  refine ⟨198208523255137001936495027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132139015503424667957663351 198208523255137001936495027)
  ·
    refine ⟨297312784882705502904742541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198208523255137001936495027 297312784882705502904742541)
    ·
      refine ⟨111492294331014563589278453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 297312784882705502904742541 111492294331014563589278453)
      ·
        refine ⟨10452402593532615336494855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111492294331014563589278453 10452402593532615336494855)
        ·
          refine ⟨15678603890298923004742283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10452402593532615336494855 15678603890298923004742283)
          ·
            refine ⟨23517905835448384507113425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15678603890298923004742283 23517905835448384507113425)
            ·
              refine ⟨17638429376586288380335069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23517905835448384507113425 17638429376586288380335069)
              ·
                refine ⟨6614411016219858142625651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17638429376586288380335069 6614411016219858142625651)
                ·
                  refine ⟨9921616524329787213938477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6614411016219858142625651 9921616524329787213938477)
                  ·
                    refine ⟨3720606196623670205226929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9921616524329787213938477 3720606196623670205226929)
                    ·
                      refine ⟨2790454647467752653920197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3720606196623670205226929 2790454647467752653920197)
                      ·
                        rfl

theorem cell23_5434391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_5434391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5434391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5434391 prefixEnd_5434391 := by exact prefixLift 5434391
  have htrace : WordTrace (prefixWord ++ tailWord_5434391) baseStart_5434391 baseEnd_5434391 := by
    simpa [prefixWord, tailWord_5434391, baseEnd_5434391] using wordTrace_append hprefix tailTrace_5434391
  have hstable : (prefixWord ++ tailWord_5434391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5434391).length < 2 ^ (prefixWord ++ tailWord_5434391).sum := by decide
  have hdescent : baseEnd_5434391 < baseStart_5434391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5434391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5434438 : List Nat := [6, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2]
def baseStart_5434438 : Nat := 118140960795 + 5434438 * 2 ^ 59
def prefixEnd_5434438 : Nat := 4983230072969 + 3 ^ 40 * 5434438 * 2
def baseEnd_5434438 : Nat := 2790478781058513970032481

theorem tailTrace_5434438 : CollatzResearch.WordTrace tailWord_5434438 prefixEnd_5434438 2790478781058513970032481 := by
  unfold tailWord_5434438
  simp only [CollatzResearch.WordTrace]
  refine ⟨6194069921436460280107999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 132140158323977819308970645 6194069921436460280107999)
  ·
    refine ⟨9291104882154690420161999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6194069921436460280107999 9291104882154690420161999)
    ·
      refine ⟨13936657323232035630242999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9291104882154690420161999 13936657323232035630242999)
      ·
        refine ⟨20904985984848053445364499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13936657323232035630242999 20904985984848053445364499)
        ·
          refine ⟨31357478977272080168046749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20904985984848053445364499 31357478977272080168046749)
          ·
            refine ⟨11759054616477030063017531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31357478977272080168046749 11759054616477030063017531)
            ·
              refine ⟨17638581924715545094526297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11759054616477030063017531 17638581924715545094526297)
              ·
                refine ⟨13228936443536658820894723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17638581924715545094526297 13228936443536658820894723)
                ·
                  refine ⟨19843404665304988231342085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13228936443536658820894723 19843404665304988231342085)
                  ·
                    refine ⟨3720638374744685293376641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19843404665304988231342085 3720638374744685293376641)
                    ·
                      refine ⟨2790478781058513970032481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3720638374744685293376641 2790478781058513970032481)
                      ·
                        rfl

theorem cell23_5434438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_5434438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5434438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5434438 prefixEnd_5434438 := by exact prefixLift 5434438
  have htrace : WordTrace (prefixWord ++ tailWord_5434438) baseStart_5434438 baseEnd_5434438 := by
    simpa [prefixWord, tailWord_5434438, baseEnd_5434438] using wordTrace_append hprefix tailTrace_5434438
  have hstable : (prefixWord ++ tailWord_5434438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5434438).length < 2 ^ (prefixWord ++ tailWord_5434438).sum := by decide
  have hdescent : baseEnd_5434438 < baseStart_5434438 := by decide
  rcases family_descends (prefixWord ++ tailWord_5434438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5434447 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 3, 7, 2]
def baseStart_5434447 : Nat := 118140960795 + 5434447 * 2 ^ 59
def prefixEnd_5434447 : Nat := 4983230072969 + 3 ^ 40 * 5434447 * 2
def baseEnd_5434447 : Nat := 2790483402384404434819939

theorem tailTrace_5434447 : CollatzResearch.WordTrace tailWord_5434447 prefixEnd_5434447 2790483402384404434819939 := by
  unfold tailWord_5434447
  simp only [CollatzResearch.WordTrace]
  refine ⟨198210565742934123500533595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132140377161956082333689063 198210565742934123500533595)
  ·
    refine ⟨297315848614401185250800393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198210565742934123500533595 297315848614401185250800393)
    ·
      refine ⟨222986886460800888938100295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297315848614401185250800393 222986886460800888938100295)
      ·
        refine ⟨334480329691201333407150443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222986886460800888938100295 334480329691201333407150443)
        ·
          refine ⟨501720494536802000110725665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334480329691201333407150443 501720494536802000110725665)
          ·
            refine ⟨376290370902601500083044249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 501720494536802000110725665 376290370902601500083044249)
            ·
              refine ⟨282217778176951125062283187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 376290370902601500083044249 282217778176951125062283187)
              ·
                refine ⟨423326667265426687593424781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 282217778176951125062283187 423326667265426687593424781)
                ·
                  refine ⟨158747500224535007847534293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 423326667265426687593424781 158747500224535007847534293)
                  ·
                    refine ⟨3720644536512539246426585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 158747500224535007847534293 3720644536512539246426585)
                    ·
                      refine ⟨2790483402384404434819939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3720644536512539246426585 2790483402384404434819939)
                      ·
                        rfl

theorem cell23_5434447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 7, 2].length) (baseStart_5434447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5434447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5434447 prefixEnd_5434447 := by exact prefixLift 5434447
  have htrace : WordTrace (prefixWord ++ tailWord_5434447) baseStart_5434447 baseEnd_5434447 := by
    simpa [prefixWord, tailWord_5434447, baseEnd_5434447] using wordTrace_append hprefix tailTrace_5434447
  have hstable : (prefixWord ++ tailWord_5434447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5434447).length < 2 ^ (prefixWord ++ tailWord_5434447).sum := by decide
  have hdescent : baseEnd_5434447 < baseStart_5434447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5434447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5434517 : List Nat := [1, 3, 2, 1, 1, 1, 2, 6, 6]
def baseStart_5434517 : Nat := 118140960795 + 5434517 * 2 ^ 59
def prefixEnd_5434517 : Nat := 4983230072969 + 3 ^ 40 * 5434517 * 2
def baseEnd_5434517 : Nat := 310057705114468795660513

theorem tailTrace_5434517 : CollatzResearch.WordTrace tailWord_5434517 prefixEnd_5434517 310057705114468795660513 := by
  unfold tailWord_5434517
  simp only [CollatzResearch.WordTrace]
  refine ⟨198213118852680525455581805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132142079235120350303721203 198213118852680525455581805)
  ·
    refine ⟨74329919569755197045843177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198213118852680525455581805 74329919569755197045843177)
    ·
      refine ⟨55747439677316397784382383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74329919569755197045843177 55747439677316397784382383)
      ·
        refine ⟨83621159515974596676573575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55747439677316397784382383 83621159515974596676573575)
        ·
          refine ⟨125431739273961895014860363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83621159515974596676573575 125431739273961895014860363)
          ·
            refine ⟨188147608910942842522290545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125431739273961895014860363 188147608910942842522290545)
            ·
              refine ⟨141110706683207131891717909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188147608910942842522290545 141110706683207131891717909)
              ·
                refine ⟨6614564375775334307424277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 141110706683207131891717909 6614564375775334307424277)
                ·
                  refine ⟨310057705114468795660513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6614564375775334307424277 310057705114468795660513)
                  ·
                    rfl

theorem cell23_5434517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 6].length) (baseStart_5434517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5434517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5434517 prefixEnd_5434517 := by exact prefixLift 5434517
  have htrace : WordTrace (prefixWord ++ tailWord_5434517) baseStart_5434517 baseEnd_5434517 := by
    simpa [prefixWord, tailWord_5434517, baseEnd_5434517] using wordTrace_append hprefix tailTrace_5434517
  have hstable : (prefixWord ++ tailWord_5434517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5434517).length < 2 ^ (prefixWord ++ tailWord_5434517).sum := by decide
  have hdescent : baseEnd_5434517 < baseStart_5434517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5434517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5434547 : List Nat := [1, 1, 1, 2, 3, 2, 2, 3, 3, 5]
def baseStart_5434547 : Nat := 118140960795 + 5434547 * 2 ^ 59
def prefixEnd_5434547 : Nat := 4983230072969 + 3 ^ 40 * 5434547 * 2
def baseEnd_5434547 : Nat := 930178250149951347856493

theorem tailTrace_5434547 : CollatzResearch.WordTrace tailWord_5434547 prefixEnd_5434547 930178250149951347856493 := by
  unfold tailWord_5434547
  simp only [CollatzResearch.WordTrace]
  refine ⟨198214213042571840579173895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132142808695047893719449263 198214213042571840579173895)
  ·
    refine ⟨297321319563857760868760843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198214213042571840579173895 297321319563857760868760843)
    ·
      refine ⟨445981979345786641303141265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297321319563857760868760843 445981979345786641303141265)
      ·
        refine ⟨334486484509339980977355949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 445981979345786641303141265 334486484509339980977355949)
        ·
          refine ⟨125432431691002492866508481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 334486484509339980977355949 125432431691002492866508481)
          ·
            refine ⟨94074323768251869649881361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125432431691002492866508481 94074323768251869649881361)
            ·
              refine ⟨70555742826188902237411021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94074323768251869649881361 70555742826188902237411021)
              ·
                refine ⟨26458403559820838339029133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70555742826188902237411021 26458403559820838339029133)
                ·
                  refine ⟨9921901334932814377135925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26458403559820838339029133 9921901334932814377135925)
                  ·
                    refine ⟨930178250149951347856493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9921901334932814377135925 930178250149951347856493)
                    ·
                      rfl

theorem cell23_5434547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 5].length) (baseStart_5434547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5434547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5434547 prefixEnd_5434547 := by exact prefixLift 5434547
  have htrace : WordTrace (prefixWord ++ tailWord_5434547) baseStart_5434547 baseEnd_5434547 := by
    simpa [prefixWord, tailWord_5434547, baseEnd_5434547] using wordTrace_append hprefix tailTrace_5434547
  have hstable : (prefixWord ++ tailWord_5434547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5434547).length < 2 ^ (prefixWord ++ tailWord_5434547).sum := by decide
  have hdescent : baseEnd_5434547 < baseStart_5434547 := by decide
  rcases family_descends (prefixWord ++ tailWord_5434547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5434628 : List Nat := [2, 3, 2, 2, 2, 2, 2, 2, 2, 4]
def baseStart_5434628 : Nat := 118140960795 + 5434628 * 2 ^ 59
def prefixEnd_5434628 : Nat := 4983230072969 + 3 ^ 40 * 5434628 * 2
def baseEnd_5434628 : Nat := 930192114127622742218869

theorem tailTrace_5434628 : CollatzResearch.WordTrace tailWord_5434628 prefixEnd_5434628 930192114127622742218869 := by
  unfold tailWord_5434628
  simp only [CollatzResearch.WordTrace]
  refine ⟨99108583677639195706436269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132144778236852260941915025 99108583677639195706436269)
  ·
    refine ⟨37165718879114698389913601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99108583677639195706436269 37165718879114698389913601)
    ·
      refine ⟨27874289159336023792435201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37165718879114698389913601 27874289159336023792435201)
      ·
        refine ⟨20905716869502017844326401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27874289159336023792435201 20905716869502017844326401)
        ·
          refine ⟨15679287652126513383244801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20905716869502017844326401 15679287652126513383244801)
          ·
            refine ⟨11759465739094885037433601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15679287652126513383244801 11759465739094885037433601)
            ·
              refine ⟨8819599304321163778075201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11759465739094885037433601 8819599304321163778075201)
              ·
                refine ⟨6614699478240872833556401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8819599304321163778075201 6614699478240872833556401)
                ·
                  refine ⟨4961024608680654625167301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6614699478240872833556401 4961024608680654625167301)
                  ·
                    refine ⟨930192114127622742218869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4961024608680654625167301 930192114127622742218869)
                    ·
                      rfl

theorem cell23_5434628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_5434628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5434628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5434628 prefixEnd_5434628 := by exact prefixLift 5434628
  have htrace : WordTrace (prefixWord ++ tailWord_5434628) baseStart_5434628 baseEnd_5434628 := by
    simpa [prefixWord, tailWord_5434628, baseEnd_5434628] using wordTrace_append hprefix tailTrace_5434628
  have hstable : (prefixWord ++ tailWord_5434628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5434628).length < 2 ^ (prefixWord ++ tailWord_5434628).sum := by decide
  have hdescent : baseEnd_5434628 < baseStart_5434628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5434628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5434634 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3]
def baseStart_5434634 : Nat := 118140960795 + 5434634 * 2 ^ 59
def prefixEnd_5434634 : Nat := 4983230072969 + 3 ^ 40 * 5434634 * 2
def baseEnd_5434634 : Nat := 2790579423266795203181579

theorem tailTrace_5434634 : CollatzResearch.WordTrace tailWord_5434634 prefixEnd_5434634 2790579423266795203181579 := by
  unfold tailWord_5434634
  simp only [CollatzResearch.WordTrace]
  refine ⟨49554346548314163609397739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132144924128837769625060637 49554346548314163609397739)
  ·
    refine ⟨74331519822471245414096609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49554346548314163609397739 74331519822471245414096609)
    ·
      refine ⟨55748639866853434060572457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74331519822471245414096609 55748639866853434060572457)
      ·
        refine ⟨41811479900140075545429343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55748639866853434060572457 41811479900140075545429343)
        ·
          refine ⟨62717219850210113318144015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41811479900140075545429343 62717219850210113318144015)
          ·
            refine ⟨94075829775315169977216023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62717219850210113318144015 94075829775315169977216023)
            ·
              refine ⟨141113744662972754965824035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94075829775315169977216023 141113744662972754965824035)
              ·
                refine ⟨211670616994459132448736053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141113744662972754965824035 211670616994459132448736053)
                ·
                  refine ⟨19844120343230543667069005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 211670616994459132448736053 19844120343230543667069005)
                  ·
                    refine ⟨7441545128711453875150877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19844120343230543667069005 7441545128711453875150877)
                    ·
                      refine ⟨2790579423266795203181579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7441545128711453875150877 2790579423266795203181579)
                      ·
                        rfl

theorem cell23_5434634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_5434634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5434634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5434634 prefixEnd_5434634 := by exact prefixLift 5434634
  have htrace : WordTrace (prefixWord ++ tailWord_5434634) baseStart_5434634 baseEnd_5434634 := by
    simpa [prefixWord, tailWord_5434634, baseEnd_5434634] using wordTrace_append hprefix tailTrace_5434634
  have hstable : (prefixWord ++ tailWord_5434634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5434634).length < 2 ^ (prefixWord ++ tailWord_5434634).sum := by decide
  have hdescent : baseEnd_5434634 < baseStart_5434634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5434634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5434635 : List Nat := [1, 1, 1, 1, 5, 4, 1, 4, 1, 2, 2]
def baseStart_5434635 : Nat := 118140960795 + 5434635 * 2 ^ 59
def prefixEnd_5434635 : Nat := 4983230072969 + 3 ^ 40 * 5434635 * 2
def baseEnd_5434635 : Nat := 2790579936747449699269075

theorem tailTrace_5434635 : CollatzResearch.WordTrace tailWord_5434635 prefixEnd_5434635 2790579936747449699269075 := by
  unfold tailWord_5434635
  simp only [CollatzResearch.WordTrace]
  refine ⟨198217422666253031608377359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132144948444168687738918239 198217422666253031608377359)
  ·
    refine ⟨297326133999379547412566039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198217422666253031608377359 297326133999379547412566039)
    ·
      refine ⟨445989200999069321118849059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297326133999379547412566039 445989200999069321118849059)
      ·
        refine ⟨668983801498603981678273589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 445989200999069321118849059 668983801498603981678273589)
        ·
          refine ⟨62717231390494123282338149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 668983801498603981678273589 62717231390494123282338149)
          ·
            refine ⟨11759480885717648115438403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62717231390494123282338149 11759480885717648115438403)
            ·
              refine ⟨17639221328576472173157605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11759480885717648115438403 17639221328576472173157605)
              ·
                refine ⟨3307353999108088532467051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17639221328576472173157605 3307353999108088532467051)
                ·
                  refine ⟨4961030998662132798700577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3307353999108088532467051 4961030998662132798700577)
                  ·
                    refine ⟨3720773248996599599025433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4961030998662132798700577 3720773248996599599025433)
                    ·
                      refine ⟨2790579936747449699269075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3720773248996599599025433 2790579936747449699269075)
                      ·
                        rfl

theorem cell23_5434635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 4, 1, 2, 2].length) (baseStart_5434635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5434635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5434635 prefixEnd_5434635 := by exact prefixLift 5434635
  have htrace : WordTrace (prefixWord ++ tailWord_5434635) baseStart_5434635 baseEnd_5434635 := by
    simpa [prefixWord, tailWord_5434635, baseEnd_5434635] using wordTrace_append hprefix tailTrace_5434635
  have hstable : (prefixWord ++ tailWord_5434635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5434635).length < 2 ^ (prefixWord ++ tailWord_5434635).sum := by decide
  have hdescent : baseEnd_5434635 < baseStart_5434635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5434635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5434669 : List Nat := [1, 5, 3, 1, 1, 2, 2, 3, 1, 2, 2]
def baseStart_5434669 : Nat := 118140960795 + 5434669 * 2 ^ 59
def prefixEnd_5434669 : Nat := 4983230072969 + 3 ^ 40 * 5434669 * 2
def baseEnd_5434669 : Nat := 2790597395089702566243919

theorem tailTrace_5434669 : CollatzResearch.WordTrace tailWord_5434669 prefixEnd_5434669 2790597395089702566243919 := by
  unfold tailWord_5434669
  simp only [CollatzResearch.WordTrace]
  refine ⟨198218662748129855415115061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132145775165419903610076707 198218662748129855415115061)
  ·
    refine ⟨18582999632637173945167037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 198218662748129855415115061 18582999632637173945167037)
    ·
      refine ⟨6968624862238940229437639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18582999632637173945167037 6968624862238940229437639)
      ·
        refine ⟨10452937293358410344156459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6968624862238940229437639 10452937293358410344156459)
        ·
          refine ⟨15679405940037615516234689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10452937293358410344156459 15679405940037615516234689)
          ·
            refine ⟨11759554455028211637176017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15679405940037615516234689 11759554455028211637176017)
            ·
              refine ⟨8819665841271158727882013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11759554455028211637176017 8819665841271158727882013)
              ·
                refine ⟨3307374690476684522955755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8819665841271158727882013 3307374690476684522955755)
                ·
                  refine ⟨4961062035715026784433633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3307374690476684522955755 4961062035715026784433633)
                  ·
                    refine ⟨3720796526786270088325225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4961062035715026784433633 3720796526786270088325225)
                    ·
                      refine ⟨2790597395089702566243919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3720796526786270088325225 2790597395089702566243919)
                      ·
                        rfl

theorem cell23_5434669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_5434669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5434669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5434669 prefixEnd_5434669 := by exact prefixLift 5434669
  have htrace : WordTrace (prefixWord ++ tailWord_5434669) baseStart_5434669 baseEnd_5434669 := by
    simpa [prefixWord, tailWord_5434669, baseEnd_5434669] using wordTrace_append hprefix tailTrace_5434669
  have hstable : (prefixWord ++ tailWord_5434669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5434669).length < 2 ^ (prefixWord ++ tailWord_5434669).sum := by decide
  have hdescent : baseEnd_5434669 < baseStart_5434669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5434669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5434684 : List Nat := [2, 2, 2, 2, 1, 3, 1, 2, 2, 6]
def baseStart_5434684 : Nat := 118140960795 + 5434684 * 2 ^ 59
def prefixEnd_5434684 : Nat := 4983230072969 + 3 ^ 40 * 5434684 * 2
def baseEnd_5434684 : Nat := 930201699099840002518783

theorem tailTrace_5434684 : CollatzResearch.WordTrace tailWord_5434684 prefixEnd_5434684 930201699099840002518783 := by
  unfold tailWord_5434684
  simp only [CollatzResearch.WordTrace]
  refine ⟨99109604921537756488455553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132146139895383675317940737 99109604921537756488455553)
  ·
    refine ⟨74332203691153317366341665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99109604921537756488455553 74332203691153317366341665)
    ·
      refine ⟨55749152768364988024756249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74332203691153317366341665 55749152768364988024756249)
      ·
        refine ⟨41811864576273741018567187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55749152768364988024756249 41811864576273741018567187)
        ·
          refine ⟨62717796864410611527850781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41811864576273741018567187 62717796864410611527850781)
          ·
            refine ⟨23519173824153979322944043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62717796864410611527850781 23519173824153979322944043)
            ·
              refine ⟨35278760736230968984416065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23519173824153979322944043 35278760736230968984416065)
              ·
                refine ⟨26459070552173226738312049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35278760736230968984416065 26459070552173226738312049)
                ·
                  refine ⟨19844302914129920053734037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26459070552173226738312049 19844302914129920053734037)
                  ·
                    refine ⟨930201699099840002518783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19844302914129920053734037 930201699099840002518783)
                    ·
                      rfl

theorem cell23_5434684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_5434684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5434684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5434684 prefixEnd_5434684 := by exact prefixLift 5434684
  have htrace : WordTrace (prefixWord ++ tailWord_5434684) baseStart_5434684 baseEnd_5434684 := by
    simpa [prefixWord, tailWord_5434684, baseEnd_5434684] using wordTrace_append hprefix tailTrace_5434684
  have hstable : (prefixWord ++ tailWord_5434684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5434684).length < 2 ^ (prefixWord ++ tailWord_5434684).sum := by decide
  have hdescent : baseEnd_5434684 < baseStart_5434684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5434684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5434685 : List Nat := [1, 4, 1, 5, 1, 1, 1, 1, 4, 1, 3]
def baseStart_5434685 : Nat := 118140960795 + 5434685 * 2 ^ 59
def prefixEnd_5434685 : Nat := 4983230072969 + 3 ^ 40 * 5434685 * 2
def baseEnd_5434685 : Nat := 2790605610780174503643845

theorem tailTrace_5434685 : CollatzResearch.WordTrace tailWord_5434685 prefixEnd_5434685 2790605610780174503643845 := by
  unfold tailWord_5434685
  simp only [CollatzResearch.WordTrace]
  refine ⟨198219246316071890147697509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132146164210714593431798339 198219246316071890147697509)
  ·
    refine ⟨37166108684263479402693283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198219246316071890147697509 37166108684263479402693283)
    ·
      refine ⟨55749163026395219104039925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37166108684263479402693283 55749163026395219104039925)
      ·
        refine ⟨5226484033724551791003743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55749163026395219104039925 5226484033724551791003743)
        ·
          refine ⟨7839726050586827686505615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5226484033724551791003743 7839726050586827686505615)
          ·
            refine ⟨11759589075880241529758423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7839726050586827686505615 11759589075880241529758423)
            ·
              refine ⟨17639383613820362294637635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11759589075880241529758423 17639383613820362294637635)
              ·
                refine ⟨26459075420730543441956453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17639383613820362294637635 26459075420730543441956453)
                ·
                  refine ⟨4961076641386976895366835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26459075420730543441956453 4961076641386976895366835)
                  ·
                    refine ⟨7441614962080465343050253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4961076641386976895366835 7441614962080465343050253)
                    ·
                      refine ⟨2790605610780174503643845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7441614962080465343050253 2790605610780174503643845)
                      ·
                        rfl

theorem cell23_5434685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_5434685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5434685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5434685 prefixEnd_5434685 := by exact prefixLift 5434685
  have htrace : WordTrace (prefixWord ++ tailWord_5434685) baseStart_5434685 baseEnd_5434685 := by
    simpa [prefixWord, tailWord_5434685, baseEnd_5434685] using wordTrace_append hprefix tailTrace_5434685
  have hstable : (prefixWord ++ tailWord_5434685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5434685).length < 2 ^ (prefixWord ++ tailWord_5434685).sum := by decide
  have hdescent : baseEnd_5434685 < baseStart_5434685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5434685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5434704 : List Nat := [2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 4]
def baseStart_5434704 : Nat := 118140960795 + 5434704 * 2 ^ 59
def prefixEnd_5434704 : Nat := 4983230072969 + 3 ^ 40 * 5434704 * 2
def baseEnd_5434704 : Nat := 2790615366912609929306257

theorem tailTrace_5434704 : CollatzResearch.WordTrace tailWord_5434704 prefixEnd_5434704 2790615366912609929306257 := by
  unfold tailWord_5434704
  simp only [CollatzResearch.WordTrace]
  refine ⟨99109969651501528196319583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132146626202002037595092777 99109969651501528196319583)
  ·
    refine ⟨148664954477252292294479375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99109969651501528196319583 148664954477252292294479375)
    ·
      refine ⟨222997431715878438441719063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148664954477252292294479375 222997431715878438441719063)
      ·
        refine ⟨334496147573817657662578595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222997431715878438441719063 334496147573817657662578595)
        ·
          refine ⟨501744221360726486493867893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334496147573817657662578595 501744221360726486493867893)
          ·
            refine ⟨47038520752568108108800115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 501744221360726486493867893 47038520752568108108800115)
            ·
              refine ⟨70557781128852162163200173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47038520752568108108800115 70557781128852162163200173)
              ·
                refine ⟨26459167923319560811200065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70557781128852162163200173 26459167923319560811200065)
                ·
                  refine ⟨19844375942489670608400049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26459167923319560811200065 19844375942489670608400049)
                  ·
                    refine ⟨14883281956867252956300037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19844375942489670608400049 14883281956867252956300037)
                    ·
                      refine ⟨2790615366912609929306257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14883281956867252956300037 2790615366912609929306257)
                      ·
                        rfl

theorem cell23_5434704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 4].length) (baseStart_5434704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5434704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5434704 prefixEnd_5434704 := by exact prefixLift 5434704
  have htrace : WordTrace (prefixWord ++ tailWord_5434704) baseStart_5434704 baseEnd_5434704 := by
    simpa [prefixWord, tailWord_5434704, baseEnd_5434704] using wordTrace_append hprefix tailTrace_5434704
  have hstable : (prefixWord ++ tailWord_5434704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5434704).length < 2 ^ (prefixWord ++ tailWord_5434704).sum := by decide
  have hdescent : baseEnd_5434704 < baseStart_5434704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5434704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5434714 : List Nat := [3, 1, 1, 2, 1, 2, 4, 2, 7]
def baseStart_5434714 : Nat := 118140960795 + 5434714 * 2 ^ 59
def prefixEnd_5434714 : Nat := 4983230072969 + 3 ^ 40 * 5434714 * 2
def baseEnd_5434714 : Nat := 310068944635461654464579

theorem tailTrace_5434714 : CollatzResearch.WordTrace tailWord_5434714 prefixEnd_5434714 310068944635461654464579 := by
  unfold tailWord_5434714
  simp only [CollatzResearch.WordTrace]
  refine ⟨49555076008241707025125799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132146869355311218733668797 49555076008241707025125799)
  ·
    refine ⟨74332614012362560537688699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49555076008241707025125799 74332614012362560537688699)
    ·
      refine ⟨111498921018543840806533049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74332614012362560537688699 111498921018543840806533049)
      ·
        refine ⟨83624190763907880604899787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111498921018543840806533049 83624190763907880604899787)
        ·
          refine ⟨125436286145861820907349681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83624190763907880604899787 125436286145861820907349681)
          ·
            refine ⟨94077214609396365680512261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125436286145861820907349681 94077214609396365680512261)
            ·
              refine ⟨17639477739261818565096049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94077214609396365680512261 17639477739261818565096049)
              ·
                refine ⟨13229608304446363923822037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17639477739261818565096049 13229608304446363923822037)
                ·
                  refine ⟨310068944635461654464579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13229608304446363923822037 310068944635461654464579)
                  ·
                    rfl

theorem cell23_5434714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 7].length) (baseStart_5434714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5434714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5434714 prefixEnd_5434714 := by exact prefixLift 5434714
  have htrace : WordTrace (prefixWord ++ tailWord_5434714) baseStart_5434714 baseEnd_5434714 := by
    simpa [prefixWord, tailWord_5434714, baseEnd_5434714] using wordTrace_append hprefix tailTrace_5434714
  have hstable : (prefixWord ++ tailWord_5434714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5434714).length < 2 ^ (prefixWord ++ tailWord_5434714).sum := by decide
  have hdescent : baseEnd_5434714 < baseStart_5434714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5434714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5434748 : List Nat := [2, 2, 2, 1, 1, 1, 7, 2, 5]
def baseStart_5434748 : Nat := 118140960795 + 5434748 * 2 ^ 59
def prefixEnd_5434748 : Nat := 4983230072969 + 3 ^ 40 * 5434748 * 2
def baseEnd_5434748 : Nat := 310070884451267528572895

theorem tailTrace_5434748 : CollatzResearch.WordTrace tailWord_5434748 prefixEnd_5434748 310070884451267528572895 := by
  unfold tailWord_5434748
  simp only [CollatzResearch.WordTrace]
  refine ⟨99110772057421825953620449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132147696076562434604827265 99110772057421825953620449)
  ·
    refine ⟨74333079043066369465215337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99110772057421825953620449 74333079043066369465215337)
    ·
      refine ⟨55749809282299777098911503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74333079043066369465215337 55749809282299777098911503)
      ·
        refine ⟨83624713923449665648367255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55749809282299777098911503 83624713923449665648367255)
        ·
          refine ⟨125437070885174498472550883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83624713923449665648367255 125437070885174498472550883)
          ·
            refine ⟨188155606327761747708826325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125437070885174498472550883 188155606327761747708826325)
            ·
              refine ⟨4409897023306915961925617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 188155606327761747708826325 4409897023306915961925617)
              ·
                refine ⟨3307422767480186971444213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4409897023306915961925617 3307422767480186971444213)
                ·
                  refine ⟨310070884451267528572895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3307422767480186971444213 310070884451267528572895)
                  ·
                    rfl

theorem cell23_5434748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 2, 5].length) (baseStart_5434748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5434748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5434748 prefixEnd_5434748 := by exact prefixLift 5434748
  have htrace : WordTrace (prefixWord ++ tailWord_5434748) baseStart_5434748 baseEnd_5434748 := by
    simpa [prefixWord, tailWord_5434748, baseEnd_5434748] using wordTrace_append hprefix tailTrace_5434748
  have hstable : (prefixWord ++ tailWord_5434748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5434748).length < 2 ^ (prefixWord ++ tailWord_5434748).sum := by decide
  have hdescent : baseEnd_5434748 < baseStart_5434748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5434748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5434865 : List Nat := [1, 2, 2, 2, 3, 3, 2, 1, 3, 1, 3]
def baseStart_5434865 : Nat := 118140960795 + 5434865 * 2 ^ 59
def prefixEnd_5434865 : Nat := 4983230072969 + 3 ^ 40 * 5434865 * 2
def baseEnd_5434865 : Nat := 2790698037297983799393017

theorem tailTrace_5434865 : CollatzResearch.WordTrace tailWord_5434865 prefixEnd_5434865 2790698037297983799393017 := by
  unfold tailWord_5434865
  simp only [CollatzResearch.WordTrace]
  refine ⟨198225811455419780889250049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132150540970279853926166699 198225811455419780889250049)
  ·
    refine ⟨148669358591564835666937537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198225811455419780889250049 148669358591564835666937537)
    ·
      refine ⟨111502018943673626750203153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148669358591564835666937537 111502018943673626750203153)
      ·
        refine ⟨83626514207755220062652365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111502018943673626750203153 83626514207755220062652365)
        ·
          refine ⟨31359942827908207523494637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83626514207755220062652365 31359942827908207523494637)
          ·
            refine ⟨11759978560465577821310489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31359942827908207523494637 11759978560465577821310489)
            ·
              refine ⟨8819983920349183365982867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11759978560465577821310489 8819983920349183365982867)
              ·
                refine ⟨13229975880523775048974301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8819983920349183365982867 13229975880523775048974301)
                ·
                  refine ⟨4961240955196415643365363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13229975880523775048974301 4961240955196415643365363)
                  ·
                    refine ⟨7441861432794623465048045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4961240955196415643365363 7441861432794623465048045)
                    ·
                      refine ⟨2790698037297983799393017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7441861432794623465048045 2790698037297983799393017)
                      ·
                        rfl

theorem cell23_5434865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 3, 1, 3].length) (baseStart_5434865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5434865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5434865 prefixEnd_5434865 := by exact prefixLift 5434865
  have htrace : WordTrace (prefixWord ++ tailWord_5434865) baseStart_5434865 baseEnd_5434865 := by
    simpa [prefixWord, tailWord_5434865, baseEnd_5434865] using wordTrace_append hprefix tailTrace_5434865
  have hstable : (prefixWord ++ tailWord_5434865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5434865).length < 2 ^ (prefixWord ++ tailWord_5434865).sum := by decide
  have hdescent : baseEnd_5434865 < baseStart_5434865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5434865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5434871 : List Nat := [1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 4]
def baseStart_5434871 : Nat := 118140960795 + 5434871 * 2 ^ 59
def prefixEnd_5434871 : Nat := 4983230072969 + 3 ^ 40 * 5434871 * 2
def baseEnd_5434871 : Nat := 2790701118181910775917989

theorem tailTrace_5434871 : CollatzResearch.WordTrace tailWord_5434871 prefixEnd_5434871 2790701118181910775917989 := by
  unfold tailWord_5434871
  simp only [CollatzResearch.WordTrace]
  refine ⟨198226030293398043913968467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132150686862265362609312311 198226030293398043913968467)
  ·
    refine ⟨297339045440097065870952701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198226030293398043913968467 297339045440097065870952701)
    ·
      refine ⟨111502142040036399701607263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 297339045440097065870952701 111502142040036399701607263)
      ·
        refine ⟨167253213060054599552410895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111502142040036399701607263 167253213060054599552410895)
        ·
          refine ⟨250879819590081899328616343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167253213060054599552410895 250879819590081899328616343)
          ·
            refine ⟨376319729385122848992924515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250879819590081899328616343 376319729385122848992924515)
            ·
              refine ⟨564479594077684273489386773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376319729385122848992924515 564479594077684273489386773)
              ·
                refine ⟨26459980972391450319815005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 564479594077684273489386773 26459980972391450319815005)
                ·
                  refine ⟨9922492864646793869930627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26459980972391450319815005 9922492864646793869930627)
                  ·
                    refine ⟨14883739296970190804895941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9922492864646793869930627 14883739296970190804895941)
                    ·
                      refine ⟨2790701118181910775917989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14883739296970190804895941 2790701118181910775917989)
                      ·
                        rfl

theorem cell23_5434871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 4].length) (baseStart_5434871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5434871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5434871 prefixEnd_5434871 := by exact prefixLift 5434871
  have htrace : WordTrace (prefixWord ++ tailWord_5434871) baseStart_5434871 baseEnd_5434871 := by
    simpa [prefixWord, tailWord_5434871, baseEnd_5434871] using wordTrace_append hprefix tailTrace_5434871
  have hstable : (prefixWord ++ tailWord_5434871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5434871).length < 2 ^ (prefixWord ++ tailWord_5434871).sum := by decide
  have hdescent : baseEnd_5434871 < baseStart_5434871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5434871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5434882 : List Nat := [3, 4, 1, 2, 1, 1, 2, 2, 3, 1, 3]
def baseStart_5434882 : Nat := 118140960795 + 5434882 * 2 ^ 59
def prefixEnd_5434882 : Nat := 4983230072969 + 3 ^ 40 * 5434882 * 2
def baseEnd_5434882 : Nat := 2790706766469110232880439

theorem tailTrace_5434882 : CollatzResearch.WordTrace tailWord_5434882 prefixEnd_5434882 2790706766469110232880439 := by
  unfold tailWord_5434882
  simp only [CollatzResearch.WordTrace]
  refine ⟨49556607874089548198154725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132150954330905461861745933 49556607874089548198154725)
  ·
    refine ⟨9291863976391790287154011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49556607874089548198154725 9291863976391790287154011)
    ·
      refine ⟨13937795964587685430731017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9291863976391790287154011 13937795964587685430731017)
      ·
        refine ⟨10453346973440764073048263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13937795964587685430731017 10453346973440764073048263)
        ·
          refine ⟨15680020460161146109572395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10453346973440764073048263 15680020460161146109572395)
          ·
            refine ⟨23520030690241719164358593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15680020460161146109572395 23520030690241719164358593)
            ·
              refine ⟨17640023017681289373268945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23520030690241719164358593 17640023017681289373268945)
              ·
                refine ⟨13230017263260967029951709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17640023017681289373268945 13230017263260967029951709)
                ·
                  refine ⟨4961256473722862636231891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13230017263260967029951709 4961256473722862636231891)
                  ·
                    refine ⟨7441884710584293954347837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4961256473722862636231891 7441884710584293954347837)
                    ·
                      refine ⟨2790706766469110232880439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7441884710584293954347837 2790706766469110232880439)
                      ·
                        rfl

theorem cell23_5434882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_5434882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5434882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5434882 prefixEnd_5434882 := by exact prefixLift 5434882
  have htrace : WordTrace (prefixWord ++ tailWord_5434882) baseStart_5434882 baseEnd_5434882 := by
    simpa [prefixWord, tailWord_5434882, baseEnd_5434882] using wordTrace_append hprefix tailTrace_5434882
  have hstable : (prefixWord ++ tailWord_5434882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5434882).length < 2 ^ (prefixWord ++ tailWord_5434882).sum := by decide
  have hdescent : baseEnd_5434882 < baseStart_5434882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5434882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5434888 : List Nat := [2, 1, 3, 2, 1, 1, 3, 4, 1, 1, 4]
def baseStart_5434888 : Nat := 118140960795 + 5434888 * 2 ^ 59
def prefixEnd_5434888 : Nat := 4983230072969 + 3 ^ 40 * 5434888 * 2
def baseEnd_5434888 : Nat := 2790709847353037209405411

theorem tailTrace_5434888 : CollatzResearch.WordTrace tailWord_5434888 prefixEnd_5434888 2790709847353037209405411 := by
  unfold tailWord_5434888
  simp only [CollatzResearch.WordTrace]
  refine ⟨99113325167168227908668659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132151100222890970544891545 99113325167168227908668659)
  ·
    refine ⟨148669987750752341863002989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99113325167168227908668659 148669987750752341863002989)
    ·
      refine ⟨55751245406532128198626121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148669987750752341863002989 55751245406532128198626121)
      ·
        refine ⟨41813434054899096148969591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55751245406532128198626121 41813434054899096148969591)
        ·
          refine ⟨62720151082348644223454387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41813434054899096148969591 62720151082348644223454387)
          ·
            refine ⟨94080226623522966335181581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62720151082348644223454387 94080226623522966335181581)
            ·
              refine ⟨35280084983821112375693093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94080226623522966335181581 35280084983821112375693093)
              ·
                refine ⟨6615015934466458570442455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35280084983821112375693093 6615015934466458570442455)
                ·
                  refine ⟨9922523901699687855663683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6615015934466458570442455 9922523901699687855663683)
                  ·
                    refine ⟨14883785852549531783495525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9922523901699687855663683 14883785852549531783495525)
                    ·
                      refine ⟨2790709847353037209405411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14883785852549531783495525 2790709847353037209405411)
                      ·
                        rfl

theorem cell23_5434888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_5434888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5434888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5434888 prefixEnd_5434888 := by exact prefixLift 5434888
  have htrace : WordTrace (prefixWord ++ tailWord_5434888) baseStart_5434888 baseEnd_5434888 := by
    simpa [prefixWord, tailWord_5434888, baseEnd_5434888] using wordTrace_append hprefix tailTrace_5434888
  have hstable : (prefixWord ++ tailWord_5434888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5434888).length < 2 ^ (prefixWord ++ tailWord_5434888).sum := by decide
  have hdescent : baseEnd_5434888 < baseStart_5434888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5434888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5434893 : List Nat := [1, 7, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_5434893 : Nat := 118140960795 + 5434893 * 2 ^ 59
def prefixEnd_5434893 : Nat := 4983230072969 + 3 ^ 40 * 5434893 * 2
def baseEnd_5434893 : Nat := 930237471585436563280963

theorem tailTrace_5434893 : CollatzResearch.WordTrace tailWord_5434893 prefixEnd_5434893 930237471585436563280963 := by
  unfold tailWord_5434893
  simp only [CollatzResearch.WordTrace]
  refine ⟨198226832699318341671269333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132151221799545561114179555 198226832699318341671269333)
  ·
    refine ⟨4645941391390273632920375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 198226832699318341671269333 4645941391390273632920375)
    ·
      refine ⟨6968912087085410449380563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4645941391390273632920375 6968912087085410449380563)
      ·
        refine ⟨10453368130628115674070845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6968912087085410449380563 10453368130628115674070845)
        ·
          refine ⟨3920013048985543377776567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10453368130628115674070845 3920013048985543377776567)
          ·
            refine ⟨5880019573478315066664851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3920013048985543377776567 5880019573478315066664851)
            ·
              refine ⟨8820029360217472599997277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5880019573478315066664851 8820029360217472599997277)
              ·
                refine ⟨3307511010081552224998979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8820029360217472599997277 3307511010081552224998979)
                ·
                  refine ⟨4961266515122328337498469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3307511010081552224998979 4961266515122328337498469)
                  ·
                    refine ⟨930237471585436563280963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4961266515122328337498469 930237471585436563280963)
                    ·
                      rfl

theorem cell23_5434893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_5434893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5434893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5434893 prefixEnd_5434893 := by exact prefixLift 5434893
  have htrace : WordTrace (prefixWord ++ tailWord_5434893) baseStart_5434893 baseEnd_5434893 := by
    simpa [prefixWord, tailWord_5434893, baseEnd_5434893] using wordTrace_append hprefix tailTrace_5434893
  have hstable : (prefixWord ++ tailWord_5434893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5434893).length < 2 ^ (prefixWord ++ tailWord_5434893).sum := by decide
  have hdescent : baseEnd_5434893 < baseStart_5434893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5434893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5434908 : List Nat := [2, 2, 3, 1, 2, 1, 4, 1, 1, 1, 5]
def baseStart_5434908 : Nat := 118140960795 + 5434908 * 2 ^ 59
def prefixEnd_5434908 : Nat := 4983230072969 + 3 ^ 40 * 5434908 * 2
def baseEnd_5434908 : Nat := 2790720116966127131155319

theorem tailTrace_5434908 : CollatzResearch.WordTrace tailWord_5434908 prefixEnd_5434908 2790720116966127131155319 := by
  unfold tailWord_5434908
  simp only [CollatzResearch.WordTrace]
  refine ⟨99113689897131999616532689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132151586529509332822043585 99113689897131999616532689)
  ·
    refine ⟨74335267422848999712399517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99113689897131999616532689 74335267422848999712399517)
    ·
      refine ⟨27875725283568374892149819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74335267422848999712399517 27875725283568374892149819)
      ·
        refine ⟨41813587925352562338224729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27875725283568374892149819 41813587925352562338224729)
        ·
          refine ⟨31360190944014421753668547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41813587925352562338224729 31360190944014421753668547)
          ·
            refine ⟨47040286416021632630502821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31360190944014421753668547 47040286416021632630502821)
            ·
              refine ⟨8820053703004056118219279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47040286416021632630502821 8820053703004056118219279)
              ·
                refine ⟨13230080554506084177328919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8820053703004056118219279 13230080554506084177328919)
                ·
                  refine ⟨19845120831759126265993379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13230080554506084177328919 19845120831759126265993379)
                  ·
                    refine ⟨29767681247638689398990069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19845120831759126265993379 29767681247638689398990069)
                    ·
                      refine ⟨2790720116966127131155319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29767681247638689398990069 2790720116966127131155319)
                      ·
                        rfl

theorem cell23_5434908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_5434908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5434908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5434908 prefixEnd_5434908 := by exact prefixLift 5434908
  have htrace : WordTrace (prefixWord ++ tailWord_5434908) baseStart_5434908 baseEnd_5434908 := by
    simpa [prefixWord, tailWord_5434908, baseEnd_5434908] using wordTrace_append hprefix tailTrace_5434908
  have hstable : (prefixWord ++ tailWord_5434908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5434908).length < 2 ^ (prefixWord ++ tailWord_5434908).sum := by decide
  have hdescent : baseEnd_5434908 < baseStart_5434908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5434908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5434938 : List Nat := [3, 1, 1, 1, 3, 2, 2, 3, 1, 3, 3]
def baseStart_5434938 : Nat := 118140960795 + 5434938 * 2 ^ 59
def prefixEnd_5434938 : Nat := 4983230072969 + 3 ^ 40 * 5434938 * 2
def baseEnd_5434938 : Nat := 2790735521385762013780181

theorem tailTrace_5434938 : CollatzResearch.WordTrace tailWord_5434938 prefixEnd_5434938 2790735521385762013780181 := by
  unfold tailWord_5434938
  simp only [CollatzResearch.WordTrace]
  refine ⟨49557118496038828589164367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132152315989436876237771645 49557118496038828589164367)
  ·
    refine ⟨74335677744058242883746551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49557118496038828589164367 74335677744058242883746551)
    ·
      refine ⟨111503516616087364325619827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74335677744058242883746551 111503516616087364325619827)
      ·
        refine ⟨167255274924131046488429741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111503516616087364325619827 167255274924131046488429741)
        ·
          refine ⟨62720728096549142433161153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167255274924131046488429741 62720728096549142433161153)
          ·
            refine ⟨47040546072411856824870865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62720728096549142433161153 47040546072411856824870865)
            ·
              refine ⟨35280409554308892618653149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47040546072411856824870865 35280409554308892618653149)
              ·
                refine ⟨13230153582865834731994931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35280409554308892618653149 13230153582865834731994931)
                ·
                  refine ⟨19845230374298752097992397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13230153582865834731994931 19845230374298752097992397)
                  ·
                    refine ⟨7441961390362032036747149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19845230374298752097992397 7441961390362032036747149)
                    ·
                      refine ⟨2790735521385762013780181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7441961390362032036747149 2790735521385762013780181)
                      ·
                        rfl

theorem cell23_5434938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 1, 3, 3].length) (baseStart_5434938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5434938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5434938 prefixEnd_5434938 := by exact prefixLift 5434938
  have htrace : WordTrace (prefixWord ++ tailWord_5434938) baseStart_5434938 baseEnd_5434938 := by
    simpa [prefixWord, tailWord_5434938, baseEnd_5434938] using wordTrace_append hprefix tailTrace_5434938
  have hstable : (prefixWord ++ tailWord_5434938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5434938).length < 2 ^ (prefixWord ++ tailWord_5434938).sum := by decide
  have hdescent : baseEnd_5434938 < baseStart_5434938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5434938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5434966 : List Nat := [5, 2, 2, 2, 1, 1, 2, 2, 2, 4]
def baseStart_5434966 : Nat := 118140960795 + 5434966 * 2 ^ 59
def prefixEnd_5434966 : Nat := 4983230072969 + 3 ^ 40 * 5434966 * 2
def baseEnd_5434966 : Nat := 930249966281362634743351

theorem tailTrace_5434966 : CollatzResearch.WordTrace tailWord_5434966 prefixEnd_5434966 930249966281362634743351 := by
  unfold tailWord_5434966
  simp only [CollatzResearch.WordTrace]
  refine ⟨12389343451753367196167297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132152996818702583425784501 12389343451753367196167297)
  ·
    refine ⟨9292007588815025397125473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12389343451753367196167297 9292007588815025397125473)
    ·
      refine ⟨6969005691611269047844105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9292007588815025397125473 6969005691611269047844105)
      ·
        refine ⟨5226754268708451785883079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6969005691611269047844105 5226754268708451785883079)
        ·
          refine ⟨7840131403062677678824619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5226754268708451785883079 7840131403062677678824619)
          ·
            refine ⟨11760197104594016518236929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7840131403062677678824619 11760197104594016518236929)
            ·
              refine ⟨8820147828445512388677697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11760197104594016518236929 8820147828445512388677697)
              ·
                refine ⟨6615110871334134291508273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8820147828445512388677697 6615110871334134291508273)
                ·
                  refine ⟨4961333153500600718631205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6615110871334134291508273 4961333153500600718631205)
                  ·
                    refine ⟨930249966281362634743351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4961333153500600718631205 930249966281362634743351)
                    ·
                      rfl

theorem cell23_5434966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_5434966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5434966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5434966 prefixEnd_5434966 := by exact prefixLift 5434966
  have htrace : WordTrace (prefixWord ++ tailWord_5434966) baseStart_5434966 baseEnd_5434966 := by
    simpa [prefixWord, tailWord_5434966, baseEnd_5434966] using wordTrace_append hprefix tailTrace_5434966
  have hstable : (prefixWord ++ tailWord_5434966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5434966).length < 2 ^ (prefixWord ++ tailWord_5434966).sum := by decide
  have hdescent : baseEnd_5434966 < baseStart_5434966 := by decide
  rcases family_descends (prefixWord ++ tailWord_5434966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5434972 : List Nat := [2, 2, 4, 1, 2, 1, 1, 4, 2, 1, 3]
def baseStart_5434972 : Nat := 118140960795 + 5434972 * 2 ^ 59
def prefixEnd_5434972 : Nat := 4983230072969 + 3 ^ 40 * 5434972 * 2
def baseEnd_5434972 : Nat := 2790752979728014880755025

theorem tailTrace_5434972 : CollatzResearch.WordTrace tailWord_5434972 prefixEnd_5434972 2790752979728014880755025 := by
  unfold tailWord_5434972
  simp only [CollatzResearch.WordTrace]
  refine ⟨99114857033016069081697585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132153142710688092108930113 99114857033016069081697585)
  ·
    refine ⟨74336142774762051811273189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99114857033016069081697585 74336142774762051811273189)
    ·
      refine ⟨13938026770267884714613723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74336142774762051811273189 13938026770267884714613723)
      ·
        refine ⟨20907040155401827071920585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13938026770267884714613723 20907040155401827071920585)
        ·
          refine ⟨15680280116551370303940439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20907040155401827071920585 15680280116551370303940439)
          ·
            refine ⟨23520420174827055455910659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15680280116551370303940439 23520420174827055455910659)
            ·
              refine ⟨35280630262240583183865989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23520420174827055455910659 35280630262240583183865989)
              ·
                refine ⟨6615118174170109346974873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35280630262240583183865989 6615118174170109346974873)
                ·
                  refine ⟨4961338630627582010231155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6615118174170109346974873 4961338630627582010231155)
                  ·
                    refine ⟨7442007945941373015346733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4961338630627582010231155 7442007945941373015346733)
                    ·
                      refine ⟨2790752979728014880755025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7442007945941373015346733 2790752979728014880755025)
                      ·
                        rfl

theorem cell23_5434972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_5434972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5434972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5434972 prefixEnd_5434972 := by exact prefixLift 5434972
  have htrace : WordTrace (prefixWord ++ tailWord_5434972) baseStart_5434972 baseEnd_5434972 := by
    simpa [prefixWord, tailWord_5434972, baseEnd_5434972] using wordTrace_append hprefix tailTrace_5434972
  have hstable : (prefixWord ++ tailWord_5434972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5434972).length < 2 ^ (prefixWord ++ tailWord_5434972).sum := by decide
  have hdescent : baseEnd_5434972 < baseStart_5434972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5434972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5434973 : List Nat := [1, 4, 4, 2, 1, 1, 1, 4, 1, 2, 2]
def baseStart_5434973 : Nat := 118140960795 + 5434973 * 2 ^ 59
def prefixEnd_5434973 : Nat := 4983230072969 + 3 ^ 40 * 5434973 * 2
def baseEnd_5434973 : Nat := 2790753493208669376842521

theorem tailTrace_5434973 : CollatzResearch.WordTrace tailWord_5434973 prefixEnd_5434973 2790753493208669376842521 := by
  unfold tailWord_5434973
  simp only [CollatzResearch.WordTrace]
  refine ⟨198229750539028515334181573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132153167026019010222787715 198229750539028515334181573)
  ·
    refine ⟨37168078226067846625159045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198229750539028515334181573 37168078226067846625159045)
    ·
      refine ⟨6969014667387721242217321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37168078226067846625159045 6969014667387721242217321)
      ·
        refine ⟨5226761000540790931662991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6969014667387721242217321 5226761000540790931662991)
        ·
          refine ⟨7840141500811186397494487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5226761000540790931662991 7840141500811186397494487)
          ·
            refine ⟨11760212251216779596241731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7840141500811186397494487 11760212251216779596241731)
            ·
              refine ⟨17640318376825169394362597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11760212251216779596241731 17640318376825169394362597)
              ·
                refine ⟨3307559695654719261442987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17640318376825169394362597 3307559695654719261442987)
                ·
                  refine ⟨4961339543482078892164481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3307559695654719261442987 4961339543482078892164481)
                  ·
                    refine ⟨3721004657611559169123361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4961339543482078892164481 3721004657611559169123361)
                    ·
                      refine ⟨2790753493208669376842521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3721004657611559169123361 2790753493208669376842521)
                      ·
                        rfl

theorem cell23_5434973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_5434973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5434973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5434973 prefixEnd_5434973 := by exact prefixLift 5434973
  have htrace : WordTrace (prefixWord ++ tailWord_5434973) baseStart_5434973 baseEnd_5434973 := by
    simpa [prefixWord, tailWord_5434973, baseEnd_5434973] using wordTrace_append hprefix tailTrace_5434973
  have hstable : (prefixWord ++ tailWord_5434973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5434973).length < 2 ^ (prefixWord ++ tailWord_5434973).sum := by decide
  have hdescent : baseEnd_5434973 < baseStart_5434973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5434973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435011 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 7]
def baseStart_5435011 : Nat := 118140960795 + 5435011 * 2 ^ 59
def prefixEnd_5435011 : Nat := 4983230072969 + 3 ^ 40 * 5435011 * 2
def baseEnd_5435011 : Nat := 2790773005473540228167345

theorem tailTrace_5435011 : CollatzResearch.WordTrace tailWord_5435011 prefixEnd_5435011 2790773005473540228167345 := by
  unfold tailWord_5435011
  simp only [CollatzResearch.WordTrace]
  refine ⟨198231136512890847824064887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132154091008593898549376591 198231136512890847824064887)
  ·
    refine ⟨297346704769336271736097331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198231136512890847824064887 297346704769336271736097331)
    ·
      refine ⟨446020057154004407604145997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297346704769336271736097331 446020057154004407604145997)
      ·
        refine ⟨167257521432751652851554749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 446020057154004407604145997 167257521432751652851554749)
        ·
          refine ⟨62721570537281869819333031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167257521432751652851554749 62721570537281869819333031)
          ·
            refine ⟨94082355805922804728999547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62721570537281869819333031 94082355805922804728999547)
            ·
              refine ⟨141123533708884207093499321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94082355805922804728999547 141123533708884207093499321)
              ·
                refine ⟨105842650281663155320124491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141123533708884207093499321 105842650281663155320124491)
                ·
                  refine ⟨158763975422494732980186737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105842650281663155320124491 158763975422494732980186737)
                  ·
                    refine ⟨119072981566871049735140053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 158763975422494732980186737 119072981566871049735140053)
                    ·
                      refine ⟨2790773005473540228167345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 119072981566871049735140053 2790773005473540228167345)
                      ·
                        rfl

theorem cell23_5435011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_5435011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435011 prefixEnd_5435011 := by exact prefixLift 5435011
  have htrace : WordTrace (prefixWord ++ tailWord_5435011) baseStart_5435011 baseEnd_5435011 := by
    simpa [prefixWord, tailWord_5435011, baseEnd_5435011] using wordTrace_append hprefix tailTrace_5435011
  have hstable : (prefixWord ++ tailWord_5435011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435011).length < 2 ^ (prefixWord ++ tailWord_5435011).sum := by decide
  have hdescent : baseEnd_5435011 < baseStart_5435011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435088 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 3]
def baseStart_5435088 : Nat := 118140960795 + 5435088 * 2 ^ 59
def prefixEnd_5435088 : Nat := 4983230072969 + 3 ^ 40 * 5435088 * 2
def baseEnd_5435088 : Nat := 2790812543483936426904491

theorem tailTrace_5435088 : CollatzResearch.WordTrace tailWord_5435088 prefixEnd_5435088 2790812543483936426904491 := by
  unfold tailWord_5435088
  simp only [CollatzResearch.WordTrace]
  refine ⟨99116972466805944987308959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132155963289074593316411945 99116972466805944987308959)
  ·
    refine ⟨148675458700208917480963439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99116972466805944987308959 148675458700208917480963439)
    ·
      refine ⟨223013188050313376221445159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148675458700208917480963439 223013188050313376221445159)
      ·
        refine ⟨334519782075470064332167739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223013188050313376221445159 334519782075470064332167739)
        ·
          refine ⟨501779673113205096498251609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334519782075470064332167739 501779673113205096498251609)
          ·
            refine ⟨376334754834903822373688707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 501779673113205096498251609 376334754834903822373688707)
            ·
              refine ⟨564502132252355733560533061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376334754834903822373688707 564502132252355733560533061)
              ·
                refine ⟨105844149797316700042599949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 564502132252355733560533061 105844149797316700042599949)
                ·
                  refine ⟨39691556173993762515974981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105844149797316700042599949 39691556173993762515974981)
                  ·
                    refine ⟨7442166782623830471745309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39691556173993762515974981 7442166782623830471745309)
                    ·
                      refine ⟨2790812543483936426904491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7442166782623830471745309 2790812543483936426904491)
                      ·
                        rfl

theorem cell23_5435088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 3].length) (baseStart_5435088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435088 prefixEnd_5435088 := by exact prefixLift 5435088
  have htrace : WordTrace (prefixWord ++ tailWord_5435088) baseStart_5435088 baseEnd_5435088 := by
    simpa [prefixWord, tailWord_5435088, baseEnd_5435088] using wordTrace_append hprefix tailTrace_5435088
  have hstable : (prefixWord ++ tailWord_5435088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435088).length < 2 ^ (prefixWord ++ tailWord_5435088).sum := by decide
  have hdescent : baseEnd_5435088 < baseStart_5435088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435122 : List Nat := [3, 2, 1, 3, 1, 1, 4, 1, 2, 2, 3]
def baseStart_5435122 : Nat := 118140960795 + 5435122 * 2 ^ 59
def prefixEnd_5435122 : Nat := 4983230072969 + 3 ^ 40 * 5435122 * 2
def baseEnd_5435122 : Nat := 2790830001826189293879335

theorem tailTrace_5435122 : CollatzResearch.WordTrace tailWord_5435122 prefixEnd_5435122 2790830001826189293879335 := by
  unfold tailWord_5435122
  simp only [CollatzResearch.WordTrace]
  refine ⟨49558796253872178445338905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132156790010325809187570413 49558796253872178445338905)
  ·
    refine ⟨37169097190404133834004179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49558796253872178445338905 37169097190404133834004179)
    ·
      refine ⟨55753645785606200751006269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37169097190404133834004179 55753645785606200751006269)
      ·
        refine ⟨20907617169602325281627351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55753645785606200751006269 20907617169602325281627351)
        ·
          refine ⟨31361425754403487922441027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20907617169602325281627351 31361425754403487922441027)
          ·
            refine ⟨47042138631605231883661541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31361425754403487922441027 47042138631605231883661541)
            ·
              refine ⟨8820400993425980978186539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47042138631605231883661541 8820400993425980978186539)
              ·
                refine ⟨13230601490138971467279809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8820400993425980978186539 13230601490138971467279809)
                ·
                  refine ⟨9922951117604228600459857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13230601490138971467279809 9922951117604228600459857)
                  ·
                    refine ⟨7442213338203171450344893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9922951117604228600459857 7442213338203171450344893)
                    ·
                      refine ⟨2790830001826189293879335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7442213338203171450344893 2790830001826189293879335)
                      ·
                        rfl

theorem cell23_5435122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_5435122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435122 prefixEnd_5435122 := by exact prefixLift 5435122
  have htrace : WordTrace (prefixWord ++ tailWord_5435122) baseStart_5435122 baseEnd_5435122 := by
    simpa [prefixWord, tailWord_5435122, baseEnd_5435122] using wordTrace_append hprefix tailTrace_5435122
  have hstable : (prefixWord ++ tailWord_5435122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435122).length < 2 ^ (prefixWord ++ tailWord_5435122).sum := by decide
  have hdescent : baseEnd_5435122 < baseStart_5435122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435145 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 3, 5, 2]
def baseStart_5435145 : Nat := 118140960795 + 5435145 * 2 ^ 59
def prefixEnd_5435145 : Nat := 4983230072969 + 3 ^ 40 * 5435145 * 2
def baseEnd_5435145 : Nat := 2790841811881242703891729

theorem tailTrace_5435145 : CollatzResearch.WordTrace tailWord_5435145 prefixEnd_5435145 2790841811881242703891729 := by
  unfold tailWord_5435145
  simp only [CollatzResearch.WordTrace]
  refine ⟨198236023894405388709442889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132157349262936925806295259 198236023894405388709442889)
  ·
    refine ⟨148677017920804041532082167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198236023894405388709442889 148677017920804041532082167)
    ·
      refine ⟨223015526881206062298123251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148677017920804041532082167 223015526881206062298123251)
      ·
        refine ⟨334523290321809093447184877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223015526881206062298123251 334523290321809093447184877)
        ·
          refine ⟨125446233870678410042694329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 334523290321809093447184877 125446233870678410042694329)
          ·
            refine ⟨94084675403008807532020747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125446233870678410042694329 94084675403008807532020747)
            ·
              refine ⟨141127013104513211298031121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94084675403008807532020747 141127013104513211298031121)
              ·
                refine ⟨105845259828384908473523341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141127013104513211298031121 105845259828384908473523341)
                ·
                  refine ⟨39691972435644340677571253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105845259828384908473523341 39691972435644340677571253)
                  ·
                    refine ⟨3721122415841656938522305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39691972435644340677571253 3721122415841656938522305)
                    ·
                      refine ⟨2790841811881242703891729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3721122415841656938522305 2790841811881242703891729)
                      ·
                        rfl

theorem cell23_5435145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 5, 2].length) (baseStart_5435145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435145 prefixEnd_5435145 := by exact prefixLift 5435145
  have htrace : WordTrace (prefixWord ++ tailWord_5435145) baseStart_5435145 baseEnd_5435145 := by
    simpa [prefixWord, tailWord_5435145, baseEnd_5435145] using wordTrace_append hprefix tailTrace_5435145
  have hstable : (prefixWord ++ tailWord_5435145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435145).length < 2 ^ (prefixWord ++ tailWord_5435145).sum := by decide
  have hdescent : baseEnd_5435145 < baseStart_5435145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435146 : List Nat := [3, 1, 2, 2, 1, 5, 2, 2, 1, 4]
def baseStart_5435146 : Nat := 118140960795 + 5435146 * 2 ^ 59
def prefixEnd_5435146 : Nat := 4983230072969 + 3 ^ 40 * 5435146 * 2
def baseEnd_5435146 : Nat := 930280775120632399993075

theorem tailTrace_5435146 : CollatzResearch.WordTrace tailWord_5435146 prefixEnd_5435146 930280775120632399993075 := by
  unfold tailWord_5435146
  simp only [CollatzResearch.WordTrace]
  refine ⟨49559015091850441470057323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132157373578267843920152861 49559015091850441470057323)
  ·
    refine ⟨74338522637775662205085985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49559015091850441470057323 74338522637775662205085985)
    ·
      refine ⟨55753891978331746653814489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74338522637775662205085985 55753891978331746653814489)
      ·
        refine ⟨41815418983748809990360867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55753891978331746653814489 41815418983748809990360867)
        ·
          refine ⟨62723128475623214985541301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41815418983748809990360867 62723128475623214985541301)
          ·
            refine ⟨5880293294589676404894497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62723128475623214985541301 5880293294589676404894497)
            ·
              refine ⟨4410219970942257303670873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5880293294589676404894497 4410219970942257303670873)
              ·
                refine ⟨3307664978206692977753155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4410219970942257303670873 3307664978206692977753155)
                ·
                  refine ⟨4961497467310039466629733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3307664978206692977753155 4961497467310039466629733)
                  ·
                    refine ⟨930280775120632399993075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4961497467310039466629733 930280775120632399993075)
                    ·
                      rfl

theorem cell23_5435146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 2, 1, 4].length) (baseStart_5435146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435146 prefixEnd_5435146 := by exact prefixLift 5435146
  have htrace : WordTrace (prefixWord ++ tailWord_5435146) baseStart_5435146 baseEnd_5435146 := by
    simpa [prefixWord, tailWord_5435146, baseEnd_5435146] using wordTrace_append hprefix tailTrace_5435146
  have hstable : (prefixWord ++ tailWord_5435146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435146).length < 2 ^ (prefixWord ++ tailWord_5435146).sum := by decide
  have hdescent : baseEnd_5435146 < baseStart_5435146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435185 : List Nat := [1, 2, 2, 3, 2, 2, 2, 2, 1, 6]
def baseStart_5435185 : Nat := 118140960795 + 5435185 * 2 ^ 59
def prefixEnd_5435185 : Nat := 4983230072969 + 3 ^ 40 * 5435185 * 2
def baseEnd_5435185 : Nat := 930287450369140849130515

theorem tailTrace_5435185 : CollatzResearch.WordTrace tailWord_5435185 prefixEnd_5435185 930287450369140849130515 := by
  unfold tailWord_5435185
  simp only [CollatzResearch.WordTrace]
  refine ⟨198237482814260475540899009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132158321876173650360599339 198237482814260475540899009)
  ·
    refine ⟨148678112110695356655674257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198237482814260475540899009 148678112110695356655674257)
    ·
      refine ⟨111508584083021517491755693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148678112110695356655674257 111508584083021517491755693)
      ·
        refine ⟨41815719031133069059408385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111508584083021517491755693 41815719031133069059408385)
        ·
          refine ⟨31361789273349801794556289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41815719031133069059408385 31361789273349801794556289)
          ·
            refine ⟨23521341955012351345917217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31361789273349801794556289 23521341955012351345917217)
            ·
              refine ⟨17641006466259263509437913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23521341955012351345917217 17641006466259263509437913)
              ·
                refine ⟨13230754849694447632078435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17641006466259263509437913 13230754849694447632078435)
                ·
                  refine ⟨19846132274541671448117653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13230754849694447632078435 19846132274541671448117653)
                  ·
                    refine ⟨930287450369140849130515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19846132274541671448117653 930287450369140849130515)
                    ·
                      rfl

theorem cell23_5435185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 6].length) (baseStart_5435185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435185 prefixEnd_5435185 := by exact prefixLift 5435185
  have htrace : WordTrace (prefixWord ++ tailWord_5435185) baseStart_5435185 baseEnd_5435185 := by
    simpa [prefixWord, tailWord_5435185, baseEnd_5435185] using wordTrace_append hprefix tailTrace_5435185
  have hstable : (prefixWord ++ tailWord_5435185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435185).length < 2 ^ (prefixWord ++ tailWord_5435185).sum := by decide
  have hdescent : baseEnd_5435185 < baseStart_5435185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435186 : List Nat := [3, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3]
def baseStart_5435186 : Nat := 118140960795 + 5435186 * 2 ^ 59
def prefixEnd_5435186 : Nat := 4983230072969 + 3 ^ 40 * 5435186 * 2
def baseEnd_5435186 : Nat := 2790862864588077043479041

theorem tailTrace_5435186 : CollatzResearch.WordTrace tailWord_5435186 prefixEnd_5435186 2790862864588077043479041 := by
  unfold tailWord_5435186
  simp only [CollatzResearch.WordTrace]
  refine ⟨49559379821814213177921353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132158346191504568474456941 49559379821814213177921353)
  ·
    refine ⟨37169534866360659883441015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49559379821814213177921353 37169534866360659883441015)
    ·
      refine ⟨55754302299540989825161523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37169534866360659883441015 55754302299540989825161523)
      ·
        refine ⟨83631453449311484737742285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55754302299540989825161523 83631453449311484737742285)
        ·
          refine ⟨31361795043491806776653357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83631453449311484737742285 31361795043491806776653357)
          ·
            refine ⟨11760673141309427541245009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31361795043491806776653357 11760673141309427541245009)
            ·
              refine ⟨8820504855982070655933757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11760673141309427541245009 8820504855982070655933757)
              ·
                refine ⟨3307689320993276495975159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8820504855982070655933757 3307689320993276495975159)
                ·
                  refine ⟨4961533981489914743962739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3307689320993276495975159 4961533981489914743962739)
                  ·
                    refine ⟨7442300972234872115944109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4961533981489914743962739 7442300972234872115944109)
                    ·
                      refine ⟨2790862864588077043479041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7442300972234872115944109 2790862864588077043479041)
                      ·
                        rfl

theorem cell23_5435186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3].length) (baseStart_5435186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435186 prefixEnd_5435186 := by exact prefixLift 5435186
  have htrace : WordTrace (prefixWord ++ tailWord_5435186) baseStart_5435186 baseEnd_5435186 := by
    simpa [prefixWord, tailWord_5435186, baseEnd_5435186] using wordTrace_append hprefix tailTrace_5435186
  have hstable : (prefixWord ++ tailWord_5435186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435186).length < 2 ^ (prefixWord ++ tailWord_5435186).sum := by decide
  have hdescent : baseEnd_5435186 < baseStart_5435186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435192 : List Nat := [2, 1, 2, 1, 3, 4, 1, 3, 1, 1, 4]
def baseStart_5435192 : Nat := 118140960795 + 5435192 * 2 ^ 59
def prefixEnd_5435192 : Nat := 4983230072969 + 3 ^ 40 * 5435192 * 2
def baseEnd_5435192 : Nat := 2790865945472004020004013

theorem tailTrace_5435192 : CollatzResearch.WordTrace tailWord_5435192 prefixEnd_5435192 2790865945472004020004013 := by
  unfold tailWord_5435192
  simp only [CollatzResearch.WordTrace]
  refine ⟨99118869062617557868201915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132158492083490077157602553 99118869062617557868201915)
  ·
    refine ⟨148678303593926336802302873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99118869062617557868201915 148678303593926336802302873)
    ·
      refine ⟨111508727695444752601727155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148678303593926336802302873 111508727695444752601727155)
      ·
        refine ⟨167263091543167128902590733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111508727695444752601727155 167263091543167128902590733)
        ·
          refine ⟨62723659328687673338471525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167263091543167128902590733 62723659328687673338471525)
          ·
            refine ⟨11760686124128938750963411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62723659328687673338471525 11760686124128938750963411)
            ·
              refine ⟨17641029186193408126445117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11760686124128938750963411 17641029186193408126445117)
              ·
                refine ⟨6615385944822528047416919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17641029186193408126445117 6615385944822528047416919)
                ·
                  refine ⟨9923078917233792071125379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6615385944822528047416919 9923078917233792071125379)
                  ·
                    refine ⟨14884618375850688106688069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9923078917233792071125379 14884618375850688106688069)
                    ·
                      refine ⟨2790865945472004020004013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14884618375850688106688069 2790865945472004020004013)
                      ·
                        rfl

theorem cell23_5435192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 1, 1, 4].length) (baseStart_5435192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435192 prefixEnd_5435192 := by exact prefixLift 5435192
  have htrace : WordTrace (prefixWord ++ tailWord_5435192) baseStart_5435192 baseEnd_5435192 := by
    simpa [prefixWord, tailWord_5435192, baseEnd_5435192] using wordTrace_append hprefix tailTrace_5435192
  have hstable : (prefixWord ++ tailWord_5435192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435192).length < 2 ^ (prefixWord ++ tailWord_5435192).sum := by decide
  have hdescent : baseEnd_5435192 < baseStart_5435192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435209 : List Nat := [1, 2, 1, 1, 2, 4, 4, 1, 3, 2, 2]
def baseStart_5435209 : Nat := 118140960795 + 5435209 * 2 ^ 59
def prefixEnd_5435209 : Nat := 4983230072969 + 3 ^ 40 * 5435209 * 2
def baseEnd_5435209 : Nat := 2790874674643130453491435

theorem tailTrace_5435209 : CollatzResearch.WordTrace tailWord_5435209 prefixEnd_5435209 2790874674643130453491435 := by
  unfold tailWord_5435209
  simp only [CollatzResearch.WordTrace]
  refine ⟨198238358166173527639772681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132158905444115685093181787 198238358166173527639772681)
  ·
    refine ⟨148678768624630145729829511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198238358166173527639772681 148678768624630145729829511)
    ·
      refine ⟨223018152936945218594744267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148678768624630145729829511 223018152936945218594744267)
      ·
        refine ⟨334527229405417827892116401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223018152936945218594744267 334527229405417827892116401)
        ·
          refine ⟨250895422054063370919087301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 334527229405417827892116401 250895422054063370919087301)
          ·
            refine ⟨47042891635136882047328869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 250895422054063370919087301 47042891635136882047328869)
            ·
              refine ⟨8820542181588165383874163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47042891635136882047328869 8820542181588165383874163)
              ·
                refine ⟨13230813272382248075811245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8820542181588165383874163 13230813272382248075811245)
                ·
                  refine ⟨4961554977143343028429217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13230813272382248075811245 4961554977143343028429217)
                  ·
                    refine ⟨3721166232857507271321913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4961554977143343028429217 3721166232857507271321913)
                    ·
                      refine ⟨2790874674643130453491435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3721166232857507271321913 2790874674643130453491435)
                      ·
                        rfl

theorem cell23_5435209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 3, 2, 2].length) (baseStart_5435209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435209 prefixEnd_5435209 := by exact prefixLift 5435209
  have htrace : WordTrace (prefixWord ++ tailWord_5435209) baseStart_5435209 baseEnd_5435209 := by
    simpa [prefixWord, tailWord_5435209, baseEnd_5435209] using wordTrace_append hprefix tailTrace_5435209
  have hstable : (prefixWord ++ tailWord_5435209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435209).length < 2 ^ (prefixWord ++ tailWord_5435209).sum := by decide
  have hdescent : baseEnd_5435209 < baseStart_5435209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435212 : List Nat := [2, 2, 1, 3, 4, 1, 1, 2, 1, 1, 5]
def baseStart_5435212 : Nat := 118140960795 + 5435212 * 2 ^ 59
def prefixEnd_5435212 : Nat := 4983230072969 + 3 ^ 40 * 5435212 * 2
def baseEnd_5435212 : Nat := 2790876215085093941753921

theorem tailTrace_5435212 : CollatzResearch.WordTrace tailWord_5435212 prefixEnd_5435212 2790876215085093941753921 := by
  unfold tailWord_5435212
  simp only [CollatzResearch.WordTrace]
  refine ⟨99119233792581329576065945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132158978390108439434754593 99119233792581329576065945)
  ·
    refine ⟨74339425344435997182049459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99119233792581329576065945 74339425344435997182049459)
    ·
      refine ⟨111509138016653995773074189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74339425344435997182049459 111509138016653995773074189)
      ·
        refine ⟨41815926756245248414902821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111509138016653995773074189 41815926756245248414902821)
        ·
          refine ⟨7840486266795984077794279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41815926756245248414902821 7840486266795984077794279)
          ·
            refine ⟨11760729400193976116691419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7840486266795984077794279 11760729400193976116691419)
            ·
              refine ⟨17641094100290964175037129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11760729400193976116691419 17641094100290964175037129)
              ·
                refine ⟨13230820575218223131277847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17641094100290964175037129 13230820575218223131277847)
                ·
                  refine ⟨19846230862827334696916771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13230820575218223131277847 19846230862827334696916771)
                  ·
                    refine ⟨29769346294241002045375157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19846230862827334696916771 29769346294241002045375157)
                    ·
                      refine ⟨2790876215085093941753921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29769346294241002045375157 2790876215085093941753921)
                      ·
                        rfl

theorem cell23_5435212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_5435212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435212 prefixEnd_5435212 := by exact prefixLift 5435212
  have htrace : WordTrace (prefixWord ++ tailWord_5435212) baseStart_5435212 baseEnd_5435212 := by
    simpa [prefixWord, tailWord_5435212, baseEnd_5435212] using wordTrace_append hprefix tailTrace_5435212
  have hstable : (prefixWord ++ tailWord_5435212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435212).length < 2 ^ (prefixWord ++ tailWord_5435212).sum := by decide
  have hdescent : baseEnd_5435212 < baseStart_5435212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435232 : List Nat := [2, 1, 1, 3, 3, 4, 2, 7]
def baseStart_5435232 : Nat := 118140960795 + 5435232 * 2 ^ 59
def prefixEnd_5435232 : Nat := 4983230072969 + 3 ^ 40 * 5435232 * 2
def baseEnd_5435232 : Nat := 103366166099932735685327

theorem tailTrace_5435232 : CollatzResearch.WordTrace tailWord_5435232 prefixEnd_5435232 103366166099932735685327 := by
  unfold tailWord_5435232
  simp only [CollatzResearch.WordTrace]
  refine ⟨99119598522545101283929975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132159464696726801711906633 99119598522545101283929975)
  ·
    refine ⟨148679397783817651925894963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99119598522545101283929975 148679397783817651925894963)
    ·
      refine ⟨223019096675726477888842445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148679397783817651925894963 223019096675726477888842445)
      ·
        refine ⟨83632161253397429208315917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223019096675726477888842445 83632161253397429208315917)
        ·
          refine ⟨31362060470024035953118469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83632161253397429208315917 31362060470024035953118469)
          ·
            refine ⟨5880386338129506741209713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31362060470024035953118469 5880386338129506741209713)
            ·
              refine ⟨4410289753597130055907285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5880386338129506741209713 4410289753597130055907285)
              ·
                refine ⟨103366166099932735685327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4410289753597130055907285 103366166099932735685327)
                ·
                  rfl

theorem cell23_5435232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 7].length) (baseStart_5435232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435232 prefixEnd_5435232 := by exact prefixLift 5435232
  have htrace : WordTrace (prefixWord ++ tailWord_5435232) baseStart_5435232 baseEnd_5435232 := by
    simpa [prefixWord, tailWord_5435232, baseEnd_5435232] using wordTrace_append hprefix tailTrace_5435232
  have hstable : (prefixWord ++ tailWord_5435232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435232).length < 2 ^ (prefixWord ++ tailWord_5435232).sum := by decide
  have hdescent : baseEnd_5435232 < baseStart_5435232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435285 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 4, 1, 5]
def baseStart_5435285 : Nat := 118140960795 + 5435285 * 2 ^ 59
def prefixEnd_5435285 : Nat := 4983230072969 + 3 ^ 40 * 5435285 * 2
def baseEnd_5435285 : Nat := 2790913699172872156141085

theorem tailTrace_5435285 : CollatzResearch.WordTrace tailWord_5435285 prefixEnd_5435285 2790913699172872156141085 := by
  unfold tailWord_5435285
  simp only [CollatzResearch.WordTrace]
  refine ⟨198241130113898192619539309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132160753409265461746359539 198241130113898192619539309)
  ·
    refine ⟨74340423792711822232327241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198241130113898192619539309 74340423792711822232327241)
    ·
      refine ⟨55755317844533866674245431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74340423792711822232327241 55755317844533866674245431)
      ·
        refine ⟨83632976766800800011368147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55755317844533866674245431 83632976766800800011368147)
        ·
          refine ⟨125449465150201200017052221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83632976766800800011368147 125449465150201200017052221)
          ·
            refine ⟨47043549431325450006394583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125449465150201200017052221 47043549431325450006394583)
            ·
              refine ⟨70565324146988175009591875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47043549431325450006394583 70565324146988175009591875)
              ·
                refine ⟨105847986220482262514387813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70565324146988175009591875 105847986220482262514387813)
                ·
                  refine ⟨19846497416340424221447715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105847986220482262514387813 19846497416340424221447715)
                  ·
                    refine ⟨29769746124510636332171573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19846497416340424221447715 29769746124510636332171573)
                    ·
                      refine ⟨2790913699172872156141085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29769746124510636332171573 2790913699172872156141085)
                      ·
                        rfl

theorem cell23_5435285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_5435285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435285 prefixEnd_5435285 := by exact prefixLift 5435285
  have htrace : WordTrace (prefixWord ++ tailWord_5435285) baseStart_5435285 baseEnd_5435285 := by
    simpa [prefixWord, tailWord_5435285, baseEnd_5435285] using wordTrace_append hprefix tailTrace_5435285
  have hstable : (prefixWord ++ tailWord_5435285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435285).length < 2 ^ (prefixWord ++ tailWord_5435285).sum := by decide
  have hdescent : baseEnd_5435285 < baseStart_5435285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435303 : List Nat := [1, 1, 6, 1, 2, 2, 3, 1, 1, 3, 2]
def baseStart_5435303 : Nat := 118140960795 + 5435303 * 2 ^ 59
def prefixEnd_5435303 : Nat := 4983230072969 + 3 ^ 40 * 5435303 * 2
def baseEnd_5435303 : Nat := 2790922941824653085716003

theorem tailTrace_5435303 : CollatzResearch.WordTrace tailWord_5435303 prefixEnd_5435303 2790922941824653085716003 := by
  unfold tailWord_5435303
  simp only [CollatzResearch.WordTrace]
  refine ⟨198241786627832981693694563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132161191085221987795796375 198241786627832981693694563)
  ·
    refine ⟨297362679941749472540541845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198241786627832981693694563 297362679941749472540541845)
    ·
      refine ⟨13938875622269506525337899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 297362679941749472540541845 13938875622269506525337899)
      ·
        refine ⟨20908313433404259788006849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13938875622269506525337899 20908313433404259788006849)
        ·
          refine ⟨15681235075053194841005137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20908313433404259788006849 15681235075053194841005137)
          ·
            refine ⟨11760926306289896130753853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15681235075053194841005137 11760926306289896130753853)
            ·
              refine ⟨4410347364858711049032695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11760926306289896130753853 4410347364858711049032695)
              ·
                refine ⟨6615521047288066573549043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4410347364858711049032695 6615521047288066573549043)
                ·
                  refine ⟨9923281570932099860323565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6615521047288066573549043 9923281570932099860323565)
                  ·
                    refine ⟨3721230589099537447621337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9923281570932099860323565 3721230589099537447621337)
                    ·
                      refine ⟨2790922941824653085716003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3721230589099537447621337 2790922941824653085716003)
                      ·
                        rfl

theorem cell23_5435303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_5435303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435303 prefixEnd_5435303 := by exact prefixLift 5435303
  have htrace : WordTrace (prefixWord ++ tailWord_5435303) baseStart_5435303 baseEnd_5435303 := by
    simpa [prefixWord, tailWord_5435303, baseEnd_5435303] using wordTrace_append hprefix tailTrace_5435303
  have hstable : (prefixWord ++ tailWord_5435303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435303).length < 2 ^ (prefixWord ++ tailWord_5435303).sum := by decide
  have hdescent : baseEnd_5435303 < baseStart_5435303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435335 : List Nat := [1, 1, 4, 1, 1, 2, 1, 4, 1, 7]
def baseStart_5435335 : Nat := 118140960795 + 5435335 * 2 ^ 59
def prefixEnd_5435335 : Nat := 4983230072969 + 3 ^ 40 * 5435335 * 2
def baseEnd_5435335 : Nat := 930313124401865653505285

theorem tailTrace_5435335 : CollatzResearch.WordTrace tailWord_5435335 prefixEnd_5435335 930313124401865653505285 := by
  unfold tailWord_5435335
  simp only [CollatzResearch.WordTrace]
  refine ⟨198242953763717051158859459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132161969175811367439239639 198242953763717051158859459)
  ·
    refine ⟨297364430645575576738289189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198242953763717051158859459 297364430645575576738289189)
    ·
      refine ⟨55755830746045420638429223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 297364430645575576738289189 55755830746045420638429223)
      ·
        refine ⟨83633746119068130957643835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55755830746045420638429223 83633746119068130957643835)
        ·
          refine ⟨125450619178602196436465753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83633746119068130957643835 125450619178602196436465753)
          ·
            refine ⟨94087964383951647327349315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125450619178602196436465753 94087964383951647327349315)
            ·
              refine ⟨141131946575927470991023973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94087964383951647327349315 141131946575927470991023973)
              ·
                refine ⟨26462239982986400810816995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 141131946575927470991023973 26462239982986400810816995)
                ·
                  refine ⟨39693359974479601216225493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26462239982986400810816995 39693359974479601216225493)
                  ·
                    refine ⟨930313124401865653505285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39693359974479601216225493 930313124401865653505285)
                    ·
                      rfl

theorem cell23_5435335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_5435335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435335 prefixEnd_5435335 := by exact prefixLift 5435335
  have htrace : WordTrace (prefixWord ++ tailWord_5435335) baseStart_5435335 baseEnd_5435335 := by
    simpa [prefixWord, tailWord_5435335, baseEnd_5435335] using wordTrace_append hprefix tailTrace_5435335
  have hstable : (prefixWord ++ tailWord_5435335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435335).length < 2 ^ (prefixWord ++ tailWord_5435335).sum := by decide
  have hdescent : baseEnd_5435335 < baseStart_5435335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435345 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 3, 2, 5]
def baseStart_5435345 : Nat := 118140960795 + 5435345 * 2 ^ 59
def prefixEnd_5435345 : Nat := 4983230072969 + 3 ^ 40 * 5435345 * 2
def baseEnd_5435345 : Nat := 2790944508012141921390809

theorem tailTrace_5435345 : CollatzResearch.WordTrace tailWord_5435345 prefixEnd_5435345 2790944508012141921390809 := by
  unfold tailWord_5435345
  simp only [CollatzResearch.WordTrace]
  refine ⟨198243318493680822866723489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132162212329120548577815659 198243318493680822866723489)
  ·
    refine ⟨148682488870260617150042617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198243318493680822866723489 148682488870260617150042617)
    ·
      refine ⟨111511866652695462862531963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148682488870260617150042617 111511866652695462862531963)
      ·
        refine ⟨167267799979043194293797945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111511866652695462862531963 167267799979043194293797945)
        ·
          refine ⟨125450849984282395720348459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167267799979043194293797945 125450849984282395720348459)
          ·
            refine ⟨188176274976423593580522689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125450849984282395720348459 188176274976423593580522689)
            ·
              refine ⟨141132206232317695185392017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188176274976423593580522689 141132206232317695185392017)
              ·
                refine ⟨105849154674238271389044013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141132206232317695185392017 105849154674238271389044013)
                ·
                  refine ⟨39693433002839351770891505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105849154674238271389044013 39693433002839351770891505)
                  ·
                    refine ⟨29770074752129513828168629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39693433002839351770891505 29770074752129513828168629)
                    ·
                      refine ⟨2790944508012141921390809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29770074752129513828168629 2790944508012141921390809)
                      ·
                        rfl

theorem cell23_5435345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_5435345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435345 prefixEnd_5435345 := by exact prefixLift 5435345
  have htrace : WordTrace (prefixWord ++ tailWord_5435345) baseStart_5435345 baseEnd_5435345 := by
    simpa [prefixWord, tailWord_5435345, baseEnd_5435345] using wordTrace_append hprefix tailTrace_5435345
  have hstable : (prefixWord ++ tailWord_5435345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435345).length < 2 ^ (prefixWord ++ tailWord_5435345).sum := by decide
  have hdescent : baseEnd_5435345 < baseStart_5435345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435372 : List Nat := [2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 4]
def baseStart_5435372 : Nat := 118140960795 + 5435372 * 2 ^ 59
def prefixEnd_5435372 : Nat := 4983230072969 + 3 ^ 40 * 5435372 * 2
def baseEnd_5435372 : Nat := 2790958371989813315753185

theorem tailTrace_5435372 : CollatzResearch.WordTrace tailWord_5435372 prefixEnd_5435372 2790958371989813315753185 := by
  unfold tailWord_5435372
  simp only [CollatzResearch.WordTrace]
  refine ⟨99122151632291503238978185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132162868843055337651970913 99122151632291503238978185)
  ·
    refine ⟨74341613724218627429233639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99122151632291503238978185 74341613724218627429233639)
    ·
      refine ⟨111512420586327941143850459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74341613724218627429233639 111512420586327941143850459)
      ·
        refine ⟨167268630879491911715775689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111512420586327941143850459 167268630879491911715775689)
        ·
          refine ⟨125451473159618933786831767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167268630879491911715775689 125451473159618933786831767)
          ·
            refine ⟨188177209739428400680247651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125451473159618933786831767 188177209739428400680247651)
            ·
              refine ⟨282265814609142601020371477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188177209739428400680247651 282265814609142601020371477)
              ·
                refine ⟨13231210059803559422829913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 282265814609142601020371477 13231210059803559422829913)
                ·
                  refine ⟨9923407544852669567122435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13231210059803559422829913 9923407544852669567122435)
                  ·
                    refine ⟨14885111317279004350683653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9923407544852669567122435 14885111317279004350683653)
                    ·
                      refine ⟨2790958371989813315753185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14885111317279004350683653 2790958371989813315753185)
                      ·
                        rfl

theorem cell23_5435372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 4].length) (baseStart_5435372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435372 prefixEnd_5435372 := by exact prefixLift 5435372
  have htrace : WordTrace (prefixWord ++ tailWord_5435372) baseStart_5435372 baseEnd_5435372 := by
    simpa [prefixWord, tailWord_5435372, baseEnd_5435372] using wordTrace_append hprefix tailTrace_5435372
  have hstable : (prefixWord ++ tailWord_5435372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435372).length < 2 ^ (prefixWord ++ tailWord_5435372).sum := by decide
  have hdescent : baseEnd_5435372 < baseStart_5435372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435389 : List Nat := [1, 4, 1, 1, 1, 2, 4, 1, 2, 4, 2]
def baseStart_5435389 : Nat := 118140960795 + 5435389 * 2 ^ 59
def prefixEnd_5435389 : Nat := 4983230072969 + 3 ^ 40 * 5435389 * 2
def baseEnd_5435389 : Nat := 2790967101160939749240607

theorem tailTrace_5435389 : CollatzResearch.WordTrace tailWord_5435389 prefixEnd_5435389 2790967101160939749240607 := by
  unfold tailWord_5435389
  simp only [CollatzResearch.WordTrace]
  refine ⟨198244923305521418381325221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132163282203680945587550147 198244923305521418381325221)
  ·
    refine ⟨37170923119785265946498479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198244923305521418381325221 37170923119785265946498479)
    ·
      refine ⟨55756384679677898919747719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37170923119785265946498479 55756384679677898919747719)
      ·
        refine ⟨83634577019516848379621579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55756384679677898919747719 83634577019516848379621579)
        ·
          refine ⟨125451865529275272569432369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83634577019516848379621579 125451865529275272569432369)
          ·
            refine ⟨94088899146956454427074277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125451865529275272569432369 94088899146956454427074277)
            ·
              refine ⟨17641668590054335205076427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94088899146956454427074277 17641668590054335205076427)
              ·
                refine ⟨26462502885081502807614641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17641668590054335205076427 26462502885081502807614641)
                ·
                  refine ⟨19846877163811127105710981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26462502885081502807614641 19846877163811127105710981)
                  ·
                    refine ⟨3721289468214586332320809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19846877163811127105710981 3721289468214586332320809)
                    ·
                      refine ⟨2790967101160939749240607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3721289468214586332320809 2790967101160939749240607)
                      ·
                        rfl

theorem cell23_5435389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 4, 2].length) (baseStart_5435389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435389 prefixEnd_5435389 := by exact prefixLift 5435389
  have htrace : WordTrace (prefixWord ++ tailWord_5435389) baseStart_5435389 baseEnd_5435389 := by
    simpa [prefixWord, tailWord_5435389, baseEnd_5435389] using wordTrace_append hprefix tailTrace_5435389
  have hstable : (prefixWord ++ tailWord_5435389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435389).length < 2 ^ (prefixWord ++ tailWord_5435389).sum := by decide
  have hdescent : baseEnd_5435389 < baseStart_5435389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435392 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 3]
def baseStart_5435392 : Nat := 118140960795 + 5435392 * 2 ^ 59
def prefixEnd_5435392 : Nat := 4983230072969 + 3 ^ 40 * 5435392 * 2
def baseEnd_5435392 : Nat := 2790968641602903237503093

theorem tailTrace_5435392 : CollatzResearch.WordTrace tailWord_5435392 prefixEnd_5435392 2790968641602903237503093 := by
  unfold tailWord_5435392
  simp only [CollatzResearch.WordTrace]
  refine ⟨99122516362255274946842215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132163355149673699929122953 99122516362255274946842215)
  ·
    refine ⟨148683774543382912420263323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99122516362255274946842215 148683774543382912420263323)
    ·
      refine ⟨223025661815074368630394985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148683774543382912420263323 223025661815074368630394985)
      ·
        refine ⟨167269246361305776472796239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223025661815074368630394985 167269246361305776472796239)
        ·
          refine ⟨250903869541958664709194359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167269246361305776472796239 250903869541958664709194359)
          ·
            refine ⟨376355804312937997063791539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250903869541958664709194359 376355804312937997063791539)
            ·
              refine ⟨564533706469406995595687309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376355804312937997063791539 564533706469406995595687309)
              ·
                refine ⟨211700139926027623348382741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 564533706469406995595687309 211700139926027623348382741)
                ·
                  refine ⟨9923444059032544844455441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 211700139926027623348382741 9923444059032544844455441)
                  ·
                    refine ⟨7442583044274408633341581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9923444059032544844455441 7442583044274408633341581)
                    ·
                      refine ⟨2790968641602903237503093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7442583044274408633341581 2790968641602903237503093)
                      ·
                        rfl

theorem cell23_5435392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 3].length) (baseStart_5435392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435392 prefixEnd_5435392 := by exact prefixLift 5435392
  have htrace : WordTrace (prefixWord ++ tailWord_5435392) baseStart_5435392 baseEnd_5435392 := by
    simpa [prefixWord, tailWord_5435392, baseEnd_5435392] using wordTrace_append hprefix tailTrace_5435392
  have hstable : (prefixWord ++ tailWord_5435392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435392).length < 2 ^ (prefixWord ++ tailWord_5435392).sum := by decide
  have hdescent : baseEnd_5435392 < baseStart_5435392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435399 : List Nat := [1, 1, 4, 3, 1, 2, 2, 2, 3, 4]
def baseStart_5435399 : Nat := 118140960795 + 5435399 * 2 ^ 59
def prefixEnd_5435399 : Nat := 4983230072969 + 3 ^ 40 * 5435399 * 2
def baseEnd_5435399 : Nat := 930324078655828236705187

theorem tailTrace_5435399 : CollatzResearch.WordTrace tailWord_5435399 prefixEnd_5435399 930324078655828236705187 := by
  unfold tailWord_5435399
  simp only [CollatzResearch.WordTrace]
  refine ⟨198245288035485190089189251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132163525356990126726126167 198245288035485190089189251)
  ·
    refine ⟨297367932053227785133783877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198245288035485190089189251 297367932053227785133783877)
    ·
      refine ⟨55756487259980209712584477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 297367932053227785133783877 55756487259980209712584477)
      ·
        refine ⟨20908682722492578642219179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55756487259980209712584477 20908682722492578642219179)
        ·
          refine ⟨31363024083738867963328769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20908682722492578642219179 31363024083738867963328769)
          ·
            refine ⟨23522268062804150972496577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31363024083738867963328769 23522268062804150972496577)
            ·
              refine ⟨17641701047103113229372433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23522268062804150972496577 17641701047103113229372433)
              ·
                refine ⟨13231275785327334922029325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17641701047103113229372433 13231275785327334922029325)
                ·
                  refine ⟨4961728419497750595760997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13231275785327334922029325 4961728419497750595760997)
                  ·
                    refine ⟨930324078655828236705187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4961728419497750595760997 930324078655828236705187)
                    ·
                      rfl

theorem cell23_5435399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_5435399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435399 prefixEnd_5435399 := by exact prefixLift 5435399
  have htrace : WordTrace (prefixWord ++ tailWord_5435399) baseStart_5435399 baseEnd_5435399 := by
    simpa [prefixWord, tailWord_5435399, baseEnd_5435399] using wordTrace_append hprefix tailTrace_5435399
  have hstable : (prefixWord ++ tailWord_5435399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435399).length < 2 ^ (prefixWord ++ tailWord_5435399).sum := by decide
  have hdescent : baseEnd_5435399 < baseStart_5435399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435439 : List Nat := [1, 1, 2, 1, 2, 1, 1, 7, 3, 1, 3]
def baseStart_5435439 : Nat := 118140960795 + 5435439 * 2 ^ 59
def prefixEnd_5435439 : Nat := 4983230072969 + 3 ^ 40 * 5435439 * 2
def baseEnd_5435439 : Nat := 2790992775193664553615377

theorem tailTrace_5435439 : CollatzResearch.WordTrace tailWord_5435439 prefixEnd_5435439 2790992775193664553615377 := by
  unfold tailWord_5435439
  simp only [CollatzResearch.WordTrace]
  refine ⟨198246746955340276920645371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132164497970226851280430247 198246746955340276920645371)
  ·
    refine ⟨297370120433010415380968057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198246746955340276920645371 297370120433010415380968057)
    ·
      refine ⟨223027590324757811535726043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297370120433010415380968057 223027590324757811535726043)
      ·
        refine ⟨334541385487136717303589065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223027590324757811535726043 334541385487136717303589065)
        ·
          refine ⟨250906039115352537977691799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 334541385487136717303589065 250906039115352537977691799)
          ·
            refine ⟨376359058673028806966537699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250906039115352537977691799 376359058673028806966537699)
            ·
              refine ⟨564538588009543210449806549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376359058673028806966537699 564538588009543210449806549)
              ·
                refine ⟨13231373156473668994917341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 564538588009543210449806549 13231373156473668994917341)
                ·
                  refine ⟨4961764933677625873094003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13231373156473668994917341 4961764933677625873094003)
                  ·
                    refine ⟨7442647400516438809641005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4961764933677625873094003 7442647400516438809641005)
                    ·
                      refine ⟨2790992775193664553615377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7442647400516438809641005 2790992775193664553615377)
                      ·
                        rfl

theorem cell23_5435439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 3, 1, 3].length) (baseStart_5435439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435439 prefixEnd_5435439 := by exact prefixLift 5435439
  have htrace : WordTrace (prefixWord ++ tailWord_5435439) baseStart_5435439 baseEnd_5435439 := by
    simpa [prefixWord, tailWord_5435439, baseEnd_5435439] using wordTrace_append hprefix tailTrace_5435439
  have hstable : (prefixWord ++ tailWord_5435439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435439).length < 2 ^ (prefixWord ++ tailWord_5435439).sum := by decide
  have hdescent : baseEnd_5435439 < baseStart_5435439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435479 : List Nat := [1, 1, 3, 2, 2, 1, 2, 5, 1, 1, 4]
def baseStart_5435479 : Nat := 118140960795 + 5435479 * 2 ^ 59
def prefixEnd_5435479 : Nat := 4983230072969 + 3 ^ 40 * 5435479 * 2
def baseEnd_5435479 : Nat := 2791013314419844397115193

theorem tailTrace_5435479 : CollatzResearch.WordTrace tailWord_5435479 prefixEnd_5435479 2791013314419844397115193 := by
  unfold tailWord_5435479
  simp only [CollatzResearch.WordTrace]
  refine ⟨198248205875195363752101491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132165470583463575834734327 198248205875195363752101491)
  ·
    refine ⟨297372308812793045628152237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198248205875195363752101491 297372308812793045628152237)
    ·
      refine ⟨111514615804797392110557089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 297372308812793045628152237 111514615804797392110557089)
      ·
        refine ⟨83635961853598044082917817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111514615804797392110557089 83635961853598044082917817)
        ·
          refine ⟨62726971390198533062188363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83635961853598044082917817 62726971390198533062188363)
          ·
            refine ⟨94090457085297799593282545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62726971390198533062188363 94090457085297799593282545)
            ·
              refine ⟨70567842813973349694961909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94090457085297799593282545 70567842813973349694961909)
              ·
                refine ⟨6615735263810001533902679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70567842813973349694961909 6615735263810001533902679)
                ·
                  refine ⟨9923602895715002300854019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6615735263810001533902679 9923602895715002300854019)
                  ·
                    refine ⟨14885404343572503451281029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9923602895715002300854019 14885404343572503451281029)
                    ·
                      refine ⟨2791013314419844397115193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14885404343572503451281029 2791013314419844397115193)
                      ·
                        rfl

theorem cell23_5435479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 1, 4].length) (baseStart_5435479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435479 prefixEnd_5435479 := by exact prefixLift 5435479
  have htrace : WordTrace (prefixWord ++ tailWord_5435479) baseStart_5435479 baseEnd_5435479 := by
    simpa [prefixWord, tailWord_5435479, baseEnd_5435479] using wordTrace_append hprefix tailTrace_5435479
  have hstable : (prefixWord ++ tailWord_5435479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435479).length < 2 ^ (prefixWord ++ tailWord_5435479).sum := by decide
  have hdescent : baseEnd_5435479 < baseStart_5435479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435492 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 3, 1, 6]
def baseStart_5435492 : Nat := 118140960795 + 5435492 * 2 ^ 59
def prefixEnd_5435492 : Nat := 4983230072969 + 3 ^ 40 * 5435492 * 2
def baseEnd_5435492 : Nat := 2791019989668352846252633

theorem tailTrace_5435492 : CollatzResearch.WordTrace tailWord_5435492 prefixEnd_5435492 2791019989668352846252633 := by
  unfold tailWord_5435492
  simp only [CollatzResearch.WordTrace]
  refine ⟨99124340012074133486162365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132165786682765511314883153 99124340012074133486162365)
  ·
    refine ⟨37171627504527800057310887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99124340012074133486162365 37171627504527800057310887)
    ·
      refine ⟨55757441256791700085966331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37171627504527800057310887 55757441256791700085966331)
      ·
        refine ⟨83636161885187550128949497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55757441256791700085966331 83636161885187550128949497)
        ·
          refine ⟨62727121413890662596712123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83636161885187550128949497 62727121413890662596712123)
          ·
            refine ⟨94090682120835993895068185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62727121413890662596712123 94090682120835993895068185)
            ·
              refine ⟨70568011590626995421301139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94090682120835993895068185 70568011590626995421301139)
              ·
                refine ⟨105852017385940493131951709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70568011590626995421301139 105852017385940493131951709)
                ·
                  refine ⟨39694506519727684924481891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105852017385940493131951709 39694506519727684924481891)
                  ·
                    refine ⟨59541759779591527386722837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39694506519727684924481891 59541759779591527386722837)
                    ·
                      refine ⟨2791019989668352846252633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59541759779591527386722837 2791019989668352846252633)
                      ·
                        rfl

theorem cell23_5435492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_5435492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435492 prefixEnd_5435492 := by exact prefixLift 5435492
  have htrace : WordTrace (prefixWord ++ tailWord_5435492) baseStart_5435492 baseEnd_5435492 := by
    simpa [prefixWord, tailWord_5435492, baseEnd_5435492] using wordTrace_append hprefix tailTrace_5435492
  have hstable : (prefixWord ++ tailWord_5435492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435492).length < 2 ^ (prefixWord ++ tailWord_5435492).sum := by decide
  have hdescent : baseEnd_5435492 < baseStart_5435492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435506 : List Nat := [3, 2, 1, 2, 2, 2, 2, 3, 2, 4]
def baseStart_5435506 : Nat := 118140960795 + 5435506 * 2 ^ 59
def prefixEnd_5435506 : Nat := 4983230072969 + 3 ^ 40 * 5435506 * 2
def baseEnd_5435506 : Nat := 930342392799171930492523

theorem tailTrace_5435506 : CollatzResearch.WordTrace tailWord_5435506 prefixEnd_5435506 930342392799171930492523 := by
  unfold tailWord_5435506
  simp only [CollatzResearch.WordTrace]
  refine ⟨49562297661524386840833593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132166127097398364908889581 49562297661524386840833593)
  ·
    refine ⟨37171723246143290130625195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49562297661524386840833593 37171723246143290130625195)
    ·
      refine ⟨55757584869214935195937793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37171723246143290130625195 55757584869214935195937793)
      ·
        refine ⟨41818188651911201396953345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55757584869214935195937793 41818188651911201396953345)
        ·
          refine ⟨31363641488933401047715009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41818188651911201396953345 31363641488933401047715009)
          ·
            refine ⟨23522731116700050785786257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31363641488933401047715009 23522731116700050785786257)
            ·
              refine ⟨17642048337525038089339693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23522731116700050785786257 17642048337525038089339693)
              ·
                refine ⟨6615768126571889283502385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17642048337525038089339693 6615768126571889283502385)
                ·
                  refine ⟨4961826094928916962626789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6615768126571889283502385 4961826094928916962626789)
                  ·
                    refine ⟨930342392799171930492523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4961826094928916962626789 930342392799171930492523)
                    ·
                      rfl

theorem cell23_5435506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_5435506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435506 prefixEnd_5435506 := by exact prefixLift 5435506
  have htrace : WordTrace (prefixWord ++ tailWord_5435506) baseStart_5435506 baseEnd_5435506 := by
    simpa [prefixWord, tailWord_5435506, baseEnd_5435506] using wordTrace_append hprefix tailTrace_5435506
  have hstable : (prefixWord ++ tailWord_5435506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435506).length < 2 ^ (prefixWord ++ tailWord_5435506).sum := by decide
  have hdescent : baseEnd_5435506 < baseStart_5435506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435513 : List Nat := [1, 2, 1, 3, 4, 2, 1, 2, 3, 2, 2]
def baseStart_5435513 : Nat := 118140960795 + 5435513 * 2 ^ 59
def prefixEnd_5435513 : Nat := 4983230072969 + 3 ^ 40 * 5435513 * 2
def baseEnd_5435513 : Nat := 2791030772762097264090037

theorem tailTrace_5435513 : CollatzResearch.WordTrace tailWord_5435513 prefixEnd_5435513 2791030772762097264090037 := by
  unfold tailWord_5435513
  simp only [CollatzResearch.WordTrace]
  refine ⟨198249445957072187558839193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132166297304714791705892795 198249445957072187558839193)
  ·
    refine ⟨148687084467804140669129395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198249445957072187558839193 148687084467804140669129395)
    ·
      refine ⟨223030626701706211003694093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148687084467804140669129395 223030626701706211003694093)
      ·
        refine ⟨83636485013139829126385285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223030626701706211003694093 83636485013139829126385285)
        ·
          refine ⟨15681840939963717961197241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83636485013139829126385285 15681840939963717961197241)
          ·
            refine ⟨11761380704972788470897931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15681840939963717961197241 11761380704972788470897931)
            ·
              refine ⟨17642071057459182706346897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11761380704972788470897931 17642071057459182706346897)
              ·
                refine ⟨13231553293094387029760173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17642071057459182706346897 13231553293094387029760173)
                ·
                  refine ⟨4961832484910395136160065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13231553293094387029760173 4961832484910395136160065)
                  ·
                    refine ⟨3721374363682796352120049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4961832484910395136160065 3721374363682796352120049)
                    ·
                      refine ⟨2791030772762097264090037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3721374363682796352120049 2791030772762097264090037)
                      ·
                        rfl

theorem cell23_5435513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 3, 2, 2].length) (baseStart_5435513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435513 prefixEnd_5435513 := by exact prefixLift 5435513
  have htrace : WordTrace (prefixWord ++ tailWord_5435513) baseStart_5435513 baseEnd_5435513 := by
    simpa [prefixWord, tailWord_5435513, baseEnd_5435513] using wordTrace_append hprefix tailTrace_5435513
  have hstable : (prefixWord ++ tailWord_5435513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435513).length < 2 ^ (prefixWord ++ tailWord_5435513).sum := by decide
  have hdescent : baseEnd_5435513 < baseStart_5435513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435529 : List Nat := [1, 2, 1, 1, 4, 2, 1, 4, 1, 3, 3]
def baseStart_5435529 : Nat := 118140960795 + 5435529 * 2 ^ 59
def prefixEnd_5435529 : Nat := 4983230072969 + 3 ^ 40 * 5435529 * 2
def baseEnd_5435529 : Nat := 2791038988452569201489963

theorem tailTrace_5435529 : CollatzResearch.WordTrace tailWord_5435529 prefixEnd_5435529 2791038988452569201489963 := by
  unfold tailWord_5435529
  simp only [CollatzResearch.WordTrace]
  refine ⟨198250029525014222291421641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132166686350009481527614427 198250029525014222291421641)
  ·
    refine ⟨148687522143760666718566231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198250029525014222291421641 148687522143760666718566231)
    ·
      refine ⟨223031283215641000077849347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148687522143760666718566231 223031283215641000077849347)
      ·
        refine ⟨334546924823461500116774021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223031283215641000077849347 334546924823461500116774021)
        ·
          refine ⟨62727548404399031271895129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 334546924823461500116774021 62727548404399031271895129)
          ·
            refine ⟨47045661303299273453921347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62727548404399031271895129 47045661303299273453921347)
            ·
              refine ⟨70568491954948910180882021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47045661303299273453921347 70568491954948910180882021)
              ·
                refine ⟨13231592241552920658915379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70568491954948910180882021 13231592241552920658915379)
                ·
                  refine ⟨19847388362329380988373069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13231592241552920658915379 19847388362329380988373069)
                  ·
                    refine ⟨7442770635873517870639901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19847388362329380988373069 7442770635873517870639901)
                    ·
                      refine ⟨2791038988452569201489963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7442770635873517870639901 2791038988452569201489963)
                      ·
                        rfl

theorem cell23_5435529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 3, 3].length) (baseStart_5435529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435529 prefixEnd_5435529 := by exact prefixLift 5435529
  have htrace : WordTrace (prefixWord ++ tailWord_5435529) baseStart_5435529 baseEnd_5435529 := by
    simpa [prefixWord, tailWord_5435529, baseEnd_5435529] using wordTrace_append hprefix tailTrace_5435529
  have hstable : (prefixWord ++ tailWord_5435529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435529).length < 2 ^ (prefixWord ++ tailWord_5435529).sum := by decide
  have hdescent : baseEnd_5435529 < baseStart_5435529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435530 : List Nat := [3, 1, 2, 3, 1, 2, 1, 5, 1, 2, 2]
def baseStart_5435530 : Nat := 118140960795 + 5435530 * 2 ^ 59
def prefixEnd_5435530 : Nat := 4983230072969 + 3 ^ 40 * 5435530 * 2
def baseEnd_5435530 : Nat := 2791039501933223697577459

theorem tailTrace_5435530 : CollatzResearch.WordTrace tailWord_5435530 prefixEnd_5435530 2791039501933223697577459 := by
  unfold tailWord_5435530
  simp only [CollatzResearch.WordTrace]
  refine ⟨49562516499502649865552011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132166710665340399641472029 49562516499502649865552011)
  ·
    refine ⟨74343774749253974798328017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49562516499502649865552011 74343774749253974798328017)
    ·
      refine ⟨55757831061940481098746013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74343774749253974798328017 55757831061940481098746013)
      ·
        refine ⟨20909186648227680412029755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55757831061940481098746013 20909186648227680412029755)
        ·
          refine ⟨31363779972341520618044633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20909186648227680412029755 31363779972341520618044633)
          ·
            refine ⟨23522834979256140463533475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31363779972341520618044633 23522834979256140463533475)
            ·
              refine ⟨35284252468884210695300213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23522834979256140463533475 35284252468884210695300213)
              ·
                refine ⟨3307898668957894752684395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35284252468884210695300213 3307898668957894752684395)
                ·
                  refine ⟨4961848003436842129026593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3307898668957894752684395 4961848003436842129026593)
                  ·
                    refine ⟨3721386002577631596769945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4961848003436842129026593 3721386002577631596769945)
                    ·
                      refine ⟨2791039501933223697577459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3721386002577631596769945 2791039501933223697577459)
                      ·
                        rfl

theorem cell23_5435530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_5435530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435530 prefixEnd_5435530 := by exact prefixLift 5435530
  have htrace : WordTrace (prefixWord ++ tailWord_5435530) baseStart_5435530 baseEnd_5435530 := by
    simpa [prefixWord, tailWord_5435530, baseEnd_5435530] using wordTrace_append hprefix tailTrace_5435530
  have hstable : (prefixWord ++ tailWord_5435530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435530).length < 2 ^ (prefixWord ++ tailWord_5435530).sum := by decide
  have hdescent : baseEnd_5435530 < baseStart_5435530 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435609 : List Nat := [1, 2, 1, 2, 3, 1, 5, 1, 7]
def baseStart_5435609 : Nat := 118140960795 + 5435609 * 2 ^ 59
def prefixEnd_5435609 : Nat := 4983230072969 + 3 ^ 40 * 5435609 * 2
def baseEnd_5435609 : Nat := 310120007433880987609955

theorem tailTrace_5435609 : CollatzResearch.WordTrace tailWord_5435609 prefixEnd_5435609 310120007433880987609955 := by
  unfold tailWord_5435609
  simp only [CollatzResearch.WordTrace]
  refine ⟨198252947364724395954333881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132168631576482930636222587 198252947364724395954333881)
  ·
    refine ⟨148689710523543296965750411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198252947364724395954333881 148689710523543296965750411)
    ·
      refine ⟨223034565785314945448625617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148689710523543296965750411 223034565785314945448625617)
      ·
        refine ⟨167275924338986209086469213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223034565785314945448625617 167275924338986209086469213)
        ·
          refine ⟨62728471627119828407425955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167275924338986209086469213 62728471627119828407425955)
          ·
            refine ⟨94092707440679742611138933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62728471627119828407425955 94092707440679742611138933)
            ·
              refine ⟨8821191322563725869794275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94092707440679742611138933 8821191322563725869794275)
              ·
                refine ⟨13231786983845588804691413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8821191322563725869794275 13231786983845588804691413)
                ·
                  refine ⟨310120007433880987609955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13231786983845588804691413 310120007433880987609955)
                  ·
                    rfl

theorem cell23_5435609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 7].length) (baseStart_5435609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435609 prefixEnd_5435609 := by exact prefixLift 5435609
  have htrace : WordTrace (prefixWord ++ tailWord_5435609) baseStart_5435609 baseEnd_5435609 := by
    simpa [prefixWord, tailWord_5435609, baseEnd_5435609] using wordTrace_append hprefix tailTrace_5435609
  have hstable : (prefixWord ++ tailWord_5435609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435609).length < 2 ^ (prefixWord ++ tailWord_5435609).sum := by decide
  have hdescent : baseEnd_5435609 < baseStart_5435609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435649 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 3, 2, 5]
def baseStart_5435649 : Nat := 118140960795 + 5435649 * 2 ^ 59
def prefixEnd_5435649 : Nat := 4983230072969 + 3 ^ 40 * 5435649 * 2
def baseEnd_5435649 : Nat := 2791100606131108731989411

theorem tailTrace_5435649 : CollatzResearch.WordTrace tailWord_5435649 prefixEnd_5435649 2791100606131108731989411 := by
  unfold tailWord_5435649
  simp only [CollatzResearch.WordTrace]
  refine ⟨198254406284579482785790001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132169604189719655190526667 198254406284579482785790001)
  ·
    refine ⟨148690804713434612089342501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198254406284579482785790001 148690804713434612089342501)
    ·
      refine ⟨27879525883768989766751719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148690804713434612089342501 27879525883768989766751719)
      ·
        refine ⟨41819288825653484650127579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27879525883768989766751719 41819288825653484650127579)
        ·
          refine ⟨62728933238480226975191369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41819288825653484650127579 62728933238480226975191369)
          ·
            refine ⟨47046699928860170231393527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62728933238480226975191369 47046699928860170231393527)
            ·
              refine ⟨70570049893290255347090291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47046699928860170231393527 70570049893290255347090291)
              ·
                refine ⟨105855074839935383020635437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70570049893290255347090291 105855074839935383020635437)
                ·
                  refine ⟨39695653064975768632738289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105855074839935383020635437 39695653064975768632738289)
                  ·
                    refine ⟨29771739798731826474553717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39695653064975768632738289 29771739798731826474553717)
                    ·
                      refine ⟨2791100606131108731989411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29771739798731826474553717 2791100606131108731989411)
                      ·
                        rfl

theorem cell23_5435649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_5435649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435649 prefixEnd_5435649 := by exact prefixLift 5435649
  have htrace : WordTrace (prefixWord ++ tailWord_5435649) baseStart_5435649 baseEnd_5435649 := by
    simpa [prefixWord, tailWord_5435649, baseEnd_5435649] using wordTrace_append hprefix tailTrace_5435649
  have hstable : (prefixWord ++ tailWord_5435649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435649).length < 2 ^ (prefixWord ++ tailWord_5435649).sum := by decide
  have hdescent : baseEnd_5435649 < baseStart_5435649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435656 : List Nat := [2, 1, 3, 2, 3, 1, 2, 2, 2, 5]
def baseStart_5435656 : Nat := 118140960795 + 5435656 * 2 ^ 59
def prefixEnd_5435656 : Nat := 4983230072969 + 3 ^ 40 * 5435656 * 2
def baseEnd_5435656 : Nat := 930368066831896734867293

theorem tailTrace_5435656 : CollatzResearch.WordTrace tailWord_5435656 prefixEnd_5435656 930368066831896734867293 := by
  unfold tailWord_5435656
  simp only [CollatzResearch.WordTrace]
  refine ⟨99127330797777061490647411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132169774397036081987529881 99127330797777061490647411)
  ·
    refine ⟨148690996196665592235971117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99127330797777061490647411 148690996196665592235971117)
    ·
      refine ⟨55759123573749597088489169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148690996196665592235971117 55759123573749597088489169)
      ·
        refine ⟨41819342680312197816366877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55759123573749597088489169 41819342680312197816366877)
        ·
          refine ⟨15682253505117074181137579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41819342680312197816366877 15682253505117074181137579)
          ·
            refine ⟨23523380257675611271706369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15682253505117074181137579 23523380257675611271706369)
            ·
              refine ⟨17642535193256708453779777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23523380257675611271706369 17642535193256708453779777)
              ·
                refine ⟨13231901394942531340334833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17642535193256708453779777 13231901394942531340334833)
                ·
                  refine ⟨9923926046206898505251125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13231901394942531340334833 9923926046206898505251125)
                  ·
                    refine ⟨930368066831896734867293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9923926046206898505251125 930368066831896734867293)
                    ·
                      rfl

theorem cell23_5435656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_5435656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435656 prefixEnd_5435656 := by exact prefixLift 5435656
  have htrace : WordTrace (prefixWord ++ tailWord_5435656) baseStart_5435656 baseEnd_5435656 := by
    simpa [prefixWord, tailWord_5435656, baseEnd_5435656] using wordTrace_append hprefix tailTrace_5435656
  have hstable : (prefixWord ++ tailWord_5435656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435656).length < 2 ^ (prefixWord ++ tailWord_5435656).sum := by decide
  have hdescent : baseEnd_5435656 < baseStart_5435656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435690 : List Nat := [3, 1, 4, 2, 2, 2, 1, 1, 2, 5]
def baseStart_5435690 : Nat := 118140960795 + 5435690 * 2 ^ 59
def prefixEnd_5435690 : Nat := 4983230072969 + 3 ^ 40 * 5435690 * 2
def baseEnd_5435690 : Nat := 930373886279314357192241

theorem tailTrace_5435690 : CollatzResearch.WordTrace tailWord_5435690 prefixEnd_5435690 930373886279314357192241 := by
  unfold tailWord_5435690
  simp only [CollatzResearch.WordTrace]
  refine ⟨49563975419357736697008131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132170601118287297858688349 49563975419357736697008131)
  ·
    refine ⟨74345963129036605045512197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49563975419357736697008131 74345963129036605045512197)
    ·
      refine ⟨13939868086694363446033537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74345963129036605045512197 13939868086694363446033537)
      ·
        refine ⟨10454901065020772584525153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13939868086694363446033537 10454901065020772584525153)
        ·
          refine ⟨7841175798765579438393865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10454901065020772584525153 7841175798765579438393865)
          ·
            refine ⟨5880881849074184578795399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7841175798765579438393865 5880881849074184578795399)
            ·
              refine ⟨8821322773611276868193099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5880881849074184578795399 8821322773611276868193099)
              ·
                refine ⟨13231984160416915302289649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8821322773611276868193099 13231984160416915302289649)
                ·
                  refine ⟨9923988120312686476717237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13231984160416915302289649 9923988120312686476717237)
                  ·
                    refine ⟨930373886279314357192241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9923988120312686476717237 930373886279314357192241)
                    ·
                      rfl

theorem cell23_5435690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_5435690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435690 prefixEnd_5435690 := by exact prefixLift 5435690
  have htrace : WordTrace (prefixWord ++ tailWord_5435690) baseStart_5435690 baseEnd_5435690 := by
    simpa [prefixWord, tailWord_5435690, baseEnd_5435690] using wordTrace_append hprefix tailTrace_5435690
  have hstable : (prefixWord ++ tailWord_5435690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435690).length < 2 ^ (prefixWord ++ tailWord_5435690).sum := by decide
  have hdescent : baseEnd_5435690 < baseStart_5435690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435696 : List Nat := [2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 3]
def baseStart_5435696 : Nat := 118140960795 + 5435696 * 2 ^ 59
def prefixEnd_5435696 : Nat := 4983230072969 + 3 ^ 40 * 5435696 * 2
def baseEnd_5435696 : Nat := 2791124739721870048101695

theorem tailTrace_5435696 : CollatzResearch.WordTrace tailWord_5435696 prefixEnd_5435696 2791124739721870048101695 := by
  unfold tailWord_5435696
  simp only [CollatzResearch.WordTrace]
  refine ⟨99128060257704604906375471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132170747010272806541833961 99128060257704604906375471)
  ·
    refine ⟨148692090386556907359563207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99128060257704604906375471 148692090386556907359563207)
    ·
      refine ⟨223038135579835361039344811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148692090386556907359563207 223038135579835361039344811)
      ·
        refine ⟨334557203369753041559017217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223038135579835361039344811 334557203369753041559017217)
        ·
          refine ⟨250917902527314781169262913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 334557203369753041559017217 250917902527314781169262913)
          ·
            refine ⟨188188426895486085876947185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250917902527314781169262913 188188426895486085876947185)
            ·
              refine ⟨141141320171614564407710389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188188426895486085876947185 141141320171614564407710389)
              ·
                refine ⟨13231998766088865413222849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 141141320171614564407710389 13231998766088865413222849)
                ·
                  refine ⟨9923999074566649059917137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13231998766088865413222849 9923999074566649059917137)
                  ·
                    refine ⟨7442999305924986794937853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9923999074566649059917137 7442999305924986794937853)
                    ·
                      refine ⟨2791124739721870048101695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7442999305924986794937853 2791124739721870048101695)
                      ·
                        rfl

theorem cell23_5435696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 3].length) (baseStart_5435696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435696 prefixEnd_5435696 := by exact prefixLift 5435696
  have htrace : WordTrace (prefixWord ++ tailWord_5435696) baseStart_5435696 baseEnd_5435696 := by
    simpa [prefixWord, tailWord_5435696, baseEnd_5435696] using wordTrace_append hprefix tailTrace_5435696
  have hstable : (prefixWord ++ tailWord_5435696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435696).length < 2 ^ (prefixWord ++ tailWord_5435696).sum := by decide
  have hdescent : baseEnd_5435696 < baseStart_5435696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435699 : List Nat := [1, 1, 1, 2, 5, 1, 2, 2, 8]
def baseStart_5435699 : Nat := 118140960795 + 5435699 * 2 ^ 59
def prefixEnd_5435699 : Nat := 4983230072969 + 3 ^ 40 * 5435699 * 2
def baseEnd_5435699 : Nat := 310125142240425948484909

theorem tailTrace_5435699 : CollatzResearch.WordTrace tailWord_5435699 prefixEnd_5435699 310125142240425948484909 := by
  unfold tailWord_5435699
  simp only [CollatzResearch.WordTrace]
  refine ⟨198256229934398341325110151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132170819956265560883406767 198256229934398341325110151)
  ·
    refine ⟨297384344901597511987665227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198256229934398341325110151 297384344901597511987665227)
    ·
      refine ⟨446076517352396267981497841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297384344901597511987665227 446076517352396267981497841)
      ·
        refine ⟨334557388014297200986123381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 446076517352396267981497841 334557388014297200986123381)
        ·
          refine ⟨31364755126340362592449067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 334557388014297200986123381 31364755126340362592449067)
          ·
            refine ⟨47047132689510543888673601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31364755126340362592449067 47047132689510543888673601)
            ·
              refine ⟨35285349517132907916505201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47047132689510543888673601 35285349517132907916505201)
              ·
                refine ⟨26464012137849680937378901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35285349517132907916505201 26464012137849680937378901)
                ·
                  refine ⟨310125142240425948484909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26464012137849680937378901 310125142240425948484909)
                  ·
                    rfl

theorem cell23_5435699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 8].length) (baseStart_5435699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435699 prefixEnd_5435699 := by exact prefixLift 5435699
  have htrace : WordTrace (prefixWord ++ tailWord_5435699) baseStart_5435699 baseEnd_5435699 := by
    simpa [prefixWord, tailWord_5435699, baseEnd_5435699] using wordTrace_append hprefix tailTrace_5435699
  have hstable : (prefixWord ++ tailWord_5435699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435699).length < 2 ^ (prefixWord ++ tailWord_5435699).sum := by decide
  have hdescent : baseEnd_5435699 < baseStart_5435699 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435719 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 8]
def baseStart_5435719 : Nat := 118140960795 + 5435719 * 2 ^ 59
def prefixEnd_5435719 : Nat := 4983230072969 + 3 ^ 40 * 5435719 * 2
def baseEnd_5435719 : Nat := 2791136549776923458114089

theorem tailTrace_5435719 : CollatzResearch.WordTrace tailWord_5435719 prefixEnd_5435719 2791136549776923458114089 := by
  unfold tailWord_5435719
  simp only [CollatzResearch.WordTrace]
  refine ⟨198256959394325884740838211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132171306262883923160558807 198256959394325884740838211)
  ·
    refine ⟨297385439091488827111257317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198256959394325884740838211 297385439091488827111257317)
    ·
      refine ⟨55759769829654155083360747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 297385439091488827111257317 55759769829654155083360747)
      ·
        refine ⟨83639654744481232625041121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55759769829654155083360747 83639654744481232625041121)
        ·
          refine ⟨62729741058360924468780841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83639654744481232625041121 62729741058360924468780841)
          ·
            refine ⟨47047305793770693351585631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62729741058360924468780841 47047305793770693351585631)
            ·
              refine ⟨70570958690656040027378447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47047305793770693351585631 70570958690656040027378447)
              ·
                refine ⟨105856438035984060041067671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70570958690656040027378447 105856438035984060041067671)
                ·
                  refine ⟨158784657053976090061601507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105856438035984060041067671 158784657053976090061601507)
                  ·
                    refine ⟨238176985580964135092402261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 158784657053976090061601507 238176985580964135092402261)
                    ·
                      refine ⟨2791136549776923458114089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 238176985580964135092402261 2791136549776923458114089)
                      ·
                        rfl

theorem cell23_5435719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_5435719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435719 prefixEnd_5435719 := by exact prefixLift 5435719
  have htrace : WordTrace (prefixWord ++ tailWord_5435719) baseStart_5435719 baseEnd_5435719 := by
    simpa [prefixWord, tailWord_5435719, baseEnd_5435719] using wordTrace_append hprefix tailTrace_5435719
  have hstable : (prefixWord ++ tailWord_5435719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435719).length < 2 ^ (prefixWord ++ tailWord_5435719).sum := by decide
  have hdescent : baseEnd_5435719 < baseStart_5435719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435743 : List Nat := [1, 1, 2, 3, 1, 2, 4, 2, 3, 1, 3]
def baseStart_5435743 : Nat := 118140960795 + 5435743 * 2 ^ 59
def prefixEnd_5435743 : Nat := 4983230072969 + 3 ^ 40 * 5435743 * 2
def baseEnd_5435743 : Nat := 2791148873312631364213979

theorem tailTrace_5435743 : CollatzResearch.WordTrace tailWord_5435743 prefixEnd_5435743 2791148873312631364213979 := by
  unfold tailWord_5435743
  simp only [CollatzResearch.WordTrace]
  refine ⟨198257834746238936839711883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132171889830825957893141255 198257834746238936839711883)
  ·
    refine ⟨297386752119358405259567825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198257834746238936839711883 297386752119358405259567825)
    ·
      refine ⟨223040064089518803944675869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297386752119358405259567825 223040064089518803944675869)
      ·
        refine ⟨83640024033569551479253451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223040064089518803944675869 83640024033569551479253451)
        ·
          refine ⟨125460036050354327218880177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83640024033569551479253451 125460036050354327218880177)
          ·
            refine ⟨94095027037765745414160133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125460036050354327218880177 94095027037765745414160133)
            ·
              refine ⟨17642817569581077265155025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94095027037765745414160133 17642817569581077265155025)
              ·
                refine ⟨13232113177185807948866269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17642817569581077265155025 13232113177185807948866269)
                ·
                  refine ⟨4962042441444677980824851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13232113177185807948866269 4962042441444677980824851)
                  ·
                    refine ⟨7443063662167016971237277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4962042441444677980824851 7443063662167016971237277)
                    ·
                      refine ⟨2791148873312631364213979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7443063662167016971237277 2791148873312631364213979)
                      ·
                        rfl

theorem cell23_5435743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 3, 1, 3].length) (baseStart_5435743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435743 prefixEnd_5435743 := by exact prefixLift 5435743
  have htrace : WordTrace (prefixWord ++ tailWord_5435743) baseStart_5435743 baseEnd_5435743 := by
    simpa [prefixWord, tailWord_5435743, baseEnd_5435743] using wordTrace_append hprefix tailTrace_5435743
  have hstable : (prefixWord ++ tailWord_5435743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435743).length < 2 ^ (prefixWord ++ tailWord_5435743).sum := by decide
  have hdescent : baseEnd_5435743 < baseStart_5435743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435753 : List Nat := [1, 2, 1, 1, 1, 3, 4, 3, 2, 3, 2]
def baseStart_5435753 : Nat := 118140960795 + 5435753 * 2 ^ 59
def prefixEnd_5435753 : Nat := 4983230072969 + 3 ^ 40 * 5435753 * 2
def baseEnd_5435753 : Nat := 2791154008119176325088933

theorem tailTrace_5435753 : CollatzResearch.WordTrace tailWord_5435753 prefixEnd_5435753 2791154008119176325088933 := by
  unfold tailWord_5435753
  simp only [CollatzResearch.WordTrace]
  refine ⟨198258199476202708547575913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132172132984135139031717275 198258199476202708547575913)
  ·
    refine ⟨148693649607152031410681935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198258199476202708547575913 148693649607152031410681935)
    ·
      refine ⟨223040474410728047116022903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148693649607152031410681935 223040474410728047116022903)
      ·
        refine ⟨334560711616092070674034355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223040474410728047116022903 334560711616092070674034355)
        ·
          refine ⟨501841067424138106011051533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334560711616092070674034355 501841067424138106011051533)
          ·
            refine ⟨188190400284051789754144325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 501841067424138106011051533 188190400284051789754144325)
            ·
              refine ⟨35285700053259710578902061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 188190400284051789754144325 35285700053259710578902061)
              ·
                refine ⟨13232137519972391467088273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35285700053259710578902061 13232137519972391467088273)
                ·
                  refine ⟨9924103139979293600316205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13232137519972391467088273 9924103139979293600316205)
                  ·
                    refine ⟨3721538677492235100118577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9924103139979293600316205 3721538677492235100118577)
                    ·
                      refine ⟨2791154008119176325088933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3721538677492235100118577 2791154008119176325088933)
                      ·
                        rfl

theorem cell23_5435753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 3, 2].length) (baseStart_5435753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435753 prefixEnd_5435753 := by exact prefixLift 5435753
  have htrace : WordTrace (prefixWord ++ tailWord_5435753) baseStart_5435753 baseEnd_5435753 := by
    simpa [prefixWord, tailWord_5435753, baseEnd_5435753] using wordTrace_append hprefix tailTrace_5435753
  have hstable : (prefixWord ++ tailWord_5435753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435753).length < 2 ^ (prefixWord ++ tailWord_5435753).sum := by decide
  have hdescent : baseEnd_5435753 < baseStart_5435753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435777 : List Nat := [1, 2, 4, 3, 1, 3, 1, 1, 3, 1, 3]
def baseStart_5435777 : Nat := 118140960795 + 5435777 * 2 ^ 59
def prefixEnd_5435777 : Nat := 4983230072969 + 3 ^ 40 * 5435777 * 2
def baseEnd_5435777 : Nat := 2791166331654884231188823

theorem tailTrace_5435777 : CollatzResearch.WordTrace tailWord_5435777 prefixEnd_5435777 2791166331654884231188823 := by
  unfold tailWord_5435777
  simp only [CollatzResearch.WordTrace]
  refine ⟨198259074828115760646449585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132172716552077173764299723 198259074828115760646449585)
  ·
    refine ⟨148694306121086820484837189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198259074828115760646449585 148694306121086820484837189)
    ·
      refine ⟨27880182397703778840906973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148694306121086820484837189 27880182397703778840906973)
      ·
        refine ⟨10455068399138917065340115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27880182397703778840906973 10455068399138917065340115)
        ·
          refine ⟨15682602598708375598010173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10455068399138917065340115 15682602598708375598010173)
          ·
            refine ⟨5880975974515640849253815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15682602598708375598010173 5880975974515640849253815)
            ·
              refine ⟨8821463961773461273880723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5880975974515640849253815 8821463961773461273880723)
              ·
                refine ⟨13232195942660191910821085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8821463961773461273880723 13232195942660191910821085)
                ·
                  refine ⟨4962073478497571966557907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13232195942660191910821085 4962073478497571966557907)
                  ·
                    refine ⟨7443110217746357949836861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4962073478497571966557907 7443110217746357949836861)
                    ·
                      refine ⟨2791166331654884231188823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7443110217746357949836861 2791166331654884231188823)
                      ·
                        rfl

theorem cell23_5435777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_5435777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435777 prefixEnd_5435777 := by exact prefixLift 5435777
  have htrace : WordTrace (prefixWord ++ tailWord_5435777) baseStart_5435777 baseEnd_5435777 := by
    simpa [prefixWord, tailWord_5435777, baseEnd_5435777] using wordTrace_append hprefix tailTrace_5435777
  have hstable : (prefixWord ++ tailWord_5435777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435777).length < 2 ^ (prefixWord ++ tailWord_5435777).sum := by decide
  have hdescent : baseEnd_5435777 < baseStart_5435777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435800 : List Nat := [2, 1, 2, 5, 1, 1, 3, 2, 1, 1, 4]
def baseStart_5435800 : Nat := 118140960795 + 5435800 * 2 ^ 59
def prefixEnd_5435800 : Nat := 4983230072969 + 3 ^ 40 * 5435800 * 2
def baseEnd_5435800 : Nat := 2791178141709937641201217

theorem tailTrace_5435800 : CollatzResearch.WordTrace tailWord_5435800 prefixEnd_5435800 2791178141709937641201217 := by
  unfold tailWord_5435800
  simp only [CollatzResearch.WordTrace]
  refine ⟨99129956853516217787268427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132173275804688290383024569 99129956853516217787268427)
  ·
    refine ⟨148694935280274326680902641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99129956853516217787268427 148694935280274326680902641)
    ·
      refine ⟨111521201460205745010676981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148694935280274326680902641 111521201460205745010676981)
      ·
        refine ⟨10455112636894288594750967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111521201460205745010676981 10455112636894288594750967)
        ·
          refine ⟨15682668955341432892126451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10455112636894288594750967 15682668955341432892126451)
          ·
            refine ⟨23524003433012149338189677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15682668955341432892126451 23524003433012149338189677)
            ·
              refine ⟨8821501287379556001821129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23524003433012149338189677 8821501287379556001821129)
              ·
                refine ⟨6616125965534667001365847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8821501287379556001821129 6616125965534667001365847)
                ·
                  refine ⟨9924188948302000502048771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6616125965534667001365847 9924188948302000502048771)
                  ·
                    refine ⟨14886283422453000753073157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9924188948302000502048771 14886283422453000753073157)
                    ·
                      refine ⟨2791178141709937641201217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14886283422453000753073157 2791178141709937641201217)
                      ·
                        rfl

theorem cell23_5435800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_5435800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435800 prefixEnd_5435800 := by exact prefixLift 5435800
  have htrace : WordTrace (prefixWord ++ tailWord_5435800) baseStart_5435800 baseEnd_5435800 := by
    simpa [prefixWord, tailWord_5435800, baseEnd_5435800] using wordTrace_append hprefix tailTrace_5435800
  have hstable : (prefixWord ++ tailWord_5435800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435800).length < 2 ^ (prefixWord ++ tailWord_5435800).sum := by decide
  have hdescent : baseEnd_5435800 < baseStart_5435800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435850 : List Nat := [3, 1, 2, 1, 2, 2, 1, 5, 2, 1, 3]
def baseStart_5435850 : Nat := 118140960795 + 5435850 * 2 ^ 59
def prefixEnd_5435850 : Nat := 4983230072969 + 3 ^ 40 * 5435850 * 2
def baseEnd_5435850 : Nat := 2791203815742662445575987

theorem tailTrace_5435850 : CollatzResearch.WordTrace tailWord_5435850 prefixEnd_5435850 2791203815742662445575987 := by
  unfold tailWord_5435850
  simp only [CollatzResearch.WordTrace]
  refine ⟨49565434339212823528464251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132174491571234196075904669 49565434339212823528464251)
  ·
    refine ⟨74348151508819235292696377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49565434339212823528464251 74348151508819235292696377)
    ·
      refine ⟨55761113631614426469522283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74348151508819235292696377 55761113631614426469522283)
      ·
        refine ⟨83641670447421639704283425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55761113631614426469522283 83641670447421639704283425)
        ·
          refine ⟨62731252835566229778212569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83641670447421639704283425 62731252835566229778212569)
          ·
            refine ⟨47048439626674672333659427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62731252835566229778212569 47048439626674672333659427)
            ·
              refine ⟨70572659440012008500489141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47048439626674672333659427 70572659440012008500489141)
              ·
                refine ⟨6616186822501125796920857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70572659440012008500489141 6616186822501125796920857)
                ·
                  refine ⟨4962140116875844347690643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6616186822501125796920857 4962140116875844347690643)
                  ·
                    refine ⟨7443210175313766521535965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4962140116875844347690643 7443210175313766521535965)
                    ·
                      refine ⟨2791203815742662445575987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7443210175313766521535965 2791203815742662445575987)
                      ·
                        rfl

theorem cell23_5435850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 2, 1, 3].length) (baseStart_5435850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435850 prefixEnd_5435850 := by exact prefixLift 5435850
  have htrace : WordTrace (prefixWord ++ tailWord_5435850) baseStart_5435850 baseEnd_5435850 := by
    simpa [prefixWord, tailWord_5435850, baseEnd_5435850] using wordTrace_append hprefix tailTrace_5435850
  have hstable : (prefixWord ++ tailWord_5435850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435850).length < 2 ^ (prefixWord ++ tailWord_5435850).sum := by decide
  have hdescent : baseEnd_5435850 < baseStart_5435850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435866 : List Nat := [3, 1, 1, 2, 3, 1, 1, 2, 1, 8]
def baseStart_5435866 : Nat := 118140960795 + 5435866 * 2 ^ 59
def prefixEnd_5435866 : Nat := 4983230072969 + 3 ^ 40 * 5435866 * 2
def baseEnd_5435866 : Nat := 930404010477711460991971

theorem tailTrace_5435866 : CollatzResearch.WordTrace tailWord_5435866 prefixEnd_5435866 930404010477711460991971 := by
  unfold tailWord_5435866
  simp only [CollatzResearch.WordTrace]
  refine ⟨49565580231198332211609863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132174880616528885897626301 49565580231198332211609863)
  ·
    refine ⟨74348370346797498317414795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49565580231198332211609863 74348370346797498317414795)
    ·
      refine ⟨111522555520196247476122193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74348370346797498317414795 111522555520196247476122193)
      ·
        refine ⟨83641916640147185607091645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111522555520196247476122193 83641916640147185607091645)
        ·
          refine ⟨31365718740055194602659367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83641916640147185607091645 31365718740055194602659367)
          ·
            refine ⟨47048578110082791903989051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31365718740055194602659367 47048578110082791903989051)
            ·
              refine ⟨70572867165124187855983577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47048578110082791903989051 70572867165124187855983577)
              ·
                refine ⟨52929650373843140891987683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70572867165124187855983577 52929650373843140891987683)
                ·
                  refine ⟨79394475560764711337981525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52929650373843140891987683 79394475560764711337981525)
                  ·
                    refine ⟨930404010477711460991971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 79394475560764711337981525 930404010477711460991971)
                    ·
                      rfl

theorem cell23_5435866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 1, 8].length) (baseStart_5435866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435866 prefixEnd_5435866 := by exact prefixLift 5435866
  have htrace : WordTrace (prefixWord ++ tailWord_5435866) baseStart_5435866 baseEnd_5435866 := by
    simpa [prefixWord, tailWord_5435866, baseEnd_5435866] using wordTrace_append hprefix tailTrace_5435866
  have hstable : (prefixWord ++ tailWord_5435866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435866).length < 2 ^ (prefixWord ++ tailWord_5435866).sum := by decide
  have hdescent : baseEnd_5435866 < baseStart_5435866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435924 : List Nat := [2, 4, 3, 1, 1, 1, 1, 2, 4, 2, 2]
def baseStart_5435924 : Nat := 118140960795 + 5435924 * 2 ^ 59
def prefixEnd_5435924 : Nat := 4983230072969 + 3 ^ 40 * 5435924 * 2
def baseEnd_5435924 : Nat := 2791241813311095156050647

theorem tailTrace_5435924 : CollatzResearch.WordTrace tailWord_5435924 prefixEnd_5435924 2791241813311095156050647 := by
  unfold tailWord_5435924
  simp only [CollatzResearch.WordTrace]
  refine ⟨99132218179291602376025413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132176290905722136501367217 99132218179291602376025413)
  ·
    refine ⟨18587290908617175445504765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99132218179291602376025413 18587290908617175445504765)
    ·
      refine ⟨6970234090731440792064287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18587290908617175445504765 6970234090731440792064287)
      ·
        refine ⟨10455351136097161188096431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6970234090731440792064287 10455351136097161188096431)
        ·
          refine ⟨15683026704145741782144647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10455351136097161188096431 15683026704145741782144647)
          ·
            refine ⟨23524540056218612673216971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15683026704145741782144647 23524540056218612673216971)
            ·
              refine ⟨35286810084327919009825457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23524540056218612673216971 35286810084327919009825457)
              ·
                refine ⟨26465107563245939257369093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35286810084327919009825457 26465107563245939257369093)
                ·
                  refine ⟨4962207668108613610756705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26465107563245939257369093 4962207668108613610756705)
                  ·
                    refine ⟨3721655751081460208067529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4962207668108613610756705 3721655751081460208067529)
                    ·
                      refine ⟨2791241813311095156050647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3721655751081460208067529 2791241813311095156050647)
                      ·
                        rfl

theorem cell23_5435924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_5435924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435924 prefixEnd_5435924 := by exact prefixLift 5435924
  have htrace : WordTrace (prefixWord ++ tailWord_5435924) baseStart_5435924 baseEnd_5435924 := by
    simpa [prefixWord, tailWord_5435924, baseEnd_5435924] using wordTrace_append hprefix tailTrace_5435924
  have hstable : (prefixWord ++ tailWord_5435924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435924).length < 2 ^ (prefixWord ++ tailWord_5435924).sum := by decide
  have hdescent : baseEnd_5435924 < baseStart_5435924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435930 : List Nat := [3, 1, 1, 3, 1, 1, 5, 3, 5]
def baseStart_5435930 : Nat := 118140960795 + 5435930 * 2 ^ 59
def prefixEnd_5435930 : Nat := 4983230072969 + 3 ^ 40 * 5435930 * 2
def baseEnd_5435930 : Nat := 310138321577224681397291

theorem tailTrace_5435930 : CollatzResearch.WordTrace tailWord_5435930 prefixEnd_5435930 310138321577224681397291 := by
  unfold tailWord_5435930
  simp only [CollatzResearch.WordTrace]
  refine ⟨49566163799140366944192311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132176436797707645184512829 49566163799140366944192311)
  ·
    refine ⟨74349245698710550416288467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49566163799140366944192311 74349245698710550416288467)
    ·
      refine ⟨111523868548065825624432701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74349245698710550416288467 111523868548065825624432701)
      ·
        refine ⟨41821450705524684609162263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111523868548065825624432701 41821450705524684609162263)
        ·
          refine ⟨62732176058287026913743395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41821450705524684609162263 62732176058287026913743395)
          ·
            refine ⟨94098264087430540370615093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62732176058287026913743395 94098264087430540370615093)
            ·
              refine ⟨8821712258196613159745165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94098264087430540370615093 8821712258196613159745165)
              ·
                refine ⟨3308142096823729934904437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8821712258196613159745165 3308142096823729934904437)
                ·
                  refine ⟨310138321577224681397291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3308142096823729934904437 310138321577224681397291)
                  ·
                    rfl

theorem cell23_5435930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 3, 5].length) (baseStart_5435930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435930 prefixEnd_5435930 := by exact prefixLift 5435930
  have htrace : WordTrace (prefixWord ++ tailWord_5435930) baseStart_5435930 baseEnd_5435930 := by
    simpa [prefixWord, tailWord_5435930, baseEnd_5435930] using wordTrace_append hprefix tailTrace_5435930
  have hstable : (prefixWord ++ tailWord_5435930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435930).length < 2 ^ (prefixWord ++ tailWord_5435930).sum := by decide
  have hdescent : baseEnd_5435930 < baseStart_5435930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435958 : List Nat := [5, 1, 2, 1, 2, 3, 2, 1, 2, 2, 2]
def baseStart_5435958 : Nat := 118140960795 + 5435958 * 2 ^ 59
def prefixEnd_5435958 : Nat := 4983230072969 + 3 ^ 40 * 5435958 * 2
def baseEnd_5435958 : Nat := 2791259271653348023025491

theorem tailTrace_5435958 : CollatzResearch.WordTrace tailWord_5435958 prefixEnd_5435958 2791259271653348023025491 := by
  unfold tailWord_5435958
  simp only [CollatzResearch.WordTrace]
  refine ⟨12391604777528751784924283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132177117626973352372525685 12391604777528751784924283)
  ·
    refine ⟨18587407166293127677386425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12391604777528751784924283 18587407166293127677386425)
    ·
      refine ⟨13940555374719845758039819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18587407166293127677386425 13940555374719845758039819)
      ·
        refine ⟨20910833062079768637059729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13940555374719845758039819 20910833062079768637059729)
        ·
          refine ⟨15683124796559826477794797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20910833062079768637059729 15683124796559826477794797)
          ·
            refine ⟨5881171798709934929173049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15683124796559826477794797 5881171798709934929173049)
            ·
              refine ⟨4410878849032451196879787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5881171798709934929173049 4410878849032451196879787)
              ·
                refine ⟨6616318273548676795319681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4410878849032451196879787 6616318273548676795319681)
                ·
                  refine ⟨4962238705161507596489761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6616318273548676795319681 4962238705161507596489761)
                  ·
                    refine ⟨3721679028871130697367321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4962238705161507596489761 3721679028871130697367321)
                    ·
                      refine ⟨2791259271653348023025491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3721679028871130697367321 2791259271653348023025491)
                      ·
                        rfl

theorem cell23_5435958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_5435958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435958 prefixEnd_5435958 := by exact prefixLift 5435958
  have htrace : WordTrace (prefixWord ++ tailWord_5435958) baseStart_5435958 baseEnd_5435958 := by
    simpa [prefixWord, tailWord_5435958, baseEnd_5435958] using wordTrace_append hprefix tailTrace_5435958
  have hstable : (prefixWord ++ tailWord_5435958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435958).length < 2 ^ (prefixWord ++ tailWord_5435958).sum := by decide
  have hdescent : baseEnd_5435958 < baseStart_5435958 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435980 : List Nat := [2, 2, 1, 3, 1, 2, 4, 1, 2, 1, 4]
def baseStart_5435980 : Nat := 118140960795 + 5435980 * 2 ^ 59
def prefixEnd_5435980 : Nat := 4983230072969 + 3 ^ 40 * 5435980 * 2
def baseEnd_5435980 : Nat := 2791270568227746936950389

theorem tailTrace_5435980 : CollatzResearch.WordTrace tailWord_5435980 prefixEnd_5435980 2791270568227746936950389 := by
  unfold tailWord_5435980
  simp only [CollatzResearch.WordTrace]
  refine ⟨99133239423190163158044697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132177652564253550877392929 99133239423190163158044697)
  ·
    refine ⟨74349929567392622368533523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99133239423190163158044697 74349929567392622368533523)
    ·
      refine ⟨111524894351088933552800285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74349929567392622368533523 111524894351088933552800285)
      ·
        refine ⟨41821835381658350082300107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111524894351088933552800285 41821835381658350082300107)
        ·
          refine ⟨62732753072487525123450161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41821835381658350082300107 62732753072487525123450161)
          ·
            refine ⟨47049564804365643842587621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62732753072487525123450161 47049564804365643842587621)
            ·
              refine ⟨8821793400818558220485179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47049564804365643842587621 8821793400818558220485179)
              ·
                refine ⟨13232690101227837330727769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8821793400818558220485179 13232690101227837330727769)
                ·
                  refine ⟨9924517575920877998045827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13232690101227837330727769 9924517575920877998045827)
                  ·
                    refine ⟨14886776363881316997068741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9924517575920877998045827 14886776363881316997068741)
                    ·
                      refine ⟨2791270568227746936950389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14886776363881316997068741 2791270568227746936950389)
                      ·
                        rfl

theorem cell23_5435980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_5435980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435980 prefixEnd_5435980 := by exact prefixLift 5435980
  have htrace : WordTrace (prefixWord ++ tailWord_5435980) baseStart_5435980 baseEnd_5435980 := by
    simpa [prefixWord, tailWord_5435980, baseEnd_5435980] using wordTrace_append hprefix tailTrace_5435980
  have hstable : (prefixWord ++ tailWord_5435980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435980).length < 2 ^ (prefixWord ++ tailWord_5435980).sum := by decide
  have hdescent : baseEnd_5435980 < baseStart_5435980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5435983 : List Nat := [1, 1, 2, 1, 1, 2, 4, 3, 1, 4, 3]
def baseStart_5435983 : Nat := 118140960795 + 5435983 * 2 ^ 59
def prefixEnd_5435983 : Nat := 4983230072969 + 3 ^ 40 * 5435983 * 2
def baseEnd_5435983 : Nat := 2791272108669710425212875

theorem tailTrace_5435983 : CollatzResearch.WordTrace tailWord_5435983 prefixEnd_5435983 2791272108669710425212875 := by
  unfold tailWord_5435983
  simp only [CollatzResearch.WordTrace]
  refine ⟨198266588265369457828448603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132177725510246305218965735 198266588265369457828448603)
  ·
    refine ⟨297399882398054186742672905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198266588265369457828448603 297399882398054186742672905)
    ·
      refine ⟨223049911798540640057004679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297399882398054186742672905 223049911798540640057004679)
      ·
        refine ⟨334574867697810960085507019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223049911798540640057004679 334574867697810960085507019)
        ·
          refine ⟨501862301546716440128260529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334574867697810960085507019 501862301546716440128260529)
          ·
            refine ⟨376396726160037330096195397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 501862301546716440128260529 376396726160037330096195397)
            ·
              refine ⟨70574386155006999393036637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 376396726160037330096195397 70574386155006999393036637)
              ·
                refine ⟨26465394808127624772388739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70574386155006999393036637 26465394808127624772388739)
                ·
                  refine ⟨39698092212191437158583109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26465394808127624772388739 39698092212191437158583109)
                  ·
                    refine ⟨7443392289785894467234333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39698092212191437158583109 7443392289785894467234333)
                    ·
                      refine ⟨2791272108669710425212875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7443392289785894467234333 2791272108669710425212875)
                      ·
                        rfl

theorem cell23_5435983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 4, 3].length) (baseStart_5435983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5435983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5435983 prefixEnd_5435983 := by exact prefixLift 5435983
  have htrace : WordTrace (prefixWord ++ tailWord_5435983) baseStart_5435983 baseEnd_5435983 := by
    simpa [prefixWord, tailWord_5435983, baseEnd_5435983] using wordTrace_append hprefix tailTrace_5435983
  have hstable : (prefixWord ++ tailWord_5435983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5435983).length < 2 ^ (prefixWord ++ tailWord_5435983).sum := by decide
  have hdescent : baseEnd_5435983 < baseStart_5435983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5435983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436000 : List Nat := [2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 3]
def baseStart_5436000 : Nat := 118140960795 + 5436000 * 2 ^ 59
def prefixEnd_5436000 : Nat := 4983230072969 + 3 ^ 40 * 5436000 * 2
def baseEnd_5436000 : Nat := 2791280837840836858700297

theorem tailTrace_5436000 : CollatzResearch.WordTrace tailWord_5436000 prefixEnd_5436000 2791280837840836858700297 := by
  unfold tailWord_5436000
  simp only [CollatzResearch.WordTrace]
  refine ⟨99133604153153934865908727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132178138870871913154544969 99133604153153934865908727)
  ·
    refine ⟨148700406229730902298863091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99133604153153934865908727 148700406229730902298863091)
    ·
      refine ⟨223050609344596353448294637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148700406229730902298863091 223050609344596353448294637)
      ·
        refine ⟨83643978504223632543110489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223050609344596353448294637 83643978504223632543110489)
        ·
          refine ⟨62732983878167724407332867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83643978504223632543110489 62732983878167724407332867)
          ·
            refine ⟨94099475817251586610999301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62732983878167724407332867 94099475817251586610999301)
            ·
              refine ⟨17643651715734672489562369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94099475817251586610999301 17643651715734672489562369)
              ·
                refine ⟨13232738786801004367171777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17643651715734672489562369 13232738786801004367171777)
                ·
                  refine ⟨9924554090100753275378833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13232738786801004367171777 9924554090100753275378833)
                  ·
                    refine ⟨7443415567575564956534125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9924554090100753275378833 7443415567575564956534125)
                    ·
                      refine ⟨2791280837840836858700297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7443415567575564956534125 2791280837840836858700297)
                      ·
                        rfl

theorem cell23_5436000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_5436000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436000 prefixEnd_5436000 := by exact prefixLift 5436000
  have htrace : WordTrace (prefixWord ++ tailWord_5436000) baseStart_5436000 baseEnd_5436000 := by
    simpa [prefixWord, tailWord_5436000, baseEnd_5436000] using wordTrace_append hprefix tailTrace_5436000
  have hstable : (prefixWord ++ tailWord_5436000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436000).length < 2 ^ (prefixWord ++ tailWord_5436000).sum := by decide
  have hdescent : baseEnd_5436000 < baseStart_5436000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436064 : List Nat := [2, 1, 1, 4, 4, 1, 2, 1, 3, 1, 3]
def baseStart_5436064 : Nat := 118140960795 + 5436064 * 2 ^ 59
def prefixEnd_5436064 : Nat := 4983230072969 + 3 ^ 40 * 5436064 * 2
def baseEnd_5436064 : Nat := 2791313700602724608300003

theorem tailTrace_5436064 : CollatzResearch.WordTrace tailWord_5436064 prefixEnd_5436064 2791313700602724608300003 := by
  unfold tailWord_5436064
  simp only [CollatzResearch.WordTrace]
  refine ⟨99134771289038004331073623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132179695052050672441431497 99134771289038004331073623)
  ·
    refine ⟨148702156933557006496610435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99134771289038004331073623 148702156933557006496610435)
    ·
      refine ⟨223053235400335509744915653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148702156933557006496610435 223053235400335509744915653)
      ·
        refine ⟨41822481637562908077171685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 223053235400335509744915653 41822481637562908077171685)
        ·
          refine ⟨7841715307043045264469691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41822481637562908077171685 7841715307043045264469691)
          ·
            refine ⟨11762572960564567896704537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7841715307043045264469691 11762572960564567896704537)
            ·
              refine ⟨8821929720423425922528403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11762572960564567896704537 8821929720423425922528403)
              ·
                refine ⟨13232894580635138883792605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8821929720423425922528403 13232894580635138883792605)
                ·
                  refine ⟨4962335467738177081422227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13232894580635138883792605 4962335467738177081422227)
                  ·
                    refine ⟨7443503201607265622133341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4962335467738177081422227 7443503201607265622133341)
                    ·
                      refine ⟨2791313700602724608300003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7443503201607265622133341 2791313700602724608300003)
                      ·
                        rfl

theorem cell23_5436064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_5436064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436064 prefixEnd_5436064 := by exact prefixLift 5436064
  have htrace : WordTrace (prefixWord ++ tailWord_5436064) baseStart_5436064 baseEnd_5436064 := by
    simpa [prefixWord, tailWord_5436064, baseEnd_5436064] using wordTrace_append hprefix tailTrace_5436064
  have hstable : (prefixWord ++ tailWord_5436064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436064).length < 2 ^ (prefixWord ++ tailWord_5436064).sum := by decide
  have hdescent : baseEnd_5436064 < baseStart_5436064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436073 : List Nat := [1, 2, 1, 1, 1, 1, 2, 5, 3, 1, 5]
def baseStart_5436073 : Nat := 118140960795 + 5436073 * 2 ^ 59
def prefixEnd_5436073 : Nat := 4983230072969 + 3 ^ 40 * 5436073 * 2
def baseEnd_5436073 : Nat := 2791318321928615073087461

theorem tailTrace_5436073 : CollatzResearch.WordTrace tailWord_5436073 prefixEnd_5436073 2791318321928615073087461 := by
  unfold tailWord_5436073
  simp only [CollatzResearch.WordTrace]
  refine ⟨198269870835043403199224873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132179913890028935466149915 198269870835043403199224873)
  ·
    refine ⟨148702403126282552399418655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198269870835043403199224873 148702403126282552399418655)
    ·
      refine ⟨223053604689423828599127983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148702403126282552399418655 223053604689423828599127983)
      ·
        refine ⟨334580407034135742898691975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223053604689423828599127983 334580407034135742898691975)
        ·
          refine ⟨501870610551203614348037963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334580407034135742898691975 501870610551203614348037963)
          ·
            refine ⟨752805915826805421522056945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501870610551203614348037963 752805915826805421522056945)
            ·
              refine ⟨564604436870104066141542709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 752805915826805421522056945 564604436870104066141542709)
              ·
                refine ⟨52931665956572256200769629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 564604436870104066141542709 52931665956572256200769629)
                ·
                  refine ⟨19849374733714596075288611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52931665956572256200769629 19849374733714596075288611)
                  ·
                    refine ⟨29774062100571894112932917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19849374733714596075288611 29774062100571894112932917)
                    ·
                      refine ⟨2791318321928615073087461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29774062100571894112932917 2791318321928615073087461)
                      ·
                        rfl

theorem cell23_5436073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 1, 5].length) (baseStart_5436073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436073 prefixEnd_5436073 := by exact prefixLift 5436073
  have htrace : WordTrace (prefixWord ++ tailWord_5436073) baseStart_5436073 baseEnd_5436073 := by
    simpa [prefixWord, tailWord_5436073, baseEnd_5436073] using wordTrace_append hprefix tailTrace_5436073
  have hstable : (prefixWord ++ tailWord_5436073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436073).length < 2 ^ (prefixWord ++ tailWord_5436073).sum := by decide
  have hdescent : baseEnd_5436073 < baseStart_5436073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436110 : List Nat := [4, 1, 1, 1, 3, 4, 9]
def baseStart_5436110 : Nat := 118140960795 + 5436110 * 2 ^ 59
def prefixEnd_5436110 : Nat := 4983230072969 + 3 ^ 40 * 5436110 * 2
def baseEnd_5436110 : Nat := 34460954576701622571911

theorem tailTrace_5436110 : CollatzResearch.WordTrace tailWord_5436110 prefixEnd_5436110 34460954576701622571911 := by
  unfold tailWord_5436110
  simp only [CollatzResearch.WordTrace]
  refine ⟨24783902541988669814790223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132180813557272905678881189 24783902541988669814790223)
  ·
    refine ⟨37175853812983004722185335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24783902541988669814790223 37175853812983004722185335)
    ·
      refine ⟨55763780719474507083278003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37175853812983004722185335 55763780719474507083278003)
      ·
        refine ⟨83645671079211760624917005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55763780719474507083278003 83645671079211760624917005)
        ·
          refine ⟨31367126654704410234343877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83645671079211760624917005 31367126654704410234343877)
          ·
            refine ⟨5881336247757076918939477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31367126654704410234343877 5881336247757076918939477)
            ·
              refine ⟨34460954576701622571911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5881336247757076918939477 34460954576701622571911)
              ·
                rfl

theorem cell23_5436110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 9].length) (baseStart_5436110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436110 prefixEnd_5436110 := by exact prefixLift 5436110
  have htrace : WordTrace (prefixWord ++ tailWord_5436110) baseStart_5436110 baseEnd_5436110 := by
    simpa [prefixWord, tailWord_5436110, baseEnd_5436110] using wordTrace_append hprefix tailTrace_5436110
  have hstable : (prefixWord ++ tailWord_5436110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436110).length < 2 ^ (prefixWord ++ tailWord_5436110).sum := by decide
  have hdescent : baseEnd_5436110 < baseStart_5436110 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436131 : List Nat := [1, 1, 1, 7, 1, 3, 2, 1, 2, 4]
def baseStart_5436131 : Nat := 118140960795 + 5436131 * 2 ^ 59
def prefixEnd_5436131 : Nat := 4983230072969 + 3 ^ 40 * 5436131 * 2
def baseEnd_5436131 : Nat := 930449367935525282054065

theorem tailTrace_5436131 : CollatzResearch.WordTrace tailWord_5436131 prefixEnd_5436131 930449367935525282054065 := by
  unfold tailWord_5436131
  simp only [CollatzResearch.WordTrace]
  refine ⟨198271986268833279104836247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132181324179222186069890831 198271986268833279104836247)
  ·
    refine ⟨297407979403249918657254371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198271986268833279104836247 297407979403249918657254371)
    ·
      refine ⟨446111969104874877985881557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297407979403249918657254371 446111969104874877985881557)
      ·
        refine ⟨10455749275895504952794099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 446111969104874877985881557 10455749275895504952794099)
        ·
          refine ⟨15683623913843257429191149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10455749275895504952794099 15683623913843257429191149)
          ·
            refine ⟨5881358967691221535946681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15683623913843257429191149 5881358967691221535946681)
            ·
              refine ⟨4411019225768416151960011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5881358967691221535946681 4411019225768416151960011)
              ·
                refine ⟨6616528838652624227940017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4411019225768416151960011 6616528838652624227940017)
                ·
                  refine ⟨4962396628989468170955013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6616528838652624227940017 4962396628989468170955013)
                  ·
                    refine ⟨930449367935525282054065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4962396628989468170955013 930449367935525282054065)
                    ·
                      rfl

theorem cell23_5436131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 1, 2, 4].length) (baseStart_5436131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436131 prefixEnd_5436131 := by exact prefixLift 5436131
  have htrace : WordTrace (prefixWord ++ tailWord_5436131) baseStart_5436131 baseEnd_5436131 := by
    simpa [prefixWord, tailWord_5436131, baseEnd_5436131] using wordTrace_append hprefix tailTrace_5436131
  have hstable : (prefixWord ++ tailWord_5436131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436131).length < 2 ^ (prefixWord ++ tailWord_5436131).sum := by decide
  have hdescent : baseEnd_5436131 < baseStart_5436131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436170 : List Nat := [3, 1, 2, 2, 1, 2, 2, 2, 2, 6]
def baseStart_5436170 : Nat := 118140960795 + 5436170 * 2 ^ 59
def prefixEnd_5436170 : Nat := 4983230072969 + 3 ^ 40 * 5436170 * 2
def baseEnd_5436170 : Nat := 930456043184033731191505

theorem tailTrace_5436170 : CollatzResearch.WordTrace tailWord_5436170 prefixEnd_5436170 930456043184033731191505 := by
  unfold tailWord_5436170
  simp only [CollatzResearch.WordTrace]
  refine ⟨49568352178922997191376491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132182272477127992510337309 49568352178922997191376491)
  ·
    refine ⟨74352528268384495787064737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49568352178922997191376491 74352528268384495787064737)
    ·
      refine ⟨55764396201288371840298553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74352528268384495787064737 55764396201288371840298553)
      ·
        refine ⟨41823297150966278880223915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55764396201288371840298553 41823297150966278880223915)
        ·
          refine ⟨62734945726449418320335873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41823297150966278880223915 62734945726449418320335873)
          ·
            refine ⟨47051209294837063740251905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62734945726449418320335873 47051209294837063740251905)
            ·
              refine ⟨35288406971127797805188929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47051209294837063740251905 35288406971127797805188929)
              ·
                refine ⟨26466305228345848353891697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35288406971127797805188929 26466305228345848353891697)
                ·
                  refine ⟨19849728921259386265418773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26466305228345848353891697 19849728921259386265418773)
                  ·
                    refine ⟨930456043184033731191505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19849728921259386265418773 930456043184033731191505)
                    ·
                      rfl

theorem cell23_5436170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_5436170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436170 prefixEnd_5436170 := by exact prefixLift 5436170
  have htrace : WordTrace (prefixWord ++ tailWord_5436170) baseStart_5436170 baseEnd_5436170 := by
    simpa [prefixWord, tailWord_5436170, baseEnd_5436170] using wordTrace_append hprefix tailTrace_5436170
  have hstable : (prefixWord ++ tailWord_5436170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436170).length < 2 ^ (prefixWord ++ tailWord_5436170).sum := by decide
  have hdescent : baseEnd_5436170 < baseStart_5436170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436194 : List Nat := [3, 3, 1, 1, 2, 2, 1, 3, 1, 4, 2]
def baseStart_5436194 : Nat := 118140960795 + 5436194 * 2 ^ 59
def prefixEnd_5436194 : Nat := 4983230072969 + 3 ^ 40 * 5436194 * 2
def baseEnd_5436194 : Nat := 2791380453087809099674405

theorem tailTrace_5436194 : CollatzResearch.WordTrace tailWord_5436194 prefixEnd_5436194 2791380453087809099674405 := by
  unfold tailWord_5436194
  simp only [CollatzResearch.WordTrace]
  refine ⟨49568571016901260216094909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132182856045070027242919757 49568571016901260216094909)
  ·
    refine ⟨18588214131337972581035591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49568571016901260216094909 18588214131337972581035591)
    ·
      refine ⟨27882321197006958871553387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18588214131337972581035591 27882321197006958871553387)
      ·
        refine ⟨41823481795510438307330081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27882321197006958871553387 41823481795510438307330081)
        ·
          refine ⟨31367611346632828730497561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41823481795510438307330081 31367611346632828730497561)
          ·
            refine ⟨23525708509974621547873171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31367611346632828730497561 23525708509974621547873171)
            ·
              refine ⟨35288562764961932321809757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23525708509974621547873171 35288562764961932321809757)
              ·
                refine ⟨13233211036860724620678659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35288562764961932321809757 13233211036860724620678659)
                ·
                  refine ⟨19849816555291086931017989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13233211036860724620678659 19849816555291086931017989)
                  ·
                    refine ⟨3721840604117078799565873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19849816555291086931017989 3721840604117078799565873)
                    ·
                      refine ⟨2791380453087809099674405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3721840604117078799565873 2791380453087809099674405)
                      ·
                        rfl

theorem cell23_5436194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_5436194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436194 prefixEnd_5436194 := by exact prefixLift 5436194
  have htrace : WordTrace (prefixWord ++ tailWord_5436194) baseStart_5436194 baseEnd_5436194 := by
    simpa [prefixWord, tailWord_5436194, baseEnd_5436194] using wordTrace_append hprefix tailTrace_5436194
  have hstable : (prefixWord ++ tailWord_5436194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436194).length < 2 ^ (prefixWord ++ tailWord_5436194).sum := by decide
  have hdescent : baseEnd_5436194 < baseStart_5436194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436240 : List Nat := [2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 5]
def baseStart_5436240 : Nat := 118140960795 + 5436240 * 2 ^ 59
def prefixEnd_5436240 : Nat := 4983230072969 + 3 ^ 40 * 5436240 * 2
def baseEnd_5436240 : Nat := 2791404073197915919699193

theorem tailTrace_5436240 : CollatzResearch.WordTrace tailWord_5436240 prefixEnd_5436240 2791404073197915919699193 := by
  unfold tailWord_5436240
  simp only [CollatzResearch.WordTrace]
  refine ⟨99137980912719195360277087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132183974550292260480369449 99137980912719195360277087)
  ·
    refine ⟨148706971369078793040415631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99137980912719195360277087 148706971369078793040415631)
    ·
      refine ⟨223060457053618189560623447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148706971369078793040415631 223060457053618189560623447)
      ·
        refine ⟨334590685580427284340935171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223060457053618189560623447 334590685580427284340935171)
        ·
          refine ⟨501886028370640926511402757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334590685580427284340935171 501886028370640926511402757)
          ·
            refine ⟨94103630319495173720888017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 501886028370640926511402757 94103630319495173720888017)
            ·
              refine ⟨70577722739621380290666013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94103630319495173720888017 70577722739621380290666013)
              ·
                refine ⟨26466646027358017608999755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70577722739621380290666013 26466646027358017608999755)
                ·
                  refine ⟨39699969041037026413499633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26466646027358017608999755 39699969041037026413499633)
                  ·
                    refine ⟨29774976780777769810124725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39699969041037026413499633 29774976780777769810124725)
                    ·
                      refine ⟨2791404073197915919699193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29774976780777769810124725 2791404073197915919699193)
                      ·
                        rfl

theorem cell23_5436240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 5].length) (baseStart_5436240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436240 prefixEnd_5436240 := by exact prefixLift 5436240
  have htrace : WordTrace (prefixWord ++ tailWord_5436240) baseStart_5436240 baseEnd_5436240 := by
    simpa [prefixWord, tailWord_5436240, baseEnd_5436240] using wordTrace_append hprefix tailTrace_5436240
  have hstable : (prefixWord ++ tailWord_5436240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436240).length < 2 ^ (prefixWord ++ tailWord_5436240).sum := by decide
  have hdescent : baseEnd_5436240 < baseStart_5436240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436267 : List Nat := [1, 1, 1, 1, 2, 2, 4, 2, 1, 6, 2]
def baseStart_5436267 : Nat := 118140960795 + 5436267 * 2 ^ 59
def prefixEnd_5436267 : Nat := 4983230072969 + 3 ^ 40 * 5436267 * 2
def baseEnd_5436267 : Nat := 2791417937175587314061569

theorem tailTrace_5436267 : CollatzResearch.WordTrace tailWord_5436267 prefixEnd_5436267 2791417937175587314061569 := by
  unfold tailWord_5436267
  simp only [CollatzResearch.WordTrace]
  refine ⟨198276946596340574331787055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132184631064227049554524703 198276946596340574331787055)
  ·
    refine ⟨297415419894510861497680583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198276946596340574331787055 297415419894510861497680583)
    ·
      refine ⟨446123129841766292246520875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297415419894510861497680583 446123129841766292246520875)
      ·
        refine ⟨669184694762649438369781313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446123129841766292246520875 669184694762649438369781313)
        ·
          refine ⟨501888521071987078777335985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 669184694762649438369781313 501888521071987078777335985)
          ·
            refine ⟨376416390803990309083001989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 501888521071987078777335985 376416390803990309083001989)
            ·
              refine ⟨70578073275748182953062873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 376416390803990309083001989 70578073275748182953062873)
              ·
                refine ⟨52933554956811137214797155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70578073275748182953062873 52933554956811137214797155)
                ·
                  refine ⟨79400332435216705822195733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52933554956811137214797155 79400332435216705822195733)
                  ·
                    refine ⟨3721890582900783085415425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79400332435216705822195733 3721890582900783085415425)
                    ·
                      refine ⟨2791417937175587314061569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3721890582900783085415425 2791417937175587314061569)
                      ·
                        rfl

theorem cell23_5436267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 6, 2].length) (baseStart_5436267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436267 prefixEnd_5436267 := by exact prefixLift 5436267
  have htrace : WordTrace (prefixWord ++ tailWord_5436267) baseStart_5436267 baseEnd_5436267 := by
    simpa [prefixWord, tailWord_5436267, baseEnd_5436267] using wordTrace_append hprefix tailTrace_5436267
  have hstable : (prefixWord ++ tailWord_5436267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436267).length < 2 ^ (prefixWord ++ tailWord_5436267).sum := by decide
  have hdescent : baseEnd_5436267 < baseStart_5436267 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436280 : List Nat := [2, 1, 2, 1, 1, 1, 1, 5, 2, 1, 6]
def baseStart_5436280 : Nat := 118140960795 + 5436280 * 2 ^ 59
def prefixEnd_5436280 : Nat := 4983230072969 + 3 ^ 40 * 5436280 * 2
def baseEnd_5436280 : Nat := 2791424612424095763199009

theorem tailTrace_5436280 : CollatzResearch.WordTrace tailWord_5436280 prefixEnd_5436280 2791424612424095763199009 := by
  unfold tailWord_5436280
  simp only [CollatzResearch.WordTrace]
  refine ⟨99138710372646738776005147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132184947163528985034673529 99138710372646738776005147)
  ·
    refine ⟨148708065558970108164007721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99138710372646738776005147 148708065558970108164007721)
    ·
      refine ⟨111531049169227581123005791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148708065558970108164007721 111531049169227581123005791)
      ·
        refine ⟨167296573753841371684508687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111531049169227581123005791 167296573753841371684508687)
        ·
          refine ⟨250944860630762057526763031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167296573753841371684508687 250944860630762057526763031)
          ·
            refine ⟨376417290946143086290144547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250944860630762057526763031 376417290946143086290144547)
            ·
              refine ⟨564625936419214629435216821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376417290946143086290144547 564625936419214629435216821)
              ·
                refine ⟨52933681539301371509551577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 564625936419214629435216821 52933681539301371509551577)
                ·
                  refine ⟨39700261154476028632163683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52933681539301371509551577 39700261154476028632163683)
                  ·
                    refine ⟨59550391731714042948245525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39700261154476028632163683 59550391731714042948245525)
                    ·
                      refine ⟨2791424612424095763199009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59550391731714042948245525 2791424612424095763199009)
                      ·
                        rfl

theorem cell23_5436280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_5436280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436280 prefixEnd_5436280 := by exact prefixLift 5436280
  have htrace : WordTrace (prefixWord ++ tailWord_5436280) baseStart_5436280 baseEnd_5436280 := by
    simpa [prefixWord, tailWord_5436280, baseEnd_5436280] using wordTrace_append hprefix tailTrace_5436280
  have hstable : (prefixWord ++ tailWord_5436280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436280).length < 2 ^ (prefixWord ++ tailWord_5436280).sum := by decide
  have hdescent : baseEnd_5436280 < baseStart_5436280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436287 : List Nat := [1, 1, 2, 2, 1, 1, 5, 1, 4, 2, 3]
def baseStart_5436287 : Nat := 118140960795 + 5436287 * 2 ^ 59
def prefixEnd_5436287 : Nat := 4983230072969 + 3 ^ 40 * 5436287 * 2
def baseEnd_5436287 : Nat := 2791428206788677235811477

theorem tailTrace_5436287 : CollatzResearch.WordTrace tailWord_5436287 prefixEnd_5436287 2791428206788677235811477 := by
  unfold tailWord_5436287
  simp only [CollatzResearch.WordTrace]
  refine ⟨198277676056268117747515115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132185117370845411831676743 198277676056268117747515115)
  ·
    refine ⟨297416514084402176621272673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198277676056268117747515115 297416514084402176621272673)
    ·
      refine ⟨223062385563301632465954505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297416514084402176621272673 223062385563301632465954505)
      ·
        refine ⟨167296789172476224349465879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223062385563301632465954505 167296789172476224349465879)
        ·
          refine ⟨250945183758714336524198819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167296789172476224349465879 250945183758714336524198819)
          ·
            refine ⟨376417775638071504786298229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250945183758714336524198819 376417775638071504786298229)
            ·
              refine ⟨35289166466069203573715459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 376417775638071504786298229 35289166466069203573715459)
              ·
                refine ⟨52933749699103805360573189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35289166466069203573715459 52933749699103805360573189)
                ·
                  refine ⟨9925078068581963505107473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52933749699103805360573189 9925078068581963505107473)
                  ·
                    refine ⟨7443808551436472628830605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9925078068581963505107473 7443808551436472628830605)
                    ·
                      refine ⟨2791428206788677235811477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7443808551436472628830605 2791428206788677235811477)
                      ·
                        rfl

theorem cell23_5436287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 2, 3].length) (baseStart_5436287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436287 prefixEnd_5436287 := by exact prefixLift 5436287
  have htrace : WordTrace (prefixWord ++ tailWord_5436287) baseStart_5436287 baseEnd_5436287 := by
    simpa [prefixWord, tailWord_5436287, baseEnd_5436287] using wordTrace_append hprefix tailTrace_5436287
  have hstable : (prefixWord ++ tailWord_5436287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436287).length < 2 ^ (prefixWord ++ tailWord_5436287).sum := by decide
  have hdescent : baseEnd_5436287 < baseStart_5436287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436321 : List Nat := [1, 2, 3, 4, 1, 2, 2, 1, 2, 2, 3]
def baseStart_5436321 : Nat := 118140960795 + 5436321 * 2 ^ 59
def prefixEnd_5436321 : Nat := 4983230072969 + 3 ^ 40 * 5436321 * 2
def baseEnd_5436321 : Nat := 2791445665130930102786321

theorem tailTrace_5436321 : CollatzResearch.WordTrace tailWord_5436321 prefixEnd_5436321 2791445665130930102786321 := by
  unfold tailWord_5436321
  simp only [CollatzResearch.WordTrace]
  refine ⟨198278916138144941554252817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132185944092096627702835211 198278916138144941554252817)
  ·
    refine ⟨148709187103608706165689613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198278916138144941554252817 148709187103608706165689613)
    ·
      refine ⟨55765945163853264812133605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148709187103608706165689613 55765945163853264812133605)
      ·
        refine ⟨10456114718222487152275051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55765945163853264812133605 10456114718222487152275051)
        ·
          refine ⟨15684172077333730728412577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10456114718222487152275051 15684172077333730728412577)
          ·
            refine ⟨11763129058000298046309433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15684172077333730728412577 11763129058000298046309433)
            ·
              refine ⟨8822346793500223534732075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11763129058000298046309433 8822346793500223534732075)
              ·
                refine ⟨13233520190250335302098113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8822346793500223534732075 13233520190250335302098113)
                ·
                  refine ⟨9925140142687751476573585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13233520190250335302098113 9925140142687751476573585)
                  ·
                    refine ⟨7443855107015813607430189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9925140142687751476573585 7443855107015813607430189)
                    ·
                      refine ⟨2791445665130930102786321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7443855107015813607430189 2791445665130930102786321)
                      ·
                        rfl

theorem cell23_5436321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_5436321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436321 prefixEnd_5436321 := by exact prefixLift 5436321
  have htrace : WordTrace (prefixWord ++ tailWord_5436321) baseStart_5436321 baseEnd_5436321 := by
    simpa [prefixWord, tailWord_5436321, baseEnd_5436321] using wordTrace_append hprefix tailTrace_5436321
  have hstable : (prefixWord ++ tailWord_5436321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436321).length < 2 ^ (prefixWord ++ tailWord_5436321).sum := by decide
  have hdescent : baseEnd_5436321 < baseStart_5436321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436367 : List Nat := [1, 1, 2, 1, 1, 6, 1, 3, 1, 6]
def baseStart_5436367 : Nat := 118140960795 + 5436367 * 2 ^ 59
def prefixEnd_5436367 : Nat := 4983230072969 + 3 ^ 40 * 5436367 * 2
def baseEnd_5436367 : Nat := 930489761747012307603703

theorem tailTrace_5436367 : CollatzResearch.WordTrace tailWord_5436367 prefixEnd_5436367 930489761747012307603703 := by
  unfold tailWord_5436367
  simp only [CollatzResearch.WordTrace]
  refine ⟨198280593895978291410427355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132187062597318860940284903 198280593895978291410427355)
  ·
    refine ⟨297420890843967437115641033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198280593895978291410427355 297420890843967437115641033)
    ·
      refine ⟨223065668132975577836730775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297420890843967437115641033 223065668132975577836730775)
      ·
        refine ⟨334598502199463366755096163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223065668132975577836730775 334598502199463366755096163)
        ·
          refine ⟨501897753299195050132644245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334598502199463366755096163 501897753299195050132644245)
          ·
            refine ⟨23526457185899767974967699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 501897753299195050132644245 23526457185899767974967699)
            ·
              refine ⟨35289685778849651962451549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23526457185899767974967699 35289685778849651962451549)
              ·
                refine ⟨13233632167068619485919331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35289685778849651962451549 13233632167068619485919331)
                ·
                  refine ⟨19850448250602929228878997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13233632167068619485919331 19850448250602929228878997)
                  ·
                    refine ⟨930489761747012307603703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19850448250602929228878997 930489761747012307603703)
                    ·
                      rfl

theorem cell23_5436367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 6].length) (baseStart_5436367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436367 prefixEnd_5436367 := by exact prefixLift 5436367
  have htrace : WordTrace (prefixWord ++ tailWord_5436367) baseStart_5436367 baseEnd_5436367 := by
    simpa [prefixWord, tailWord_5436367, baseEnd_5436367] using wordTrace_append hprefix tailTrace_5436367
  have hstable : (prefixWord ++ tailWord_5436367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436367).length < 2 ^ (prefixWord ++ tailWord_5436367).sum := by decide
  have hdescent : baseEnd_5436367 < baseStart_5436367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436378 : List Nat := [3, 1, 1, 2, 4, 3, 1, 1, 2, 3, 2]
def baseStart_5436378 : Nat := 118140960795 + 5436378 * 2 ^ 59
def prefixEnd_5436378 : Nat := 4983230072969 + 3 ^ 40 * 5436378 * 2
def baseEnd_5436378 : Nat := 2791474933528236379773559

theorem tailTrace_5436378 : CollatzResearch.WordTrace tailWord_5436378 prefixEnd_5436378 2791474933528236379773559 := by
  unfold tailWord_5436378
  simp only [CollatzResearch.WordTrace]
  refine ⟨49570248774734610072269447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132187330065958960192718525 49570248774734610072269447)
  ·
    refine ⟨74355373162101915108404171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49570248774734610072269447 74355373162101915108404171)
    ·
      refine ⟨111533059743152872662606257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74355373162101915108404171 111533059743152872662606257)
      ·
        refine ⟨83649794807364654496954693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111533059743152872662606257 83649794807364654496954693)
        ·
          refine ⟨15684336526380872718179005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83649794807364654496954693 15684336526380872718179005)
          ·
            refine ⟨5881626197392827269317127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15684336526380872718179005 5881626197392827269317127)
            ·
              refine ⟨8822439296089240903975691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5881626197392827269317127 8822439296089240903975691)
              ·
                refine ⟨13233658944133861355963537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8822439296089240903975691 13233658944133861355963537)
                ·
                  refine ⟨9925244208100396016972653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13233658944133861355963537 9925244208100396016972653)
                  ·
                    refine ⟨3721966578037648506364745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9925244208100396016972653 3721966578037648506364745)
                    ·
                      refine ⟨2791474933528236379773559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3721966578037648506364745 2791474933528236379773559)
                      ·
                        rfl

theorem cell23_5436378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 3, 2].length) (baseStart_5436378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436378 prefixEnd_5436378 := by exact prefixLift 5436378
  have htrace : WordTrace (prefixWord ++ tailWord_5436378) baseStart_5436378 baseEnd_5436378 := by
    simpa [prefixWord, tailWord_5436378, baseEnd_5436378] using wordTrace_append hprefix tailTrace_5436378
  have hstable : (prefixWord ++ tailWord_5436378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436378).length < 2 ^ (prefixWord ++ tailWord_5436378).sum := by decide
  have hdescent : baseEnd_5436378 < baseStart_5436378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436391 : List Nat := [1, 1, 5, 2, 2, 2, 1, 3, 1, 1, 4]
def baseStart_5436391 : Nat := 118140960795 + 5436391 * 2 ^ 59
def prefixEnd_5436391 : Nat := 4983230072969 + 3 ^ 40 * 5436391 * 2
def baseEnd_5436391 : Nat := 2791481608776744828910999

theorem tailTrace_5436391 : CollatzResearch.WordTrace tailWord_5436391 prefixEnd_5436391 2791481608776744828910999 := by
  unfold tailWord_5436391
  simp only [CollatzResearch.WordTrace]
  refine ⟨198281469247891343509301027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132187646165260895672867351 198281469247891343509301027)
  ·
    refine ⟨297422203871837015263951541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198281469247891343509301027 297422203871837015263951541)
    ·
      refine ⟨27883331612984720180995457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 297422203871837015263951541 27883331612984720180995457)
      ·
        refine ⟨20912498709738540135746593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27883331612984720180995457 20912498709738540135746593)
        ·
          refine ⟨15684374032303905101809945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20912498709738540135746593 15684374032303905101809945)
          ·
            refine ⟨11763280524227928826357459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15684374032303905101809945 11763280524227928826357459)
            ·
              refine ⟨17644920786341893239536189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11763280524227928826357459 17644920786341893239536189)
              ·
                refine ⟨6616845294878209964826071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17644920786341893239536189 6616845294878209964826071)
                ·
                  refine ⟨9925267942317314947239107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6616845294878209964826071 9925267942317314947239107)
                  ·
                    refine ⟨14887901913475972420858661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9925267942317314947239107 14887901913475972420858661)
                    ·
                      refine ⟨2791481608776744828910999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14887901913475972420858661 2791481608776744828910999)
                      ·
                        rfl

theorem cell23_5436391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_5436391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436391 prefixEnd_5436391 := by exact prefixLift 5436391
  have htrace : WordTrace (prefixWord ++ tailWord_5436391) baseStart_5436391 baseEnd_5436391 := by
    simpa [prefixWord, tailWord_5436391, baseEnd_5436391] using wordTrace_append hprefix tailTrace_5436391
  have hstable : (prefixWord ++ tailWord_5436391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436391).length < 2 ^ (prefixWord ++ tailWord_5436391).sum := by decide
  have hdescent : baseEnd_5436391 < baseStart_5436391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436401 : List Nat := [1, 2, 2, 2, 4, 1, 3, 2, 2, 4]
def baseStart_5436401 : Nat := 118140960795 + 5436401 * 2 ^ 59
def prefixEnd_5436401 : Nat := 4983230072969 + 3 ^ 40 * 5436401 * 2
def baseEnd_5436401 : Nat := 930495581194429929928651

theorem tailTrace_5436401 : CollatzResearch.WordTrace tailWord_5436401 prefixEnd_5436401 930495581194429929928651 := by
  unfold tailWord_5436401
  simp only [CollatzResearch.WordTrace]
  refine ⟨198281833977855115217165057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132187889318570076811443371 198281833977855115217165057)
  ·
    refine ⟨148711375483391336412873793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198281833977855115217165057 148711375483391336412873793)
    ·
      refine ⟨111533531612543502309655345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148711375483391336412873793 111533531612543502309655345)
      ·
        refine ⟨83650148709407626732241509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111533531612543502309655345 83650148709407626732241509)
        ·
          refine ⟨15684402883013930012295283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83650148709407626732241509 15684402883013930012295283)
          ·
            refine ⟨23526604324520895018442925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15684402883013930012295283 23526604324520895018442925)
            ·
              refine ⟨8822476621695335631916097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23526604324520895018442925 8822476621695335631916097)
              ·
                refine ⟨6616857466271501723937073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8822476621695335631916097 6616857466271501723937073)
                ·
                  refine ⟨4962643099703626292952805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6616857466271501723937073 4962643099703626292952805)
                  ·
                    refine ⟨930495581194429929928651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4962643099703626292952805 930495581194429929928651)
                    ·
                      rfl

theorem cell23_5436401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 2, 2, 4].length) (baseStart_5436401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436401 prefixEnd_5436401 := by exact prefixLift 5436401
  have htrace : WordTrace (prefixWord ++ tailWord_5436401) baseStart_5436401 baseEnd_5436401 := by
    simpa [prefixWord, tailWord_5436401, baseEnd_5436401] using wordTrace_append hprefix tailTrace_5436401
  have hstable : (prefixWord ++ tailWord_5436401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436401).length < 2 ^ (prefixWord ++ tailWord_5436401).sum := by decide
  have hdescent : baseEnd_5436401 < baseStart_5436401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436407 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 1, 9, 3]
def baseStart_5436407 : Nat := 118140960795 + 5436407 * 2 ^ 59
def prefixEnd_5436407 : Nat := 4983230072969 + 3 ^ 40 * 5436407 * 2
def baseEnd_5436407 : Nat := 2791489824467216766310925

theorem tailTrace_5436407 : CollatzResearch.WordTrace tailWord_5436407 prefixEnd_5436407 2791489824467216766310925 := by
  unfold tailWord_5436407
  simp only [CollatzResearch.WordTrace]
  refine ⟨198282052815833378241883475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132188035210555585494588983 198282052815833378241883475)
  ·
    refine ⟨297423079223750067362825213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198282052815833378241883475 297423079223750067362825213)
    ·
      refine ⟨111533654708906275261059455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 297423079223750067362825213 111533654708906275261059455)
      ·
        refine ⟨167300482063359412891589183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111533654708906275261059455 167300482063359412891589183)
        ·
          refine ⟨250950723095039119337383775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167300482063359412891589183 250950723095039119337383775)
          ·
            refine ⟨376426084642558679006075663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250950723095039119337383775 376426084642558679006075663)
            ·
              refine ⟨564639126963838018509113495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376426084642558679006075663 564639126963838018509113495)
              ·
                refine ⟨846958690445757027763670243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 564639126963838018509113495 846958690445757027763670243)
                ·
                  refine ⟨1270438035668635541645505365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 846958690445757027763670243 1270438035668635541645505365)
                  ·
                    refine ⟨7443972865245911376829133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 1270438035668635541645505365 7443972865245911376829133)
                    ·
                      refine ⟨2791489824467216766310925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7443972865245911376829133 2791489824467216766310925)
                      ·
                        rfl

theorem cell23_5436407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 9, 3].length) (baseStart_5436407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436407 prefixEnd_5436407 := by exact prefixLift 5436407
  have htrace : WordTrace (prefixWord ++ tailWord_5436407) baseStart_5436407 baseEnd_5436407 := by
    simpa [prefixWord, tailWord_5436407, baseEnd_5436407] using wordTrace_append hprefix tailTrace_5436407
  have hstable : (prefixWord ++ tailWord_5436407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436407).length < 2 ^ (prefixWord ++ tailWord_5436407).sum := by decide
  have hdescent : baseEnd_5436407 < baseStart_5436407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436467 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 5]
def baseStart_5436467 : Nat := 118140960795 + 5436467 * 2 ^ 59
def prefixEnd_5436467 : Nat := 4983230072969 + 3 ^ 40 * 5436467 * 2
def baseEnd_5436467 : Nat := 2791520633306486531560649

theorem tailTrace_5436467 : CollatzResearch.WordTrace tailWord_5436467 prefixEnd_5436467 2791520633306486531560649 := by
  unfold tailWord_5436467
  simp only [CollatzResearch.WordTrace]
  refine ⟨198284241195616008489067655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132189494130410672326045103 198284241195616008489067655)
  ·
    refine ⟨297426361793424012733601483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198284241195616008489067655 297426361793424012733601483)
    ·
      refine ⟨446139542690136019100402225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297426361793424012733601483 446139542690136019100402225)
      ·
        refine ⟨334604657017602014325301669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 446139542690136019100402225 334604657017602014325301669)
        ·
          refine ⟨62738373190800377685994063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 334604657017602014325301669 62738373190800377685994063)
          ·
            refine ⟨94107559786200566528991095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62738373190800377685994063 94107559786200566528991095)
            ·
              refine ⟨141161339679300849793486643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94107559786200566528991095 141161339679300849793486643)
              ·
                refine ⟨211742009518951274690229965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141161339679300849793486643 211742009518951274690229965)
                ·
                  refine ⟨79403253569606728008836237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 211742009518951274690229965 79403253569606728008836237)
                  ·
                    refine ⟨29776220088602523003313589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79403253569606728008836237 29776220088602523003313589)
                    ·
                      refine ⟨2791520633306486531560649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29776220088602523003313589 2791520633306486531560649)
                      ·
                        rfl

theorem cell23_5436467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 5].length) (baseStart_5436467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436467 prefixEnd_5436467 := by exact prefixLift 5436467
  have htrace : WordTrace (prefixWord ++ tailWord_5436467) baseStart_5436467 baseEnd_5436467 := by
    simpa [prefixWord, tailWord_5436467, baseEnd_5436467] using wordTrace_append hprefix tailTrace_5436467
  have hstable : (prefixWord ++ tailWord_5436467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436467).length < 2 ^ (prefixWord ++ tailWord_5436467).sum := by decide
  have hdescent : baseEnd_5436467 < baseStart_5436467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436498 : List Nat := [3, 2, 2, 1, 3, 2, 1, 2, 1, 4, 2]
def baseStart_5436498 : Nat := 118140960795 + 5436498 * 2 ^ 59
def prefixEnd_5436498 : Nat := 4983230072969 + 3 ^ 40 * 5436498 * 2
def baseEnd_5436498 : Nat := 2791536551206775910273007

theorem tailTrace_5436498 : CollatzResearch.WordTrace tailWord_5436498 prefixEnd_5436498 2791536551206775910273007 := by
  unfold tailWord_5436498
  simp only [CollatzResearch.WordTrace]
  refine ⟨49571342964625925195861537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132190247905669133855630765 49571342964625925195861537)
  ·
    refine ⟨37178507223469443896896153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49571342964625925195861537 37178507223469443896896153)
    ·
      refine ⟨27883880417602082922672115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37178507223469443896896153 27883880417602082922672115)
      ·
        refine ⟨41825820626403124384008173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27883880417602082922672115 41825820626403124384008173)
        ·
          refine ⟨15684682734901171644003065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41825820626403124384008173 15684682734901171644003065)
          ·
            refine ⟨11763512051175878733002299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15684682734901171644003065 11763512051175878733002299)
            ·
              refine ⟨17645268076763818099503449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11763512051175878733002299 17645268076763818099503449)
              ·
                refine ⟨13233951057572863574627587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17645268076763818099503449 13233951057572863574627587)
                ·
                  refine ⟨19850926586359295361941381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13233951057572863574627587 19850926586359295361941381)
                  ·
                    refine ⟨3722048734942367880364009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19850926586359295361941381 3722048734942367880364009)
                    ·
                      refine ⟨2791536551206775910273007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3722048734942367880364009 2791536551206775910273007)
                      ·
                        rfl

theorem cell23_5436498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_5436498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436498 prefixEnd_5436498 := by exact prefixLift 5436498
  have htrace : WordTrace (prefixWord ++ tailWord_5436498) baseStart_5436498 baseEnd_5436498 := by
    simpa [prefixWord, tailWord_5436498, baseEnd_5436498] using wordTrace_append hprefix tailTrace_5436498
  have hstable : (prefixWord ++ tailWord_5436498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436498).length < 2 ^ (prefixWord ++ tailWord_5436498).sum := by decide
  have hdescent : baseEnd_5436498 < baseStart_5436498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436521 : List Nat := [1, 2, 1, 1, 1, 7, 1, 4, 5]
def baseStart_5436521 : Nat := 118140960795 + 5436521 * 2 ^ 59
def prefixEnd_5436521 : Nat := 4983230072969 + 3 ^ 40 * 5436521 * 2
def baseEnd_5436521 : Nat := 310172040140203257809489

theorem tailTrace_5436521 : CollatzResearch.WordTrace tailWord_5436521 prefixEnd_5436521 310172040140203257809489 := by
  unfold tailWord_5436521
  simp only [CollatzResearch.WordTrace]
  refine ⟨198286210737420375711533417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132190807158280250474355611 198286210737420375711533417)
  ·
    refine ⟨148714658053065281783650063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198286210737420375711533417 148714658053065281783650063)
    ·
      refine ⟨223071987079597922675475095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148714658053065281783650063 223071987079597922675475095)
      ·
        refine ⟨334607980619396884013212643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223071987079597922675475095 334607980619396884013212643)
        ·
          refine ⟨501911970929095326019818965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334607980619396884013212643 501911970929095326019818965)
          ·
            refine ⟨11763561818650671703589507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 501911970929095326019818965 11763561818650671703589507)
            ·
              refine ⟨17645342727976007555384261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11763561818650671703589507 17645342727976007555384261)
              ·
                refine ⟨3308501761495501416634549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17645342727976007555384261 3308501761495501416634549)
                ·
                  refine ⟨310172040140203257809489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3308501761495501416634549 310172040140203257809489)
                  ·
                    rfl

theorem cell23_5436521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 4, 5].length) (baseStart_5436521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436521 prefixEnd_5436521 := by exact prefixLift 5436521
  have htrace : WordTrace (prefixWord ++ tailWord_5436521) baseStart_5436521 baseEnd_5436521 := by
    simpa [prefixWord, tailWord_5436521, baseEnd_5436521] using wordTrace_append hprefix tailTrace_5436521
  have hstable : (prefixWord ++ tailWord_5436521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436521).length < 2 ^ (prefixWord ++ tailWord_5436521).sum := by decide
  have hdescent : baseEnd_5436521 < baseStart_5436521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436541 : List Nat := [1, 4, 1, 1, 3, 1, 1, 2, 2, 5, 2]
def baseStart_5436541 : Nat := 118140960795 + 5436541 * 2 ^ 59
def prefixEnd_5436541 : Nat := 4983230072969 + 3 ^ 40 * 5436541 * 2
def baseEnd_5436541 : Nat := 2791558630874919242035309

theorem tailTrace_5436541 : CollatzResearch.WordTrace tailWord_5436541 prefixEnd_5436541 2791558630874919242035309 := by
  unfold tailWord_5436541
  simp only [CollatzResearch.WordTrace]
  refine ⟨198286940197347919127261477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132191293464898612751507651 198286940197347919127261477)
  ·
    refine ⟨37178801287002734836361527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198286940197347919127261477 37178801287002734836361527)
    ·
      refine ⟨55768201930504102254542291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37178801287002734836361527 55768201930504102254542291)
      ·
        refine ⟨83652302895756153381813437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55768201930504102254542291 83652302895756153381813437)
        ·
          refine ⟨31369613585908557518180039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83652302895756153381813437 31369613585908557518180039)
          ·
            refine ⟨47054420378862836277270059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31369613585908557518180039 47054420378862836277270059)
            ·
              refine ⟨70581630568294254415905089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47054420378862836277270059 70581630568294254415905089)
              ·
                refine ⟨52936222926220690811928817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70581630568294254415905089 52936222926220690811928817)
                ·
                  refine ⟨39702167194665518108946613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52936222926220690811928817 39702167194665518108946613)
                  ·
                    refine ⟨3722078174499892322713745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39702167194665518108946613 3722078174499892322713745)
                    ·
                      refine ⟨2791558630874919242035309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3722078174499892322713745 2791558630874919242035309)
                      ·
                        rfl

theorem cell23_5436541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 5, 2].length) (baseStart_5436541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436541 prefixEnd_5436541 := by exact prefixLift 5436541
  have htrace : WordTrace (prefixWord ++ tailWord_5436541) baseStart_5436541 baseEnd_5436541 := by
    simpa [prefixWord, tailWord_5436541, baseEnd_5436541] using wordTrace_append hprefix tailTrace_5436541
  have hstable : (prefixWord ++ tailWord_5436541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436541).length < 2 ^ (prefixWord ++ tailWord_5436541).sum := by decide
  have hdescent : baseEnd_5436541 < baseStart_5436541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436581 : List Nat := [1, 3, 1, 2, 1, 4, 1, 3, 3, 4]
def baseStart_5436581 : Nat := 118140960795 + 5436581 * 2 ^ 59
def prefixEnd_5436581 : Nat := 4983230072969 + 3 ^ 40 * 5436581 * 2
def baseEnd_5436581 : Nat := 930526390033699695178375

theorem tailTrace_5436581 : CollatzResearch.WordTrace tailWord_5436581 prefixEnd_5436581 930526390033699695178375 := by
  unfold tailWord_5436581
  simp only [CollatzResearch.WordTrace]
  refine ⟨198288399117203005958717597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132192266078135337305811731 198288399117203005958717597)
  ·
    refine ⟨74358149668951127234519099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198288399117203005958717597 74358149668951127234519099)
    ·
      refine ⟨111537224503426690851778649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74358149668951127234519099 111537224503426690851778649)
      ·
        refine ⟨83652918377570018138833987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111537224503426690851778649 83652918377570018138833987)
        ·
          refine ⟨125479377566355027208250981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83652918377570018138833987 125479377566355027208250981)
          ·
            refine ⟨23527383293691567601547059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125479377566355027208250981 23527383293691567601547059)
            ·
              refine ⟨35291074940537351402320589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23527383293691567601547059 35291074940537351402320589)
              ·
                refine ⟨13234153102701506775870221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35291074940537351402320589 13234153102701506775870221)
                ·
                  refine ⟨4962807413513065040951333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13234153102701506775870221 4962807413513065040951333)
                  ·
                    refine ⟨930526390033699695178375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4962807413513065040951333 930526390033699695178375)
                    ·
                      rfl

theorem cell23_5436581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 3, 4].length) (baseStart_5436581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436581 prefixEnd_5436581 := by exact prefixLift 5436581
  have htrace : WordTrace (prefixWord ++ tailWord_5436581) baseStart_5436581 baseEnd_5436581 := by
    simpa [prefixWord, tailWord_5436581, baseEnd_5436581] using wordTrace_append hprefix tailTrace_5436581
  have hstable : (prefixWord ++ tailWord_5436581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436581).length < 2 ^ (prefixWord ++ tailWord_5436581).sum := by decide
  have hdescent : baseEnd_5436581 < baseStart_5436581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436632 : List Nat := [2, 1, 2, 2, 5, 1, 3, 2, 1, 4]
def baseStart_5436632 : Nat := 118140960795 + 5436632 * 2 ^ 59
def prefixEnd_5436632 : Nat := 4983230072969 + 3 ^ 40 * 5436632 * 2
def baseEnd_5436632 : Nat := 930535119204826128665797

theorem tailTrace_5436632 : CollatzResearch.WordTrace tailWord_5436632 prefixEnd_5436632 930535119204826128665797 := by
  unfold tailWord_5436632
  simp only [CollatzResearch.WordTrace]
  refine ⟨99145129620009120834412075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132193506160012161112549433 99145129620009120834412075)
  ·
    refine ⟨148717694430013681251618113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99145129620009120834412075 148717694430013681251618113)
    ·
      refine ⟨111538270822510260938713585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148717694430013681251618113 111538270822510260938713585)
      ·
        refine ⟨83653703116882695704035189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111538270822510260938713585 83653703116882695704035189)
        ·
          refine ⟨7842534667207752722253299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83653703116882695704035189 7842534667207752722253299)
          ·
            refine ⟨11763802000811629083379949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7842534667207752722253299 11763802000811629083379949)
            ·
              refine ⟨4411425750304360906267481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11763802000811629083379949 4411425750304360906267481)
              ·
                refine ⟨3308569312728270679700611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4411425750304360906267481 3308569312728270679700611)
                ·
                  refine ⟨4962853969092406019550917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3308569312728270679700611 4962853969092406019550917)
                  ·
                    refine ⟨930535119204826128665797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4962853969092406019550917 930535119204826128665797)
                    ·
                      rfl

theorem cell23_5436632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 2, 1, 4].length) (baseStart_5436632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436632 prefixEnd_5436632 := by exact prefixLift 5436632
  have htrace : WordTrace (prefixWord ++ tailWord_5436632) baseStart_5436632 baseEnd_5436632 := by
    simpa [prefixWord, tailWord_5436632, baseEnd_5436632] using wordTrace_append hprefix tailTrace_5436632
  have hstable : (prefixWord ++ tailWord_5436632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436632).length < 2 ^ (prefixWord ++ tailWord_5436632).sum := by decide
  have hdescent : baseEnd_5436632 < baseStart_5436632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436634 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 7]
def baseStart_5436634 : Nat := 118140960795 + 5436634 * 2 ^ 59
def prefixEnd_5436634 : Nat := 4983230072969 + 3 ^ 40 * 5436634 * 2
def baseEnd_5436634 : Nat := 2791606384575787378172381

theorem tailTrace_5436634 : CollatzResearch.WordTrace tailWord_5436634 prefixEnd_5436634 2791606384575787378172381 := by
  unfold tailWord_5436634
  simp only [CollatzResearch.WordTrace]
  refine ⟨49572583046502749002599239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132193554790673997340264637 49572583046502749002599239)
  ·
    refine ⟨74358874569754123503898859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49572583046502749002599239 74358874569754123503898859)
    ·
      refine ⟨111538311854631185255848289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74358874569754123503898859 111538311854631185255848289)
      ·
        refine ⟨83653733890973388941886217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111538311854631185255848289 83653733890973388941886217)
        ·
          refine ⟨62740300418230041706414663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83653733890973388941886217 62740300418230041706414663)
          ·
            refine ⟨94110450627345062559621995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62740300418230041706414663 94110450627345062559621995)
            ·
              refine ⟨141165675941017593839432993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94110450627345062559621995 141165675941017593839432993)
              ·
                refine ⟨105874256955763195379574745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141165675941017593839432993 105874256955763195379574745)
                ·
                  refine ⟨79405692716822396534681059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105874256955763195379574745 79405692716822396534681059)
                  ·
                    refine ⟨119108539075233594802021589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79405692716822396534681059 119108539075233594802021589)
                    ·
                      refine ⟨2791606384575787378172381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 119108539075233594802021589 2791606384575787378172381)
                      ·
                        rfl

theorem cell23_5436634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_5436634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436634 prefixEnd_5436634 := by exact prefixLift 5436634
  have htrace : WordTrace (prefixWord ++ tailWord_5436634) baseStart_5436634 baseEnd_5436634 := by
    simpa [prefixWord, tailWord_5436634, baseEnd_5436634] using wordTrace_append hprefix tailTrace_5436634
  have hstable : (prefixWord ++ tailWord_5436634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436634).length < 2 ^ (prefixWord ++ tailWord_5436634).sum := by decide
  have hdescent : baseEnd_5436634 < baseStart_5436634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436645 : List Nat := [1, 3, 1, 4, 3, 2, 2, 1, 6]
def baseStart_5436645 : Nat := 118140960795 + 5436645 * 2 ^ 59
def prefixEnd_5436645 : Nat := 4983230072969 + 3 ^ 40 * 5436645 * 2
def baseEnd_5436645 : Nat := 310179114762554092792759

theorem tailTrace_5436645 : CollatzResearch.WordTrace tailWord_5436645 prefixEnd_5436645 310179114762554092792759 := by
  unfold tailWord_5436645
  simp only [CollatzResearch.WordTrace]
  refine ⟨198290733388971144889047389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132193822259314096592698259 198290733388971144889047389)
  ·
    refine ⟨74359025020864179333392771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198290733388971144889047389 74359025020864179333392771)
    ·
      refine ⟨111538537531296269000089157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74359025020864179333392771 111538537531296269000089157)
      ·
        refine ⟨20913475787118050437516717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111538537531296269000089157 20913475787118050437516717)
        ·
          refine ⟨7842553420169268914068769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20913475787118050437516717 7842553420169268914068769)
          ·
            refine ⟨5881915065126951685551577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7842553420169268914068769 5881915065126951685551577)
            ·
              refine ⟨4411436298845213764163683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5881915065126951685551577 4411436298845213764163683)
              ·
                refine ⟨6617154448267820646245525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4411436298845213764163683 6617154448267820646245525)
                ·
                  refine ⟨310179114762554092792759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6617154448267820646245525 310179114762554092792759)
                  ·
                    rfl

theorem cell23_5436645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 6].length) (baseStart_5436645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436645 prefixEnd_5436645 := by exact prefixLift 5436645
  have htrace : WordTrace (prefixWord ++ tailWord_5436645) baseStart_5436645 baseEnd_5436645 := by
    simpa [prefixWord, tailWord_5436645, baseEnd_5436645] using wordTrace_append hprefix tailTrace_5436645
  have hstable : (prefixWord ++ tailWord_5436645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436645).length < 2 ^ (prefixWord ++ tailWord_5436645).sum := by decide
  have hdescent : baseEnd_5436645 < baseStart_5436645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436648 : List Nat := [2, 1, 4, 1, 2, 1, 1, 2, 4, 3, 2]
def baseStart_5436648 : Nat := 118140960795 + 5436648 * 2 ^ 59
def prefixEnd_5436648 : Nat := 4983230072969 + 3 ^ 40 * 5436648 * 2
def baseEnd_5436648 : Nat := 2791613573304950323397317

theorem tailTrace_5436648 : CollatzResearch.WordTrace tailWord_5436648 prefixEnd_5436648 2791613573304950323397317 := by
  unfold tailWord_5436648
  simp only [CollatzResearch.WordTrace]
  refine ⟨99145421403980138200703299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132193895205306850934271065 99145421403980138200703299)
  ·
    refine ⟨148718132105970207301054949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99145421403980138200703299 148718132105970207301054949)
    ·
      refine ⟨27884649769869413868947803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148718132105970207301054949 27884649769869413868947803)
      ·
        refine ⟨41826974654804120803421705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27884649769869413868947803 41826974654804120803421705)
        ·
          refine ⟨31370230991103090602566279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41826974654804120803421705 31370230991103090602566279)
          ·
            refine ⟨47055346486654635903849419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31370230991103090602566279 47055346486654635903849419)
            ·
              refine ⟨70583019729981953855774129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47055346486654635903849419 70583019729981953855774129)
              ·
                refine ⟨52937264797486465391830597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70583019729981953855774129 52937264797486465391830597)
                ·
                  refine ⟨9925737149528712260968237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52937264797486465391830597 9925737149528712260968237)
                  ·
                    refine ⟨3722151431073267097863089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9925737149528712260968237 3722151431073267097863089)
                    ·
                      refine ⟨2791613573304950323397317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3722151431073267097863089 2791613573304950323397317)
                      ·
                        rfl

theorem cell23_5436648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_5436648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436648 prefixEnd_5436648 := by exact prefixLift 5436648
  have htrace : WordTrace (prefixWord ++ tailWord_5436648) baseStart_5436648 baseEnd_5436648 := by
    simpa [prefixWord, tailWord_5436648, baseEnd_5436648] using wordTrace_append hprefix tailTrace_5436648
  have hstable : (prefixWord ++ tailWord_5436648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436648).length < 2 ^ (prefixWord ++ tailWord_5436648).sum := by decide
  have hdescent : baseEnd_5436648 < baseStart_5436648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436658 : List Nat := [3, 2, 1, 3, 3, 1, 1, 1, 3, 5]
def baseStart_5436658 : Nat := 118140960795 + 5436658 * 2 ^ 59
def prefixEnd_5436658 : Nat := 4983230072969 + 3 ^ 40 * 5436658 * 2
def baseEnd_5436658 : Nat := 930539569370498428090757

theorem tailTrace_5436658 : CollatzResearch.WordTrace tailWord_5436658 prefixEnd_5436658 930539569370498428090757 := by
  unfold tailWord_5436658
  simp only [CollatzResearch.WordTrace]
  refine ⟨49572801884481012027317657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132194138358616032072847085 49572801884481012027317657)
  ·
    refine ⟨37179601413360759020488243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49572801884481012027317657 37179601413360759020488243)
    ·
      refine ⟨55769402120041138530732365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37179601413360759020488243 55769402120041138530732365)
      ·
        refine ⟨20913525795015426949024637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55769402120041138530732365 20913525795015426949024637)
        ·
          refine ⟨7842572173130785105884239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20913525795015426949024637 7842572173130785105884239)
          ·
            refine ⟨11763858259696177658826359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7842572173130785105884239 11763858259696177658826359)
            ·
              refine ⟨17645787389544266488239539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11763858259696177658826359 17645787389544266488239539)
              ·
                refine ⟨26468681084316399732359309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17645787389544266488239539 26468681084316399732359309)
                ·
                  refine ⟨9925755406618649899634741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26468681084316399732359309 9925755406618649899634741)
                  ·
                    refine ⟨930539569370498428090757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9925755406618649899634741 930539569370498428090757)
                    ·
                      rfl

theorem cell23_5436658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_5436658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436658 prefixEnd_5436658 := by exact prefixLift 5436658
  have htrace : WordTrace (prefixWord ++ tailWord_5436658) baseStart_5436658 baseEnd_5436658 := by
    simpa [prefixWord, tailWord_5436658, baseEnd_5436658] using wordTrace_append hprefix tailTrace_5436658
  have hstable : (prefixWord ++ tailWord_5436658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436658).length < 2 ^ (prefixWord ++ tailWord_5436658).sum := by decide
  have hdescent : baseEnd_5436658 < baseStart_5436658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436664 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 2, 5, 5]
def baseStart_5436664 : Nat := 118140960795 + 5436664 * 2 ^ 59
def prefixEnd_5436664 : Nat := 4983230072969 + 3 ^ 40 * 5436664 * 2
def baseEnd_5436664 : Nat := 2791621788995422260797243

theorem tailTrace_5436664 : CollatzResearch.WordTrace tailWord_5436664 prefixEnd_5436664 2791621788995422260797243 := by
  unfold tailWord_5436664
  simp only [CollatzResearch.WordTrace]
  refine ⟨99145713187951155566994523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132194284250601540755992697 99145713187951155566994523)
  ·
    refine ⟨148718569781926733350491785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99145713187951155566994523 148718569781926733350491785)
    ·
      refine ⟨111538927336445050012868839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148718569781926733350491785 111538927336445050012868839)
      ·
        refine ⟨167308391004667575019303259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111538927336445050012868839 167308391004667575019303259)
        ·
          refine ⟨250962586507001362528954889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167308391004667575019303259 250962586507001362528954889)
          ·
            refine ⟨188221939880251021896716167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250962586507001362528954889 188221939880251021896716167)
            ·
              refine ⟨282332909820376532845074251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188221939880251021896716167 282332909820376532845074251)
              ·
                refine ⟨423499364730564799267611377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 282332909820376532845074251 423499364730564799267611377)
                ·
                  refine ⟨317624523547923599450708533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 423499364730564799267611377 317624523547923599450708533)
                  ·
                    refine ⟨29777299082617837448503925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 317624523547923599450708533 29777299082617837448503925)
                    ·
                      refine ⟨2791621788995422260797243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29777299082617837448503925 2791621788995422260797243)
                      ·
                        rfl

theorem cell23_5436664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_5436664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436664 prefixEnd_5436664 := by exact prefixLift 5436664
  have htrace : WordTrace (prefixWord ++ tailWord_5436664) baseStart_5436664 baseEnd_5436664 := by
    simpa [prefixWord, tailWord_5436664, baseEnd_5436664] using wordTrace_append hprefix tailTrace_5436664
  have hstable : (prefixWord ++ tailWord_5436664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436664).length < 2 ^ (prefixWord ++ tailWord_5436664).sum := by decide
  have hdescent : baseEnd_5436664 < baseStart_5436664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436671 : List Nat := [1, 1, 2, 2, 1, 6, 1, 2, 1, 6]
def baseStart_5436671 : Nat := 118140960795 + 5436671 * 2 ^ 59
def prefixEnd_5436671 : Nat := 4983230072969 + 3 ^ 40 * 5436671 * 2
def baseEnd_5436671 : Nat := 930541794453334577803237

theorem tailTrace_5436671 : CollatzResearch.WordTrace tailWord_5436671 prefixEnd_5436671 930541794453334577803237 := by
  unfold tailWord_5436671
  simp only [CollatzResearch.WordTrace]
  refine ⟨198291681686876951329493867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132194454457917967552995911 198291681686876951329493867)
  ·
    refine ⟨297437522530315426994240801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198291681686876951329493867 297437522530315426994240801)
    ·
      refine ⟨223078141897736570245680601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297437522530315426994240801 223078141897736570245680601)
      ·
        refine ⟨167308606423302427684260451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223078141897736570245680601 167308606423302427684260451)
        ·
          refine ⟨250962909634953641526390677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167308606423302427684260451 250962909634953641526390677)
          ·
            refine ⟨11763886389138451946549563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 250962909634953641526390677 11763886389138451946549563)
            ·
              refine ⟨17645829583707677919824345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11763886389138451946549563 17645829583707677919824345)
              ·
                refine ⟨13234372187780758439868259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17645829583707677919824345 13234372187780758439868259)
                ·
                  refine ⟨19851558281671137659802389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13234372187780758439868259 19851558281671137659802389)
                  ·
                    refine ⟨930541794453334577803237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19851558281671137659802389 930541794453334577803237)
                    ·
                      rfl

theorem cell23_5436671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 6].length) (baseStart_5436671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436671 prefixEnd_5436671 := by exact prefixLift 5436671
  have htrace : WordTrace (prefixWord ++ tailWord_5436671) baseStart_5436671 baseEnd_5436671 := by
    simpa [prefixWord, tailWord_5436671, baseEnd_5436671] using wordTrace_append hprefix tailTrace_5436671
  have hstable : (prefixWord ++ tailWord_5436671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436671).length < 2 ^ (prefixWord ++ tailWord_5436671).sum := by decide
  have hdescent : baseEnd_5436671 < baseStart_5436671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436684 : List Nat := [2, 2, 1, 2, 2, 14]
def baseStart_5436684 : Nat := 118140960795 + 5436684 * 2 ^ 59
def prefixEnd_5436684 : Nat := 4983230072969 + 3 ^ 40 * 5436684 * 2
def baseEnd_5436684 : Nat := 11488197772051490463157

theorem tailTrace_5436684 : CollatzResearch.WordTrace tailWord_5436684 prefixEnd_5436684 11488197772051490463157 := by
  unfold tailWord_5436684
  simp only [CollatzResearch.WordTrace]
  refine ⟨99146077917914927274858553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132194770557219903033144737 99146077917914927274858553)
  ·
    refine ⟨74359558438436195456143915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99146077917914927274858553 74359558438436195456143915)
    ·
      refine ⟨111539337657654293184215873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74359558438436195456143915 111539337657654293184215873)
      ·
        refine ⟨83654503243240719888161905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111539337657654293184215873 83654503243240719888161905)
        ·
          refine ⟨62740877432430539916121429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83654503243240719888161905 62740877432430539916121429)
          ·
            refine ⟨11488197772051490463157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 62740877432430539916121429 11488197772051490463157)
            ·
              rfl

theorem cell23_5436684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 14].length) (baseStart_5436684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436684 prefixEnd_5436684 := by exact prefixLift 5436684
  have htrace : WordTrace (prefixWord ++ tailWord_5436684) baseStart_5436684 baseEnd_5436684 := by
    simpa [prefixWord, tailWord_5436684, baseEnd_5436684] using wordTrace_append hprefix tailTrace_5436684
  have hstable : (prefixWord ++ tailWord_5436684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436684).length < 2 ^ (prefixWord ++ tailWord_5436684).sum := by decide
  have hdescent : baseEnd_5436684 < baseStart_5436684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436695 : List Nat := [1, 1, 3, 4, 1, 1, 2, 3, 3, 2, 2]
def baseStart_5436695 : Nat := 118140960795 + 5436695 * 2 ^ 59
def prefixEnd_5436695 : Nat := 4983230072969 + 3 ^ 40 * 5436695 * 2
def baseEnd_5436695 : Nat := 2791637706895711639509601

theorem tailTrace_5436695 : CollatzResearch.WordTrace tailWord_5436695 prefixEnd_5436695 2791637706895711639509601 := by
  unfold tailWord_5436695
  simp only [CollatzResearch.WordTrace]
  refine ⟨198292557038790003428367539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132195038025860002285578359 198292557038790003428367539)
  ·
    refine ⟨297438835558185005142551309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198292557038790003428367539 297438835558185005142551309)
    ·
      refine ⟨111539563334319376928456741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 297438835558185005142551309 111539563334319376928456741)
      ·
        refine ⟨20913668125184883174085639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111539563334319376928456741 20913668125184883174085639)
        ·
          refine ⟨31370502187777324761128459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20913668125184883174085639 31370502187777324761128459)
          ·
            refine ⟨47055753281665987141692689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31370502187777324761128459 47055753281665987141692689)
            ·
              refine ⟨35291814961249490356269517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47055753281665987141692689 35291814961249490356269517)
              ·
                refine ⟨13234430610468558883601069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35291814961249490356269517 13234430610468558883601069)
                ·
                  refine ⟨4962911478925709581350401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13234430610468558883601069 4962911478925709581350401)
                  ·
                    refine ⟨3722183609194282186012801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4962911478925709581350401 3722183609194282186012801)
                    ·
                      refine ⟨2791637706895711639509601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3722183609194282186012801 2791637706895711639509601)
                      ·
                        rfl

theorem cell23_5436695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_5436695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436695 prefixEnd_5436695 := by exact prefixLift 5436695
  have htrace : WordTrace (prefixWord ++ tailWord_5436695) baseStart_5436695 baseEnd_5436695 := by
    simpa [prefixWord, tailWord_5436695, baseEnd_5436695] using wordTrace_append hprefix tailTrace_5436695
  have hstable : (prefixWord ++ tailWord_5436695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436695).length < 2 ^ (prefixWord ++ tailWord_5436695).sum := by decide
  have hdescent : baseEnd_5436695 < baseStart_5436695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436698 : List Nat := [3, 1, 1, 3, 3, 1, 1, 2, 3, 2, 3]
def baseStart_5436698 : Nat := 118140960795 + 5436698 * 2 ^ 59
def prefixEnd_5436698 : Nat := 4983230072969 + 3 ^ 40 * 5436698 * 2
def baseEnd_5436698 : Nat := 2791639247337675127772087

theorem tailTrace_5436698 : CollatzResearch.WordTrace tailWord_5436698 prefixEnd_5436698 2791639247337675127772087 := by
  unfold tailWord_5436698
  simp only [CollatzResearch.WordTrace]
  refine ⟨49573166614444783735181687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132195110971852756627151165 49573166614444783735181687)
  ·
    refine ⟨74359749921667175602772531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49573166614444783735181687 74359749921667175602772531)
    ·
      refine ⟨111539624882500763404158797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74359749921667175602772531 111539624882500763404158797)
      ·
        refine ⟨41827359330937786276559549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111539624882500763404158797 41827359330937786276559549)
        ·
          refine ⟨15685259749101669853709831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41827359330937786276559549 15685259749101669853709831)
          ·
            refine ⟨23527889623652504780564747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15685259749101669853709831 23527889623652504780564747)
            ·
              refine ⟨35291834435478757170847121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23527889623652504780564747 35291834435478757170847121)
              ·
                refine ⟨26468875826609067878135341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35291834435478757170847121 26468875826609067878135341)
                ·
                  refine ⟨9925828434978400454300753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26468875826609067878135341 9925828434978400454300753)
                  ·
                    refine ⟨7444371326233800340725565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9925828434978400454300753 7444371326233800340725565)
                    ·
                      refine ⟨2791639247337675127772087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7444371326233800340725565 2791639247337675127772087)
                      ·
                        rfl

theorem cell23_5436698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_5436698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436698 prefixEnd_5436698 := by exact prefixLift 5436698
  have htrace : WordTrace (prefixWord ++ tailWord_5436698) baseStart_5436698 baseEnd_5436698 := by
    simpa [prefixWord, tailWord_5436698, baseEnd_5436698] using wordTrace_append hprefix tailTrace_5436698
  have hstable : (prefixWord ++ tailWord_5436698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436698).length < 2 ^ (prefixWord ++ tailWord_5436698).sum := by decide
  have hdescent : baseEnd_5436698 < baseStart_5436698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436708 : List Nat := [2, 3, 1, 3, 1, 1, 4, 1, 1, 2, 4]
def baseStart_5436708 : Nat := 118140960795 + 5436708 * 2 ^ 59
def prefixEnd_5436708 : Nat := 4983230072969 + 3 ^ 40 * 5436708 * 2
def baseEnd_5436708 : Nat := 2791644382144220088647041

theorem tailTrace_5436708 : CollatzResearch.WordTrace tailWord_5436708 prefixEnd_5436708 2791644382144220088647041 := by
  unfold tailWord_5436708
  simp only [CollatzResearch.WordTrace]
  refine ⟨99146515593871453324295389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132195354125161937765727185 99146515593871453324295389)
  ·
    refine ⟨37179943347701794996610771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99146515593871453324295389 37179943347701794996610771)
    ·
      refine ⟨55769915021552692494916157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37179943347701794996610771 55769915021552692494916157)
      ·
        refine ⟨20913718133082259685593559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55769915021552692494916157 20913718133082259685593559)
        ·
          refine ⟨31370577199623389528390339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20913718133082259685593559 31370577199623389528390339)
          ·
            refine ⟨47055865799435084292585509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31370577199623389528390339 47055865799435084292585509)
            ·
              refine ⟨8822974837394078304859783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47055865799435084292585509 8822974837394078304859783)
              ·
                refine ⟨13234462256091117457289675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8822974837394078304859783 13234462256091117457289675)
                ·
                  refine ⟨19851693384136676185934513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13234462256091117457289675 19851693384136676185934513)
                  ·
                    refine ⟨14888770038102507139450885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19851693384136676185934513 14888770038102507139450885)
                    ·
                      refine ⟨2791644382144220088647041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14888770038102507139450885 2791644382144220088647041)
                      ·
                        rfl

theorem cell23_5436708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_5436708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436708 prefixEnd_5436708 := by exact prefixLift 5436708
  have htrace : WordTrace (prefixWord ++ tailWord_5436708) baseStart_5436708 baseEnd_5436708 := by
    simpa [prefixWord, tailWord_5436708, baseEnd_5436708] using wordTrace_append hprefix tailTrace_5436708
  have hstable : (prefixWord ++ tailWord_5436708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436708).length < 2 ^ (prefixWord ++ tailWord_5436708).sum := by decide
  have hdescent : baseEnd_5436708 < baseStart_5436708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436712 : List Nat := [2, 1, 5, 1, 2, 2, 1, 2, 3, 2, 2]
def baseStart_5436712 : Nat := 118140960795 + 5436712 * 2 ^ 59
def prefixEnd_5436712 : Nat := 4983230072969 + 3 ^ 40 * 5436712 * 2
def baseEnd_5436712 : Nat := 2791646436066838072997023

theorem tailTrace_5436712 : CollatzResearch.WordTrace tailWord_5436712 prefixEnd_5436712 2791646436066838072997023 := by
  unfold tailWord_5436712
  simp only [CollatzResearch.WordTrace]
  refine ⟨99146588539864207665868195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132195451386485610221157593 99146588539864207665868195)
  ·
    refine ⟨148719882809796311498802293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99146588539864207665868195 148719882809796311498802293)
    ·
      refine ⟨13942489013418404203012715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 148719882809796311498802293 13942489013418404203012715)
      ·
        refine ⟨20913733520127606304519073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13942489013418404203012715 20913733520127606304519073)
        ·
          refine ⟨15685300140095704728389305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20913733520127606304519073 15685300140095704728389305)
          ·
            refine ⟨11763975105071778546291979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15685300140095704728389305 11763975105071778546291979)
            ·
              refine ⟨17645962657607667819437969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11763975105071778546291979 17645962657607667819437969)
              ·
                refine ⟨13234471993205750864578477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17645962657607667819437969 13234471993205750864578477)
                ·
                  refine ⟨4962926997452156574216929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13234471993205750864578477 4962926997452156574216929)
                  ·
                    refine ⟨3722195248089117430662697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4962926997452156574216929 3722195248089117430662697)
                    ·
                      refine ⟨2791646436066838072997023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3722195248089117430662697 2791646436066838072997023)
                      ·
                        rfl

theorem cell23_5436712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_5436712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436712 prefixEnd_5436712 := by exact prefixLift 5436712
  have htrace : WordTrace (prefixWord ++ tailWord_5436712) baseStart_5436712 baseEnd_5436712 := by
    simpa [prefixWord, tailWord_5436712, baseEnd_5436712] using wordTrace_append hprefix tailTrace_5436712
  have hstable : (prefixWord ++ tailWord_5436712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436712).length < 2 ^ (prefixWord ++ tailWord_5436712).sum := by decide
  have hdescent : baseEnd_5436712 < baseStart_5436712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436726 : List Nat := [5, 1, 2, 3, 2, 1, 2, 1, 1, 5]
def baseStart_5436726 : Nat := 118140960795 + 5436726 * 2 ^ 59
def prefixEnd_5436726 : Nat := 4983230072969 + 3 ^ 40 * 5436726 * 2
def baseEnd_5436726 : Nat := 930551208265333672740653

theorem tailTrace_5436726 : CollatzResearch.WordTrace tailWord_5436726 prefixEnd_5436726 930551208265333672740653 := by
  unfold tailWord_5436726
  simp only [CollatzResearch.WordTrace]
  refine ⟨12393355481354855982671627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132195791801118463815164021 12393355481354855982671627)
  ·
    refine ⟨18590033222032283974007441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12393355481354855982671627 18590033222032283974007441)
    ·
      refine ⟨13942524916524212980505581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18590033222032283974007441 13942524916524212980505581)
      ·
        refine ⟨5228446843696579867689593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13942524916524212980505581 5228446843696579867689593)
        ·
          refine ⟨3921335132772434900767195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5228446843696579867689593 3921335132772434900767195)
          ·
            refine ⟨5882002699158652351150793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3921335132772434900767195 5882002699158652351150793)
            ·
              refine ⟨4411502024368989263363095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5882002699158652351150793 4411502024368989263363095)
              ·
                refine ⟨6617253036553483895044643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4411502024368989263363095 6617253036553483895044643)
                ·
                  refine ⟨9925879554830225842566965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6617253036553483895044643 9925879554830225842566965)
                  ·
                    refine ⟨930551208265333672740653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9925879554830225842566965 930551208265333672740653)
                    ·
                      rfl

theorem cell23_5436726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_5436726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436726 prefixEnd_5436726 := by exact prefixLift 5436726
  have htrace : WordTrace (prefixWord ++ tailWord_5436726) baseStart_5436726 baseEnd_5436726 := by
    simpa [prefixWord, tailWord_5436726, baseEnd_5436726] using wordTrace_append hprefix tailTrace_5436726
  have hstable : (prefixWord ++ tailWord_5436726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436726).length < 2 ^ (prefixWord ++ tailWord_5436726).sum := by decide
  have hdescent : baseEnd_5436726 < baseStart_5436726 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436728 : List Nat := [2, 1, 2, 1, 3, 1, 1, 4, 4, 1, 3]
def baseStart_5436728 : Nat := 118140960795 + 5436728 * 2 ^ 59
def prefixEnd_5436728 : Nat := 4983230072969 + 3 ^ 40 * 5436728 * 2
def baseEnd_5436728 : Nat := 2791654651757310010396949

theorem tailTrace_5436728 : CollatzResearch.WordTrace tailWord_5436728 prefixEnd_5436728 2791654651757310010396949 := by
  unfold tailWord_5436728
  simp only [CollatzResearch.WordTrace]
  refine ⟨99146880323835225032159419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132195840431780300042879225 99146880323835225032159419)
  ·
    refine ⟨148720320485752837548239129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99146880323835225032159419 148720320485752837548239129)
    ·
      refine ⟨111540240364314628161179347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148720320485752837548239129 111540240364314628161179347)
      ·
        refine ⟨167310360546471942241769021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111540240364314628161179347 167310360546471942241769021)
        ·
          refine ⟨62741385204926978340663383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167310360546471942241769021 62741385204926978340663383)
          ·
            refine ⟨94112077807390467510995075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62741385204926978340663383 94112077807390467510995075)
            ·
              refine ⟨141168116711085701266492613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94112077807390467510995075 141168116711085701266492613)
              ·
                refine ⟨26469021883328568987467365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 141168116711085701266492613 26469021883328568987467365)
                ·
                  refine ⟨4962941603124106685150131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26469021883328568987467365 4962941603124106685150131)
                  ·
                    refine ⟨7444412404686160027725197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4962941603124106685150131 7444412404686160027725197)
                    ·
                      refine ⟨2791654651757310010396949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7444412404686160027725197 2791654651757310010396949)
                      ·
                        rfl

theorem cell23_5436728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 4, 1, 3].length) (baseStart_5436728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436728 prefixEnd_5436728 := by exact prefixLift 5436728
  have htrace : WordTrace (prefixWord ++ tailWord_5436728) baseStart_5436728 baseEnd_5436728 := by
    simpa [prefixWord, tailWord_5436728, baseEnd_5436728] using wordTrace_append hprefix tailTrace_5436728
  have hstable : (prefixWord ++ tailWord_5436728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436728).length < 2 ^ (prefixWord ++ tailWord_5436728).sum := by decide
  have hdescent : baseEnd_5436728 < baseStart_5436728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436729 : List Nat := [1, 2, 1, 6, 3, 1, 2, 1, 1, 1, 4]
def baseStart_5436729 : Nat := 118140960795 + 5436729 * 2 ^ 59
def prefixEnd_5436729 : Nat := 4983230072969 + 3 ^ 40 * 5436729 * 2
def baseEnd_5436729 : Nat := 2791655165237964506484445

theorem tailTrace_5436729 : CollatzResearch.WordTrace tailWord_5436729 prefixEnd_5436729 2791655165237964506484445 := by
  unfold tailWord_5436729
  simp only [CollatzResearch.WordTrace]
  refine ⟨198293797120666827235105241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132195864747111218156736827 198293797120666827235105241)
  ·
    refine ⟨148720347840500120426328931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198293797120666827235105241 148720347840500120426328931)
    ·
      refine ⟨223080521760750180639493397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148720347840500120426328931 223080521760750180639493397)
      ·
        refine ⟨10456899457535164717476253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 223080521760750180639493397 10456899457535164717476253)
        ·
          refine ⟨3921337296575686769053595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10456899457535164717476253 3921337296575686769053595)
          ·
            refine ⟨5882005944863530153580393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3921337296575686769053595 5882005944863530153580393)
            ·
              refine ⟨4411504458647647615185295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5882005944863530153580393 4411504458647647615185295)
              ·
                refine ⟨6617256687971471422777943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4411504458647647615185295 6617256687971471422777943)
                ·
                  refine ⟨9925885031957207134166915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6617256687971471422777943 9925885031957207134166915)
                  ·
                    refine ⟨14888827547935810701250373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9925885031957207134166915 14888827547935810701250373)
                    ·
                      refine ⟨2791655165237964506484445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14888827547935810701250373 2791655165237964506484445)
                      ·
                        rfl

theorem cell23_5436729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_5436729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436729 prefixEnd_5436729 := by exact prefixLift 5436729
  have htrace : WordTrace (prefixWord ++ tailWord_5436729) baseStart_5436729 baseEnd_5436729 := by
    simpa [prefixWord, tailWord_5436729, baseEnd_5436729] using wordTrace_append hprefix tailTrace_5436729
  have hstable : (prefixWord ++ tailWord_5436729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436729).length < 2 ^ (prefixWord ++ tailWord_5436729).sum := by decide
  have hdescent : baseEnd_5436729 < baseStart_5436729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436732 : List Nat := [2, 2, 2, 2, 1, 5, 2, 1, 1, 2, 3]
def baseStart_5436732 : Nat := 118140960795 + 5436732 * 2 ^ 59
def prefixEnd_5436732 : Nat := 4983230072969 + 3 ^ 40 * 5436732 * 2
def baseEnd_5436732 : Nat := 2791656705679927994746931

theorem tailTrace_5436732 : CollatzResearch.WordTrace tailWord_5436732 prefixEnd_5436732 2791656705679927994746931 := by
  unfold tailWord_5436732
  simp only [CollatzResearch.WordTrace]
  refine ⟨99146953269827979373732225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132195937693103972498309633 99146953269827979373732225)
  ·
    refine ⟨74360214952370984530299169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99146953269827979373732225 74360214952370984530299169)
    ·
      refine ⟨55770161214278238397724377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74360214952370984530299169 55770161214278238397724377)
      ·
        refine ⟨41827620910708678798293283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55770161214278238397724377 41827620910708678798293283)
        ·
          refine ⟨62741431366063018197439925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41827620910708678798293283 62741431366063018197439925)
          ·
            refine ⟨5882009190568407956009993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62741431366063018197439925 5882009190568407956009993)
            ·
              refine ⟨4411506892926305967007495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5882009190568407956009993 4411506892926305967007495)
              ·
                refine ⟨6617260339389458950511243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4411506892926305967007495 6617260339389458950511243)
                ·
                  refine ⟨9925890509084188425766865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6617260339389458950511243 9925890509084188425766865)
                  ·
                    refine ⟨7444417881813141319325149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9925890509084188425766865 7444417881813141319325149)
                    ·
                      refine ⟨2791656705679927994746931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7444417881813141319325149 2791656705679927994746931)
                      ·
                        rfl

theorem cell23_5436732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_5436732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436732 prefixEnd_5436732 := by exact prefixLift 5436732
  have htrace : WordTrace (prefixWord ++ tailWord_5436732) baseStart_5436732 baseEnd_5436732 := by
    simpa [prefixWord, tailWord_5436732, baseEnd_5436732] using wordTrace_append hprefix tailTrace_5436732
  have hstable : (prefixWord ++ tailWord_5436732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436732).length < 2 ^ (prefixWord ++ tailWord_5436732).sum := by decide
  have hdescent : baseEnd_5436732 < baseStart_5436732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436745 : List Nat := [1, 2, 1, 1, 2, 3, 5, 2, 2, 1, 3]
def baseStart_5436745 : Nat := 118140960795 + 5436745 * 2 ^ 59
def prefixEnd_5436745 : Nat := 4983230072969 + 3 ^ 40 * 5436745 * 2
def baseEnd_5436745 : Nat := 2791663380928436443884371

theorem tailTrace_5436745 : CollatzResearch.WordTrace tailWord_5436745 prefixEnd_5436745 2791663380928436443884371 := by
  unfold tailWord_5436745
  simp only [CollatzResearch.WordTrace]
  refine ⟨198294380688608861967687689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132196253792405907978458459 198294380688608861967687689)
  ·
    refine ⟨148720785516456646475765767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198294380688608861967687689 148720785516456646475765767)
    ·
      refine ⟨223081178274684969713648651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148720785516456646475765767 223081178274684969713648651)
      ·
        refine ⟨334621767412027454570472977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223081178274684969713648651 334621767412027454570472977)
        ·
          refine ⟨250966325559020590927854733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 334621767412027454570472977 250966325559020590927854733)
          ·
            refine ⟨94112372084632721597945525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 250966325559020590927854733 94112372084632721597945525)
            ·
              refine ⟨8823034882934317649807393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94112372084632721597945525 8823034882934317649807393)
              ·
                refine ⟨6617276162200738237355545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8823034882934317649807393 6617276162200738237355545)
                ·
                  refine ⟨4962957121650553678016659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6617276162200738237355545 4962957121650553678016659)
                  ·
                    refine ⟨7444435682475830517024989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4962957121650553678016659 7444435682475830517024989)
                    ·
                      refine ⟨2791663380928436443884371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7444435682475830517024989 2791663380928436443884371)
                      ·
                        rfl

theorem cell23_5436745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 2, 1, 3].length) (baseStart_5436745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436745 prefixEnd_5436745 := by exact prefixLift 5436745
  have htrace : WordTrace (prefixWord ++ tailWord_5436745) baseStart_5436745 baseEnd_5436745 := by
    simpa [prefixWord, tailWord_5436745, baseEnd_5436745] using wordTrace_append hprefix tailTrace_5436745
  have hstable : (prefixWord ++ tailWord_5436745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436745).length < 2 ^ (prefixWord ++ tailWord_5436745).sum := by decide
  have hdescent : baseEnd_5436745 < baseStart_5436745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436761 : List Nat := [1, 2, 1, 2, 2, 2, 4, 1, 2, 6]
def baseStart_5436761 : Nat := 118140960795 + 5436761 * 2 ^ 59
def prefixEnd_5436761 : Nat := 4983230072969 + 3 ^ 40 * 5436761 * 2
def baseEnd_5436761 : Nat := 930557198872969460428099

theorem tailTrace_5436761 : CollatzResearch.WordTrace tailWord_5436761 prefixEnd_5436761 930557198872969460428099 := by
  unfold tailWord_5436761
  simp only [CollatzResearch.WordTrace]
  refine ⟨198294964256550896700270137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132196642837700597800180091 198294964256550896700270137)
  ·
    refine ⟨148721223192413172525202603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198294964256550896700270137 148721223192413172525202603)
    ·
      refine ⟨223081834788619758787803905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148721223192413172525202603 223081834788619758787803905)
      ·
        refine ⟨167311376091464819090852929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223081834788619758787803905 167311376091464819090852929)
        ·
          refine ⟨125483532068598614318139697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167311376091464819090852929 125483532068598614318139697)
          ·
            refine ⟨94112649051448960738604773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125483532068598614318139697 94112649051448960738604773)
            ·
              refine ⟨17646121697146680138488395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94112649051448960738604773 17646121697146680138488395)
              ·
                refine ⟨26469182545720020207732593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17646121697146680138488395 26469182545720020207732593)
                ·
                  refine ⟨19851886909290015155799445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26469182545720020207732593 19851886909290015155799445)
                  ·
                    refine ⟨930557198872969460428099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19851886909290015155799445 930557198872969460428099)
                    ·
                      rfl

theorem cell23_5436761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 6].length) (baseStart_5436761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436761 prefixEnd_5436761 := by exact prefixLift 5436761
  have htrace : WordTrace (prefixWord ++ tailWord_5436761) baseStart_5436761 baseEnd_5436761 := by
    simpa [prefixWord, tailWord_5436761, baseEnd_5436761] using wordTrace_append hprefix tailTrace_5436761
  have hstable : (prefixWord ++ tailWord_5436761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436761).length < 2 ^ (prefixWord ++ tailWord_5436761).sum := by decide
  have hdescent : baseEnd_5436761 < baseStart_5436761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436772 : List Nat := [2, 3, 1, 1, 3, 3, 2, 2, 1, 3, 2]
def baseStart_5436772 : Nat := 118140960795 + 5436772 * 2 ^ 59
def prefixEnd_5436772 : Nat := 4983230072969 + 3 ^ 40 * 5436772 * 2
def baseEnd_5436772 : Nat := 2791677244906107838246747

theorem tailTrace_5436772 : CollatzResearch.WordTrace tailWord_5436772 prefixEnd_5436772 2791677244906107838246747 := by
  unfold tailWord_5436772
  simp only [CollatzResearch.WordTrace]
  refine ⟨99147682729755522789460285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132196910306340697052613713 99147682729755522789460285)
  ·
    refine ⟨37180381023658321046047607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99147682729755522789460285 37180381023658321046047607)
    ·
      refine ⟨55770571535487481569071411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37180381023658321046047607 55770571535487481569071411)
      ·
        refine ⟨83655857303231222353607117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55770571535487481569071411 83655857303231222353607117)
        ·
          refine ⟨31370946488711708382602669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83655857303231222353607117 31370946488711708382602669)
          ·
            refine ⟨11764104933266890643476001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31370946488711708382602669 11764104933266890643476001)
            ·
              refine ⟨8823078699950167982607001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11764104933266890643476001 8823078699950167982607001)
              ·
                refine ⟨6617309024962625986955251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8823078699950167982607001 6617309024962625986955251)
                ·
                  refine ⟨9925963537443938980432877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6617309024962625986955251 9925963537443938980432877)
                  ·
                    refine ⟨3722236326541477117662329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9925963537443938980432877 3722236326541477117662329)
                    ·
                      refine ⟨2791677244906107838246747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3722236326541477117662329 2791677244906107838246747)
                      ·
                        rfl

theorem cell23_5436772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 1, 3, 2].length) (baseStart_5436772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436772 prefixEnd_5436772 := by exact prefixLift 5436772
  have htrace : WordTrace (prefixWord ++ tailWord_5436772) baseStart_5436772 baseEnd_5436772 := by
    simpa [prefixWord, tailWord_5436772, baseEnd_5436772] using wordTrace_append hprefix tailTrace_5436772
  have hstable : (prefixWord ++ tailWord_5436772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436772).length < 2 ^ (prefixWord ++ tailWord_5436772).sum := by decide
  have hdescent : baseEnd_5436772 < baseStart_5436772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436785 : List Nat := [1, 2, 2, 2, 1, 2, 3, 2, 4, 2, 2]
def baseStart_5436785 : Nat := 118140960795 + 5436785 * 2 ^ 59
def prefixEnd_5436785 : Nat := 4983230072969 + 3 ^ 40 * 5436785 * 2
def baseEnd_5436785 : Nat := 2791683920154616287384187

theorem tailTrace_5436785 : CollatzResearch.WordTrace tailWord_5436785 prefixEnd_5436785 2791683920154616287384187 := by
  unfold tailWord_5436785
  simp only [CollatzResearch.WordTrace]
  refine ⟨198295839608463948799143809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132197226405642632532762539 198295839608463948799143809)
  ·
    refine ⟨148721879706347961599357857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198295839608463948799143809 148721879706347961599357857)
    ·
      refine ⟨111541409779760971199518393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148721879706347961599357857 111541409779760971199518393)
      ·
        refine ⟨83656057334820728399638795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111541409779760971199518393 83656057334820728399638795)
        ·
          refine ⟨125484086002231092599458193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83656057334820728399638795 125484086002231092599458193)
          ·
            refine ⟨94113064501673319449593645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125484086002231092599458193 94113064501673319449593645)
            ·
              refine ⟨35292399188127494793597617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94113064501673319449593645 35292399188127494793597617)
              ·
                refine ⟨26469299391095621095198213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35292399188127494793597617 26469299391095621095198213)
                ·
                  refine ⟨4962993635830428955349665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26469299391095621095198213 4962993635830428955349665)
                  ·
                    refine ⟨3722245226872821716512249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4962993635830428955349665 3722245226872821716512249)
                    ·
                      refine ⟨2791683920154616287384187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3722245226872821716512249 2791683920154616287384187)
                      ·
                        rfl

theorem cell23_5436785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 4, 2, 2].length) (baseStart_5436785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436785 prefixEnd_5436785 := by exact prefixLift 5436785
  have htrace : WordTrace (prefixWord ++ tailWord_5436785) baseStart_5436785 baseEnd_5436785 := by
    simpa [prefixWord, tailWord_5436785, baseEnd_5436785] using wordTrace_append hprefix tailTrace_5436785
  have hstable : (prefixWord ++ tailWord_5436785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436785).length < 2 ^ (prefixWord ++ tailWord_5436785).sum := by decide
  have hdescent : baseEnd_5436785 < baseStart_5436785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436808 : List Nat := [2, 1, 3, 3, 1, 2, 3, 1, 7]
def baseStart_5436808 : Nat := 118140960795 + 5436808 * 2 ^ 59
def prefixEnd_5436808 : Nat := 4983230072969 + 3 ^ 40 * 5436808 * 2
def baseEnd_5436808 : Nat := 310188414467741077488509

theorem tailTrace_5436808 : CollatzResearch.WordTrace tailWord_5436808 prefixEnd_5436808 310188414467741077488509 := by
  unfold tailWord_5436808
  simp only [CollatzResearch.WordTrace]
  refine ⟨99148339243690311863615539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132197785658253749151487385 99148339243690311863615539)
  ·
    refine ⟨148722508865535467795423309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99148339243690311863615539 148722508865535467795423309)
    ·
      refine ⟨55770940824575800423283741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148722508865535467795423309 55770940824575800423283741)
      ·
        refine ⟨20914102809215925158731403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55770940824575800423283741 20914102809215925158731403)
        ·
          refine ⟨31371154213823887738097105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20914102809215925158731403 31371154213823887738097105)
          ·
            refine ⟨23528365660367915803572829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31371154213823887738097105 23528365660367915803572829)
            ·
              refine ⟨8823137122637968426339811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23528365660367915803572829 8823137122637968426339811)
              ·
                refine ⟨13234705683956952639509717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8823137122637968426339811 13234705683956952639509717)
                ·
                  refine ⟨310188414467741077488509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13234705683956952639509717 310188414467741077488509)
                  ·
                    rfl

theorem cell23_5436808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 7].length) (baseStart_5436808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436808 prefixEnd_5436808 := by exact prefixLift 5436808
  have htrace : WordTrace (prefixWord ++ tailWord_5436808) baseStart_5436808 baseEnd_5436808 := by
    simpa [prefixWord, tailWord_5436808, baseEnd_5436808] using wordTrace_append hprefix tailTrace_5436808
  have hstable : (prefixWord ++ tailWord_5436808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436808).length < 2 ^ (prefixWord ++ tailWord_5436808).sum := by decide
  have hdescent : baseEnd_5436808 < baseStart_5436808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436821 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 3, 7]
def baseStart_5436821 : Nat := 118140960795 + 5436821 * 2 ^ 59
def prefixEnd_5436821 : Nat := 4983230072969 + 3 ^ 40 * 5436821 * 2
def baseEnd_5436821 : Nat := 930567468486059382178007

theorem tailTrace_5436821 : CollatzResearch.WordTrace tailWord_5436821 prefixEnd_5436821 930567468486059382178007 := by
  unfold tailWord_5436821
  simp only [CollatzResearch.WordTrace]
  refine ⟨198297152636333526947454317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132198101757555684631636211 198297152636333526947454317)
  ·
    refine ⟨74361432238625072605295369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198297152636333526947454317 74361432238625072605295369)
    ·
      refine ⟨55771074178968804453971527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74361432238625072605295369 55771074178968804453971527)
      ·
        refine ⟨83656611268453206680957291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55771074178968804453971527 83656611268453206680957291)
        ·
          refine ⟨125484916902679810021435937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83656611268453206680957291 125484916902679810021435937)
          ·
            refine ⟨94113687677009857516076953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125484916902679810021435937 94113687677009857516076953)
            ·
              refine ⟨70585265757757393137057715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94113687677009857516076953 70585265757757393137057715)
              ·
                refine ⟨105877898636636089705586573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70585265757757393137057715 105877898636636089705586573)
                ·
                  refine ⟨39704211988738533639594965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105877898636636089705586573 39704211988738533639594965)
                  ·
                    refine ⟨930567468486059382178007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39704211988738533639594965 930567468486059382178007)
                    ·
                      rfl

theorem cell23_5436821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_5436821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436821 prefixEnd_5436821 := by exact prefixLift 5436821
  have htrace : WordTrace (prefixWord ++ tailWord_5436821) baseStart_5436821 baseEnd_5436821 := by
    simpa [prefixWord, tailWord_5436821, baseEnd_5436821] using wordTrace_append hprefix tailTrace_5436821
  have hstable : (prefixWord ++ tailWord_5436821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436821).length < 2 ^ (prefixWord ++ tailWord_5436821).sum := by decide
  have hdescent : baseEnd_5436821 < baseStart_5436821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436866 : List Nat := [3, 5, 2, 1, 1, 1, 1, 1, 2, 2, 4]
def baseStart_5436866 : Nat := 118140960795 + 5436866 * 2 ^ 59
def prefixEnd_5436866 : Nat := 4983230072969 + 3 ^ 40 * 5436866 * 2
def baseEnd_5436866 : Nat := 2791725512087630470471315

theorem tailTrace_5436866 : CollatzResearch.WordTrace tailWord_5436866 prefixEnd_5436866 2791725512087630470471315 := by
  unfold tailWord_5436866
  simp only [CollatzResearch.WordTrace]
  refine ⟨49574698480292624908210613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132199195947446999755228301 49574698480292624908210613)
  ·
    refine ⟨4647627982527433585144745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49574698480292624908210613 4647627982527433585144745)
    ·
      refine ⟨3485720986895575188858559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4647627982527433585144745 3485720986895575188858559)
      ·
        refine ⟨5228581480343362783287839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3485720986895575188858559 5228581480343362783287839)
        ·
          refine ⟨7842872220515044174931759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5228581480343362783287839 7842872220515044174931759)
          ·
            refine ⟨11764308330772566262397639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7842872220515044174931759 11764308330772566262397639)
            ·
              refine ⟨17646462496158849393596459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11764308330772566262397639 17646462496158849393596459)
              ·
                refine ⟨26469693744238274090394689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17646462496158849393596459 26469693744238274090394689)
                ·
                  refine ⟨19852270308178705567796017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26469693744238274090394689 19852270308178705567796017)
                  ·
                    refine ⟨14889202731134029175847013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19852270308178705567796017 14889202731134029175847013)
                    ·
                      refine ⟨2791725512087630470471315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14889202731134029175847013 2791725512087630470471315)
                      ·
                        rfl

theorem cell23_5436866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_5436866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436866 prefixEnd_5436866 := by exact prefixLift 5436866
  have htrace : WordTrace (prefixWord ++ tailWord_5436866) baseStart_5436866 baseEnd_5436866 := by
    simpa [prefixWord, tailWord_5436866, baseEnd_5436866] using wordTrace_append hprefix tailTrace_5436866
  have hstable : (prefixWord ++ tailWord_5436866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436866).length < 2 ^ (prefixWord ++ tailWord_5436866).sum := by decide
  have hdescent : baseEnd_5436866 < baseStart_5436866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436881 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 12]
def baseStart_5436881 : Nat := 118140960795 + 5436881 * 2 ^ 59
def prefixEnd_5436881 : Nat := 4983230072969 + 3 ^ 40 * 5436881 * 2
def baseEnd_5436881 : Nat := 310192579366383101309305

theorem tailTrace_5436881 : CollatzResearch.WordTrace tailWord_5436881 prefixEnd_5436881 310192579366383101309305 := by
  unfold tailWord_5436881
  simp only [CollatzResearch.WordTrace]
  refine ⟨198299341016116157194638497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132199560677410771463092331 198299341016116157194638497)
  ·
    refine ⟨148724505762087117895978873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198299341016116157194638497 148724505762087117895978873)
    ·
      refine ⟨111543379321565338421984155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148724505762087117895978873 111543379321565338421984155)
      ·
        refine ⟨167315068982348007632976233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111543379321565338421984155 167315068982348007632976233)
        ·
          refine ⟨125486301736761005724732175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167315068982348007632976233 125486301736761005724732175)
          ·
            refine ⟨188229452605141508587098263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125486301736761005724732175 188229452605141508587098263)
            ·
              refine ⟨282344178907712262880647395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188229452605141508587098263 282344178907712262880647395)
              ·
                refine ⟨423516268361568394320971093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 282344178907712262880647395 423516268361568394320971093)
                ·
                  refine ⟨310192579366383101309305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 423516268361568394320971093 310192579366383101309305)
                  ·
                    rfl

theorem cell23_5436881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 12].length) (baseStart_5436881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436881 prefixEnd_5436881 := by exact prefixLift 5436881
  have htrace : WordTrace (prefixWord ++ tailWord_5436881) baseStart_5436881 baseEnd_5436881 := by
    simpa [prefixWord, tailWord_5436881, baseEnd_5436881] using wordTrace_append hprefix tailTrace_5436881
  have hstable : (prefixWord ++ tailWord_5436881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436881).length < 2 ^ (prefixWord ++ tailWord_5436881).sum := by decide
  have hdescent : baseEnd_5436881 < baseStart_5436881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436885 : List Nat := [1, 3, 2, 3, 1, 1, 3, 2, 3, 4]
def baseStart_5436885 : Nat := 118140960795 + 5436885 * 2 ^ 59
def prefixEnd_5436885 : Nat := 4983230072969 + 3 ^ 40 * 5436885 * 2
def baseEnd_5436885 : Nat := 930578422740021965377909

theorem tailTrace_5436885 : CollatzResearch.WordTrace tailWord_5436885 prefixEnd_5436885 930578422740021965377909 := by
  unfold tailWord_5436885
  simp only [CollatzResearch.WordTrace]
  refine ⟨198299486908101665877784109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132199657938734443918522739 198299486908101665877784109)
  ·
    refine ⟨74362307590538124704169041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198299486908101665877784109 74362307590538124704169041)
    ·
      refine ⟨55771730692903593528126781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74362307590538124704169041 55771730692903593528126781)
      ·
        refine ⟨20914399009838847573047543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55771730692903593528126781 20914399009838847573047543)
        ·
          refine ⟨31371598514758271359571315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20914399009838847573047543 31371598514758271359571315)
          ·
            refine ⟨47057397772137407039356973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31371598514758271359571315 47057397772137407039356973)
            ·
              refine ⟨17646524164551527639758865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47057397772137407039356973 17646524164551527639758865)
              ·
                refine ⟨13234893123413645729819149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17646524164551527639758865 13234893123413645729819149)
                ·
                  refine ⟨4963084921280117148682181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13234893123413645729819149 4963084921280117148682181)
                  ·
                    refine ⟨930578422740021965377909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4963084921280117148682181 930578422740021965377909)
                    ·
                      rfl

theorem cell23_5436885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_5436885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436885 prefixEnd_5436885 := by exact prefixLift 5436885
  have htrace : WordTrace (prefixWord ++ tailWord_5436885) baseStart_5436885 baseEnd_5436885 := by
    simpa [prefixWord, tailWord_5436885, baseEnd_5436885] using wordTrace_append hprefix tailTrace_5436885
  have hstable : (prefixWord ++ tailWord_5436885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436885).length < 2 ^ (prefixWord ++ tailWord_5436885).sum := by decide
  have hdescent : baseEnd_5436885 < baseStart_5436885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436945 : List Nat := [1, 2, 2, 1, 1, 2, 6, 2, 1, 5]
def baseStart_5436945 : Nat := 118140960795 + 5436945 * 2 ^ 59
def prefixEnd_5436945 : Nat := 4983230072969 + 3 ^ 40 * 5436945 * 2
def baseEnd_5436945 : Nat := 930588692353111887127817

theorem tailTrace_5436945 : CollatzResearch.WordTrace tailWord_5436945 prefixEnd_5436945 930588692353111887127817 := by
  unfold tailWord_5436945
  simp only [CollatzResearch.WordTrace]
  refine ⟨198301675287884296124968289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132201116858589530749978859 198301675287884296124968289)
  ·
    refine ⟨148726256465913222093726217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198301675287884296124968289 148726256465913222093726217)
    ·
      refine ⟨111544692349434916570294663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148726256465913222093726217 111544692349434916570294663)
      ·
        refine ⟨167317038524152374855441995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111544692349434916570294663 167317038524152374855441995)
        ·
          refine ⟨250975557786228562283162993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167317038524152374855441995 250975557786228562283162993)
          ·
            refine ⟨188231668339671421712372245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250975557786228562283162993 188231668339671421712372245)
            ·
              refine ⟨8823359453422097892767449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 188231668339671421712372245 8823359453422097892767449)
              ·
                refine ⟨6617519590066573419575587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8823359453422097892767449 6617519590066573419575587)
                ·
                  refine ⟨9926279385099860129363381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6617519590066573419575587 9926279385099860129363381)
                  ·
                    refine ⟨930588692353111887127817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9926279385099860129363381 930588692353111887127817)
                    ·
                      rfl

theorem cell23_5436945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 5].length) (baseStart_5436945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436945 prefixEnd_5436945 := by exact prefixLift 5436945
  have htrace : WordTrace (prefixWord ++ tailWord_5436945) baseStart_5436945 baseEnd_5436945 := by
    simpa [prefixWord, tailWord_5436945, baseEnd_5436945] using wordTrace_append hprefix tailTrace_5436945
  have hstable : (prefixWord ++ tailWord_5436945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436945).length < 2 ^ (prefixWord ++ tailWord_5436945).sum := by decide
  have hdescent : baseEnd_5436945 < baseStart_5436945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436959 : List Nat := [1, 1, 2, 4, 1, 1, 5, 3, 1, 1, 3]
def baseStart_5436959 : Nat := 118140960795 + 5436959 * 2 ^ 59
def prefixEnd_5436959 : Nat := 4983230072969 + 3 ^ 40 * 5436959 * 2
def baseEnd_5436959 : Nat := 2791773265788498606608387

theorem tailTrace_5436959 : CollatzResearch.WordTrace tailWord_5436959 prefixEnd_5436959 2791773265788498606608387 := by
  unfold tailWord_5436959
  simp only [CollatzResearch.WordTrace]
  refine ⟨198302185909833576515977931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132201457273222384343985287 198302185909833576515977931)
  ·
    refine ⟨297453278864750364773966897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198302185909833576515977931 297453278864750364773966897)
    ·
      refine ⟨223089959148562773580475173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297453278864750364773966897 223089959148562773580475173)
      ·
        refine ⟨41829367340355520046339095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 223089959148562773580475173 41829367340355520046339095)
        ·
          refine ⟨62744051010533280069508643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41829367340355520046339095 62744051010533280069508643)
          ·
            refine ⟨94116076515799920104262965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62744051010533280069508643 94116076515799920104262965)
            ·
              refine ⟨8823382173356242509774653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94116076515799920104262965 8823382173356242509774653)
              ·
                refine ⟨3308768315008590941165495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8823382173356242509774653 3308768315008590941165495)
                ·
                  refine ⟨4963152472512886411748243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3308768315008590941165495 4963152472512886411748243)
                  ·
                    refine ⟨7444728708769329617622365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4963152472512886411748243 7444728708769329617622365)
                    ·
                      refine ⟨2791773265788498606608387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7444728708769329617622365 2791773265788498606608387)
                      ·
                        rfl

theorem cell23_5436959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_5436959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436959 prefixEnd_5436959 := by exact prefixLift 5436959
  have htrace : WordTrace (prefixWord ++ tailWord_5436959) baseStart_5436959 baseEnd_5436959 := by
    simpa [prefixWord, tailWord_5436959, baseEnd_5436959] using wordTrace_append hprefix tailTrace_5436959
  have hstable : (prefixWord ++ tailWord_5436959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436959).length < 2 ^ (prefixWord ++ tailWord_5436959).sum := by decide
  have hdescent : baseEnd_5436959 < baseStart_5436959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436985 : List Nat := [1, 2, 1, 5, 1, 2, 2, 2, 1, 1, 5]
def baseStart_5436985 : Nat := 118140960795 + 5436985 * 2 ^ 59
def prefixEnd_5436985 : Nat := 4983230072969 + 3 ^ 40 * 5436985 * 2
def baseEnd_5436985 : Nat := 2791786616285515504883267

theorem tailTrace_5436985 : CollatzResearch.WordTrace tailWord_5436985 prefixEnd_5436985 2791786616285515504883267 := by
  unfold tailWord_5436985
  simp only [CollatzResearch.WordTrace]
  refine ⟨198303134207739382956424409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132202089471826255304282939 198303134207739382956424409)
  ·
    refine ⟨148727350655804537217318307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198303134207739382956424409 148727350655804537217318307)
    ·
      refine ⟨223091025983706805825977461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148727350655804537217318307 223091025983706805825977461)
      ·
        refine ⟨20914783685972513046185387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 223091025983706805825977461 20914783685972513046185387)
        ·
          refine ⟨31372175528958769569278081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20914783685972513046185387 31372175528958769569278081)
          ·
            refine ⟨23529131646719077176958561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31372175528958769569278081 23529131646719077176958561)
            ·
              refine ⟨17646848735039307882718921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23529131646719077176958561 17646848735039307882718921)
              ·
                refine ⟨13235136551279480912039191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17646848735039307882718921 13235136551279480912039191)
                ·
                  refine ⟨19852704826919221368058787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13235136551279480912039191 19852704826919221368058787)
                  ·
                    refine ⟨29779057240378832052088181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19852704826919221368058787 29779057240378832052088181)
                    ·
                      refine ⟨2791786616285515504883267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29779057240378832052088181 2791786616285515504883267)
                      ·
                        rfl

theorem cell23_5436985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_5436985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436985 prefixEnd_5436985 := by exact prefixLift 5436985
  have htrace : WordTrace (prefixWord ++ tailWord_5436985) baseStart_5436985 baseEnd_5436985 := by
    simpa [prefixWord, tailWord_5436985, baseEnd_5436985] using wordTrace_append hprefix tailTrace_5436985
  have hstable : (prefixWord ++ tailWord_5436985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436985).length < 2 ^ (prefixWord ++ tailWord_5436985).sum := by decide
  have hdescent : baseEnd_5436985 < baseStart_5436985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5436999 : List Nat := [1, 1, 4, 1, 5, 2, 1, 2, 1, 1, 4]
def baseStart_5436999 : Nat := 118140960795 + 5436999 * 2 ^ 59
def prefixEnd_5436999 : Nat := 4983230072969 + 3 ^ 40 * 5436999 * 2
def baseEnd_5436999 : Nat := 2791793805014678450108203

theorem tailTrace_5436999 : CollatzResearch.WordTrace tailWord_5436999 prefixEnd_5436999 2791793805014678450108203 := by
  unfold tailWord_5436999
  simp only [CollatzResearch.WordTrace]
  refine ⟨198303644829688663347434051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132202429886459108898289367 198303644829688663347434051)
  ·
    refine ⟨297455467244532995021151077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198303644829688663347434051 297455467244532995021151077)
    ·
      refine ⟨55772900108349936566465827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 297455467244532995021151077 55772900108349936566465827)
      ·
        refine ⟨83659350162524904849698741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55772900108349936566465827 83659350162524904849698741)
        ·
          refine ⟨7843064077736709829659257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83659350162524904849698741 7843064077736709829659257)
          ·
            refine ⟨5882298058302532372244443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7843064077736709829659257 5882298058302532372244443)
            ·
              refine ⟨8823447087453798558366665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5882298058302532372244443 8823447087453798558366665)
              ·
                refine ⟨6617585315590348918774999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8823447087453798558366665 6617585315590348918774999)
                ·
                  refine ⟨9926377973385523378162499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6617585315590348918774999 9926377973385523378162499)
                  ·
                    refine ⟨14889566960078285067243749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9926377973385523378162499 14889566960078285067243749)
                    ·
                      refine ⟨2791793805014678450108203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14889566960078285067243749 2791793805014678450108203)
                      ·
                        rfl

theorem cell23_5436999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 1, 4].length) (baseStart_5436999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5436999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5436999 prefixEnd_5436999 := by exact prefixLift 5436999
  have htrace : WordTrace (prefixWord ++ tailWord_5436999) baseStart_5436999 baseEnd_5436999 := by
    simpa [prefixWord, tailWord_5436999, baseEnd_5436999] using wordTrace_append hprefix tailTrace_5436999
  have hstable : (prefixWord ++ tailWord_5436999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5436999).length < 2 ^ (prefixWord ++ tailWord_5436999).sum := by decide
  have hdescent : baseEnd_5436999 < baseStart_5436999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5436999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437015 : List Nat := [1, 1, 3, 2, 2, 3, 1, 1, 3, 3, 3]
def baseStart_5437015 : Nat := 118140960795 + 5437015 * 2 ^ 59
def prefixEnd_5437015 : Nat := 4983230072969 + 3 ^ 40 * 5437015 * 2
def baseEnd_5437015 : Nat := 2791802020705150387508129

theorem tailTrace_5437015 : CollatzResearch.WordTrace tailWord_5437015 prefixEnd_5437015 2791802020705150387508129 := by
  unfold tailWord_5437015
  simp only [CollatzResearch.WordTrace]
  refine ⟨198304228397630698080016499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132202818931753798720010999 198304228397630698080016499)
  ·
    refine ⟨297456342596446047120024749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198304228397630698080016499 297456342596446047120024749)
    ·
      refine ⟨111546128473667267670009281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 297456342596446047120024749 111546128473667267670009281)
      ·
        refine ⟨83659596355250450752506961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111546128473667267670009281 83659596355250450752506961)
        ·
          refine ⟨62744697266437838064380221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83659596355250450752506961 62744697266437838064380221)
          ·
            refine ⟨23529261474914189274142583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62744697266437838064380221 23529261474914189274142583)
            ·
              refine ⟨35293892212371283911213875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23529261474914189274142583 35293892212371283911213875)
              ·
                refine ⟨52940838318556925866820813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35293892212371283911213875 52940838318556925866820813)
                ·
                  refine ⟨19852814369458847200057805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52940838318556925866820813 19852814369458847200057805)
                  ·
                    refine ⟨7444805388547067700021677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19852814369458847200057805 7444805388547067700021677)
                    ·
                      refine ⟨2791802020705150387508129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7444805388547067700021677 2791802020705150387508129)
                      ·
                        rfl

theorem cell23_5437015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_5437015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5437015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5437015 prefixEnd_5437015 := by exact prefixLift 5437015
  have htrace : WordTrace (prefixWord ++ tailWord_5437015) baseStart_5437015 baseEnd_5437015 := by
    simpa [prefixWord, tailWord_5437015, baseEnd_5437015] using wordTrace_append hprefix tailTrace_5437015
  have hstable : (prefixWord ++ tailWord_5437015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437015).length < 2 ^ (prefixWord ++ tailWord_5437015).sum := by decide
  have hdescent : baseEnd_5437015 < baseStart_5437015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437018 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 4, 7]
def baseStart_5437018 : Nat := 118140960795 + 5437018 * 2 ^ 59
def prefixEnd_5437018 : Nat := 4983230072969 + 3 ^ 40 * 5437018 * 2
def baseEnd_5437018 : Nat := 930601187049037958590205

theorem tailTrace_5437018 : CollatzResearch.WordTrace tailWord_5437018 prefixEnd_5437018 930601187049037958590205 := by
  unfold tailWord_5437018
  simp only [CollatzResearch.WordTrace]
  refine ⟨49576084454154957398093927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132202891877746553061583805 49576084454154957398093927)
  ·
    refine ⟨74364126681232436097140891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49576084454154957398093927 74364126681232436097140891)
    ·
      refine ⟨111546190021848654145711337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74364126681232436097140891 111546190021848654145711337)
      ·
        refine ⟨83659642516386490609283503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111546190021848654145711337 83659642516386490609283503)
        ·
          refine ⟨125489463774579735913925255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83659642516386490609283503 125489463774579735913925255)
          ·
            refine ⟨188234195661869603870887883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125489463774579735913925255 188234195661869603870887883)
            ·
              refine ⟨282351293492804405806331825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188234195661869603870887883 282351293492804405806331825)
              ·
                refine ⟨211763470119603304354748869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 282351293492804405806331825 211763470119603304354748869)
                ·
                  refine ⟨39705650647425619566515413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 211763470119603304354748869 39705650647425619566515413)
                  ·
                    refine ⟨930601187049037958590205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39705650647425619566515413 930601187049037958590205)
                    ·
                      rfl

theorem cell23_5437018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 4, 7].length) (baseStart_5437018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5437018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5437018 prefixEnd_5437018 := by exact prefixLift 5437018
  have htrace : WordTrace (prefixWord ++ tailWord_5437018) baseStart_5437018 baseEnd_5437018 := by
    simpa [prefixWord, tailWord_5437018, baseEnd_5437018] using wordTrace_append hprefix tailTrace_5437018
  have hstable : (prefixWord ++ tailWord_5437018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437018).length < 2 ^ (prefixWord ++ tailWord_5437018).sum := by decide
  have hdescent : baseEnd_5437018 < baseStart_5437018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437126 : List Nat := [6, 1, 2, 1, 1, 2, 1, 1, 2, 1, 5]
def baseStart_5437126 : Nat := 118140960795 + 5437126 * 2 ^ 59
def prefixEnd_5437126 : Nat := 4983230072969 + 3 ^ 40 * 5437126 * 2
def baseEnd_5437126 : Nat := 2791859017057799453220119

theorem tailTrace_5437126 : CollatzResearch.WordTrace tailWord_5437126 prefixEnd_5437126 2791859017057799453220119 := by
  unfold tailWord_5437126
  simp only [CollatzResearch.WordTrace]
  refine ⟨6197133653132142626165851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 132205517933485709358204821 6197133653132142626165851)
  ·
    refine ⟨9295700479698213939248777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6197133653132142626165851 9295700479698213939248777)
    ·
      refine ⟨6971775359773660454436583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9295700479698213939248777 6971775359773660454436583)
      ·
        refine ⟨10457663039660490681654875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6971775359773660454436583 10457663039660490681654875)
        ·
          refine ⟨15686494559490736022482313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10457663039660490681654875 15686494559490736022482313)
          ·
            refine ⟨11764870919618052016861735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15686494559490736022482313 11764870919618052016861735)
            ·
              refine ⟨17647306379427078025292603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11764870919618052016861735 17647306379427078025292603)
              ·
                refine ⟨26470959569140617037938905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17647306379427078025292603 26470959569140617037938905)
                ·
                  refine ⟨19853219676855462778454179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26470959569140617037938905 19853219676855462778454179)
                  ·
                    refine ⟨29779829515283194167681269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19853219676855462778454179 29779829515283194167681269)
                    ·
                      refine ⟨2791859017057799453220119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29779829515283194167681269 2791859017057799453220119)
                      ·
                        rfl

theorem cell23_5437126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_5437126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5437126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5437126 prefixEnd_5437126 := by exact prefixLift 5437126
  have htrace : WordTrace (prefixWord ++ tailWord_5437126) baseStart_5437126 baseEnd_5437126 := by
    simpa [prefixWord, tailWord_5437126, baseEnd_5437126] using wordTrace_append hprefix tailTrace_5437126
  have hstable : (prefixWord ++ tailWord_5437126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437126).length < 2 ^ (prefixWord ++ tailWord_5437126).sum := by decide
  have hdescent : baseEnd_5437126 < baseStart_5437126 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437175 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 4]
def baseStart_5437175 : Nat := 118140960795 + 5437175 * 2 ^ 59
def prefixEnd_5437175 : Nat := 4983230072969 + 3 ^ 40 * 5437175 * 2
def baseEnd_5437175 : Nat := 2791884177609869761507393

theorem tailTrace_5437175 : CollatzResearch.WordTrace tailWord_5437175 prefixEnd_5437175 2791884177609869761507393 := by
  unfold tailWord_5437175
  simp only [CollatzResearch.WordTrace]
  refine ⟨198310064077051045405840979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132206709384700696937227319 198310064077051045405840979)
  ·
    refine ⟨297465096115576568108761469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198310064077051045405840979 297465096115576568108761469)
    ·
      refine ⟨111549411043341213040785551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 297465096115576568108761469 111549411043341213040785551)
      ·
        refine ⟨167324116565011819561178327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111549411043341213040785551 167324116565011819561178327)
        ·
          refine ⟨250986174847517729341767491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167324116565011819561178327 250986174847517729341767491)
          ·
            refine ⟨376479262271276594012651237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250986174847517729341767491 376479262271276594012651237)
            ·
              refine ⟨70589861675864361377372107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 376479262271276594012651237 70589861675864361377372107)
              ·
                refine ⟨105884792513796542066058161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70589861675864361377372107 105884792513796542066058161)
                ·
                  refine ⟨79413594385347406549543621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105884792513796542066058161 79413594385347406549543621)
                  ·
                    refine ⟨14890048947252638728039429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79413594385347406549543621 14890048947252638728039429)
                    ·
                      refine ⟨2791884177609869761507393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14890048947252638728039429 2791884177609869761507393)
                      ·
                        rfl

theorem cell23_5437175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_5437175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5437175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5437175 prefixEnd_5437175 := by exact prefixLift 5437175
  have htrace : WordTrace (prefixWord ++ tailWord_5437175) baseStart_5437175 baseEnd_5437175 := by
    simpa [prefixWord, tailWord_5437175, baseEnd_5437175] using wordTrace_append hprefix tailTrace_5437175
  have hstable : (prefixWord ++ tailWord_5437175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437175).length < 2 ^ (prefixWord ++ tailWord_5437175).sum := by decide
  have hdescent : baseEnd_5437175 < baseStart_5437175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437185 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 10]
def baseStart_5437185 : Nat := 118140960795 + 5437185 * 2 ^ 59
def prefixEnd_5437185 : Nat := 4983230072969 + 3 ^ 40 * 5437185 * 2
def baseEnd_5437185 : Nat := 310209923601823858042483

theorem tailTrace_5437185 : CollatzResearch.WordTrace tailWord_5437185 prefixEnd_5437185 310209923601823858042483 := by
  unfold tailWord_5437185
  simp only [CollatzResearch.WordTrace]
  refine ⟨198310428807014817113705009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132206952538009878075803339 198310428807014817113705009)
  ·
    refine ⟨148732821605261112835278757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198310428807014817113705009 148732821605261112835278757)
    ·
      refine ⟨27887404050986458656614767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148732821605261112835278757 27887404050986458656614767)
      ·
        refine ⟨41831106076479687984922151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27887404050986458656614767 41831106076479687984922151)
        ·
          refine ⟨62746659114719531977383227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41831106076479687984922151 62746659114719531977383227)
          ·
            refine ⟨94119988672079297966074841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62746659114719531977383227 94119988672079297966074841)
            ·
              refine ⟨70589991504059473474556131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94119988672079297966074841 70589991504059473474556131)
              ·
                refine ⟨105884987256089210211834197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70589991504059473474556131 105884987256089210211834197)
                ·
                  refine ⟨310209923601823858042483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 105884987256089210211834197 310209923601823858042483)
                  ·
                    rfl

theorem cell23_5437185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 10].length) (baseStart_5437185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5437185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5437185 prefixEnd_5437185 := by exact prefixLift 5437185
  have htrace : WordTrace (prefixWord ++ tailWord_5437185) baseStart_5437185 baseEnd_5437185 := by
    simpa [prefixWord, tailWord_5437185, baseEnd_5437185] using wordTrace_append hprefix tailTrace_5437185
  have hstable : (prefixWord ++ tailWord_5437185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437185).length < 2 ^ (prefixWord ++ tailWord_5437185).sum := by decide
  have hdescent : baseEnd_5437185 < baseStart_5437185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437239 : List Nat := [1, 1, 3, 1, 2, 1, 2, 5, 2, 3, 2]
def baseStart_5437239 : Nat := 118140960795 + 5437239 * 2 ^ 59
def prefixEnd_5437239 : Nat := 4983230072969 + 3 ^ 40 * 5437239 * 2
def baseEnd_5437239 : Nat := 2791917040371757511107099

theorem tailTrace_5437239 : CollatzResearch.WordTrace tailWord_5437239 prefixEnd_5437239 2791917040371757511107099 := by
  unfold tailWord_5437239
  simp only [CollatzResearch.WordTrace]
  refine ⟨198312398348819184336170771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132208265565879456224113847 198312398348819184336170771)
  ·
    refine ⟨297468597523228776504256157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198312398348819184336170771 297468597523228776504256157)
    ·
      refine ⟨111550724071210791189096059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 297468597523228776504256157 111550724071210791189096059)
      ·
        refine ⟨167326086106816186783644089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111550724071210791189096059 167326086106816186783644089)
        ·
          refine ⟨125494564580112140087733067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167326086106816186783644089 125494564580112140087733067)
          ·
            refine ⟨188241846870168210131599601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125494564580112140087733067 188241846870168210131599601)
            ·
              refine ⟨141181385152626157598699701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188241846870168210131599601 141181385152626157598699701)
              ·
                refine ⟨13235754858058702274878097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 141181385152626157598699701 13235754858058702274878097)
                ·
                  refine ⟨9926816143544026706158573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13235754858058702274878097 9926816143544026706158573)
                  ·
                    refine ⟨3722556053829010014809465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9926816143544026706158573 3722556053829010014809465)
                    ·
                      refine ⟨2791917040371757511107099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3722556053829010014809465 2791917040371757511107099)
                      ·
                        rfl

theorem cell23_5437239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 3, 2].length) (baseStart_5437239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5437239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5437239 prefixEnd_5437239 := by exact prefixLift 5437239
  have htrace : WordTrace (prefixWord ++ tailWord_5437239) baseStart_5437239 baseEnd_5437239 := by
    simpa [prefixWord, tailWord_5437239, baseEnd_5437239] using wordTrace_append hprefix tailTrace_5437239
  have hstable : (prefixWord ++ tailWord_5437239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437239).length < 2 ^ (prefixWord ++ tailWord_5437239).sum := by decide
  have hdescent : baseEnd_5437239 < baseStart_5437239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437279 : List Nat := [1, 1, 2, 3, 1, 6, 1, 1, 1, 6]
def baseStart_5437279 : Nat := 118140960795 + 5437279 * 2 ^ 59
def prefixEnd_5437279 : Nat := 4983230072969 + 3 ^ 40 * 5437279 * 2
def baseEnd_5437279 : Nat := 930645859865979118202305

theorem tailTrace_5437279 : CollatzResearch.WordTrace tailWord_5437279 prefixEnd_5437279 930645859865979118202305 := by
  unfold tailWord_5437279
  simp only [CollatzResearch.WordTrace]
  refine ⟨198313857268674271167626891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132209238179116180778417927 198313857268674271167626891)
  ·
    refine ⟨297470785903011406751440337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198313857268674271167626891 297470785903011406751440337)
    ·
      refine ⟨223103089427258555063580253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297470785903011406751440337 223103089427258555063580253)
      ·
        refine ⟨83663658535221958148842595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223103089427258555063580253 83663658535221958148842595)
        ·
          refine ⟨125495487802832937223263893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83663658535221958148842595 125495487802832937223263893)
          ·
            refine ⟨5882600990757793932340495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 125495487802832937223263893 5882600990757793932340495)
            ·
              refine ⟨8823901486136690898510743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5882600990757793932340495 8823901486136690898510743)
              ·
                refine ⟨13235852229205036347766115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8823901486136690898510743 13235852229205036347766115)
                ·
                  refine ⟨19853778343807554521649173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13235852229205036347766115 19853778343807554521649173)
                  ·
                    refine ⟨930645859865979118202305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19853778343807554521649173 930645859865979118202305)
                    ·
                      rfl

theorem cell23_5437279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 6].length) (baseStart_5437279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5437279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5437279 prefixEnd_5437279 := by exact prefixLift 5437279
  have htrace : WordTrace (prefixWord ++ tailWord_5437279) baseStart_5437279 baseEnd_5437279 := by
    simpa [prefixWord, tailWord_5437279, baseEnd_5437279] using wordTrace_append hprefix tailTrace_5437279
  have hstable : (prefixWord ++ tailWord_5437279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437279).length < 2 ^ (prefixWord ++ tailWord_5437279).sum := by decide
  have hdescent : baseEnd_5437279 < baseStart_5437279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437292 : List Nat := [2, 2, 1, 1, 4, 3, 1, 9]
def baseStart_5437292 : Nat := 118140960795 + 5437292 * 2 ^ 59
def prefixEnd_5437292 : Nat := 4983230072969 + 3 ^ 40 * 5437292 * 2
def baseEnd_5437292 : Nat := 103405342772090585323865

theorem tailTrace_5437292 : CollatzResearch.WordTrace tailWord_5437292 prefixEnd_5437292 103405342772090585323865 := by
  unfold tailWord_5437292
  simp only [CollatzResearch.WordTrace]
  refine ⟨99157165708813587193925065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132209554278418116258566753 99157165708813587193925065)
  ·
    refine ⟨74367874281610190395443799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99157165708813587193925065 74367874281610190395443799)
    ·
      refine ⟨111551811422415285593165699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74367874281610190395443799 111551811422415285593165699)
      ·
        refine ⟨167327717133622928389748549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111551811422415285593165699 167327717133622928389748549)
        ·
          refine ⟨31373946962554299073077853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 167327717133622928389748549 31373946962554299073077853)
          ·
            refine ⟨11765230110957862152404195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31373946962554299073077853 11765230110957862152404195)
            ·
              refine ⟨17647845166436793228606293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11765230110957862152404195 17647845166436793228606293)
              ·
                refine ⟨103405342772090585323865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17647845166436793228606293 103405342772090585323865)
                ·
                  rfl

theorem cell23_5437292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 9].length) (baseStart_5437292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5437292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5437292 prefixEnd_5437292 := by exact prefixLift 5437292
  have htrace : WordTrace (prefixWord ++ tailWord_5437292) baseStart_5437292 baseEnd_5437292 := by
    simpa [prefixWord, tailWord_5437292, baseEnd_5437292] using wordTrace_append hprefix tailTrace_5437292
  have hstable : (prefixWord ++ tailWord_5437292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437292).length < 2 ^ (prefixWord ++ tailWord_5437292).sum := by decide
  have hdescent : baseEnd_5437292 < baseStart_5437292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437320 : List Nat := [2, 1, 3, 3, 3, 2, 1, 1, 3, 2, 2]
def baseStart_5437320 : Nat := 118140960795 + 5437320 * 2 ^ 59
def prefixEnd_5437320 : Nat := 4983230072969 + 3 ^ 40 * 5437320 * 2
def baseEnd_5437320 : Nat := 2791958632304771694194227

theorem tailTrace_5437320 : CollatzResearch.WordTrace tailWord_5437320 prefixEnd_5437320 2791958632304771694194227 := by
  unfold tailWord_5437320
  simp only [CollatzResearch.WordTrace]
  refine ⟨99157676330762867584934707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132210235107683823446579609 99157676330762867584934707)
  ·
    refine ⟨148736514496144301377402061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99157676330762867584934707 148736514496144301377402061)
    ·
      refine ⟨55776192936054113016525773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148736514496144301377402061 55776192936054113016525773)
      ·
        refine ⟨20916072351020292381197165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55776192936054113016525773 20916072351020292381197165)
        ·
          refine ⟨7843527131632609642948937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20916072351020292381197165 7843527131632609642948937)
          ·
            refine ⟨5882645348724457232211703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7843527131632609642948937 5882645348724457232211703)
            ·
              refine ⟨8823968023086685848317555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5882645348724457232211703 8823968023086685848317555)
              ·
                refine ⟨13235952034630028772476333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8823968023086685848317555 13235952034630028772476333)
                ·
                  refine ⟨4963482012986260789678625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13235952034630028772476333 4963482012986260789678625)
                  ·
                    refine ⟨3722611509739695592258969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4963482012986260789678625 3722611509739695592258969)
                    ·
                      refine ⟨2791958632304771694194227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3722611509739695592258969 2791958632304771694194227)
                      ·
                        rfl

theorem cell23_5437320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_5437320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5437320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5437320 prefixEnd_5437320 := by exact prefixLift 5437320
  have htrace : WordTrace (prefixWord ++ tailWord_5437320) baseStart_5437320 baseEnd_5437320 := by
    simpa [prefixWord, tailWord_5437320, baseEnd_5437320] using wordTrace_append hprefix tailTrace_5437320
  have hstable : (prefixWord ++ tailWord_5437320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437320).length < 2 ^ (prefixWord ++ tailWord_5437320).sum := by decide
  have hdescent : baseEnd_5437320 < baseStart_5437320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437326 : List Nat := [4, 1, 1, 5, 1, 1, 2, 8]
def baseStart_5437326 : Nat := 118140960795 + 5437326 * 2 ^ 59
def prefixEnd_5437326 : Nat := 4983230072969 + 3 ^ 40 * 5437326 * 2
def baseEnd_5437326 : Nat := 103405989377359210026637

theorem tailTrace_5437326 : CollatzResearch.WordTrace tailWord_5437326 prefixEnd_5437326 103405989377359210026637 := by
  unfold tailWord_5437326
  simp only [CollatzResearch.WordTrace]
  refine ⟨24789446437437999774323479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132210380999669332129725221 24789446437437999774323479)
  ·
    refine ⟨37184169656156999661485219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24789446437437999774323479 37184169656156999661485219)
    ·
      refine ⟨55776254484235499492227829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37184169656156999661485219 55776254484235499492227829)
      ·
        refine ⟨5229023857897078077396359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55776254484235499492227829 5229023857897078077396359)
        ·
          refine ⟨7843535786845617116094539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5229023857897078077396359 7843535786845617116094539)
          ·
            refine ⟨11765303680268425674141809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7843535786845617116094539 11765303680268425674141809)
            ·
              refine ⟨8823977760201319255606357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11765303680268425674141809 8823977760201319255606357)
              ·
                refine ⟨103405989377359210026637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8823977760201319255606357 103405989377359210026637)
                ·
                  rfl

theorem cell23_5437326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 8].length) (baseStart_5437326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5437326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5437326 prefixEnd_5437326 := by exact prefixLift 5437326
  have htrace : WordTrace (prefixWord ++ tailWord_5437326) baseStart_5437326 baseEnd_5437326 := by
    simpa [prefixWord, tailWord_5437326, baseEnd_5437326] using wordTrace_append hprefix tailTrace_5437326
  have hstable : (prefixWord ++ tailWord_5437326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437326).length < 2 ^ (prefixWord ++ tailWord_5437326).sum := by decide
  have hdescent : baseEnd_5437326 < baseStart_5437326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437330 : List Nat := [3, 2, 3, 2, 1, 3, 2, 1, 2, 4]
def baseStart_5437330 : Nat := 118140960795 + 5437330 * 2 ^ 59
def prefixEnd_5437330 : Nat := 4983230072969 + 3 ^ 40 * 5437330 * 2
def baseEnd_5437330 : Nat := 930654589037105551689727

theorem tailTrace_5437330 : CollatzResearch.WordTrace tailWord_5437330 prefixEnd_5437330 930654589037105551689727 := by
  unfold tailWord_5437330
  simp only [CollatzResearch.WordTrace]
  refine ⟨49578929347872376719433361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132210478260993004585155629 49578929347872376719433361)
  ·
    refine ⟨37184197010904282539575021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49578929347872376719433361 37184197010904282539575021)
    ·
      refine ⟨13944073879089105952340633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37184197010904282539575021 13944073879089105952340633)
      ·
        refine ⟨10458055409316829464255475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13944073879089105952340633 10458055409316829464255475)
        ·
          refine ⟨15687083113975244196383213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10458055409316829464255475 15687083113975244196383213)
          ·
            refine ⟨5882656167740716573643705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15687083113975244196383213 5882656167740716573643705)
            ·
              refine ⟨4411992125805537430232779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5882656167740716573643705 4411992125805537430232779)
              ·
                refine ⟨6617988188708306145349169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4411992125805537430232779 6617988188708306145349169)
                ·
                  refine ⟨4963491141531229609011877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6617988188708306145349169 4963491141531229609011877)
                  ·
                    refine ⟨930654589037105551689727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4963491141531229609011877 930654589037105551689727)
                    ·
                      rfl

theorem cell23_5437330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_5437330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5437330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5437330 prefixEnd_5437330 := by exact prefixLift 5437330
  have htrace : WordTrace (prefixWord ++ tailWord_5437330) baseStart_5437330 baseEnd_5437330 := by
    simpa [prefixWord, tailWord_5437330, baseEnd_5437330] using wordTrace_append hprefix tailTrace_5437330
  have hstable : (prefixWord ++ tailWord_5437330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437330).length < 2 ^ (prefixWord ++ tailWord_5437330).sum := by decide
  have hdescent : baseEnd_5437330 < baseStart_5437330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437363 : List Nat := [1, 1, 1, 2, 3, 1, 7, 1, 1, 3, 2]
def baseStart_5437363 : Nat := 118140960795 + 5437363 * 2 ^ 59
def prefixEnd_5437363 : Nat := 4983230072969 + 3 ^ 40 * 5437363 * 2
def baseEnd_5437363 : Nat := 2791980711972915025956529

theorem tailTrace_5437363 : CollatzResearch.WordTrace tailWord_5437363 prefixEnd_5437363 2791980711972915025956529 := by
  unfold tailWord_5437363
  simp only [CollatzResearch.WordTrace]
  refine ⟨198316921000369953513684743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132211280666913302342456495 198316921000369953513684743)
  ·
    refine ⟨297475381500554930270527115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198316921000369953513684743 297475381500554930270527115)
    ·
      refine ⟨446213072250832395405790673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297475381500554930270527115 446213072250832395405790673)
      ·
        refine ⟨334659804188124296554343005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 446213072250832395405790673 334659804188124296554343005)
        ·
          refine ⟨125497426570546611207878627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 334659804188124296554343005 125497426570546611207878627)
          ·
            refine ⟨188246139855819916811817941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125497426570546611207878627 188246139855819916811817941)
            ·
              refine ⟨4412018902870779300276983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 188246139855819916811817941 4412018902870779300276983)
              ·
                refine ⟨6618028354306168950415475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4412018902870779300276983 6618028354306168950415475)
                ·
                  refine ⟨9927042531459253425623213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6618028354306168950415475 9927042531459253425623213)
                  ·
                    refine ⟨3722640949297220034608705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9927042531459253425623213 3722640949297220034608705)
                    ·
                      refine ⟨2791980711972915025956529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3722640949297220034608705 2791980711972915025956529)
                      ·
                        rfl

theorem cell23_5437363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 1, 3, 2].length) (baseStart_5437363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5437363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5437363 prefixEnd_5437363 := by exact prefixLift 5437363
  have htrace : WordTrace (prefixWord ++ tailWord_5437363) baseStart_5437363 baseEnd_5437363 := by
    simpa [prefixWord, tailWord_5437363, baseEnd_5437363] using wordTrace_append hprefix tailTrace_5437363
  have hstable : (prefixWord ++ tailWord_5437363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437363).length < 2 ^ (prefixWord ++ tailWord_5437363).sum := by decide
  have hdescent : baseEnd_5437363 < baseStart_5437363 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437444 : List Nat := [2, 3, 2, 4, 1, 1, 3, 1, 2, 2, 2]
def baseStart_5437444 : Nat := 118140960795 + 5437444 * 2 ^ 59
def prefixEnd_5437444 : Nat := 4983230072969 + 3 ^ 40 * 5437444 * 2
def baseEnd_5437444 : Nat := 2792022303905929209043657

theorem tailTrace_5437444 : CollatzResearch.WordTrace tailWord_5437444 prefixEnd_5437444 2792022303905929209043657 := by
  unfold tailWord_5437444
  simp only [CollatzResearch.WordTrace]
  refine ⟨99159937656538252173691693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132213250208717669564922257 99159937656538252173691693)
  ·
    refine ⟨37184976621201844565134385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99159937656538252173691693 37184976621201844565134385)
    ·
      refine ⟨27888732465901383423850789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37184976621201844565134385 27888732465901383423850789)
      ·
        refine ⟨5229137337356509391972023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27888732465901383423850789 5229137337356509391972023)
        ·
          refine ⟨7843706006034764087958035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5229137337356509391972023 7843706006034764087958035)
          ·
            refine ⟨11765559009052146131937053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7843706006034764087958035 11765559009052146131937053)
            ·
              refine ⟨4412084628394554799476395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11765559009052146131937053 4412084628394554799476395)
              ·
                refine ⟨6618126942591832199214593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4412084628394554799476395 6618126942591832199214593)
                ·
                  refine ⟨4963595206943874149410945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6618126942591832199214593 4963595206943874149410945)
                  ·
                    refine ⟨3722696405207905612058209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4963595206943874149410945 3722696405207905612058209)
                    ·
                      refine ⟨2792022303905929209043657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3722696405207905612058209 2792022303905929209043657)
                      ·
                        rfl

theorem cell23_5437444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_5437444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5437444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5437444 prefixEnd_5437444 := by exact prefixLift 5437444
  have htrace : WordTrace (prefixWord ++ tailWord_5437444) baseStart_5437444 baseEnd_5437444 := by
    simpa [prefixWord, tailWord_5437444, baseEnd_5437444] using wordTrace_append hprefix tailTrace_5437444
  have hstable : (prefixWord ++ tailWord_5437444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437444).length < 2 ^ (prefixWord ++ tailWord_5437444).sum := by decide
  have hdescent : baseEnd_5437444 < baseStart_5437444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437489 : List Nat := [1, 2, 2, 3, 1, 3, 2, 1, 8]
def baseStart_5437489 : Nat := 118140960795 + 5437489 * 2 ^ 59
def prefixEnd_5437489 : Nat := 4983230072969 + 3 ^ 40 * 5437489 * 2
def baseEnd_5437489 : Nat := 310227267837264614775661

theorem tailTrace_5437489 : CollatzResearch.WordTrace tailWord_5437489 prefixEnd_5437489 310227267837264614775661 := by
  unfold tailWord_5437489
  simp only [CollatzResearch.WordTrace]
  refine ⟨198321516597913477032771521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132214344398608984688514347 198321516597913477032771521)
  ·
    refine ⟨148741137448435107774578641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198321516597913477032771521 148741137448435107774578641)
    ·
      refine ⟨111555853086326330830933981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148741137448435107774578641 111555853086326330830933981)
      ·
        refine ⟨41833444907372374061600243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111555853086326330830933981 41833444907372374061600243)
        ·
          refine ⟨62750167361058561092400365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41833444907372374061600243 62750167361058561092400365)
          ·
            refine ⟨23531312760396960409650137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62750167361058561092400365 23531312760396960409650137)
            ·
              refine ⟨17648484570297720307237603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23531312760396960409650137 17648484570297720307237603)
              ·
                refine ⟨26472726855446580460856405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17648484570297720307237603 26472726855446580460856405)
                ·
                  refine ⟨310227267837264614775661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26472726855446580460856405 310227267837264614775661)
                  ·
                    rfl

theorem cell23_5437489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 8].length) (baseStart_5437489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5437489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5437489 prefixEnd_5437489 := by exact prefixLift 5437489
  have htrace : WordTrace (prefixWord ++ tailWord_5437489) baseStart_5437489 baseEnd_5437489 := by
    simpa [prefixWord, tailWord_5437489, baseEnd_5437489] using wordTrace_append hprefix tailTrace_5437489
  have hstable : (prefixWord ++ tailWord_5437489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437489).length < 2 ^ (prefixWord ++ tailWord_5437489).sum := by decide
  have hdescent : baseEnd_5437489 < baseStart_5437489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437493 : List Nat := [1, 3, 3, 1, 1, 1, 2, 6, 1, 4]
def baseStart_5437493 : Nat := 118140960795 + 5437493 * 2 ^ 59
def prefixEnd_5437493 : Nat := 4983230072969 + 3 ^ 40 * 5437493 * 2
def baseEnd_5437493 : Nat := 930682488152666505776977

theorem tailTrace_5437493 : CollatzResearch.WordTrace tailWord_5437493 prefixEnd_5437493 930682488152666505776977 := by
  unfold tailWord_5437493
  simp only [CollatzResearch.WordTrace]
  refine ⟨198321662489898985715917133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132214441659932657143944755 198321662489898985715917133)
  ·
    refine ⟨74370623433712119643468925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198321662489898985715917133 74370623433712119643468925)
    ·
      refine ⟨27888983787642044866300847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74370623433712119643468925 27888983787642044866300847)
      ·
        refine ⟨41833475681463067299451271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27888983787642044866300847 41833475681463067299451271)
        ·
          refine ⟨62750213522194600949176907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41833475681463067299451271 62750213522194600949176907)
          ·
            refine ⟨94125320283291901423765361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62750213522194600949176907 94125320283291901423765361)
            ·
              refine ⟨70593990212468926067824021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94125320283291901423765361 70593990212468926067824021)
              ·
                refine ⟨3309093291209480909429251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70593990212468926067824021 3309093291209480909429251)
                ·
                  refine ⟨4963639936814221364143877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3309093291209480909429251 4963639936814221364143877)
                  ·
                    refine ⟨930682488152666505776977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4963639936814221364143877 930682488152666505776977)
                    ·
                      rfl

theorem cell23_5437493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_5437493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5437493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5437493 prefixEnd_5437493 := by exact prefixLift 5437493
  have htrace : WordTrace (prefixWord ++ tailWord_5437493) baseStart_5437493 baseEnd_5437493 := by
    simpa [prefixWord, tailWord_5437493, baseEnd_5437493] using wordTrace_append hprefix tailTrace_5437493
  have hstable : (prefixWord ++ tailWord_5437493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437493).length < 2 ^ (prefixWord ++ tailWord_5437493).sum := by decide
  have hdescent : baseEnd_5437493 < baseStart_5437493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437519 : List Nat := [1, 1, 2, 1, 1, 2, 2, 5, 3, 5]
def baseStart_5437519 : Nat := 118140960795 + 5437519 * 2 ^ 59
def prefixEnd_5437519 : Nat := 4983230072969 + 3 ^ 40 * 5437519 * 2
def baseEnd_5437519 : Nat := 930686938318338805201937

theorem tailTrace_5437519 : CollatzResearch.WordTrace tailWord_5437519 prefixEnd_5437519 930686938318338805201937 := by
  unfold tailWord_5437519
  simp only [CollatzResearch.WordTrace]
  refine ⟨198322610787804792156363611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132215073858536528104242407 198322610787804792156363611)
  ·
    refine ⟨297483916181707188234545417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198322610787804792156363611 297483916181707188234545417)
    ·
      refine ⟨223112937136280391175909063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297483916181707188234545417 223112937136280391175909063)
      ·
        refine ⟨334669405704420586763863595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223112937136280391175909063 334669405704420586763863595)
        ·
          refine ⟨502004108556630880145795393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334669405704420586763863595 502004108556630880145795393)
          ·
            refine ⟨376503081417473160109346545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 502004108556630880145795393 376503081417473160109346545)
            ·
              refine ⟨282377311063104870082009909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 376503081417473160109346545 282377311063104870082009909)
              ·
                refine ⟨26472872912166081570188429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 282377311063104870082009909 26472872912166081570188429)
                ·
                  refine ⟨9927327342062280588820661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26472872912166081570188429 9927327342062280588820661)
                  ·
                    refine ⟨930686938318338805201937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9927327342062280588820661 930686938318338805201937)
                    ·
                      rfl

theorem cell23_5437519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 5].length) (baseStart_5437519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5437519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5437519 prefixEnd_5437519 := by exact prefixLift 5437519
  have htrace : WordTrace (prefixWord ++ tailWord_5437519) baseStart_5437519 baseEnd_5437519 := by
    simpa [prefixWord, tailWord_5437519, baseEnd_5437519] using wordTrace_append hprefix tailTrace_5437519
  have hstable : (prefixWord ++ tailWord_5437519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437519).length < 2 ^ (prefixWord ++ tailWord_5437519).sum := by decide
  have hdescent : baseEnd_5437519 < baseStart_5437519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437543 : List Nat := [1, 1, 5, 1, 1, 2, 1, 4, 2, 3, 2]
def baseStart_5437543 : Nat := 118140960795 + 5437543 * 2 ^ 59
def prefixEnd_5437543 : Nat := 4983230072969 + 3 ^ 40 * 5437543 * 2
def baseEnd_5437543 : Nat := 2792073138490724321705701

theorem tailTrace_5437543 : CollatzResearch.WordTrace tailWord_5437543 prefixEnd_5437543 2792073138490724321705701 := by
  unfold tailWord_5437543
  simp only [CollatzResearch.WordTrace]
  refine ⟨198323486139717844255237283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132215657426478562836824855 198323486139717844255237283)
  ·
    refine ⟨297485229209576766382855925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198323486139717844255237283 297485229209576766382855925)
    ·
      refine ⟨27889240238397821848392743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 297485229209576766382855925 27889240238397821848392743)
      ·
        refine ⟨41833860357596732772589115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27889240238397821848392743 41833860357596732772589115)
        ·
          refine ⟨62750790536395099158883673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41833860357596732772589115 62750790536395099158883673)
          ·
            refine ⟨47063092902296324369162755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62750790536395099158883673 47063092902296324369162755)
            ·
              refine ⟨70594639353444486553744133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47063092902296324369162755 70594639353444486553744133)
              ·
                refine ⟨13236494878770841228827025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70594639353444486553744133 13236494878770841228827025)
                ·
                  refine ⟨9927371159078130921620269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13236494878770841228827025 9927371159078130921620269)
                  ·
                    refine ⟨3722764184654299095607601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9927371159078130921620269 3722764184654299095607601)
                    ·
                      refine ⟨2792073138490724321705701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3722764184654299095607601 2792073138490724321705701)
                      ·
                        rfl

theorem cell23_5437543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_5437543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5437543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5437543 prefixEnd_5437543 := by exact prefixLift 5437543
  have htrace : WordTrace (prefixWord ++ tailWord_5437543) baseStart_5437543 baseEnd_5437543 := by
    simpa [prefixWord, tailWord_5437543, baseEnd_5437543] using wordTrace_append hprefix tailTrace_5437543
  have hstable : (prefixWord ++ tailWord_5437543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437543).length < 2 ^ (prefixWord ++ tailWord_5437543).sum := by decide
  have hdescent : baseEnd_5437543 < baseStart_5437543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437600 : List Nat := [2, 1, 1, 4, 2, 4, 1, 2, 2, 4]
def baseStart_5437600 : Nat := 118140960795 + 5437600 * 2 ^ 59
def prefixEnd_5437600 : Nat := 4983230072969 + 3 ^ 40 * 5437600 * 2
def baseEnd_5437600 : Nat := 930700802296010199564313

theorem tailTrace_5437600 : CollatzResearch.WordTrace tailWord_5437600 prefixEnd_5437600 930700802296010199564313 := by
  unfold tailWord_5437600
  simp only [CollatzResearch.WordTrace]
  refine ⟨99162782550255671495031127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132217043400340895326708169 99162782550255671495031127)
  ·
    refine ⟨148744173825383507242546691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99162782550255671495031127 148744173825383507242546691)
    ·
      refine ⟨223116260738075260863820037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148744173825383507242546691 223116260738075260863820037)
      ·
        refine ⟨41834298888389111411966257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 223116260738075260863820037 41834298888389111411966257)
        ·
          refine ⟨31375724166291833558974693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41834298888389111411966257 31375724166291833558974693)
          ·
            refine ⟨5882948281179718792307755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31375724166291833558974693 5882948281179718792307755)
            ·
              refine ⟨8824422421769578188461633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5882948281179718792307755 8824422421769578188461633)
              ·
                refine ⟨6618316816327183641346225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8824422421769578188461633 6618316816327183641346225)
                ·
                  refine ⟨4963737612245387731009669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6618316816327183641346225 4963737612245387731009669)
                  ·
                    refine ⟨930700802296010199564313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4963737612245387731009669 930700802296010199564313)
                    ·
                      rfl

theorem cell23_5437600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 2, 4].length) (baseStart_5437600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5437600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5437600 prefixEnd_5437600 := by exact prefixLift 5437600
  have htrace : WordTrace (prefixWord ++ tailWord_5437600) baseStart_5437600 baseEnd_5437600 := by
    simpa [prefixWord, tailWord_5437600, baseEnd_5437600] using wordTrace_append hprefix tailTrace_5437600
  have hstable : (prefixWord ++ tailWord_5437600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437600).length < 2 ^ (prefixWord ++ tailWord_5437600).sum := by decide
  have hdescent : baseEnd_5437600 < baseStart_5437600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437610 : List Nat := [3, 1, 5, 1, 2, 1, 1, 2, 1, 1, 5]
def baseStart_5437610 : Nat := 118140960795 + 5437610 * 2 ^ 59
def prefixEnd_5437610 : Nat := 4983230072969 + 3 ^ 40 * 5437610 * 2
def baseEnd_5437610 : Nat := 2792107541694575559567893

theorem tailTrace_5437610 : CollatzResearch.WordTrace tailWord_5437610 prefixEnd_5437610 2792107541694575559567893 := by
  unfold tailWord_5437610
  simp only [CollatzResearch.WordTrace]
  refine ⟨49581482457618778674481571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132217286553650076465284189 49581482457618778674481571)
  ·
    refine ⟨74372223686428168011722357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49581482457618778674481571 74372223686428168011722357)
    ·
      refine ⟨6972395970602640751098971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74372223686428168011722357 6972395970602640751098971)
      ·
        refine ⟨10458593955903961126648457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6972395970602640751098971 10458593955903961126648457)
        ·
          refine ⟨7843945466927970844986343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10458593955903961126648457 7843945466927970844986343)
          ·
            refine ⟨11765918200391956267479515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7843945466927970844986343 11765918200391956267479515)
            ·
              refine ⟨17648877300587934401219273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11765918200391956267479515 17648877300587934401219273)
              ·
                refine ⟨13236657975440950800914455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17648877300587934401219273 13236657975440950800914455)
                ·
                  refine ⟨19854986963161426201371683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13236657975440950800914455 19854986963161426201371683)
                  ·
                    refine ⟨29782480444742139302057525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19854986963161426201371683 29782480444742139302057525)
                    ·
                      refine ⟨2792107541694575559567893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29782480444742139302057525 2792107541694575559567893)
                      ·
                        rfl

theorem cell23_5437610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_5437610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5437610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5437610 prefixEnd_5437610 := by exact prefixLift 5437610
  have htrace : WordTrace (prefixWord ++ tailWord_5437610) baseStart_5437610 baseEnd_5437610 := by
    simpa [prefixWord, tailWord_5437610, baseEnd_5437610] using wordTrace_append hprefix tailTrace_5437610
  have hstable : (prefixWord ++ tailWord_5437610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437610).length < 2 ^ (prefixWord ++ tailWord_5437610).sum := by decide
  have hdescent : baseEnd_5437610 < baseStart_5437610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437617 : List Nat := [1, 2, 2, 5, 2, 1, 3, 1, 2, 4]
def baseStart_5437617 : Nat := 118140960795 + 5437617 * 2 ^ 59
def prefixEnd_5437617 : Nat := 4983230072969 + 3 ^ 40 * 5437617 * 2
def baseEnd_5437617 : Nat := 930703712019719010726787

theorem tailTrace_5437617 : CollatzResearch.WordTrace tailWord_5437617 prefixEnd_5437617 930703712019719010726787 := by
  unfold tailWord_5437617
  simp only [CollatzResearch.WordTrace]
  refine ⟨198326185141449754893431105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132217456760966503262287403 198326185141449754893431105)
  ·
    refine ⟨148744638856087316170073329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198326185141449754893431105 148744638856087316170073329)
    ·
      refine ⟨111558479142065487127554997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148744638856087316170073329 111558479142065487127554997)
      ·
        refine ⟨10458607419568639418208281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111558479142065487127554997 10458607419568639418208281)
        ·
          refine ⟨7843955564676479563656211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10458607419568639418208281 7843955564676479563656211)
          ·
            refine ⟨11765933347014719345484317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7843955564676479563656211 11765933347014719345484317)
            ·
              refine ⟨4412225005130519754556619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11765933347014719345484317 4412225005130519754556619)
              ·
                refine ⟨6618337507695779631834929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4412225005130519754556619 6618337507695779631834929)
                ·
                  refine ⟨4963753130771834723876197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6618337507695779631834929 4963753130771834723876197)
                  ·
                    refine ⟨930703712019719010726787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4963753130771834723876197 930703712019719010726787)
                    ·
                      rfl

theorem cell23_5437617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 2, 4].length) (baseStart_5437617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5437617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5437617 prefixEnd_5437617 := by exact prefixLift 5437617
  have htrace : WordTrace (prefixWord ++ tailWord_5437617) baseStart_5437617 baseEnd_5437617 := by
    simpa [prefixWord, tailWord_5437617, baseEnd_5437617] using wordTrace_append hprefix tailTrace_5437617
  have hstable : (prefixWord ++ tailWord_5437617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437617).length < 2 ^ (prefixWord ++ tailWord_5437617).sum := by decide
  have hdescent : baseEnd_5437617 < baseStart_5437617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437623 : List Nat := [1, 1, 3, 1, 4, 2, 3, 1, 1, 3, 3]
def baseStart_5437623 : Nat := 118140960795 + 5437623 * 2 ^ 59
def prefixEnd_5437623 : Nat := 4983230072969 + 3 ^ 40 * 5437623 * 2
def baseEnd_5437623 : Nat := 2792114216943084008705333

theorem tailTrace_5437623 : CollatzResearch.WordTrace tailWord_5437623 prefixEnd_5437623 2792114216943084008705333 := by
  unfold tailWord_5437623
  simp only [CollatzResearch.WordTrace]
  refine ⟨198326403979428017918149523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132217602652952011945433015 198326403979428017918149523)
  ·
    refine ⟨297489605969142026877224285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198326403979428017918149523 297489605969142026877224285)
    ·
      refine ⟨111558602238428260078959107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 297489605969142026877224285 111558602238428260078959107)
      ·
        refine ⟨167337903357642390118438661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111558602238428260078959107 167337903357642390118438661)
        ·
          refine ⟨31375856879557948147207249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 167337903357642390118438661 31375856879557948147207249)
          ·
            refine ⟨23531892659668461110405437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31375856879557948147207249 23531892659668461110405437)
            ·
              refine ⟨8824459747375672916402039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23531892659668461110405437 8824459747375672916402039)
              ·
                refine ⟨13236689621063509374603059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8824459747375672916402039 13236689621063509374603059)
                ·
                  refine ⟨19855034431595264061904589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13236689621063509374603059 19855034431595264061904589)
                  ·
                    refine ⟨7445637911848224023214221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19855034431595264061904589 7445637911848224023214221)
                    ·
                      refine ⟨2792114216943084008705333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7445637911848224023214221 2792114216943084008705333)
                      ·
                        rfl

theorem cell23_5437623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 3, 3].length) (baseStart_5437623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5437623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5437623 prefixEnd_5437623 := by exact prefixLift 5437623
  have htrace : WordTrace (prefixWord ++ tailWord_5437623) baseStart_5437623 baseEnd_5437623 := by
    simpa [prefixWord, tailWord_5437623, baseEnd_5437623] using wordTrace_append hprefix tailTrace_5437623
  have hstable : (prefixWord ++ tailWord_5437623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437623).length < 2 ^ (prefixWord ++ tailWord_5437623).sum := by decide
  have hdescent : baseEnd_5437623 < baseStart_5437623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437630 : List Nat := [4, 2, 1, 1, 4, 2, 2, 7]
def baseStart_5437630 : Nat := 118140960795 + 5437630 * 2 ^ 59
def prefixEnd_5437630 : Nat := 4983230072969 + 3 ^ 40 * 5437630 * 2
def baseEnd_5437630 : Nat := 103411770789172795604363

theorem tailTrace_5437630 : CollatzResearch.WordTrace tailWord_5437630 prefixEnd_5437630 103411770789172795604363 := by
  unfold tailWord_5437630
  simp only [CollatzResearch.WordTrace]
  refine ⟨24790832411300332264206793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132217772860268438742436229 24790832411300332264206793)
  ·
    refine ⟨18593124308475249198155095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24790832411300332264206793 18593124308475249198155095)
    ·
      refine ⟨27889686462712873797232643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18593124308475249198155095 27889686462712873797232643)
      ·
        refine ⟨41834529694069310695848965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27889686462712873797232643 41834529694069310695848965)
        ·
          refine ⟨7843974317637995755471681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41834529694069310695848965 7843974317637995755471681)
          ·
            refine ⟨5882980738228496816603761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7843974317637995755471681 5882980738228496816603761)
            ·
              refine ⟨4412235553671372612452821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5882980738228496816603761 4412235553671372612452821)
              ·
                refine ⟨103411770789172795604363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4412235553671372612452821 103411770789172795604363)
                ·
                  rfl

theorem cell23_5437630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 7].length) (baseStart_5437630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5437630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5437630 prefixEnd_5437630 := by exact prefixLift 5437630
  have htrace : WordTrace (prefixWord ++ tailWord_5437630) baseStart_5437630 baseEnd_5437630 := by
    simpa [prefixWord, tailWord_5437630, baseEnd_5437630] using wordTrace_append hprefix tailTrace_5437630
  have hstable : (prefixWord ++ tailWord_5437630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437630).length < 2 ^ (prefixWord ++ tailWord_5437630).sum := by decide
  have hdescent : baseEnd_5437630 < baseStart_5437630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437676 : List Nat := [2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 4]
def baseStart_5437676 : Nat := 118140960795 + 5437676 * 2 ^ 59
def prefixEnd_5437676 : Nat := 4983230072969 + 3 ^ 40 * 5437676 * 2
def baseEnd_5437676 : Nat := 2792141431417772301342589

theorem tailTrace_5437676 : CollatzResearch.WordTrace tailWord_5437676 prefixEnd_5437676 2792141431417772301342589 := by
  unfold tailWord_5437676
  simp only [CollatzResearch.WordTrace]
  refine ⟨99164168524118003984914441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132218891365490671979885921 99164168524118003984914441)
  ·
    refine ⟨74373126393088502988685831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99164168524118003984914441 74373126393088502988685831)
    ·
      refine ⟨111559689589632754483028747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74373126393088502988685831 111559689589632754483028747)
      ·
        refine ⟨167339534384449131724543121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111559689589632754483028747 167339534384449131724543121)
        ·
          refine ⟨125504650788336848793407341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167339534384449131724543121 125504650788336848793407341)
          ·
            refine ⟨47064244045626318297527753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125504650788336848793407341 47064244045626318297527753)
            ·
              refine ⟨35298183034219738723145815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47064244045626318297527753 35298183034219738723145815)
              ·
                refine ⟨52947274551329608084718723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35298183034219738723145815 52947274551329608084718723)
                ·
                  refine ⟨79420911826994412127078085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52947274551329608084718723 79420911826994412127078085)
                  ·
                    refine ⟨14891420967561452273827141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79420911826994412127078085 14891420967561452273827141)
                    ·
                      refine ⟨2792141431417772301342589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14891420967561452273827141 2792141431417772301342589)
                      ·
                        rfl

theorem cell23_5437676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_5437676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5437676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5437676 prefixEnd_5437676 := by exact prefixLift 5437676
  have htrace : WordTrace (prefixWord ++ tailWord_5437676) baseStart_5437676 baseEnd_5437676 := by
    simpa [prefixWord, tailWord_5437676, baseEnd_5437676] using wordTrace_append hprefix tailTrace_5437676
  have hstable : (prefixWord ++ tailWord_5437676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437676).length < 2 ^ (prefixWord ++ tailWord_5437676).sum := by decide
  have hdescent : baseEnd_5437676 < baseStart_5437676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437723 : List Nat := [1, 1, 1, 1, 1, 1, 7, 1, 2, 5, 2]
def baseStart_5437723 : Nat := 118140960795 + 5437723 * 2 ^ 59
def prefixEnd_5437723 : Nat := 4983230072969 + 3 ^ 40 * 5437723 * 2
def baseEnd_5437723 : Nat := 2792165565008533617454873

theorem tailTrace_5437723 : CollatzResearch.WordTrace tailWord_5437723 prefixEnd_5437723 2792165565008533617454873 := by
  unfold tailWord_5437723
  simp only [CollatzResearch.WordTrace]
  refine ⟨198330051279065734996789823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132220034186043823331193215 198330051279065734996789823)
  ·
    refine ⟨297495076918598602495184735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198330051279065734996789823 297495076918598602495184735)
    ·
      refine ⟨446242615377897903742777103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297495076918598602495184735 446242615377897903742777103)
      ·
        refine ⟨669363923066846855614165655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446242615377897903742777103 669363923066846855614165655)
        ·
          refine ⟨1004045884600270283421248483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 669363923066846855614165655 1004045884600270283421248483)
          ·
            refine ⟨1506068826900405425131872725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1004045884600270283421248483 1506068826900405425131872725)
            ·
              refine ⟨35298488130478252151528267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1506068826900405425131872725 35298488130478252151528267)
              ·
                refine ⟨52947732195717378227292401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35298488130478252151528267 52947732195717378227292401)
                ·
                  refine ⟨39710799146788033670469301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52947732195717378227292401 39710799146788033670469301)
                  ·
                    refine ⟨3722887420011378156606497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39710799146788033670469301 3722887420011378156606497)
                    ·
                      refine ⟨2792165565008533617454873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3722887420011378156606497 2792165565008533617454873)
                      ·
                        rfl

theorem cell23_5437723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 5, 2].length) (baseStart_5437723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5437723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5437723 prefixEnd_5437723 := by exact prefixLift 5437723
  have htrace : WordTrace (prefixWord ++ tailWord_5437723) baseStart_5437723 baseEnd_5437723 := by
    simpa [prefixWord, tailWord_5437723, baseEnd_5437723] using wordTrace_append hprefix tailTrace_5437723
  have hstable : (prefixWord ++ tailWord_5437723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437723).length < 2 ^ (prefixWord ++ tailWord_5437723).sum := by decide
  have hdescent : baseEnd_5437723 < baseStart_5437723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437730 : List Nat := [3, 3, 1, 1, 3, 2, 1, 1, 2, 3, 3]
def baseStart_5437730 : Nat := 118140960795 + 5437730 * 2 ^ 59
def prefixEnd_5437730 : Nat := 4983230072969 + 3 ^ 40 * 5437730 * 2
def baseEnd_5437730 : Nat := 2792169159373115090067341

theorem tailTrace_5437730 : CollatzResearch.WordTrace tailWord_5437730 prefixEnd_5437730 2792169159373115090067341 := by
  unfold tailWord_5437730
  simp only [CollatzResearch.WordTrace]
  refine ⟨49582576647510093798073661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132220204393360250128196429 49582576647510093798073661)
  ·
    refine ⟨18593466242816285174277623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49582576647510093798073661 18593466242816285174277623)
    ·
      refine ⟨27890199364224427761416435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18593466242816285174277623 27890199364224427761416435)
      ·
        refine ⟨41835299046336641642124653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27890199364224427761416435 41835299046336641642124653)
        ·
          refine ⟨15688237142376240615796745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41835299046336641642124653 15688237142376240615796745)
          ·
            refine ⟨11766177856782180461847559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15688237142376240615796745 11766177856782180461847559)
            ·
              refine ⟨17649266785173270692771339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11766177856782180461847559 17649266785173270692771339)
              ·
                refine ⟨26473900177759906039157009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17649266785173270692771339 26473900177759906039157009)
                ·
                  refine ⟨19855425133319929529367757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26473900177759906039157009 19855425133319929529367757)
                  ·
                    refine ⟨7445784424994973573512909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19855425133319929529367757 7445784424994973573512909)
                    ·
                      refine ⟨2792169159373115090067341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7445784424994973573512909 2792169159373115090067341)
                      ·
                        rfl

theorem cell23_5437730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_5437730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5437730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5437730 prefixEnd_5437730 := by exact prefixLift 5437730
  have htrace : WordTrace (prefixWord ++ tailWord_5437730) baseStart_5437730 baseEnd_5437730 := by
    simpa [prefixWord, tailWord_5437730, baseEnd_5437730] using wordTrace_append hprefix tailTrace_5437730
  have hstable : (prefixWord ++ tailWord_5437730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437730).length < 2 ^ (prefixWord ++ tailWord_5437730).sum := by decide
  have hdescent : baseEnd_5437730 < baseStart_5437730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437780 : List Nat := [2, 4, 1, 1, 2, 2, 1, 3, 3, 4]
def baseStart_5437780 : Nat := 118140960795 + 5437780 * 2 ^ 59
def prefixEnd_5437780 : Nat := 4983230072969 + 3 ^ 40 * 5437780 * 2
def baseEnd_5437780 : Nat := 930731611135279964814037

theorem tailTrace_5437780 : CollatzResearch.WordTrace tailWord_5437780 prefixEnd_5437780 930731611135279964814037 := by
  unfold tailWord_5437780
  simp only [CollatzResearch.WordTrace]
  refine ⟨99166065119929616865807397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132221420159906155821076529 99166065119929616865807397)
  ·
    refine ⟨18593637209986803162338887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99166065119929616865807397 18593637209986803162338887)
    ·
      refine ⟨27890455814980204743508331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18593637209986803162338887 27890455814980204743508331)
      ·
        refine ⟨41835683722470307115262497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27890455814980204743508331 41835683722470307115262497)
        ·
          refine ⟨31376762791852730336446873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41835683722470307115262497 31376762791852730336446873)
          ·
            refine ⟨23532572093889547752335155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31376762791852730336446873 23532572093889547752335155)
            ·
              refine ⟨35298858140834321628502733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23532572093889547752335155 35298858140834321628502733)
              ·
                refine ⟨13237071802812870610688525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35298858140834321628502733 13237071802812870610688525)
                ·
                  refine ⟨4963901926054826479008197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13237071802812870610688525 4963901926054826479008197)
                  ·
                    refine ⟨930731611135279964814037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4963901926054826479008197 930731611135279964814037)
                    ·
                      rfl

theorem cell23_5437780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_5437780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5437780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5437780 prefixEnd_5437780 := by exact prefixLift 5437780
  have htrace : WordTrace (prefixWord ++ tailWord_5437780) baseStart_5437780 baseEnd_5437780 := by
    simpa [prefixWord, tailWord_5437780, baseEnd_5437780] using wordTrace_append hprefix tailTrace_5437780
  have hstable : (prefixWord ++ tailWord_5437780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437780).length < 2 ^ (prefixWord ++ tailWord_5437780).sum := by decide
  have hdescent : baseEnd_5437780 < baseStart_5437780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437844 : List Nat := [2, 4, 2, 1, 3, 2, 2, 1, 6]
def baseStart_5437844 : Nat := 118140960795 + 5437844 * 2 ^ 59
def prefixEnd_5437844 : Nat := 4983230072969 + 3 ^ 40 * 5437844 * 2
def baseEnd_5437844 : Nat := 310247521796414182671313

theorem tailTrace_5437844 : CollatzResearch.WordTrace tailWord_5437844 prefixEnd_5437844 310247521796414182671313 := by
  unfold tailWord_5437844
  simp only [CollatzResearch.WordTrace]
  refine ⟨99167232255813686330972293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132222976341084915107963057 99167232255813686330972293)
  ·
    refine ⟨18593856047965066187057305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99167232255813686330972293 18593856047965066187057305)
    ·
      refine ⟨13945392035973799640292979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18593856047965066187057305 13945392035973799640292979)
      ·
        refine ⟨20918088053960699460439469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13945392035973799640292979 20918088053960699460439469)
        ·
          refine ⟨7844283020235262297664801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20918088053960699460439469 7844283020235262297664801)
          ·
            refine ⟨5883212265176446723248601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7844283020235262297664801 5883212265176446723248601)
            ·
              refine ⟨4412409198882335042436451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5883212265176446723248601 4412409198882335042436451)
              ·
                refine ⟨6618613798323502563654677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4412409198882335042436451 6618613798323502563654677)
                ·
                  refine ⟨310247521796414182671313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6618613798323502563654677 310247521796414182671313)
                  ·
                    rfl

theorem cell23_5437844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_5437844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5437844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5437844 prefixEnd_5437844 := by exact prefixLift 5437844
  have htrace : WordTrace (prefixWord ++ tailWord_5437844) baseStart_5437844 baseEnd_5437844 := by
    simpa [prefixWord, tailWord_5437844, baseEnd_5437844] using wordTrace_append hprefix tailTrace_5437844
  have hstable : (prefixWord ++ tailWord_5437844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437844).length < 2 ^ (prefixWord ++ tailWord_5437844).sum := by decide
  have hdescent : baseEnd_5437844 < baseStart_5437844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437857 : List Nat := [1, 2, 3, 5, 1, 1, 1, 1, 3, 5]
def baseStart_5437857 : Nat := 118140960795 + 5437857 * 2 ^ 59
def prefixEnd_5437857 : Nat := 4983230072969 + 3 ^ 40 * 5437857 * 2
def baseEnd_5437857 : Nat := 930744790472078697726419

theorem tailTrace_5437857 : CollatzResearch.WordTrace tailWord_5437857 prefixEnd_5437857 930744790472078697726419 := by
  unfold tailWord_5437857
  simp only [CollatzResearch.WordTrace]
  refine ⟨198334938660580275882167825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132223292440386850588111883 198334938660580275882167825)
  ·
    refine ⟨148751203995435206911625869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198334938660580275882167825 148751203995435206911625869)
    ·
      refine ⟨55781701498288202591859701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148751203995435206911625869 55781701498288202591859701)
      ·
        refine ⟨5229534515464518992986847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55781701498288202591859701 5229534515464518992986847)
        ·
          refine ⟨7844301773196778489480271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5229534515464518992986847 7844301773196778489480271)
          ·
            refine ⟨11766452659795167734220407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7844301773196778489480271 11766452659795167734220407)
            ·
              refine ⟨17649678989692751601330611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11766452659795167734220407 17649678989692751601330611)
              ·
                refine ⟨26474518484539127401995917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17649678989692751601330611 26474518484539127401995917)
                ·
                  refine ⟨9927944431702172775748469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26474518484539127401995917 9927944431702172775748469)
                  ·
                    refine ⟨930744790472078697726419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9927944431702172775748469 930744790472078697726419)
                    ·
                      rfl

theorem cell23_5437857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_5437857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5437857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5437857 prefixEnd_5437857 := by exact prefixLift 5437857
  have htrace : WordTrace (prefixWord ++ tailWord_5437857) baseStart_5437857 baseEnd_5437857 := by
    simpa [prefixWord, tailWord_5437857, baseEnd_5437857] using wordTrace_append hprefix tailTrace_5437857
  have hstable : (prefixWord ++ tailWord_5437857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437857).length < 2 ^ (prefixWord ++ tailWord_5437857).sum := by decide
  have hdescent : baseEnd_5437857 < baseStart_5437857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437860 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 2, 6, 2]
def baseStart_5437860 : Nat := 118140960795 + 5437860 * 2 ^ 59
def prefixEnd_5437860 : Nat := 4983230072969 + 3 ^ 40 * 5437860 * 2
def baseEnd_5437860 : Nat := 2792235911858199581441743

theorem tailTrace_5437860 : CollatzResearch.WordTrace tailWord_5437860 prefixEnd_5437860 2792235911858199581441743 := by
  unfold tailWord_5437860
  simp only [CollatzResearch.WordTrace]
  refine ⟨99167524039784703697263517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132223365386379604929684689 99167524039784703697263517)
  ·
    refine ⟨37187821514919263886473819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99167524039784703697263517 37187821514919263886473819)
    ·
      refine ⟨55781732272378895829710729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37187821514919263886473819 55781732272378895829710729)
      ·
        refine ⟨41836299204284171872283047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55781732272378895829710729 41836299204284171872283047)
        ·
          refine ⟨62754448806426257808424571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41836299204284171872283047 62754448806426257808424571)
          ·
            refine ⟨94131673209639386712636857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62754448806426257808424571 94131673209639386712636857)
            ·
              refine ⟨70598754907229540034477643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94131673209639386712636857 70598754907229540034477643)
              ·
                refine ⟨105898132360844310051716465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70598754907229540034477643 105898132360844310051716465)
                ·
                  refine ⟨79423599270633232538787349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105898132360844310051716465 79423599270633232538787349)
                  ·
                    refine ⟨3722981215810932775255657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79423599270633232538787349 3722981215810932775255657)
                    ·
                      refine ⟨2792235911858199581441743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3722981215810932775255657 2792235911858199581441743)
                      ·
                        rfl

theorem cell23_5437860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_5437860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5437860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5437860 prefixEnd_5437860 := by exact prefixLift 5437860
  have htrace : WordTrace (prefixWord ++ tailWord_5437860) baseStart_5437860 baseEnd_5437860 := by
    simpa [prefixWord, tailWord_5437860, baseEnd_5437860] using wordTrace_append hprefix tailTrace_5437860
  have hstable : (prefixWord ++ tailWord_5437860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437860).length < 2 ^ (prefixWord ++ tailWord_5437860).sum := by decide
  have hdescent : baseEnd_5437860 < baseStart_5437860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437864 : List Nat := [2, 1, 6, 1, 1, 1, 1, 3, 2, 3, 2]
def baseStart_5437864 : Nat := 118140960795 + 5437864 * 2 ^ 59
def prefixEnd_5437864 : Nat := 4983230072969 + 3 ^ 40 * 5437864 * 2
def baseEnd_5437864 : Nat := 2792237965780817565791725

theorem tailTrace_5437864 : CollatzResearch.WordTrace tailWord_5437864 prefixEnd_5437864 2792237965780817565791725 := by
  unfold tailWord_5437864
  simp only [CollatzResearch.WordTrace]
  refine ⟨99167596985777458038836323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132223462647703277385115097 99167596985777458038836323)
  ·
    refine ⟨148751395478666187058254485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99167596985777458038836323 148751395478666187058254485)
    ·
      refine ⟨6972721663062477518355679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 148751395478666187058254485 6972721663062477518355679)
      ·
        refine ⟨10459082494593716277533519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6972721663062477518355679 10459082494593716277533519)
        ·
          refine ⟨15688623741890574416300279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10459082494593716277533519 15688623741890574416300279)
          ·
            refine ⟨23532935612835861624450419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15688623741890574416300279 23532935612835861624450419)
            ·
              refine ⟨35299403419253792436675629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23532935612835861624450419 35299403419253792436675629)
              ·
                refine ⟨13237276282220172163753361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35299403419253792436675629 13237276282220172163753361)
                ·
                  refine ⟨9927957211665129122815021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13237276282220172163753361 9927957211665129122815021)
                  ·
                    refine ⟨3722983954374423421055633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9927957211665129122815021 3722983954374423421055633)
                    ·
                      refine ⟨2792237965780817565791725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3722983954374423421055633 2792237965780817565791725)
                      ·
                        rfl

theorem cell23_5437864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_5437864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5437864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5437864 prefixEnd_5437864 := by exact prefixLift 5437864
  have htrace : WordTrace (prefixWord ++ tailWord_5437864) baseStart_5437864 baseEnd_5437864 := by
    simpa [prefixWord, tailWord_5437864, baseEnd_5437864] using wordTrace_append hprefix tailTrace_5437864
  have hstable : (prefixWord ++ tailWord_5437864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437864).length < 2 ^ (prefixWord ++ tailWord_5437864).sum := by decide
  have hdescent : baseEnd_5437864 < baseStart_5437864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437913 : List Nat := [1, 2, 1, 2, 4, 1, 1, 2, 2, 7]
def baseStart_5437913 : Nat := 118140960795 + 5437913 * 2 ^ 59
def prefixEnd_5437913 : Nat := 4983230072969 + 3 ^ 40 * 5437913 * 2
def baseEnd_5437913 : Nat := 930754375444295958026333

theorem tailTrace_5437913 : CollatzResearch.WordTrace tailWord_5437913 prefixEnd_5437913 930754375444295958026333 := by
  unfold tailWord_5437913
  simp only [CollatzResearch.WordTrace]
  refine ⟨198336981148377397446206393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132224654098918264964137595 198336981148377397446206393)
  ·
    refine ⟨148752735861283048084654795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198336981148377397446206393 148752735861283048084654795)
    ·
      refine ⟨223129103791924572126982193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148752735861283048084654795 223129103791924572126982193)
      ·
        refine ⟨167346827843943429095236645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223129103791924572126982193 167346827843943429095236645)
        ·
          refine ⟨31377530220739392955356871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 167346827843943429095236645 31377530220739392955356871)
          ·
            refine ⟨47066295331109089433035307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31377530220739392955356871 47066295331109089433035307)
            ·
              refine ⟨70599442996663634149552961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47066295331109089433035307 70599442996663634149552961)
              ·
                refine ⟨52949582247497725612164721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70599442996663634149552961 52949582247497725612164721)
                ·
                  refine ⟨39712186685623294209123541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52949582247497725612164721 39712186685623294209123541)
                  ·
                    refine ⟨930754375444295958026333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39712186685623294209123541 930754375444295958026333)
                    ·
                      rfl

theorem cell23_5437913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 7].length) (baseStart_5437913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5437913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5437913 prefixEnd_5437913 := by exact prefixLift 5437913
  have htrace : WordTrace (prefixWord ++ tailWord_5437913) baseStart_5437913 baseEnd_5437913 := by
    simpa [prefixWord, tailWord_5437913, baseEnd_5437913] using wordTrace_append hprefix tailTrace_5437913
  have hstable : (prefixWord ++ tailWord_5437913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437913).length < 2 ^ (prefixWord ++ tailWord_5437913).sum := by decide
  have hdescent : baseEnd_5437913 < baseStart_5437913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437927 : List Nat := [1, 1, 5, 2, 1, 1, 2, 2, 4, 1, 3]
def baseStart_5437927 : Nat := 118140960795 + 5437927 * 2 ^ 59
def prefixEnd_5437927 : Nat := 4983230072969 + 3 ^ 40 * 5437927 * 2
def baseEnd_5437927 : Nat := 2792270315062050819303935

theorem tailTrace_5437927 : CollatzResearch.WordTrace tailWord_5437927 prefixEnd_5437927 2792270315062050819303935 := by
  unfold tailWord_5437927
  simp only [CollatzResearch.WordTrace]
  refine ⟨198337491770326677837216035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132224994513551118558144023 198337491770326677837216035)
  ·
    refine ⟨297506237655490016755824053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198337491770326677837216035 297506237655490016755824053)
    ·
      refine ⟨27891209780202189070858505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 297506237655490016755824053 27891209780202189070858505)
      ·
        refine ⟨20918407335151641803143879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27891209780202189070858505 20918407335151641803143879)
        ·
          refine ⟨31377611002727462704715819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20918407335151641803143879 31377611002727462704715819)
          ·
            refine ⟨47066416504091194057073729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31377611002727462704715819 47066416504091194057073729)
            ·
              refine ⟨35299812378068395542805297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47066416504091194057073729 35299812378068395542805297)
              ·
                refine ⟨26474859283551296657103973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35299812378068395542805297 26474859283551296657103973)
                ·
                  refine ⟨4964036115665868123206995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26474859283551296657103973 4964036115665868123206995)
                  ·
                    refine ⟨7446054173498802184810493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4964036115665868123206995 7446054173498802184810493)
                    ·
                      refine ⟨2792270315062050819303935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7446054173498802184810493 2792270315062050819303935)
                      ·
                        rfl

theorem cell23_5437927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_5437927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5437927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5437927 prefixEnd_5437927 := by exact prefixLift 5437927
  have htrace : WordTrace (prefixWord ++ tailWord_5437927) baseStart_5437927 baseEnd_5437927 := by
    simpa [prefixWord, tailWord_5437927, baseEnd_5437927] using wordTrace_append hprefix tailTrace_5437927
  have hstable : (prefixWord ++ tailWord_5437927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437927).length < 2 ^ (prefixWord ++ tailWord_5437927).sum := by decide
  have hdescent : baseEnd_5437927 < baseStart_5437927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437958 : List Nat := [6, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4]
def baseStart_5437958 : Nat := 118140960795 + 5437958 * 2 ^ 59
def prefixEnd_5437958 : Nat := 4983230072969 + 3 ^ 40 * 5437958 * 2
def baseEnd_5437958 : Nat := 2792286232962340198016293

theorem tailTrace_5437958 : CollatzResearch.WordTrace tailWord_5437958 prefixEnd_5437958 2792286232962340198016293 := by
  unfold tailWord_5437958
  simp only [CollatzResearch.WordTrace]
  refine ⟨6198081951037949066612329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 132225748288809580087729685 6198081951037949066612329)
  ·
    refine ⟨4648561463278461799959247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6198081951037949066612329 4648561463278461799959247)
    ·
      refine ⟨6972842194917692699938871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4648561463278461799959247 6972842194917692699938871)
      ·
        refine ⟨10459263292376539049908307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6972842194917692699938871 10459263292376539049908307)
        ·
          refine ⟨15688894938564808574862461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10459263292376539049908307 15688894938564808574862461)
          ·
            refine ⟨5883335601961803215573423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15688894938564808574862461 5883335601961803215573423)
            ·
              refine ⟨8825003402942704823360135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5883335601961803215573423 8825003402942704823360135)
              ·
                refine ⟨13237505104414057235040203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8825003402942704823360135 13237505104414057235040203)
                ·
                  refine ⟨19856257656621085852560305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13237505104414057235040203 19856257656621085852560305)
                  ·
                    refine ⟨14892193242465814389420229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19856257656621085852560305 14892193242465814389420229)
                    ·
                      refine ⟨2792286232962340198016293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14892193242465814389420229 2792286232962340198016293)
                      ·
                        rfl

theorem cell23_5437958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_5437958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5437958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5437958 prefixEnd_5437958 := by exact prefixLift 5437958
  have htrace : WordTrace (prefixWord ++ tailWord_5437958) baseStart_5437958 baseEnd_5437958 := by
    simpa [prefixWord, tailWord_5437958, baseEnd_5437958] using wordTrace_append hprefix tailTrace_5437958
  have hstable : (prefixWord ++ tailWord_5437958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437958).length < 2 ^ (prefixWord ++ tailWord_5437958).sum := by decide
  have hdescent : baseEnd_5437958 < baseStart_5437958 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5437967 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 6, 2, 2]
def baseStart_5437967 : Nat := 118140960795 + 5437967 * 2 ^ 59
def prefixEnd_5437967 : Nat := 4983230072969 + 3 ^ 40 * 5437967 * 2
def baseEnd_5437967 : Nat := 2792290854288230662803751

theorem tailTrace_5437967 : CollatzResearch.WordTrace tailWord_5437967 prefixEnd_5437967 2792290854288230662803751 := by
  unfold tailWord_5437967
  simp only [CollatzResearch.WordTrace]
  refine ⟨198338950690181764668672155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132225967126787843112448103 198338950690181764668672155)
  ·
    refine ⟨297508426035272647003008233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198338950690181764668672155 297508426035272647003008233)
    ·
      refine ⟨223131319526454485252256175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297508426035272647003008233 223131319526454485252256175)
      ·
        refine ⟨334696979289681727878384263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223131319526454485252256175 334696979289681727878384263)
        ·
          refine ⟨502045468934522591817576395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334696979289681727878384263 502045468934522591817576395)
          ·
            refine ⟨753068203401783887726364593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502045468934522591817576395 753068203401783887726364593)
            ·
              refine ⟨564801152551337915794773445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 753068203401783887726364593 564801152551337915794773445)
              ·
                refine ⟨105900216103375859211520021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 564801152551337915794773445 105900216103375859211520021)
                ·
                  refine ⟨4964072629845743400540001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 105900216103375859211520021 4964072629845743400540001)
                  ·
                    refine ⟨3723054472384307550405001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4964072629845743400540001 3723054472384307550405001)
                    ·
                      refine ⟨2792290854288230662803751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3723054472384307550405001 2792290854288230662803751)
                      ·
                        rfl

theorem cell23_5437967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 6, 2, 2].length) (baseStart_5437967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5437967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5437967 prefixEnd_5437967 := by exact prefixLift 5437967
  have htrace : WordTrace (prefixWord ++ tailWord_5437967) baseStart_5437967 baseEnd_5437967 := by
    simpa [prefixWord, tailWord_5437967, baseEnd_5437967] using wordTrace_append hprefix tailTrace_5437967
  have hstable : (prefixWord ++ tailWord_5437967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5437967).length < 2 ^ (prefixWord ++ tailWord_5437967).sum := by decide
  have hdescent : baseEnd_5437967 < baseStart_5437967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5437967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438000 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 3]
def baseStart_5438000 : Nat := 118140960795 + 5438000 * 2 ^ 59
def prefixEnd_5438000 : Nat := 4983230072969 + 3 ^ 40 * 5438000 * 2
def baseEnd_5438000 : Nat := 2792307799149829033691099

theorem tailTrace_5438000 : CollatzResearch.WordTrace tailWord_5438000 prefixEnd_5438000 2792307799149829033691099 := by
  unfold tailWord_5438000
  simp only [CollatzResearch.WordTrace]
  refine ⟨99170077149531105652311727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132226769532708140869748969 99170077149531105652311727)
  ·
    refine ⟨148755115724296658478467591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99170077149531105652311727 148755115724296658478467591)
    ·
      refine ⟨223132673586444987717701387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148755115724296658478467591 223132673586444987717701387)
      ·
        refine ⟨334699010379667481576552081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223132673586444987717701387 334699010379667481576552081)
        ·
          refine ⟨251024257784750611182414061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 334699010379667481576552081 251024257784750611182414061)
          ·
            refine ⟨94134096669281479193405273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 251024257784750611182414061 94134096669281479193405273)
            ·
              refine ⟨70600572501961109395053955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94134096669281479193405273 70600572501961109395053955)
              ·
                refine ⟨105900858752941664092580933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70600572501961109395053955 105900858752941664092580933)
                ·
                  refine ⟨19856411016176562017358925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105900858752941664092580933 19856411016176562017358925)
                  ·
                    refine ⟨7446154131066210756509597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19856411016176562017358925 7446154131066210756509597)
                    ·
                      refine ⟨2792307799149829033691099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7446154131066210756509597 2792307799149829033691099)
                      ·
                        rfl

theorem cell23_5438000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 3].length) (baseStart_5438000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438000 prefixEnd_5438000 := by exact prefixLift 5438000
  have htrace : WordTrace (prefixWord ++ tailWord_5438000) baseStart_5438000 baseEnd_5438000 := by
    simpa [prefixWord, tailWord_5438000, baseEnd_5438000] using wordTrace_append hprefix tailTrace_5438000
  have hstable : (prefixWord ++ tailWord_5438000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438000).length < 2 ^ (prefixWord ++ tailWord_5438000).sum := by decide
  have hdescent : baseEnd_5438000 < baseStart_5438000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438040 : List Nat := [2, 1, 2, 2, 1, 2, 2, 3, 1, 3, 4]
def baseStart_5438040 : Nat := 118140960795 + 5438040 * 2 ^ 59
def prefixEnd_5438040 : Nat := 4983230072969 + 3 ^ 40 * 5438040 * 2
def baseEnd_5438040 : Nat := 2792328338376008877190915

theorem tailTrace_5438040 : CollatzResearch.WordTrace tailWord_5438040 prefixEnd_5438040 2792328338376008877190915 := by
  unfold tailWord_5438040
  simp only [CollatzResearch.WordTrace]
  refine ⟨99170806609458649068039787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132227742145944865424053049 99170806609458649068039787)
  ·
    refine ⟨148756209914187973602059681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99170806609458649068039787 148756209914187973602059681)
    ·
      refine ⟨111567157435640980201544761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148756209914187973602059681 111567157435640980201544761)
      ·
        refine ⟨83675368076730735151158571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111567157435640980201544761 83675368076730735151158571)
        ·
          refine ⟨125513052115096102726737857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83675368076730735151158571 125513052115096102726737857)
          ·
            refine ⟨94134789086322077045053393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125513052115096102726737857 94134789086322077045053393)
            ·
              refine ⟨70601091814741557783790045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94134789086322077045053393 70601091814741557783790045)
              ·
                refine ⟨26475409430528084168921267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70601091814741557783790045 26475409430528084168921267)
                ·
                  refine ⟨39713114145792126253381901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26475409430528084168921267 39713114145792126253381901)
                  ·
                    refine ⟨14892417804672047345018213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39713114145792126253381901 14892417804672047345018213)
                    ·
                      refine ⟨2792328338376008877190915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14892417804672047345018213 2792328338376008877190915)
                      ·
                        rfl

theorem cell23_5438040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_5438040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438040 prefixEnd_5438040 := by exact prefixLift 5438040
  have htrace : WordTrace (prefixWord ++ tailWord_5438040) baseStart_5438040 baseEnd_5438040 := by
    simpa [prefixWord, tailWord_5438040, baseEnd_5438040] using wordTrace_append hprefix tailTrace_5438040
  have hstable : (prefixWord ++ tailWord_5438040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438040).length < 2 ^ (prefixWord ++ tailWord_5438040).sum := by decide
  have hdescent : baseEnd_5438040 < baseStart_5438040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438057 : List Nat := [1, 2, 1, 1, 1, 4, 1, 4, 2, 4, 2]
def baseStart_5438057 : Nat := 118140960795 + 5438057 * 2 ^ 59
def prefixEnd_5438057 : Nat := 4983230072969 + 3 ^ 40 * 5438057 * 2
def baseEnd_5438057 : Nat := 2792337067547135310678337

theorem tailTrace_5438057 : CollatzResearch.WordTrace tailWord_5438057 prefixEnd_5438057 2792337067547135310678337 := by
  unfold tailWord_5438057
  simp only [CollatzResearch.WordTrace]
  refine ⟨198342233259855710039448425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132228155506570473359632283 198342233259855710039448425)
  ·
    refine ⟨148756674944891782529586319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198342233259855710039448425 148756674944891782529586319)
    ·
      refine ⟨223135012417337673794379479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148756674944891782529586319 223135012417337673794379479)
      ·
        refine ⟨334702518626006510691569219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223135012417337673794379479 334702518626006510691569219)
        ·
          refine ⟨502053777939009766037353829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334702518626006510691569219 502053777939009766037353829)
          ·
            refine ⟨94135083363564331132003843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 502053777939009766037353829 94135083363564331132003843)
            ·
              refine ⟨141202625045346496698005765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94135083363564331132003843 141202625045346496698005765)
              ·
                refine ⟨26475492196002468130876081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 141202625045346496698005765 26475492196002468130876081)
                ·
                  refine ⟨19856619147001851098157061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26475492196002468130876081 19856619147001851098157061)
                  ·
                    refine ⟨3723116090062847080904449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19856619147001851098157061 3723116090062847080904449)
                    ·
                      refine ⟨2792337067547135310678337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3723116090062847080904449 2792337067547135310678337)
                      ·
                        rfl

theorem cell23_5438057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 4, 2].length) (baseStart_5438057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438057 prefixEnd_5438057 := by exact prefixLift 5438057
  have htrace : WordTrace (prefixWord ++ tailWord_5438057) baseStart_5438057 baseEnd_5438057 := by
    simpa [prefixWord, tailWord_5438057, baseEnd_5438057] using wordTrace_append hprefix tailTrace_5438057
  have hstable : (prefixWord ++ tailWord_5438057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438057).length < 2 ^ (prefixWord ++ tailWord_5438057).sum := by decide
  have hdescent : baseEnd_5438057 < baseStart_5438057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438084 : List Nat := [2, 3, 2, 1, 3, 2, 1, 2, 3, 4]
def baseStart_5438084 : Nat := 118140960795 + 5438084 * 2 ^ 59
def prefixEnd_5438084 : Nat := 4983230072969 + 3 ^ 40 * 5438084 * 2
def baseEnd_5438084 : Nat := 930783643841602235013571

theorem tailTrace_5438084 : CollatzResearch.WordTrace tailWord_5438084 prefixEnd_5438084 930783643841602235013571 := by
  unfold tailWord_5438084
  simp only [CollatzResearch.WordTrace]
  refine ⟨99171609015378946825340653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132228812020505262433787537 99171609015378946825340653)
  ·
    refine ⟨37189353380767105059502745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99171609015378946825340653 37189353380767105059502745)
    ·
      refine ⟨27892015035575328794627059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37189353380767105059502745 27892015035575328794627059)
      ·
        refine ⟨41838022553362993191940589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27892015035575328794627059 41838022553362993191940589)
        ·
          refine ⟨15689258457511122446977721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41838022553362993191940589 15689258457511122446977721)
          ·
            refine ⟨11766943843133341835233291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15689258457511122446977721 11766943843133341835233291)
            ·
              refine ⟨17650415764700012752849937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11766943843133341835233291 17650415764700012752849937)
              ·
                refine ⟨13237811823525009564637453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17650415764700012752849937 13237811823525009564637453)
                ·
                  refine ⟨4964179433821878586739045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13237811823525009564637453 4964179433821878586739045)
                  ·
                    refine ⟨930783643841602235013571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4964179433821878586739045 930783643841602235013571)
                    ·
                      rfl

theorem cell23_5438084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_5438084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438084 prefixEnd_5438084 := by exact prefixLift 5438084
  have htrace : WordTrace (prefixWord ++ tailWord_5438084) baseStart_5438084 baseEnd_5438084 := by
    simpa [prefixWord, tailWord_5438084, baseEnd_5438084] using wordTrace_append hprefix tailTrace_5438084
  have hstable : (prefixWord ++ tailWord_5438084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438084).length < 2 ^ (prefixWord ++ tailWord_5438084).sum := by decide
  have hdescent : baseEnd_5438084 < baseStart_5438084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438144 : List Nat := [2, 1, 1, 2, 4, 3, 2, 2, 1, 5]
def baseStart_5438144 : Nat := 118140960795 + 5438144 * 2 ^ 59
def prefixEnd_5438144 : Nat := 4983230072969 + 3 ^ 40 * 5438144 * 2
def baseEnd_5438144 : Nat := 930793913454692156763479

theorem tailTrace_5438144 : CollatzResearch.WordTrace tailWord_5438144 prefixEnd_5438144 930793913454692156763479 := by
  unfold tailWord_5438144
  simp only [CollatzResearch.WordTrace]
  refine ⟨99172703205270261948932743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132230270940360349265243657 99172703205270261948932743)
  ·
    refine ⟨148759054807905392923399115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99172703205270261948932743 148759054807905392923399115)
    ·
      refine ⟨223138582211858089385098673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148759054807905392923399115 223138582211858089385098673)
      ·
        refine ⟨167353936658893567038824005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223138582211858089385098673 167353936658893567038824005)
        ·
          refine ⟨31378863123542543819779501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 167353936658893567038824005 31378863123542543819779501)
          ·
            refine ⟨11767073671328453932417313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31378863123542543819779501 11767073671328453932417313)
            ·
              refine ⟨8825305253496340449312985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11767073671328453932417313 8825305253496340449312985)
              ·
                refine ⟨6618978940122255336984739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8825305253496340449312985 6618978940122255336984739)
                ·
                  refine ⟨9928468410183383005477109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6618978940122255336984739 9928468410183383005477109)
                  ·
                    refine ⟨930793913454692156763479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9928468410183383005477109 930793913454692156763479)
                    ·
                      rfl

theorem cell23_5438144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 1, 5].length) (baseStart_5438144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438144 prefixEnd_5438144 := by exact prefixLift 5438144
  have htrace : WordTrace (prefixWord ++ tailWord_5438144) baseStart_5438144 baseEnd_5438144 := by
    simpa [prefixWord, tailWord_5438144, baseEnd_5438144] using wordTrace_append hprefix tailTrace_5438144
  have hstable : (prefixWord ++ tailWord_5438144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438144).length < 2 ^ (prefixWord ++ tailWord_5438144).sum := by decide
  have hdescent : baseEnd_5438144 < baseStart_5438144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438158 : List Nat := [4, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3]
def baseStart_5438158 : Nat := 118140960795 + 5438158 * 2 ^ 59
def prefixEnd_5438158 : Nat := 4983230072969 + 3 ^ 40 * 5438158 * 2
def baseEnd_5438158 : Nat := 2792388929093239415515373

theorem tailTrace_5438158 : CollatzResearch.WordTrace tailWord_5438158 prefixEnd_5438158 2792388929093239415515373 := by
  unfold tailWord_5438158
  simp only [CollatzResearch.WordTrace]
  refine ⟨24793239629061225536109391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132230611354993202859250085 24793239629061225536109391)
  ·
    refine ⟨37189859443591838304164087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24793239629061225536109391 37189859443591838304164087)
    ·
      refine ⟨55784789165387757456246131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37189859443591838304164087 55784789165387757456246131)
      ·
        refine ⟨83677183748081636184369197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55784789165387757456246131 83677183748081636184369197)
        ·
          refine ⟨31378943905530613569138449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83677183748081636184369197 31378943905530613569138449)
          ·
            refine ⟨23534207929147960176853837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31378943905530613569138449 23534207929147960176853837)
            ·
              refine ⟨8825327973430485066320189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23534207929147960176853837 8825327973430485066320189)
              ·
                refine ⟨3309497990036431899870071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8825327973430485066320189 3309497990036431899870071)
                ·
                  refine ⟨4964246985054647849805107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3309497990036431899870071 4964246985054647849805107)
                  ·
                    refine ⟨7446370477581971774707661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4964246985054647849805107 7446370477581971774707661)
                    ·
                      refine ⟨2792388929093239415515373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7446370477581971774707661 2792388929093239415515373)
                      ·
                        rfl

theorem cell23_5438158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3].length) (baseStart_5438158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438158 prefixEnd_5438158 := by exact prefixLift 5438158
  have htrace : WordTrace (prefixWord ++ tailWord_5438158) baseStart_5438158 baseEnd_5438158 := by
    simpa [prefixWord, tailWord_5438158, baseEnd_5438158] using wordTrace_append hprefix tailTrace_5438158
  have hstable : (prefixWord ++ tailWord_5438158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438158).length < 2 ^ (prefixWord ++ tailWord_5438158).sum := by decide
  have hdescent : baseEnd_5438158 < baseStart_5438158 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438167 : List Nat := [1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 5]
def baseStart_5438167 : Nat := 118140960795 + 5438167 * 2 ^ 59
def prefixEnd_5438167 : Nat := 4983230072969 + 3 ^ 40 * 5438167 * 2
def baseEnd_5438167 : Nat := 2792393550419129880302831

theorem tailTrace_5438167 : CollatzResearch.WordTrace tailWord_5438167 prefixEnd_5438167 2792393550419129880302831 := by
  unfold tailWord_5438167
  simp only [CollatzResearch.WordTrace]
  refine ⟨198346245289457198825952755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132230830192971465883968503 198346245289457198825952755)
  ·
    refine ⟨297519367934185798238929133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198346245289457198825952755 297519367934185798238929133)
    ·
      refine ⟨111569762975319674339598425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 297519367934185798238929133 111569762975319674339598425)
      ·
        refine ⟨83677322231489755754698819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111569762975319674339598425 83677322231489755754698819)
        ·
          refine ⟨125515983347234633632048229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83677322231489755754698819 125515983347234633632048229)
          ·
            refine ⟨23534246877606493806009043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125515983347234633632048229 23534246877606493806009043)
            ·
              refine ⟨35301370316409740709013565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23534246877606493806009043 35301370316409740709013565)
              ·
                refine ⟨13238013868653652765880087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35301370316409740709013565 13238013868653652765880087)
                ·
                  refine ⟨19857020802980479148820131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13238013868653652765880087 19857020802980479148820131)
                  ·
                    refine ⟨29785531204470718723230197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19857020802980479148820131 29785531204470718723230197)
                    ·
                      refine ⟨2792393550419129880302831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29785531204470718723230197 2792393550419129880302831)
                      ·
                        rfl

theorem cell23_5438167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_5438167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438167 prefixEnd_5438167 := by exact prefixLift 5438167
  have htrace : WordTrace (prefixWord ++ tailWord_5438167) baseStart_5438167 baseEnd_5438167 := by
    simpa [prefixWord, tailWord_5438167, baseEnd_5438167] using wordTrace_append hprefix tailTrace_5438167
  have hstable : (prefixWord ++ tailWord_5438167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438167).length < 2 ^ (prefixWord ++ tailWord_5438167).sum := by decide
  have hdescent : baseEnd_5438167 < baseStart_5438167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438177 : List Nat := [1, 2, 3, 1, 4, 1, 1, 2, 1, 1, 6]
def baseStart_5438177 : Nat := 118140960795 + 5438177 * 2 ^ 59
def prefixEnd_5438177 : Nat := 4983230072969 + 3 ^ 40 * 5438177 * 2
def baseEnd_5438177 : Nat := 2792398685225674841177785

theorem tailTrace_5438177 : CollatzResearch.WordTrace tailWord_5438177 prefixEnd_5438177 2792398685225674841177785 := by
  unfold tailWord_5438177
  simp only [CollatzResearch.WordTrace]
  refine ⟨198346610019420970533816785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132231073346280647022544523 198346610019420970533816785)
  ·
    refine ⟨148759957514565727900362589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198346610019420970533816785 148759957514565727900362589)
    ·
      refine ⟨55784984067962147962635971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148759957514565727900362589 55784984067962147962635971)
      ·
        refine ⟨83677476101943221943953957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55784984067962147962635971 83677476101943221943953957)
        ·
          refine ⟨15689526769114354114491367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83677476101943221943953957 15689526769114354114491367)
          ·
            refine ⟨23534290153671531171737051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15689526769114354114491367 23534290153671531171737051)
            ·
              refine ⟨35301435230507296757605577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23534290153671531171737051 35301435230507296757605577)
              ·
                refine ⟨26476076422880472568204183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35301435230507296757605577 26476076422880472568204183)
                ·
                  refine ⟨39714114634320708852306275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26476076422880472568204183 39714114634320708852306275)
                  ·
                    refine ⟨59571171951481063278459413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39714114634320708852306275 59571171951481063278459413)
                    ·
                      refine ⟨2792398685225674841177785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59571171951481063278459413 2792398685225674841177785)
                      ·
                        rfl

theorem cell23_5438177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_5438177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438177 prefixEnd_5438177 := by exact prefixLift 5438177
  have htrace : WordTrace (prefixWord ++ tailWord_5438177) baseStart_5438177 baseEnd_5438177 := by
    simpa [prefixWord, tailWord_5438177, baseEnd_5438177] using wordTrace_append hprefix tailTrace_5438177
  have hstable : (prefixWord ++ tailWord_5438177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438177).length < 2 ^ (prefixWord ++ tailWord_5438177).sum := by decide
  have hdescent : baseEnd_5438177 < baseStart_5438177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438191 : List Nat := [1, 1, 2, 1, 5, 2, 4, 1, 2, 4]
def baseStart_5438191 : Nat := 118140960795 + 5438191 * 2 ^ 59
def prefixEnd_5438191 : Nat := 4983230072969 + 3 ^ 40 * 5438191 * 2
def baseEnd_5438191 : Nat := 930801957984945928800907

theorem tailTrace_5438191 : CollatzResearch.WordTrace tailWord_5438191 prefixEnd_5438191 930801957984945928800907 := by
  unfold tailWord_5438191
  simp only [CollatzResearch.WordTrace]
  refine ⟨198347120641370250924826427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132231413760913500616550951 198347120641370250924826427)
  ·
    refine ⟨297520680962055376387239641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198347120641370250924826427 297520680962055376387239641)
    ·
      refine ⟨223140510721541532290429731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297520680962055376387239641 223140510721541532290429731)
      ·
        refine ⟨334710766082312298435644597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223140510721541532290429731 334710766082312298435644597)
        ·
          refine ⟨31379134320216777978341681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 334710766082312298435644597 31379134320216777978341681)
          ·
            refine ⟨23534350740162583483756261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31379134320216777978341681 23534350740162583483756261)
            ·
              refine ⟨4412690763780484403204299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23534350740162583483756261 4412690763780484403204299)
              ·
                refine ⟨6619036145670726604806449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4412690763780484403204299 6619036145670726604806449)
                ·
                  refine ⟨4964277109253044953604837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6619036145670726604806449 4964277109253044953604837)
                  ·
                    refine ⟨930801957984945928800907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4964277109253044953604837 930801957984945928800907)
                    ·
                      rfl

theorem cell23_5438191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 2, 4].length) (baseStart_5438191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438191 prefixEnd_5438191 := by exact prefixLift 5438191
  have htrace : WordTrace (prefixWord ++ tailWord_5438191) baseStart_5438191 baseEnd_5438191 := by
    simpa [prefixWord, tailWord_5438191, baseEnd_5438191] using wordTrace_append hprefix tailTrace_5438191
  have hstable : (prefixWord ++ tailWord_5438191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438191).length < 2 ^ (prefixWord ++ tailWord_5438191).sum := by decide
  have hdescent : baseEnd_5438191 < baseStart_5438191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438271 : List Nat := [1, 1, 2, 2, 5, 1, 2, 2, 1, 4, 2]
def baseStart_5438271 : Nat := 118140960795 + 5438271 * 2 ^ 59
def prefixEnd_5438271 : Nat := 4983230072969 + 3 ^ 40 * 5438271 * 2
def baseEnd_5438271 : Nat := 2792446952407197473402353

theorem tailTrace_5438271 : CollatzResearch.WordTrace tailWord_5438271 prefixEnd_5438271 2792446952407197473402353 := by
  unfold tailWord_5438271
  simp only [CollatzResearch.WordTrace]
  refine ⟨198350038481080424587738667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132233358987386949725159111 198350038481080424587738667)
  ·
    refine ⟨297525057721620636881608001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198350038481080424587738667 297525057721620636881608001)
    ·
      refine ⟨223143793291215477661206001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297525057721620636881608001 223143793291215477661206001)
      ·
        refine ⟨167357844968411608245904501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223143793291215477661206001 167357844968411608245904501)
        ·
          refine ⟨15689797965788588273053547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 167357844968411608245904501 15689797965788588273053547)
          ·
            refine ⟨23534696948682882409580321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15689797965788588273053547 23534696948682882409580321)
            ·
              refine ⟨17651022711512161807185241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23534696948682882409580321 17651022711512161807185241)
              ·
                refine ⟨13238267033634121355388931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17651022711512161807185241 13238267033634121355388931)
                ·
                  refine ⟨19857400550451182033083397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13238267033634121355388931 19857400550451182033083397)
                  ·
                    refine ⟨3723262603209596631203137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19857400550451182033083397 3723262603209596631203137)
                    ·
                      refine ⟨2792446952407197473402353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3723262603209596631203137 2792446952407197473402353)
                      ·
                        rfl

theorem cell23_5438271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 4, 2].length) (baseStart_5438271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438271 prefixEnd_5438271 := by exact prefixLift 5438271
  have htrace : WordTrace (prefixWord ++ tailWord_5438271) baseStart_5438271 baseEnd_5438271 := by
    simpa [prefixWord, tailWord_5438271, baseEnd_5438271] using wordTrace_append hprefix tailTrace_5438271
  have hstable : (prefixWord ++ tailWord_5438271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438271).length < 2 ^ (prefixWord ++ tailWord_5438271).sum := by decide
  have hdescent : baseEnd_5438271 < baseStart_5438271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438284 : List Nat := [2, 2, 1, 3, 3, 1, 1, 2, 2, 2, 4]
def baseStart_5438284 : Nat := 118140960795 + 5438284 * 2 ^ 59
def prefixEnd_5438284 : Nat := 4983230072969 + 3 ^ 40 * 5438284 * 2
def baseEnd_5438284 : Nat := 2792453627655705922539793

theorem tailTrace_5438284 : CollatzResearch.WordTrace tailWord_5438284 prefixEnd_5438284 2792453627655705922539793 := by
  unfold tailWord_5438284
  simp only [CollatzResearch.WordTrace]
  refine ⟨99175256315016663903980953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132233675086688885205307937 99175256315016663903980953)
  ·
    refine ⟨74381442236262497927985715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99175256315016663903980953 74381442236262497927985715)
    ·
      refine ⟨111572163354393746891978573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74381442236262497927985715 111572163354393746891978573)
      ·
        refine ⟨41839561257897655084491965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111572163354393746891978573 41839561257897655084491965)
        ·
          refine ⟨15689835471711620656684487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41839561257897655084491965 15689835471711620656684487)
          ·
            refine ⟨23534753207567430985026731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15689835471711620656684487 23534753207567430985026731)
            ·
              refine ⟨35302129811351146477540097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23534753207567430985026731 35302129811351146477540097)
              ·
                refine ⟨26476597358513359858155073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35302129811351146477540097 26476597358513359858155073)
                ·
                  refine ⟨19857448018885019893616305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26476597358513359858155073 19857448018885019893616305)
                  ·
                    refine ⟨14893086014163764920212229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19857448018885019893616305 14893086014163764920212229)
                    ·
                      refine ⟨2792453627655705922539793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14893086014163764920212229 2792453627655705922539793)
                      ·
                        rfl

theorem cell23_5438284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_5438284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438284 prefixEnd_5438284 := by exact prefixLift 5438284
  have htrace : WordTrace (prefixWord ++ tailWord_5438284) baseStart_5438284 baseEnd_5438284 := by
    simpa [prefixWord, tailWord_5438284, baseEnd_5438284] using wordTrace_append hprefix tailTrace_5438284
  have hstable : (prefixWord ++ tailWord_5438284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438284).length < 2 ^ (prefixWord ++ tailWord_5438284).sum := by decide
  have hdescent : baseEnd_5438284 < baseStart_5438284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438288 : List Nat := [2, 1, 1, 1, 1, 4, 5, 2, 2, 2, 2]
def baseStart_5438288 : Nat := 118140960795 + 5438288 * 2 ^ 59
def prefixEnd_5438288 : Nat := 4983230072969 + 3 ^ 40 * 5438288 * 2
def baseEnd_5438288 : Nat := 2792455681578323906889775

theorem tailTrace_5438288 : CollatzResearch.WordTrace tailWord_5438288 prefixEnd_5438288 2792455681578323906889775 := by
  unfold tailWord_5438288
  simp only [CollatzResearch.WordTrace]
  refine ⟨99175329261009418245553759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132233772348012557660738345 99175329261009418245553759)
  ·
    refine ⟨148762993891514127368330639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99175329261009418245553759 148762993891514127368330639)
    ·
      refine ⟨223144490837271191052495959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148762993891514127368330639 223144490837271191052495959)
      ·
        refine ⟨334716736255906786578743939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223144490837271191052495959 334716736255906786578743939)
        ·
          refine ⟨502075104383860179868115909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334716736255906786578743939 502075104383860179868115909)
          ·
            refine ⟨94139082071973783725271733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 502075104383860179868115909 94139082071973783725271733)
            ·
              refine ⟨8825538944247542224244225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94139082071973783725271733 8825538944247542224244225)
              ·
                refine ⟨6619154208185656668183169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8825538944247542224244225 6619154208185656668183169)
                ·
                  refine ⟨4964365656139242501137377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6619154208185656668183169 4964365656139242501137377)
                  ·
                    refine ⟨3723274242104431875853033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4964365656139242501137377 3723274242104431875853033)
                    ·
                      refine ⟨2792455681578323906889775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3723274242104431875853033 2792455681578323906889775)
                      ·
                        rfl

theorem cell23_5438288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 2, 2, 2].length) (baseStart_5438288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438288 prefixEnd_5438288 := by exact prefixLift 5438288
  have htrace : WordTrace (prefixWord ++ tailWord_5438288) baseStart_5438288 baseEnd_5438288 := by
    simpa [prefixWord, tailWord_5438288, baseEnd_5438288] using wordTrace_append hprefix tailTrace_5438288
  have hstable : (prefixWord ++ tailWord_5438288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438288).length < 2 ^ (prefixWord ++ tailWord_5438288).sum := by decide
  have hdescent : baseEnd_5438288 < baseStart_5438288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438304 : List Nat := [2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 3]
def baseStart_5438304 : Nat := 118140960795 + 5438304 * 2 ^ 59
def prefixEnd_5438304 : Nat := 4983230072969 + 3 ^ 40 * 5438304 * 2
def baseEnd_5438304 : Nat := 2792463897268795844289701

theorem tailTrace_5438304 : CollatzResearch.WordTrace tailWord_5438304 prefixEnd_5438304 2792463897268795844289701 := by
  unfold tailWord_5438304
  simp only [CollatzResearch.WordTrace]
  refine ⟨99175621044980435611844983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132234161393307247482459977 99175621044980435611844983)
  ·
    refine ⟨148763431567470653417767475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99175621044980435611844983 148763431567470653417767475)
    ·
      refine ⟨223145147351205980126651213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148763431567470653417767475 223145147351205980126651213)
      ·
        refine ⟨83679430256702242547494205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223145147351205980126651213 83679430256702242547494205)
        ·
          refine ⟨31379786346263340955310327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83679430256702242547494205 31379786346263340955310327)
          ·
            refine ⟨47069679519395011432965491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31379786346263340955310327 47069679519395011432965491)
            ·
              refine ⟨70604519279092517149448237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47069679519395011432965491 70604519279092517149448237)
              ·
                refine ⟨26476694729659693931043089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70604519279092517149448237 26476694729659693931043089)
                ·
                  refine ⟨19857521047244770448282317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26476694729659693931043089 19857521047244770448282317)
                  ·
                    refine ⟨7446570392716788918105869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19857521047244770448282317 7446570392716788918105869)
                    ·
                      refine ⟨2792463897268795844289701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7446570392716788918105869 2792463897268795844289701)
                      ·
                        rfl

theorem cell23_5438304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_5438304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438304 prefixEnd_5438304 := by exact prefixLift 5438304
  have htrace : WordTrace (prefixWord ++ tailWord_5438304) baseStart_5438304 baseEnd_5438304 := by
    simpa [prefixWord, tailWord_5438304, baseEnd_5438304] using wordTrace_append hprefix tailTrace_5438304
  have hstable : (prefixWord ++ tailWord_5438304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438304).length < 2 ^ (prefixWord ++ tailWord_5438304).sum := by decide
  have hdescent : baseEnd_5438304 < baseStart_5438304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438452 : List Nat := [2, 6, 2, 1, 1, 1, 1, 1, 8]
def baseStart_5438452 : Nat := 118140960795 + 5438452 * 2 ^ 59
def prefixEnd_5438452 : Nat := 4983230072969 + 3 ^ 40 * 5438452 * 2
def baseEnd_5438452 : Nat := 310282210267295696137669

theorem tailTrace_5438452 : CollatzResearch.WordTrace tailWord_5438452 prefixEnd_5438452 310282210267295696137669 := by
  unfold tailWord_5438452
  simp only [CollatzResearch.WordTrace]
  refine ⟨99178320046712346250038805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132237760062283128333385073 99178320046712346250038805)
  ·
    refine ⟨4648983752189641230470569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 99178320046712346250038805 4648983752189641230470569)
    ·
      refine ⟨3486737814142230922852927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4648983752189641230470569 3486737814142230922852927)
      ·
        refine ⟨5230106721213346384279391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3486737814142230922852927 5230106721213346384279391)
        ·
          refine ⟨7845160081820019576419087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5230106721213346384279391 7845160081820019576419087)
          ·
            refine ⟨11767740122730029364628631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7845160081820019576419087 11767740122730029364628631)
            ·
              refine ⟨17651610184095044046942947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11767740122730029364628631 17651610184095044046942947)
              ·
                refine ⟨26477415276142566070414421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17651610184095044046942947 26477415276142566070414421)
                ·
                  refine ⟨310282210267295696137669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26477415276142566070414421 310282210267295696137669)
                  ·
                    rfl

theorem cell23_5438452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_5438452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438452 prefixEnd_5438452 := by exact prefixLift 5438452
  have htrace : WordTrace (prefixWord ++ tailWord_5438452) baseStart_5438452 baseEnd_5438452 := by
    simpa [prefixWord, tailWord_5438452, baseEnd_5438452] using wordTrace_append hprefix tailTrace_5438452
  have hstable : (prefixWord ++ tailWord_5438452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438452).length < 2 ^ (prefixWord ++ tailWord_5438452).sum := by decide
  have hdescent : baseEnd_5438452 < baseStart_5438452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438462 : List Nat := [4, 2, 2, 2, 2, 1, 2, 1, 3, 1, 3]
def baseStart_5438462 : Nat := 118140960795 + 5438462 * 2 ^ 59
def prefixEnd_5438462 : Nat := 4983230072969 + 3 ^ 40 * 5438462 * 2
def baseEnd_5438462 : Nat := 2792545027212206226113975

theorem tailTrace_5438462 : CollatzResearch.WordTrace tailWord_5438462 prefixEnd_5438462 2792545027212206226113975 := by
  unfold tailWord_5438462
  simp only [CollatzResearch.WordTrace]
  refine ⟨24794625602923558025992705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132238003215592309471961093 24794625602923558025992705)
  ·
    refine ⟨18595969202192668519494529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24794625602923558025992705 18595969202192668519494529)
    ·
      refine ⟨13946976901644501389620897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18595969202192668519494529 13946976901644501389620897)
      ·
        refine ⟨10460232676233376042215673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13946976901644501389620897 10460232676233376042215673)
        ·
          refine ⟨7845174507175032031661755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10460232676233376042215673 7845174507175032031661755)
          ·
            refine ⟨11767761760762548047492633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7845174507175032031661755 11767761760762548047492633)
            ·
              refine ⟨8825821320571911035619475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11767761760762548047492633 8825821320571911035619475)
              ·
                refine ⟨13238731980857866553429213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8825821320571911035619475 13238731980857866553429213)
                ·
                  refine ⟨4964524492821699957535955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13238731980857866553429213 4964524492821699957535955)
                  ·
                    refine ⟨7446786739232549936303933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4964524492821699957535955 7446786739232549936303933)
                    ·
                      refine ⟨2792545027212206226113975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7446786739232549936303933 2792545027212206226113975)
                      ·
                        rfl

theorem cell23_5438462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_5438462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438462 prefixEnd_5438462 := by exact prefixLift 5438462
  have htrace : WordTrace (prefixWord ++ tailWord_5438462) baseStart_5438462 baseEnd_5438462 := by
    simpa [prefixWord, tailWord_5438462, baseEnd_5438462] using wordTrace_append hprefix tailTrace_5438462
  have hstable : (prefixWord ++ tailWord_5438462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438462).length < 2 ^ (prefixWord ++ tailWord_5438462).sum := by decide
  have hdescent : baseEnd_5438462 < baseStart_5438462 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438471 : List Nat := [1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 5]
def baseStart_5438471 : Nat := 118140960795 + 5438471 * 2 ^ 59
def prefixEnd_5438471 : Nat := 4983230072969 + 3 ^ 40 * 5438471 * 2
def baseEnd_5438471 : Nat := 2792549648538096690901433

theorem tailTrace_5438471 : CollatzResearch.WordTrace tailWord_5438471 prefixEnd_5438471 2792549648538096690901433 := by
  unfold tailWord_5438471
  simp only [CollatzResearch.WordTrace]
  refine ⟨198357333080355858745019267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132238222053570572496679511 198357333080355858745019267)
  ·
    refine ⟨297535999620533788117528901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198357333080355858745019267 297535999620533788117528901)
    ·
      refine ⟨55787999928850085272036669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 297535999620533788117528901 55787999928850085272036669)
      ·
        refine ⟨20920499973318781977013751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55787999928850085272036669 20920499973318781977013751)
        ·
          refine ⟨31380749959978172965520627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20920499973318781977013751 31380749959978172965520627)
          ·
            refine ⟨47071124939967259448280941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31380749959978172965520627 47071124939967259448280941)
            ·
              refine ⟨17651671852487722293105353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47071124939967259448280941 17651671852487722293105353)
              ·
                refine ⟨13238753889365791719829015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17651671852487722293105353 13238753889365791719829015)
                ·
                  refine ⟨19858130834048687579743523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13238753889365791719829015 19858130834048687579743523)
                  ·
                    refine ⟨29787196251073031369615285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19858130834048687579743523 29787196251073031369615285)
                    ·
                      refine ⟨2792549648538096690901433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29787196251073031369615285 2792549648538096690901433)
                      ·
                        rfl

theorem cell23_5438471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_5438471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438471 prefixEnd_5438471 := by exact prefixLift 5438471
  have htrace : WordTrace (prefixWord ++ tailWord_5438471) baseStart_5438471 baseEnd_5438471 := by
    simpa [prefixWord, tailWord_5438471, baseEnd_5438471] using wordTrace_append hprefix tailTrace_5438471
  have hstable : (prefixWord ++ tailWord_5438471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438471).length < 2 ^ (prefixWord ++ tailWord_5438471).sum := by decide
  have hdescent : baseEnd_5438471 < baseStart_5438471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438478 : List Nat := [4, 1, 1, 2, 2, 4, 1, 1, 1, 6]
def baseStart_5438478 : Nat := 118140960795 + 5438478 * 2 ^ 59
def prefixEnd_5438478 : Nat := 4983230072969 + 3 ^ 40 * 5438478 * 2
def baseEnd_5438478 : Nat := 930851080967559387837967

theorem tailTrace_5438478 : CollatzResearch.WordTrace tailWord_5438478 prefixEnd_5438478 930851080967559387837967 := by
  unfold tailWord_5438478
  simp only [CollatzResearch.WordTrace]
  refine ⟨24794698548916312367565511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132238392260886999293682725 24794698548916312367565511)
  ·
    refine ⟨37192047823374468551348267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24794698548916312367565511 37192047823374468551348267)
    ·
      refine ⟨55788071735061702827022401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37192047823374468551348267 55788071735061702827022401)
      ·
        refine ⟨41841053801296277120266801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55788071735061702827022401 41841053801296277120266801)
        ·
          refine ⟨31380790350972207840200101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41841053801296277120266801 31380790350972207840200101)
          ·
            refine ⟨5883898190807288970037519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31380790350972207840200101 5883898190807288970037519)
            ·
              refine ⟨8825847286210933455056279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5883898190807288970037519 8825847286210933455056279)
              ·
                refine ⟨13238770929316400182584419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8825847286210933455056279 13238770929316400182584419)
                ·
                  refine ⟨19858156393974600273876629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13238770929316400182584419 19858156393974600273876629)
                  ·
                    refine ⟨930851080967559387837967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19858156393974600273876629 930851080967559387837967)
                    ·
                      rfl

theorem cell23_5438478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_5438478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438478 prefixEnd_5438478 := by exact prefixLift 5438478
  have htrace : WordTrace (prefixWord ++ tailWord_5438478) baseStart_5438478 baseEnd_5438478 := by
    simpa [prefixWord, tailWord_5438478, baseEnd_5438478] using wordTrace_append hprefix tailTrace_5438478
  have hstable : (prefixWord ++ tailWord_5438478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438478).length < 2 ^ (prefixWord ++ tailWord_5438478).sum := by decide
  have hdescent : baseEnd_5438478 < baseStart_5438478 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438485 : List Nat := [1, 3, 2, 1, 4, 1, 2, 2, 3, 2, 2]
def baseStart_5438485 : Nat := 118140960795 + 5438485 * 2 ^ 59
def prefixEnd_5438485 : Nat := 4983230072969 + 3 ^ 40 * 5438485 * 2
def baseEnd_5438485 : Nat := 2792556837267259636126369

theorem tailTrace_5438485 : CollatzResearch.WordTrace tailWord_5438485 prefixEnd_5438485 2792556837267259636126369 := by
  unfold tailWord_5438485
  simp only [CollatzResearch.WordTrace]
  refine ⟨198357843702305139136028909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132238562468203426090685939 198357843702305139136028909)
  ·
    refine ⟨74384191388364427176010841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198357843702305139136028909 74384191388364427176010841)
    ·
      refine ⟨55788143541273320382008131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74384191388364427176010841 55788143541273320382008131)
      ·
        refine ⟨83682215311909980573012197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55788143541273320382008131 83682215311909980573012197)
        ·
          refine ⟨15690415370983121357439787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83682215311909980573012197 15690415370983121357439787)
          ·
            refine ⟨23535623056474682036159681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15690415370983121357439787 23535623056474682036159681)
            ·
              refine ⟨17651717292356011527119761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23535623056474682036159681 17651717292356011527119761)
              ·
                refine ⟨13238787969267008645339821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17651717292356011527119761 13238787969267008645339821)
                ·
                  refine ⟨4964545488475128242002433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13238787969267008645339821 4964545488475128242002433)
                  ·
                    refine ⟨3723409116356346181501825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4964545488475128242002433 3723409116356346181501825)
                    ·
                      refine ⟨2792556837267259636126369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3723409116356346181501825 2792556837267259636126369)
                      ·
                        rfl

theorem cell23_5438485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 3, 2, 2].length) (baseStart_5438485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438485 prefixEnd_5438485 := by exact prefixLift 5438485
  have htrace : WordTrace (prefixWord ++ tailWord_5438485) baseStart_5438485 baseEnd_5438485 := by
    simpa [prefixWord, tailWord_5438485, baseEnd_5438485] using wordTrace_append hprefix tailTrace_5438485
  have hstable : (prefixWord ++ tailWord_5438485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438485).length < 2 ^ (prefixWord ++ tailWord_5438485).sum := by decide
  have hdescent : baseEnd_5438485 < baseStart_5438485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438488 : List Nat := [2, 1, 2, 3, 2, 2, 1, 4, 1, 2, 3]
def baseStart_5438488 : Nat := 118140960795 + 5438488 * 2 ^ 59
def prefixEnd_5438488 : Nat := 4983230072969 + 3 ^ 40 * 5438488 * 2
def baseEnd_5438488 : Nat := 2792558377709223124388855

theorem tailTrace_5438488 : CollatzResearch.WordTrace tailWord_5438488 prefixEnd_5438488 2792558377709223124388855 := by
  unfold tailWord_5438488
  simp only [CollatzResearch.WordTrace]
  refine ⟨99178976560647135324194059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132238635414196180432258745 99178976560647135324194059)
  ·
    refine ⟨148768464840970702986291089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99178976560647135324194059 148768464840970702986291089)
    ·
      refine ⟨111576348630728027239718317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148768464840970702986291089 111576348630728027239718317)
      ·
        refine ⟨41841130736523010214894369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111576348630728027239718317 41841130736523010214894369)
        ·
          refine ⟨31380848052392257661170777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41841130736523010214894369 31380848052392257661170777)
          ·
            refine ⟨23535636039294193245878083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31380848052392257661170777 23535636039294193245878083)
            ·
              refine ⟨35303454058941289868817125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23535636039294193245878083 35303454058941289868817125)
              ·
                refine ⟨6619397636051491850403211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35303454058941289868817125 6619397636051491850403211)
                ·
                  refine ⟨9929096454077237775604817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6619397636051491850403211 9929096454077237775604817)
                  ·
                    refine ⟨7446822340557928331703613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9929096454077237775604817 7446822340557928331703613)
                    ·
                      refine ⟨2792558377709223124388855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7446822340557928331703613 2792558377709223124388855)
                      ·
                        rfl

theorem cell23_5438488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_5438488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438488 prefixEnd_5438488 := by exact prefixLift 5438488
  have htrace : WordTrace (prefixWord ++ tailWord_5438488) baseStart_5438488 baseEnd_5438488 := by
    simpa [prefixWord, tailWord_5438488, baseEnd_5438488] using wordTrace_append hprefix tailTrace_5438488
  have hstable : (prefixWord ++ tailWord_5438488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438488).length < 2 ^ (prefixWord ++ tailWord_5438488).sum := by decide
  have hdescent : baseEnd_5438488 < baseStart_5438488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438496 : List Nat := [2, 1, 1, 7, 2, 1, 1, 3, 1, 1, 3]
def baseStart_5438496 : Nat := 118140960795 + 5438496 * 2 ^ 59
def prefixEnd_5438496 : Nat := 4983230072969 + 3 ^ 40 * 5438496 * 2
def baseEnd_5438496 : Nat := 2792562485554459093088819

theorem tailTrace_5438496 : CollatzResearch.WordTrace tailWord_5438496 prefixEnd_5438496 2792562485554459093088819 := by
  unfold tailWord_5438496
  simp only [CollatzResearch.WordTrace]
  refine ⟨99179122452632644007339671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132238829936843525343119561 99179122452632644007339671)
  ·
    refine ⟨148768683678948966011009507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99179122452632644007339671 148768683678948966011009507)
    ·
      refine ⟨223153025518423449016514261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148768683678948966011009507 223153025518423449016514261)
      ·
        refine ⟨5230149035588049586324553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 223153025518423449016514261 5230149035588049586324553)
        ·
          refine ⟨3922611776691037189743415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5230149035588049586324553 3922611776691037189743415)
          ·
            refine ⟨5883917665036555784615123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3922611776691037189743415 5883917665036555784615123)
            ·
              refine ⟨8825876497554833676922685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5883917665036555784615123 8825876497554833676922685)
              ·
                refine ⟨3309703686583062628846007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8825876497554833676922685 3309703686583062628846007)
                ·
                  refine ⟨4964555529874593943269011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3309703686583062628846007 4964555529874593943269011)
                  ·
                    refine ⟨7446833294811890914903517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4964555529874593943269011 7446833294811890914903517)
                    ·
                      refine ⟨2792562485554459093088819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7446833294811890914903517 2792562485554459093088819)
                      ·
                        rfl

theorem cell23_5438496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_5438496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438496 prefixEnd_5438496 := by exact prefixLift 5438496
  have htrace : WordTrace (prefixWord ++ tailWord_5438496) baseStart_5438496 baseEnd_5438496 := by
    simpa [prefixWord, tailWord_5438496, baseEnd_5438496] using wordTrace_append hprefix tailTrace_5438496
  have hstable : (prefixWord ++ tailWord_5438496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438496).length < 2 ^ (prefixWord ++ tailWord_5438496).sum := by decide
  have hdescent : baseEnd_5438496 < baseStart_5438496 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438501 : List Nat := [1, 3, 1, 2, 2, 2, 2, 1, 3, 3, 3]
def baseStart_5438501 : Nat := 118140960795 + 5438501 * 2 ^ 59
def prefixEnd_5438501 : Nat := 4983230072969 + 3 ^ 40 * 5438501 * 2
def baseEnd_5438501 : Nat := 2792565052957731573526295

theorem tailTrace_5438501 : CollatzResearch.WordTrace tailWord_5438501 prefixEnd_5438501 2792565052957731573526295 := by
  unfold tailWord_5438501
  simp only [CollatzResearch.WordTrace]
  refine ⟨198358427270247173868611357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132238951513498115912407571 198358427270247173868611357)
  ·
    refine ⟨74384410226342690200729259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198358427270247173868611357 74384410226342690200729259)
    ·
      refine ⟨111576615339514035301093889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74384410226342690200729259 111576615339514035301093889)
      ·
        refine ⟨83682461504635526475820417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111576615339514035301093889 83682461504635526475820417)
        ·
          refine ⟨62761846128476644856865313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83682461504635526475820417 62761846128476644856865313)
          ·
            refine ⟨47071384596357483642648985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62761846128476644856865313 47071384596357483642648985)
            ·
              refine ⟨35303538447268112731986739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47071384596357483642648985 35303538447268112731986739)
              ·
                refine ⟨52955307670902169097980109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35303538447268112731986739 52955307670902169097980109)
                ·
                  refine ⟨19858240376588313411742541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52955307670902169097980109 19858240376588313411742541)
                  ·
                    refine ⟨7446840141220617529403453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19858240376588313411742541 7446840141220617529403453)
                    ·
                      refine ⟨2792565052957731573526295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7446840141220617529403453 2792565052957731573526295)
                      ·
                        rfl

theorem cell23_5438501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_5438501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438501 prefixEnd_5438501 := by exact prefixLift 5438501
  have htrace : WordTrace (prefixWord ++ tailWord_5438501) baseStart_5438501 baseEnd_5438501 := by
    simpa [prefixWord, tailWord_5438501, baseEnd_5438501] using wordTrace_append hprefix tailTrace_5438501
  have hstable : (prefixWord ++ tailWord_5438501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438501).length < 2 ^ (prefixWord ++ tailWord_5438501).sum := by decide
  have hdescent : baseEnd_5438501 < baseStart_5438501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438511 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 1, 9, 2]
def baseStart_5438511 : Nat := 118140960795 + 5438511 * 2 ^ 59
def prefixEnd_5438511 : Nat := 4983230072969 + 3 ^ 40 * 5438511 * 2
def baseEnd_5438511 : Nat := 2792570187764276534401249

theorem tailTrace_5438511 : CollatzResearch.WordTrace tailWord_5438511 prefixEnd_5438511 2792570187764276534401249 := by
  unfold tailWord_5438511
  simp only [CollatzResearch.WordTrace]
  refine ⟨198358792000210945576475387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132239194666807297050983591 198358792000210945576475387)
  ·
    refine ⟨297538188000316418364713081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198358792000210945576475387 297538188000316418364713081)
    ·
      refine ⟨223153641000237313773534811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297538188000316418364713081 223153641000237313773534811)
      ·
        refine ⟨334730461500355970660302217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223153641000237313773534811 334730461500355970660302217)
        ·
          refine ⟨251047846125266977995226663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 334730461500355970660302217 251047846125266977995226663)
          ·
            refine ⟨376571769187900466992839995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251047846125266977995226663 376571769187900466992839995)
            ·
              refine ⟨564857653781850700489259993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376571769187900466992839995 564857653781850700489259993)
              ·
                refine ⟨423643240336388025366944995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 564857653781850700489259993 423643240336388025366944995)
                ·
                  refine ⟨635464860504582038050417493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 423643240336388025366944995 635464860504582038050417493)
                  ·
                    refine ⟨3723426917019035379201665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 635464860504582038050417493 3723426917019035379201665)
                    ·
                      refine ⟨2792570187764276534401249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3723426917019035379201665 2792570187764276534401249)
                      ·
                        rfl

theorem cell23_5438511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 9, 2].length) (baseStart_5438511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438511 prefixEnd_5438511 := by exact prefixLift 5438511
  have htrace : WordTrace (prefixWord ++ tailWord_5438511) baseStart_5438511 baseEnd_5438511 := by
    simpa [prefixWord, tailWord_5438511, baseEnd_5438511] using wordTrace_append hprefix tailTrace_5438511
  have hstable : (prefixWord ++ tailWord_5438511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438511).length < 2 ^ (prefixWord ++ tailWord_5438511).sum := by decide
  have hdescent : baseEnd_5438511 < baseStart_5438511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438528 : List Nat := [2, 1, 1, 2, 2, 3, 2, 2, 3, 3, 2]
def baseStart_5438528 : Nat := 118140960795 + 5438528 * 2 ^ 59
def prefixEnd_5438528 : Nat := 4983230072969 + 3 ^ 40 * 5438528 * 2
def baseEnd_5438528 : Nat := 2792578916935402967888671

theorem tailTrace_5438528 : CollatzResearch.WordTrace tailWord_5438528 prefixEnd_5438528 2792578916935402967888671 := by
  unfold tailWord_5438528
  simp only [CollatzResearch.WordTrace]
  refine ⟨99179706020574678739922119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132239608027432904986562825 99179706020574678739922119)
  ·
    refine ⟨148769559030862018109883179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99179706020574678739922119 148769559030862018109883179)
    ·
      refine ⟨223154338546293027164824769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148769559030862018109883179 223154338546293027164824769)
      ·
        refine ⟨167365753909719770373618577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223154338546293027164824769 167365753909719770373618577)
        ·
          refine ⟨125524315432289827780213933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167365753909719770373618577 125524315432289827780213933)
          ·
            refine ⟨47071618287108685417580225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125524315432289827780213933 47071618287108685417580225)
            ·
              refine ⟨35303713715331514063185169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47071618287108685417580225 35303713715331514063185169)
              ·
                refine ⟨26477785286498635547388877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35303713715331514063185169 26477785286498635547388877)
                ·
                  refine ⟨9929169482436988330270829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26477785286498635547388877 9929169482436988330270829)
                  ·
                    refine ⟨3723438555913870623851561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9929169482436988330270829 3723438555913870623851561)
                    ·
                      refine ⟨2792578916935402967888671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3723438555913870623851561 2792578916935402967888671)
                      ·
                        rfl

theorem cell23_5438528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 3, 3, 2].length) (baseStart_5438528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438528 prefixEnd_5438528 := by exact prefixLift 5438528
  have htrace : WordTrace (prefixWord ++ tailWord_5438528) baseStart_5438528 baseEnd_5438528 := by
    simpa [prefixWord, tailWord_5438528, baseEnd_5438528] using wordTrace_append hprefix tailTrace_5438528
  have hstable : (prefixWord ++ tailWord_5438528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438528).length < 2 ^ (prefixWord ++ tailWord_5438528).sum := by decide
  have hdescent : baseEnd_5438528 < baseStart_5438528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438529 : List Nat := [1, 2, 5, 1, 4, 1, 2, 1, 2, 4]
def baseStart_5438529 : Nat := 118140960795 + 5438529 * 2 ^ 59
def prefixEnd_5438529 : Nat := 4983230072969 + 3 ^ 40 * 5438529 * 2
def baseEnd_5438529 : Nat := 930859810138685821325389

theorem tailTrace_5438529 : CollatzResearch.WordTrace tailWord_5438529 prefixEnd_5438529 930859810138685821325389 := by
  unfold tailWord_5438529
  simp only [CollatzResearch.WordTrace]
  refine ⟨198359448514145734650630641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132239632342763823100420427 198359448514145734650630641)
  ·
    refine ⟨148769586385609300987972981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198359448514145734650630641 148769586385609300987972981)
    ·
      refine ⟨13947148723650871967622467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 148769586385609300987972981 13947148723650871967622467)
      ·
        refine ⟨20920723085476307951433701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13947148723650871967622467 20920723085476307951433701)
        ·
          refine ⟨3922635578526807740893819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20920723085476307951433701 3922635578526807740893819)
          ·
            refine ⟨5883953367790211611340729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3922635578526807740893819 5883953367790211611340729)
            ·
              refine ⟨4412965025842658708505547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5883953367790211611340729 4412965025842658708505547)
              ·
                refine ⟨6619447538763988062758321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4412965025842658708505547 6619447538763988062758321)
                ·
                  refine ⟨4964585654072991047068741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6619447538763988062758321 4964585654072991047068741)
                  ·
                    refine ⟨930859810138685821325389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4964585654072991047068741 930859810138685821325389)
                    ·
                      rfl

theorem cell23_5438529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_5438529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438529 prefixEnd_5438529 := by exact prefixLift 5438529
  have htrace : WordTrace (prefixWord ++ tailWord_5438529) baseStart_5438529 baseEnd_5438529 := by
    simpa [prefixWord, tailWord_5438529, baseEnd_5438529] using wordTrace_append hprefix tailTrace_5438529
  have hstable : (prefixWord ++ tailWord_5438529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438529).length < 2 ^ (prefixWord ++ tailWord_5438529).sum := by decide
  have hdescent : baseEnd_5438529 < baseStart_5438529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438535 : List Nat := [1, 1, 4, 1, 3, 3, 1, 3, 2, 1, 3]
def baseStart_5438535 : Nat := 118140960795 + 5438535 * 2 ^ 59
def prefixEnd_5438535 : Nat := 4983230072969 + 3 ^ 40 * 5438535 * 2
def baseEnd_5438535 : Nat := 2792582511299984440501139

theorem tailTrace_5438535 : CollatzResearch.WordTrace tailWord_5438535 prefixEnd_5438535 2792582511299984440501139 := by
  unfold tailWord_5438535
  simp only [CollatzResearch.WordTrace]
  refine ⟨198359667352123997675349059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132239778234749331783566039 198359667352123997675349059)
  ·
    refine ⟨297539501028185996513023589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198359667352123997675349059 297539501028185996513023589)
    ·
      refine ⟨55788656442784874346191923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 297539501028185996513023589 55788656442784874346191923)
      ·
        refine ⟨83682984664177311519287885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55788656442784874346191923 83682984664177311519287885)
        ·
          refine ⟨31381119249066491819732957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83682984664177311519287885 31381119249066491819732957)
          ·
            refine ⟨11767919718399934432399859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31381119249066491819732957 11767919718399934432399859)
            ·
              refine ⟨17651879577599901648599789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11767919718399934432399859 17651879577599901648599789)
              ·
                refine ⟨6619454841599963118224921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17651879577599901648599789 6619454841599963118224921)
                ·
                  refine ⟨4964591131199972338668691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6619454841599963118224921 4964591131199972338668691)
                  ·
                    refine ⟨7446886696799958508003037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4964591131199972338668691 7446886696799958508003037)
                    ·
                      refine ⟨2792582511299984440501139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7446886696799958508003037 2792582511299984440501139)
                      ·
                        rfl

theorem cell23_5438535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 2, 1, 3].length) (baseStart_5438535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438535 prefixEnd_5438535 := by exact prefixLift 5438535
  have htrace : WordTrace (prefixWord ++ tailWord_5438535) baseStart_5438535 baseEnd_5438535 := by
    simpa [prefixWord, tailWord_5438535, baseEnd_5438535] using wordTrace_append hprefix tailTrace_5438535
  have hstable : (prefixWord ++ tailWord_5438535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438535).length < 2 ^ (prefixWord ++ tailWord_5438535).sum := by decide
  have hdescent : baseEnd_5438535 < baseStart_5438535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438545 : List Nat := [1, 2, 2, 1, 3, 1, 5, 2, 1, 3, 2]
def baseStart_5438545 : Nat := 118140960795 + 5438545 * 2 ^ 59
def prefixEnd_5438545 : Nat := 4983230072969 + 3 ^ 40 * 5438545 * 2
def baseEnd_5438545 : Nat := 2792587646106529401376093

theorem tailTrace_5438545 : CollatzResearch.WordTrace tailWord_5438545 prefixEnd_5438545 2792587646106529401376093 := by
  unfold tailWord_5438545
  simp only [CollatzResearch.WordTrace]
  refine ⟨198360032082087769383213089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132240021388058512922142059 198360032082087769383213089)
  ·
    refine ⟨148770024061565827037409817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198360032082087769383213089 148770024061565827037409817)
    ·
      refine ⟨111577518046174370278057363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148770024061565827037409817 111577518046174370278057363)
      ·
        refine ⟨167366277069261555417086045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111577518046174370278057363 167366277069261555417086045)
        ·
          refine ⟨62762353900973083281407267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167366277069261555417086045 62762353900973083281407267)
          ·
            refine ⟨94143530851459624922110901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62762353900973083281407267 94143530851459624922110901)
            ·
              refine ⟨8825956017324339836447897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94143530851459624922110901 8825956017324339836447897)
              ·
                refine ⟨6619467012993254877335923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8825956017324339836447897 6619467012993254877335923)
                ·
                  refine ⟨9929200519489882316003885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6619467012993254877335923 9929200519489882316003885)
                  ·
                    refine ⟨3723450194808705868501457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9929200519489882316003885 3723450194808705868501457)
                    ·
                      refine ⟨2792587646106529401376093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3723450194808705868501457 2792587646106529401376093)
                      ·
                        rfl

theorem cell23_5438545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 3, 2].length) (baseStart_5438545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438545 prefixEnd_5438545 := by exact prefixLift 5438545
  have htrace : WordTrace (prefixWord ++ tailWord_5438545) baseStart_5438545 baseEnd_5438545 := by
    simpa [prefixWord, tailWord_5438545, baseEnd_5438545] using wordTrace_append hprefix tailTrace_5438545
  have hstable : (prefixWord ++ tailWord_5438545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438545).length < 2 ^ (prefixWord ++ tailWord_5438545).sum := by decide
  have hdescent : baseEnd_5438545 < baseStart_5438545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438561 : List Nat := [1, 2, 3, 1, 1, 2, 4, 1, 2, 1, 5]
def baseStart_5438561 : Nat := 118140960795 + 5438561 * 2 ^ 59
def prefixEnd_5438561 : Nat := 4983230072969 + 3 ^ 40 * 5438561 * 2
def baseEnd_5438561 : Nat := 2792595861797001338776019

theorem tailTrace_5438561 : CollatzResearch.WordTrace tailWord_5438561 prefixEnd_5438561 2792595861797001338776019 := by
  unfold tailWord_5438561
  simp only [CollatzResearch.WordTrace]
  refine ⟨198360615650029804115795537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132240410433353202743863691 198360615650029804115795537)
  ·
    refine ⟨148770461737522353086846653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198360615650029804115795537 148770461737522353086846653)
    ·
      refine ⟨55788923151570882407567495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148770461737522353086846653 55788923151570882407567495)
      ·
        refine ⟨83683384727356323611351243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55788923151570882407567495 83683384727356323611351243)
        ·
          refine ⟨125525077091034485417026865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83683384727356323611351243 125525077091034485417026865)
          ·
            refine ⟨94143807818275864062770149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125525077091034485417026865 94143807818275864062770149)
            ·
              refine ⟨17651963965926724511769403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94143807818275864062770149 17651963965926724511769403)
              ·
                refine ⟨26477945948890086767654105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17651963965926724511769403 26477945948890086767654105)
                ·
                  refine ⟨19858459461667565075740579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26477945948890086767654105 19858459461667565075740579)
                  ·
                    refine ⟨29787689192501347613610869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19858459461667565075740579 29787689192501347613610869)
                    ·
                      refine ⟨2792595861797001338776019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29787689192501347613610869 2792595861797001338776019)
                      ·
                        rfl

theorem cell23_5438561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_5438561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438561 prefixEnd_5438561 := by exact prefixLift 5438561
  have htrace : WordTrace (prefixWord ++ tailWord_5438561) baseStart_5438561 baseEnd_5438561 := by
    simpa [prefixWord, tailWord_5438561, baseEnd_5438561] using wordTrace_append hprefix tailTrace_5438561
  have hstable : (prefixWord ++ tailWord_5438561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438561).length < 2 ^ (prefixWord ++ tailWord_5438561).sum := by decide
  have hdescent : baseEnd_5438561 < baseStart_5438561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438615 : List Nat := [1, 1, 3, 3, 3, 2, 2, 3, 5]
def baseStart_5438615 : Nat := 118140960795 + 5438615 * 2 ^ 59
def prefixEnd_5438615 : Nat := 4983230072969 + 3 ^ 40 * 5438615 * 2
def baseEnd_5438615 : Nat := 310291509972482680833419

theorem tailTrace_5438615 : CollatzResearch.WordTrace tailWord_5438615 prefixEnd_5438615 310291509972482680833419 := by
  unfold tailWord_5438615
  simp only [CollatzResearch.WordTrace]
  refine ⟨198362585191834171338261299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132241723461222780892174199 198362585191834171338261299)
  ·
    refine ⟨297543877787751257007391949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198362585191834171338261299 297543877787751257007391949)
    ·
      refine ⟨111578954170406721377771981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 297543877787751257007391949 111578954170406721377771981)
      ·
        refine ⟨41842107813902520516664493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111578954170406721377771981 41842107813902520516664493)
        ·
          refine ⟨15690790430213445193749185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41842107813902520516664493 15690790430213445193749185)
          ·
            refine ⟨11768092822660083895311889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15690790430213445193749185 11768092822660083895311889)
            ·
              refine ⟨8826069616995062921483917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11768092822660083895311889 8826069616995062921483917)
              ·
                refine ⟨3309776106373148595556469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8826069616995062921483917 3309776106373148595556469)
                ·
                  refine ⟨310291509972482680833419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3309776106373148595556469 310291509972482680833419)
                  ·
                    rfl

theorem cell23_5438615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 3, 5].length) (baseStart_5438615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438615 prefixEnd_5438615 := by exact prefixLift 5438615
  have htrace : WordTrace (prefixWord ++ tailWord_5438615) baseStart_5438615 baseEnd_5438615 := by
    simpa [prefixWord, tailWord_5438615, baseEnd_5438615] using wordTrace_append hprefix tailTrace_5438615
  have hstable : (prefixWord ++ tailWord_5438615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438615).length < 2 ^ (prefixWord ++ tailWord_5438615).sum := by decide
  have hdescent : baseEnd_5438615 < baseStart_5438615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438626 : List Nat := [3, 3, 1, 3, 2, 2, 1, 2, 2, 2, 2]
def baseStart_5438626 : Nat := 118140960795 + 5438626 * 2 ^ 59
def prefixEnd_5438626 : Nat := 4983230072969 + 3 ^ 40 * 5438626 * 2
def baseEnd_5438626 : Nat := 2792629238039543584463221

theorem tailTrace_5438626 : CollatzResearch.WordTrace tailWord_5438626 prefixEnd_5438626 2792629238039543584463221 := by
  unfold tailWord_5438626
  simp only [CollatzResearch.WordTrace]
  refine ⟨49590746598698580054227933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132241990929862880144607821 49590746598698580054227933)
  ·
    refine ⟨18596529974511967520335475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49590746598698580054227933 18596529974511967520335475)
    ·
      refine ⟨27894794961767951280503213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18596529974511967520335475 27894794961767951280503213)
      ·
        refine ⟨10460548110662981730188705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27894794961767951280503213 10460548110662981730188705)
        ·
          refine ⟨7845411082997236297641529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10460548110662981730188705 7845411082997236297641529)
          ·
            refine ⟨5884058312247927223231147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7845411082997236297641529 5884058312247927223231147)
            ·
              refine ⟨8826087468371890834846721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5884058312247927223231147 8826087468371890834846721)
              ·
                refine ⟨6619565601278918126135041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8826087468371890834846721 6619565601278918126135041)
                ·
                  refine ⟨4964674200959188594601281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6619565601278918126135041 4964674200959188594601281)
                  ·
                    refine ⟨3723505650719391445950961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4964674200959188594601281 3723505650719391445950961)
                    ·
                      refine ⟨2792629238039543584463221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3723505650719391445950961 2792629238039543584463221)
                      ·
                        rfl

theorem cell23_5438626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_5438626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438626 prefixEnd_5438626 := by exact prefixLift 5438626
  have htrace : WordTrace (prefixWord ++ tailWord_5438626) baseStart_5438626 baseEnd_5438626 := by
    simpa [prefixWord, tailWord_5438626, baseEnd_5438626] using wordTrace_append hprefix tailTrace_5438626
  have hstable : (prefixWord ++ tailWord_5438626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438626).length < 2 ^ (prefixWord ++ tailWord_5438626).sum := by decide
  have hdescent : baseEnd_5438626 < baseStart_5438626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438648 : List Nat := [2, 1, 2, 1, 2, 1, 2, 3, 1, 6, 2]
def baseStart_5438648 : Nat := 118140960795 + 5438648 * 2 ^ 59
def prefixEnd_5438648 : Nat := 4983230072969 + 3 ^ 40 * 5438648 * 2
def baseEnd_5438648 : Nat := 2792640534613942498388119

theorem tailTrace_5438648 : CollatzResearch.WordTrace tailWord_5438648 prefixEnd_5438648 2792640534613942498388119 := by
  unfold tailWord_5438648
  simp only [CollatzResearch.WordTrace]
  refine ⟨99181894400357308987106299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132242525867143078649475065 99181894400357308987106299)
  ·
    refine ⟨148772841600535963480659449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99181894400357308987106299 148772841600535963480659449)
    ·
      refine ⟨111579631200401972610494587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148772841600535963480659449 111579631200401972610494587)
      ·
        refine ⟨167369446800602958915741881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111579631200401972610494587 167369446800602958915741881)
        ·
          refine ⟨125527085100452219186806411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167369446800602958915741881 125527085100452219186806411)
          ·
            refine ⟨188290627650678328780209617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125527085100452219186806411 188290627650678328780209617)
            ·
              refine ⟨141217970738008746585157213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188290627650678328780209617 141217970738008746585157213)
              ·
                refine ⟨52956739026753279969433955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141217970738008746585157213 52956739026753279969433955)
                ·
                  refine ⟨79435108540129919954150933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52956739026753279969433955 79435108540129919954150933)
                  ·
                    refine ⟨3723520712818589997850825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79435108540129919954150933 3723520712818589997850825)
                    ·
                      refine ⟨2792640534613942498388119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3723520712818589997850825 2792640534613942498388119)
                      ·
                        rfl

theorem cell23_5438648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 1, 6, 2].length) (baseStart_5438648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438648 prefixEnd_5438648 := by exact prefixLift 5438648
  have htrace : WordTrace (prefixWord ++ tailWord_5438648) baseStart_5438648 baseEnd_5438648 := by
    simpa [prefixWord, tailWord_5438648, baseEnd_5438648] using wordTrace_append hprefix tailTrace_5438648
  have hstable : (prefixWord ++ tailWord_5438648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438648).length < 2 ^ (prefixWord ++ tailWord_5438648).sum := by decide
  have hdescent : baseEnd_5438648 < baseStart_5438648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438661 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 1, 6, 4]
def baseStart_5438661 : Nat := 118140960795 + 5438661 * 2 ^ 59
def prefixEnd_5438661 : Nat := 4983230072969 + 3 ^ 40 * 5438661 * 2
def baseEnd_5438661 : Nat := 2792647209862450947525559

theorem tailTrace_5438661 : CollatzResearch.WordTrace tailWord_5438661 prefixEnd_5438661 2792647209862450947525559 := by
  unfold tailWord_5438661
  simp only [CollatzResearch.WordTrace]
  refine ⟨198364262949667521194435837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132242841966445014129623891 198364262949667521194435837)
  ·
    refine ⟨74386598606125320447913439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198364262949667521194435837 74386598606125320447913439)
    ·
      refine ⟨111579897909187980671870159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74386598606125320447913439 111579897909187980671870159)
      ·
        refine ⟨167369846863781971007805239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111579897909187980671870159 167369846863781971007805239)
        ·
          refine ⟨251054770295672956511707859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167369846863781971007805239 251054770295672956511707859)
          ·
            refine ⟨376582155443509434767561789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251054770295672956511707859 376582155443509434767561789)
            ·
              refine ⟨141218308291316038037835671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 376582155443509434767561789 141218308291316038037835671)
              ·
                refine ⟨211827462436974057056753507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141218308291316038037835671 211827462436974057056753507)
                ·
                  refine ⟨317741193655461085585130261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 211827462436974057056753507 317741193655461085585130261)
                  ·
                    refine ⟨14894118452599738386802981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 317741193655461085585130261 14894118452599738386802981)
                    ·
                      refine ⟨2792647209862450947525559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14894118452599738386802981 2792647209862450947525559)
                      ·
                        rfl

theorem cell23_5438661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_5438661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438661 prefixEnd_5438661 := by exact prefixLift 5438661
  have htrace : WordTrace (prefixWord ++ tailWord_5438661) baseStart_5438661 baseEnd_5438661 := by
    simpa [prefixWord, tailWord_5438661, baseEnd_5438661] using wordTrace_append hprefix tailTrace_5438661
  have hstable : (prefixWord ++ tailWord_5438661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438661).length < 2 ^ (prefixWord ++ tailWord_5438661).sum := by decide
  have hdescent : baseEnd_5438661 < baseStart_5438661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438711 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 7]
def baseStart_5438711 : Nat := 118140960795 + 5438711 * 2 ^ 59
def prefixEnd_5438711 : Nat := 4983230072969 + 3 ^ 40 * 5438711 * 2
def baseEnd_5438711 : Nat := 2792672883895175751900329

theorem tailTrace_5438711 : CollatzResearch.WordTrace tailWord_5438711 prefixEnd_5438711 2792672883895175751900329 := by
  unfold tailWord_5438711
  simp only [CollatzResearch.WordTrace]
  refine ⟨198366086599486379733755987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132244057732990919822503991 198366086599486379733755987)
  ·
    refine ⟨297549129899229569600633981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198366086599486379733755987 297549129899229569600633981)
    ·
      refine ⟨111580923712211088600237743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 297549129899229569600633981 111580923712211088600237743)
      ·
        refine ⟨167371385568316632900356615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111580923712211088600237743 167371385568316632900356615)
        ·
          refine ⟨251057078352474949350534923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167371385568316632900356615 251057078352474949350534923)
          ·
            refine ⟨376585617528712424025802385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251057078352474949350534923 376585617528712424025802385)
            ·
              refine ⟨282439213146534318019351789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 376585617528712424025802385 282439213146534318019351789)
              ·
                refine ⟨105914704929950369257256921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 282439213146534318019351789 105914704929950369257256921)
                ·
                  refine ⟨79436028697462776942942691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105914704929950369257256921 79436028697462776942942691)
                  ·
                    refine ⟨119154043046194165414414037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79436028697462776942942691 119154043046194165414414037)
                    ·
                      refine ⟨2792672883895175751900329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 119154043046194165414414037 2792672883895175751900329)
                      ·
                        rfl

theorem cell23_5438711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_5438711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438711 prefixEnd_5438711 := by exact prefixLift 5438711
  have htrace : WordTrace (prefixWord ++ tailWord_5438711) baseStart_5438711 baseEnd_5438711 := by
    simpa [prefixWord, tailWord_5438711, baseEnd_5438711] using wordTrace_append hprefix tailTrace_5438711
  have hstable : (prefixWord ++ tailWord_5438711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438711).length < 2 ^ (prefixWord ++ tailWord_5438711).sum := by decide
  have hdescent : baseEnd_5438711 < baseStart_5438711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438772 : List Nat := [2, 5, 1, 1, 1, 1, 2, 4, 1, 1, 4]
def baseStart_5438772 : Nat := 118140960795 + 5438772 * 2 ^ 59
def prefixEnd_5438772 : Nat := 4983230072969 + 3 ^ 40 * 5438772 * 2
def baseEnd_5438772 : Nat := 2792704206215100013237549

theorem tailTrace_5438772 : CollatzResearch.WordTrace tailWord_5438772 prefixEnd_5438772 2792704206215100013237549 := by
  unfold tailWord_5438772
  simp only [CollatzResearch.WordTrace]
  refine ⟨99184155726132693575863285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132245540968176924767817713 99184155726132693575863285)
  ·
    refine ⟨9298514599324940022737183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99184155726132693575863285 9298514599324940022737183)
    ·
      refine ⟨13947771898987410034105775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9298514599324940022737183 13947771898987410034105775)
      ·
        refine ⟨20921657848481115051158663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13947771898987410034105775 20921657848481115051158663)
        ·
          refine ⟨31382486772721672576737995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20921657848481115051158663 31382486772721672576737995)
          ·
            refine ⟨47073730159082508865106993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31382486772721672576737995 47073730159082508865106993)
            ·
              refine ⟨35305297619311881648830245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47073730159082508865106993 35305297619311881648830245)
              ·
                refine ⟨6619743303620977809155671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35305297619311881648830245 6619743303620977809155671)
                ·
                  refine ⟨9929614955431466713733507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6619743303620977809155671 9929614955431466713733507)
                  ·
                    refine ⟨14894422433147200070600261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9929614955431466713733507 14894422433147200070600261)
                    ·
                      refine ⟨2792704206215100013237549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14894422433147200070600261 2792704206215100013237549)
                      ·
                        rfl

theorem cell23_5438772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_5438772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438772 prefixEnd_5438772 := by exact prefixLift 5438772
  have htrace : WordTrace (prefixWord ++ tailWord_5438772) baseStart_5438772 baseEnd_5438772 := by
    simpa [prefixWord, tailWord_5438772, baseEnd_5438772] using wordTrace_append hprefix tailTrace_5438772
  have hstable : (prefixWord ++ tailWord_5438772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438772).length < 2 ^ (prefixWord ++ tailWord_5438772).sum := by decide
  have hdescent : baseEnd_5438772 < baseStart_5438772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438915 : List Nat := [1, 1, 1, 3, 1, 1, 6, 2, 2, 5]
def baseStart_5438915 : Nat := 118140960795 + 5438915 * 2 ^ 59
def prefixEnd_5438915 : Nat := 4983230072969 + 3 ^ 40 * 5438915 * 2
def baseEnd_5438915 : Nat := 930925877982897651249797

theorem tailTrace_5438915 : CollatzResearch.WordTrace tailWord_5438915 prefixEnd_5438915 930925877982897651249797 := by
  unfold tailWord_5438915
  simp only [CollatzResearch.WordTrace]
  refine ⟨198373527090747322574182199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132249018060498215049454799 198373527090747322574182199)
  ·
    refine ⟨297560290636120983861273299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198373527090747322574182199 297560290636120983861273299)
    ·
      refine ⟨446340435954181475791909949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297560290636120983861273299 446340435954181475791909949)
      ·
        refine ⟨167377663482818053421966231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 446340435954181475791909949 167377663482818053421966231)
        ·
          refine ⟨251066495224227080132949347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167377663482818053421966231 251066495224227080132949347)
          ·
            refine ⟨376599742836340620199424021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251066495224227080132949347 376599742836340620199424021)
            ·
              refine ⟨17653112945453466571848001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 376599742836340620199424021 17653112945453466571848001)
              ·
                refine ⟨13239834709090099928886001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17653112945453466571848001 13239834709090099928886001)
                ·
                  refine ⟨9929876031817574946664501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13239834709090099928886001 9929876031817574946664501)
                  ·
                    refine ⟨930925877982897651249797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9929876031817574946664501 930925877982897651249797)
                    ·
                      rfl

theorem cell23_5438915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 5].length) (baseStart_5438915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438915 prefixEnd_5438915 := by exact prefixLift 5438915
  have htrace : WordTrace (prefixWord ++ tailWord_5438915) baseStart_5438915 baseEnd_5438915 := by
    simpa [prefixWord, tailWord_5438915, baseEnd_5438915] using wordTrace_append hprefix tailTrace_5438915
  have hstable : (prefixWord ++ tailWord_5438915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438915).length < 2 ^ (prefixWord ++ tailWord_5438915).sum := by decide
  have hdescent : baseEnd_5438915 < baseStart_5438915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438922 : List Nat := [3, 1, 2, 1, 2, 3, 1, 1, 2, 5, 2]
def baseStart_5438922 : Nat := 118140960795 + 5438922 * 2 ^ 59
def prefixEnd_5438922 : Nat := 4983230072969 + 3 ^ 40 * 5438922 * 2
def baseEnd_5438922 : Nat := 2792781228313274426361859

theorem tailTrace_5438922 : CollatzResearch.WordTrace tailWord_5438922 prefixEnd_5438922 2792781228313274426361859 := by
  unfold tailWord_5438922
  simp only [CollatzResearch.WordTrace]
  refine ⟨49593445600430490692421755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132249188267814641846458013 49593445600430490692421755)
  ·
    refine ⟨74390168400645736038632633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49593445600430490692421755 74390168400645736038632633)
    ·
      refine ⟨55792626300484302028974475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74390168400645736038632633 55792626300484302028974475)
      ·
        refine ⟨83688939450726453043461713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55792626300484302028974475 83688939450726453043461713)
        ·
          refine ⟨62766704588044839782596285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83688939450726453043461713 62766704588044839782596285)
          ·
            refine ⟨23537514220516814918473607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62766704588044839782596285 23537514220516814918473607)
            ·
              refine ⟨35306271330775222377710411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23537514220516814918473607 35306271330775222377710411)
              ·
                refine ⟨52959406996162833566565617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35306271330775222377710411 52959406996162833566565617)
                ·
                  refine ⟨39719555247122125174924213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52959406996162833566565617 39719555247122125174924213)
                  ·
                    refine ⟨3723708304417699235149145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39719555247122125174924213 3723708304417699235149145)
                    ·
                      refine ⟨2792781228313274426361859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3723708304417699235149145 2792781228313274426361859)
                      ·
                        rfl

theorem cell23_5438922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 2, 5, 2].length) (baseStart_5438922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438922 prefixEnd_5438922 := by exact prefixLift 5438922
  have htrace : WordTrace (prefixWord ++ tailWord_5438922) baseStart_5438922 baseEnd_5438922 := by
    simpa [prefixWord, tailWord_5438922, baseEnd_5438922] using wordTrace_append hprefix tailTrace_5438922
  have hstable : (prefixWord ++ tailWord_5438922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438922).length < 2 ^ (prefixWord ++ tailWord_5438922).sum := by decide
  have hdescent : baseEnd_5438922 < baseStart_5438922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438935 : List Nat := [1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 4]
def baseStart_5438935 : Nat := 118140960795 + 5438935 * 2 ^ 59
def prefixEnd_5438935 : Nat := 4983230072969 + 3 ^ 40 * 5438935 * 2
def baseEnd_5438935 : Nat := 2792787903561782875499299

theorem tailTrace_5438935 : CollatzResearch.WordTrace tailWord_5438935 prefixEnd_5438935 2792787903561782875499299 := by
  unfold tailWord_5438935
  simp only [CollatzResearch.WordTrace]
  refine ⟨198374256550674865989910259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132249504367116577326606839 198374256550674865989910259)
  ·
    refine ⟨297561384826012298984865389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198374256550674865989910259 297561384826012298984865389)
    ·
      refine ⟨111585519309754612119324521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 297561384826012298984865389 111585519309754612119324521)
      ·
        refine ⟨83689139482315959089493391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111585519309754612119324521 83689139482315959089493391)
        ·
          refine ⟨125533709223473938634240087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83689139482315959089493391 125533709223473938634240087)
          ·
            refine ⟨188300563835210907951360131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125533709223473938634240087 188300563835210907951360131)
            ·
              refine ⟨282450845752816361927040197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188300563835210907951360131 282450845752816361927040197)
              ·
                refine ⟨52959533578653067861320037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 282450845752816361927040197 52959533578653067861320037)
                ·
                  refine ⟨9929912545997450223997507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52959533578653067861320037 9929912545997450223997507)
                  ·
                    refine ⟨14894868818996175335996261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9929912545997450223997507 14894868818996175335996261)
                    ·
                      refine ⟨2792787903561782875499299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14894868818996175335996261 2792787903561782875499299)
                      ·
                        rfl

theorem cell23_5438935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_5438935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438935 prefixEnd_5438935 := by exact prefixLift 5438935
  have htrace : WordTrace (prefixWord ++ tailWord_5438935) baseStart_5438935 baseEnd_5438935 := by
    simpa [prefixWord, tailWord_5438935, baseEnd_5438935] using wordTrace_append hprefix tailTrace_5438935
  have hstable : (prefixWord ++ tailWord_5438935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438935).length < 2 ^ (prefixWord ++ tailWord_5438935).sum := by decide
  have hdescent : baseEnd_5438935 < baseStart_5438935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438949 : List Nat := [1, 3, 1, 5, 1, 3, 1, 1, 2, 5]
def baseStart_5438949 : Nat := 118140960795 + 5438949 * 2 ^ 59
def prefixEnd_5438949 : Nat := 4983230072969 + 3 ^ 40 * 5438949 * 2
def baseEnd_5438949 : Nat := 930931697430315273574745

theorem tailTrace_5438949 : CollatzResearch.WordTrace tailWord_5438949 prefixEnd_5438949 930931697430315273574745 := by
  unfold tailWord_5438949
  simp only [CollatzResearch.WordTrace]
  refine ⟨198374767172624146380919901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132249844781749430920613267 198374767172624146380919901)
  ·
    refine ⟨74390537689734054892844963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198374767172624146380919901 74390537689734054892844963)
    ·
      refine ⟨111585806534601082339267445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74390537689734054892844963 111585806534601082339267445)
      ·
        refine ⟨10461169362618851469306323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111585806534601082339267445 10461169362618851469306323)
        ·
          refine ⟨15691754043928277203959485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10461169362618851469306323 15691754043928277203959485)
          ·
            refine ⟨5884407766473103951484807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15691754043928277203959485 5884407766473103951484807)
            ·
              refine ⟨8826611649709655927227211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5884407766473103951484807 8826611649709655927227211)
              ·
                refine ⟨13239917474564483890840817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8826611649709655927227211 13239917474564483890840817)
                ·
                  refine ⟨9929938105923362918130613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13239917474564483890840817 9929938105923362918130613)
                  ·
                    refine ⟨930931697430315273574745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9929938105923362918130613 930931697430315273574745)
                    ·
                      rfl

theorem cell23_5438949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 5].length) (baseStart_5438949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438949 prefixEnd_5438949 := by exact prefixLift 5438949
  have htrace : WordTrace (prefixWord ++ tailWord_5438949) baseStart_5438949 baseEnd_5438949 := by
    simpa [prefixWord, tailWord_5438949, baseEnd_5438949] using wordTrace_append hprefix tailTrace_5438949
  have hstable : (prefixWord ++ tailWord_5438949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438949).length < 2 ^ (prefixWord ++ tailWord_5438949).sum := by decide
  have hdescent : baseEnd_5438949 < baseStart_5438949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438952 : List Nat := [2, 1, 4, 1, 1, 2, 1, 2, 1, 6, 2]
def baseStart_5438952 : Nat := 118140960795 + 5438952 * 2 ^ 59
def prefixEnd_5438952 : Nat := 4983230072969 + 3 ^ 40 * 5438952 * 2
def baseEnd_5438952 : Nat := 2792796632732909308986721

theorem tailTrace_5438952 : CollatzResearch.WordTrace tailWord_5438952 prefixEnd_5438952 2792796632732909308986721 := by
  unfold tailWord_5438952
  simp only [CollatzResearch.WordTrace]
  refine ⟨99187438295806638946639555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132249917727742185262186073 99187438295806638946639555)
  ·
    refine ⟨148781157443709958419959333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99187438295806638946639555 148781157443709958419959333)
    ·
      refine ⟨27896467020695617203742375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148781157443709958419959333 27896467020695617203742375)
      ·
        refine ⟨41844700531043425805613563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27896467020695617203742375 41844700531043425805613563)
        ·
          refine ⟨62767050796565138708420345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41844700531043425805613563 62767050796565138708420345)
          ·
            refine ⟨47075288097423854031315259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62767050796565138708420345 47075288097423854031315259)
            ·
              refine ⟨70612932146135781046972889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47075288097423854031315259 70612932146135781046972889)
              ·
                refine ⟨52959699109601835785229667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70612932146135781046972889 52959699109601835785229667)
                ·
                  refine ⟨79439548664402753677844501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52959699109601835785229667 79439548664402753677844501)
                  ·
                    refine ⟨3723728843643879078648961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79439548664402753677844501 3723728843643879078648961)
                    ·
                      refine ⟨2792796632732909308986721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3723728843643879078648961 2792796632732909308986721)
                      ·
                        rfl

theorem cell23_5438952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_5438952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438952 prefixEnd_5438952 := by exact prefixLift 5438952
  have htrace : WordTrace (prefixWord ++ tailWord_5438952) baseStart_5438952 baseEnd_5438952 := by
    simpa [prefixWord, tailWord_5438952, baseEnd_5438952] using wordTrace_append hprefix tailTrace_5438952
  have hstable : (prefixWord ++ tailWord_5438952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438952).length < 2 ^ (prefixWord ++ tailWord_5438952).sum := by decide
  have hdescent : baseEnd_5438952 < baseStart_5438952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438972 : List Nat := [2, 2, 2, 1, 2, 1, 2, 4, 2, 2, 3]
def baseStart_5438972 : Nat := 118140960795 + 5438972 * 2 ^ 59
def prefixEnd_5438972 : Nat := 4983230072969 + 3 ^ 40 * 5438972 * 2
def baseEnd_5438972 : Nat := 2792806902345999230736629

theorem tailTrace_5438972 : CollatzResearch.WordTrace tailWord_5438972 prefixEnd_5438972 2792806902345999230736629 := by
  unfold tailWord_5438972
  simp only [CollatzResearch.WordTrace]
  refine ⟨99187803025770410654503585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132250404034360547539338113 99187803025770410654503585)
  ·
    refine ⟨74390852269327807990877689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99187803025770410654503585 74390852269327807990877689)
    ·
      refine ⟨55793139201995855993158267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74390852269327807990877689 55793139201995855993158267)
      ·
        refine ⟨83689708802993783989737401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55793139201995855993158267 83689708802993783989737401)
        ·
          refine ⟨62767281602245337992303051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83689708802993783989737401 62767281602245337992303051)
          ·
            refine ⟨94150922403368006988454577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62767281602245337992303051 94150922403368006988454577)
            ·
              refine ⟨70613191802526005241340933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94150922403368006988454577 70613191802526005241340933)
              ·
                refine ⟨13239973462973625982751425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70613191802526005241340933 13239973462973625982751425)
                ·
                  refine ⟨9929980097230219487063569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13239973462973625982751425 9929980097230219487063569)
                  ·
                    refine ⟨7447485072922664615297677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9929980097230219487063569 7447485072922664615297677)
                    ·
                      refine ⟨2792806902345999230736629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7447485072922664615297677 2792806902345999230736629)
                      ·
                        rfl

theorem cell23_5438972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_5438972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438972 prefixEnd_5438972 := by exact prefixLift 5438972
  have htrace : WordTrace (prefixWord ++ tailWord_5438972) baseStart_5438972 baseEnd_5438972 := by
    simpa [prefixWord, tailWord_5438972, baseEnd_5438972] using wordTrace_append hprefix tailTrace_5438972
  have hstable : (prefixWord ++ tailWord_5438972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438972).length < 2 ^ (prefixWord ++ tailWord_5438972).sum := by decide
  have hdescent : baseEnd_5438972 < baseStart_5438972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5438975 : List Nat := [1, 1, 2, 2, 1, 2, 2, 6, 6]
def baseStart_5438975 : Nat := 118140960795 + 5438975 * 2 ^ 59
def prefixEnd_5438975 : Nat := 4983230072969 + 3 ^ 40 * 5438975 * 2
def baseEnd_5438975 : Nat := 310312049198662524333235

theorem tailTrace_5438975 : CollatzResearch.WordTrace tailWord_5438975 prefixEnd_5438975 310312049198662524333235 := by
  unfold tailWord_5438975
  simp only [CollatzResearch.WordTrace]
  refine ⟨198375715470529952821366379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132250476980353301880910919 198375715470529952821366379)
  ·
    refine ⟨297563573205794929232049569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198375715470529952821366379 297563573205794929232049569)
    ·
      refine ⟨223172679904346196924037177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297563573205794929232049569 223172679904346196924037177)
      ·
        refine ⟨167379509928259647693027883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223172679904346196924037177 167379509928259647693027883)
        ·
          refine ⟨251069264892389471539541825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167379509928259647693027883 251069264892389471539541825)
          ·
            refine ⟨188301948669292103654656369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251069264892389471539541825 188301948669292103654656369)
            ·
              refine ⟨141226461501969077740992277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188301948669292103654656369 141226461501969077740992277)
              ·
                refine ⟨6619990382904800519109013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 141226461501969077740992277 6619990382904800519109013)
                ·
                  refine ⟨310312049198662524333235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6619990382904800519109013 310312049198662524333235)
                  ·
                    rfl

theorem cell23_5438975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 6].length) (baseStart_5438975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5438975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5438975 prefixEnd_5438975 := by exact prefixLift 5438975
  have htrace : WordTrace (prefixWord ++ tailWord_5438975) baseStart_5438975 baseEnd_5438975 := by
    simpa [prefixWord, tailWord_5438975, baseEnd_5438975] using wordTrace_append hprefix tailTrace_5438975
  have hstable : (prefixWord ++ tailWord_5438975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5438975).length < 2 ^ (prefixWord ++ tailWord_5438975).sum := by decide
  have hdescent : baseEnd_5438975 < baseStart_5438975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5438975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439029 : List Nat := [1, 3, 3, 1, 1, 3, 1, 1, 4, 3, 2]
def baseStart_5439029 : Nat := 118140960795 + 5439029 * 2 ^ 59
def prefixEnd_5439029 : Nat := 4983230072969 + 3 ^ 40 * 5439029 * 2
def baseEnd_5439029 : Nat := 2792836170743305507723867

theorem tailTrace_5439029 : CollatzResearch.WordTrace tailWord_5439029 prefixEnd_5439029 2792836170743305507723867 := by
  unfold tailWord_5439029
  simp only [CollatzResearch.WordTrace]
  refine ⟨198377685012334320043832141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132251790008222880029221427 198377685012334320043832141)
  ·
    refine ⟨74391631879625370016437053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198377685012334320043832141 74391631879625370016437053)
    ·
      refine ⟨27896861954859513756163895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74391631879625370016437053 27896861954859513756163895)
      ·
        refine ⟨41845292932289270634245843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27896861954859513756163895 41845292932289270634245843)
        ·
          refine ⟨62767939398433905951368765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41845292932289270634245843 62767939398433905951368765)
          ·
            refine ⟨23537977274412714731763287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62767939398433905951368765 23537977274412714731763287)
            ·
              refine ⟨35306965911619072097644931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23537977274412714731763287 35306965911619072097644931)
              ·
                refine ⟨52960448867428608146467397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35306965911619072097644931 52960448867428608146467397)
                ·
                  refine ⟨9930084162642864027462637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52960448867428608146467397 9930084162642864027462637)
                  ·
                    refine ⟨3723781560991074010298489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9930084162642864027462637 3723781560991074010298489)
                    ·
                      refine ⟨2792836170743305507723867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3723781560991074010298489 2792836170743305507723867)
                      ·
                        rfl

theorem cell23_5439029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_5439029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439029 prefixEnd_5439029 := by exact prefixLift 5439029
  have htrace : WordTrace (prefixWord ++ tailWord_5439029) baseStart_5439029 baseEnd_5439029 := by
    simpa [prefixWord, tailWord_5439029, baseEnd_5439029] using wordTrace_append hprefix tailTrace_5439029
  have hstable : (prefixWord ++ tailWord_5439029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439029).length < 2 ^ (prefixWord ++ tailWord_5439029).sum := by decide
  have hdescent : baseEnd_5439029 < baseStart_5439029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439030 : List Nat := [5, 1, 2, 1, 3, 1, 3, 2, 1, 4]
def baseStart_5439030 : Nat := 118140960795 + 5439030 * 2 ^ 59
def prefixEnd_5439030 : Nat := 4983230072969 + 3 ^ 40 * 5439030 * 2
def baseEnd_5439030 : Nat := 930945561407986667937121

theorem tailTrace_5439030 : CollatzResearch.WordTrace tailWord_5439030 prefixEnd_5439030 930945561407986667937121 := by
  unfold tailWord_5439030
  simp only [CollatzResearch.WordTrace]
  refine ⟨12398607592833168575913659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132251814323553798143079029 12398607592833168575913659)
  ·
    refine ⟨18597911389249752863870489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12398607592833168575913659 18597911389249752863870489)
    ·
      refine ⟨13948433541937314647902867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18597911389249752863870489 13948433541937314647902867)
      ·
        refine ⟨20922650312905971971854301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13948433541937314647902867 20922650312905971971854301)
        ·
          refine ⟨7845993867339739489445363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20922650312905971971854301 7845993867339739489445363)
          ·
            refine ⟨11768990801009609234168045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7845993867339739489445363 11768990801009609234168045)
            ·
              refine ⟨4413371550378603462813017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11768990801009609234168045 4413371550378603462813017)
              ·
                refine ⟨3310028662783952597109763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4413371550378603462813017 3310028662783952597109763)
                ·
                  refine ⟨4965042994175928895664645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3310028662783952597109763 4965042994175928895664645)
                  ·
                    refine ⟨930945561407986667937121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4965042994175928895664645 930945561407986667937121)
                    ·
                      rfl

theorem cell23_5439030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_5439030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439030 prefixEnd_5439030 := by exact prefixLift 5439030
  have htrace : WordTrace (prefixWord ++ tailWord_5439030) baseStart_5439030 baseEnd_5439030 := by
    simpa [prefixWord, tailWord_5439030, baseEnd_5439030] using wordTrace_append hprefix tailTrace_5439030
  have hstable : (prefixWord ++ tailWord_5439030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439030).length < 2 ^ (prefixWord ++ tailWord_5439030).sum := by decide
  have hdescent : baseEnd_5439030 < baseStart_5439030 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5439076 : List Nat := [2, 3, 1, 1, 2, 4, 3, 1, 1, 1, 4]
def baseStart_5439076 : Nat := 118140960795 + 5439076 * 2 ^ 59
def prefixEnd_5439076 : Nat := 4983230072969 + 3 ^ 40 * 5439076 * 2
def baseEnd_5439076 : Nat := 2792860304334066823836151

theorem tailTrace_5439076 : CollatzResearch.WordTrace tailWord_5439076 prefixEnd_5439076 2792860304334066823836151 := by
  unfold tailWord_5439076
  simp only [CollatzResearch.WordTrace]
  refine ⟨99189699621582023535396541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132252932828776031380528721 99189699621582023535396541)
  ·
    refine ⟨37196137358093258825773703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99189699621582023535396541 37196137358093258825773703)
    ·
      refine ⟨55794206037139888238660555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37196137358093258825773703 55794206037139888238660555)
      ·
        refine ⟨83691309055709832357990833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55794206037139888238660555 83691309055709832357990833)
        ·
          refine ⟨62768481791782374268493125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83691309055709832357990833 62768481791782374268493125)
          ·
            refine ⟨11769090335959195175342461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62768481791782374268493125 11769090335959195175342461)
            ·
              refine ⟨4413408875984698190753423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11769090335959195175342461 4413408875984698190753423)
              ·
                refine ⟨6620113313977047286130135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4413408875984698190753423 6620113313977047286130135)
                ·
                  refine ⟨9930169970965570929195203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6620113313977047286130135 9930169970965570929195203)
                  ·
                    refine ⟨14895254956448356393792805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9930169970965570929195203 14895254956448356393792805)
                    ·
                      refine ⟨2792860304334066823836151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14895254956448356393792805 2792860304334066823836151)
                      ·
                        rfl

theorem cell23_5439076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 1, 1, 4].length) (baseStart_5439076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5439076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5439076 prefixEnd_5439076 := by exact prefixLift 5439076
  have htrace : WordTrace (prefixWord ++ tailWord_5439076) baseStart_5439076 baseEnd_5439076 := by
    simpa [prefixWord, tailWord_5439076, baseEnd_5439076] using wordTrace_append hprefix tailTrace_5439076
  have hstable : (prefixWord ++ tailWord_5439076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5439076).length < 2 ^ (prefixWord ++ tailWord_5439076).sum := by decide
  have hdescent : baseEnd_5439076 < baseStart_5439076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5439076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
