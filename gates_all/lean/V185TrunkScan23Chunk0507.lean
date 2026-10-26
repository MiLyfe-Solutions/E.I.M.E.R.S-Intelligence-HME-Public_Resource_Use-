import V185TrunkScan23Chunk0506

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2998931 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 6]
def baseStart_2998931 : Nat := 118140960795 + 2998931 * 2 ^ 59
def prefixEnd_2998931 : Nat := 4983230072969 + 3 ^ 40 * 2998931 * 2
def baseEnd_2998931 : Nat := 1539893052668711402370673

theorem tailTrace_2998931 : CollatzResearch.WordTrace tailWord_2998931 prefixEnd_2998931 1539893052668711402370673 := by
  unfold tailWord_2998931
  simp only [CollatzResearch.WordTrace]
  refine ⟨109379999498392638483444647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72919999665595092322296431 109379999498392638483444647)
  ·
    refine ⟨164069999247588957725166971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109379999498392638483444647 164069999247588957725166971)
    ·
      refine ⟨246104998871383436587750457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164069999247588957725166971 246104998871383436587750457)
      ·
        refine ⟨184578749153537577440812843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246104998871383436587750457 184578749153537577440812843)
        ·
          refine ⟨276868123730306366161219265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184578749153537577440812843 276868123730306366161219265)
          ·
            refine ⟨207651092797729774620914449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276868123730306366161219265 207651092797729774620914449)
            ·
              refine ⟨155738319598297330965685837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207651092797729774620914449 155738319598297330965685837)
              ·
                refine ⟨58401869849361499112132189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155738319598297330965685837 58401869849361499112132189)
                ·
                  refine ⟨21900701193510562167049571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58401869849361499112132189 21900701193510562167049571)
                  ·
                    refine ⟨32851051790265843250574357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21900701193510562167049571 32851051790265843250574357)
                    ·
                      refine ⟨1539893052668711402370673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32851051790265843250574357 1539893052668711402370673)
                      ·
                        rfl

theorem cell23_2998931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 6].length) (baseStart_2998931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998931 prefixEnd_2998931 := by exact prefixLift 2998931
  have htrace : WordTrace (prefixWord ++ tailWord_2998931) baseStart_2998931 baseEnd_2998931 := by
    simpa [prefixWord, tailWord_2998931, baseEnd_2998931] using wordTrace_append hprefix tailTrace_2998931
  have hstable : (prefixWord ++ tailWord_2998931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998931).length < 2 ^ (prefixWord ++ tailWord_2998931).sum := by decide
  have hdescent : baseEnd_2998931 < baseStart_2998931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998948 : List Nat := [2, 3, 1, 2, 2, 1, 3, 1, 1, 1, 6]
def baseStart_2998948 : Nat := 118140960795 + 2998948 * 2 ^ 59
def prefixEnd_2998948 : Nat := 4983230072969 + 3 ^ 40 * 2998948 * 2
def baseEnd_2998948 : Nat := 1539901781839837835858095

theorem tailTrace_2998948 : CollatzResearch.WordTrace tailWord_2998948 prefixEnd_2998948 1539901781839837835858095 := by
  unfold tailWord_2998948
  simp only [CollatzResearch.WordTrace]
  refine ⟨54690309769665525193406749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72920413026220700257875665 54690309769665525193406749)
  ·
    refine ⟨20508866163624571947527531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54690309769665525193406749 20508866163624571947527531)
    ·
      refine ⟨30763299245436857921291297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20508866163624571947527531 30763299245436857921291297)
      ·
        refine ⟨23072474434077643440968473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30763299245436857921291297 23072474434077643440968473)
        ·
          refine ⟨17304355825558232580726355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23072474434077643440968473 17304355825558232580726355)
          ·
            refine ⟨25956533738337348871089533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17304355825558232580726355 25956533738337348871089533)
            ·
              refine ⟨9733700151876505826658575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25956533738337348871089533 9733700151876505826658575)
              ·
                refine ⟨14600550227814758739987863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9733700151876505826658575 14600550227814758739987863)
                ·
                  refine ⟨21900825341722138109981795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14600550227814758739987863 21900825341722138109981795)
                  ·
                    refine ⟨32851238012583207164972693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21900825341722138109981795 32851238012583207164972693)
                    ·
                      refine ⟨1539901781839837835858095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32851238012583207164972693 1539901781839837835858095)
                      ·
                        rfl

theorem cell23_2998948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_2998948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998948 prefixEnd_2998948 := by exact prefixLift 2998948
  have htrace : WordTrace (prefixWord ++ tailWord_2998948) baseStart_2998948 baseEnd_2998948 := by
    simpa [prefixWord, tailWord_2998948, baseEnd_2998948] using wordTrace_append hprefix tailTrace_2998948
  have hstable : (prefixWord ++ tailWord_2998948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998948).length < 2 ^ (prefixWord ++ tailWord_2998948).sum := by decide
  have hdescent : baseEnd_2998948 < baseStart_2998948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998971 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 3, 9]
def baseStart_2998971 : Nat := 118140960795 + 2998971 * 2 ^ 59
def prefixEnd_2998971 : Nat := 4983230072969 + 3 ^ 40 * 2998971 * 2
def baseEnd_2998971 : Nat := 513304530631630415290163

theorem tailTrace_2998971 : CollatzResearch.WordTrace tailWord_2998971 prefixEnd_2998971 513304530631630415290163 := by
  unfold tailWord_2998971
  simp only [CollatzResearch.WordTrace]
  refine ⟨109381458418247725314900767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72920972278831816876600511 109381458418247725314900767)
  ·
    refine ⟨164072187627371587972351151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109381458418247725314900767 164072187627371587972351151)
    ·
      refine ⟨246108281441057381958526727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164072187627371587972351151 246108281441057381958526727)
      ·
        refine ⟨369162422161586072937790091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246108281441057381958526727 369162422161586072937790091)
        ·
          refine ⟨553743633242379109406685137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369162422161586072937790091 553743633242379109406685137)
          ·
            refine ⟨415307724931784332055013853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 553743633242379109406685137 415307724931784332055013853)
            ·
              refine ⟨155740396849419124520630195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 415307724931784332055013853 155740396849419124520630195)
              ·
                refine ⟨233610595274128686780945293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155740396849419124520630195 233610595274128686780945293)
                ·
                  refine ⟨87603973227798257542854485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 233610595274128686780945293 87603973227798257542854485)
                  ·
                    refine ⟨513304530631630415290163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 87603973227798257542854485 513304530631630415290163)
                    ·
                      rfl

theorem cell23_2998971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 9].length) (baseStart_2998971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998971 prefixEnd_2998971 := by exact prefixLift 2998971
  have htrace : WordTrace (prefixWord ++ tailWord_2998971) baseStart_2998971 baseEnd_2998971 := by
    simpa [prefixWord, tailWord_2998971, baseEnd_2998971] using wordTrace_append hprefix tailTrace_2998971
  have hstable : (prefixWord ++ tailWord_2998971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998971).length < 2 ^ (prefixWord ++ tailWord_2998971).sum := by decide
  have hdescent : baseEnd_2998971 < baseStart_2998971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998996 : List Nat := [2, 4, 1, 3, 2, 2, 2, 1, 2, 4]
def baseStart_2998996 : Nat := 118140960795 + 2998996 * 2 ^ 59
def prefixEnd_2998996 : Nat := 4983230072969 + 3 ^ 40 * 2998996 * 2
def baseEnd_2998996 : Nat := 513308809637084549352625

theorem tailTrace_2998996 : CollatzResearch.WordTrace tailWord_2998996 prefixEnd_2998996 513308809637084549352625 := by
  unfold tailWord_2998996
  simp only [CollatzResearch.WordTrace]
  refine ⟨54691185121578577292280421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72921580162104769723040561 54691185121578577292280421)
  ·
    refine ⟨10254597210295983242302579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54691185121578577292280421 10254597210295983242302579)
    ·
      refine ⟨15381895815443974863453869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10254597210295983242302579 15381895815443974863453869)
      ·
        refine ⟨5768210930791490573795201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15381895815443974863453869 5768210930791490573795201)
        ·
          refine ⟨4326158198093617930346401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5768210930791490573795201 4326158198093617930346401)
          ·
            refine ⟨3244618648570213447759801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4326158198093617930346401 3244618648570213447759801)
            ·
              refine ⟨2433463986427660085819851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3244618648570213447759801 2433463986427660085819851)
              ·
                refine ⟨3650195979641490128729777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2433463986427660085819851 3650195979641490128729777)
                ·
                  refine ⟨2737646984731117596547333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3650195979641490128729777 2737646984731117596547333)
                  ·
                    refine ⟨513308809637084549352625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2737646984731117596547333 513308809637084549352625)
                    ·
                      rfl

theorem cell23_2998996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_2998996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2998996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2998996 prefixEnd_2998996 := by exact prefixLift 2998996
  have htrace : WordTrace (prefixWord ++ tailWord_2998996) baseStart_2998996 baseEnd_2998996 := by
    simpa [prefixWord, tailWord_2998996, baseEnd_2998996] using wordTrace_append hprefix tailTrace_2998996
  have hstable : (prefixWord ++ tailWord_2998996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998996).length < 2 ^ (prefixWord ++ tailWord_2998996).sum := by decide
  have hdescent : baseEnd_2998996 < baseStart_2998996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999002 : List Nat := [3, 1, 1, 2, 2, 2, 3, 3, 2, 1, 3]
def baseStart_2999002 : Nat := 118140960795 + 2999002 * 2 ^ 59
def prefixEnd_2999002 : Nat := 4983230072969 + 3 ^ 40 * 2999002 * 2
def baseEnd_2999002 : Nat := 1539929509795180624582847

theorem tailTrace_2999002 : CollatzResearch.WordTrace tailWord_2999002 prefixEnd_2999002 1539929509795180624582847 := by
  unfold tailWord_2999002
  simp only [CollatzResearch.WordTrace]
  refine ⟨27345647270283854402319815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72921726054090278406186173 27345647270283854402319815)
  ·
    refine ⟨41018470905425781603479723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27345647270283854402319815 41018470905425781603479723)
    ·
      refine ⟨61527706358138672405219585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41018470905425781603479723 61527706358138672405219585)
      ·
        refine ⟨46145779768604004303914689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61527706358138672405219585 46145779768604004303914689)
        ·
          refine ⟨34609334826453003227936017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46145779768604004303914689 34609334826453003227936017)
          ·
            refine ⟨25957001119839752420952013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34609334826453003227936017 25957001119839752420952013)
            ·
              refine ⟨9733875419939907157857005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25957001119839752420952013 9733875419939907157857005)
              ·
                refine ⟨3650203282477465184196377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9733875419939907157857005 3650203282477465184196377)
                ·
                  refine ⟨2737652461858098888147283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3650203282477465184196377 2737652461858098888147283)
                  ·
                    refine ⟨4106478692787148332220925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2737652461858098888147283 4106478692787148332220925)
                    ·
                      refine ⟨1539929509795180624582847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4106478692787148332220925 1539929509795180624582847)
                      ·
                        rfl

theorem cell23_2999002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 2, 1, 3].length) (baseStart_2999002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999002 prefixEnd_2999002 := by exact prefixLift 2999002
  have htrace : WordTrace (prefixWord ++ tailWord_2999002) baseStart_2999002 baseEnd_2999002 := by
    simpa [prefixWord, tailWord_2999002, baseEnd_2999002] using wordTrace_append hprefix tailTrace_2999002
  have hstable : (prefixWord ++ tailWord_2999002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999002).length < 2 ^ (prefixWord ++ tailWord_2999002).sum := by decide
  have hdescent : baseEnd_2999002 < baseStart_2999002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999012 : List Nat := [2, 3, 1, 1, 1, 5, 1, 1, 3, 3, 2]
def baseStart_2999012 : Nat := 118140960795 + 2999012 * 2 ^ 59
def prefixEnd_2999012 : Nat := 4983230072969 + 3 ^ 40 * 2999012 * 2
def baseEnd_2999012 : Nat := 1539934644601725585457801

theorem tailTrace_2999012 : CollatzResearch.WordTrace tailWord_2999012 prefixEnd_2999012 1539934644601725585457801 := by
  unfold tailWord_2999012
  simp only [CollatzResearch.WordTrace]
  refine ⟨54691476905549594658571645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72921969207399459544762193 54691476905549594658571645)
  ·
    refine ⟨20509303839581097996964367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54691476905549594658571645 20509303839581097996964367)
    ·
      refine ⟨30763955759371646995446551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20509303839581097996964367 30763955759371646995446551)
      ·
        refine ⟨46145933639057470493169827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30763955759371646995446551 46145933639057470493169827)
        ·
          refine ⟨69218900458586205739754741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46145933639057470493169827 69218900458586205739754741)
          ·
            refine ⟨6489271917992456788102007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69218900458586205739754741 6489271917992456788102007)
            ·
              refine ⟨9733907876988685182153011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6489271917992456788102007 9733907876988685182153011)
              ·
                refine ⟨14600861815483027773229517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9733907876988685182153011 14600861815483027773229517)
                ·
                  refine ⟨5475323180806135414961069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14600861815483027773229517 5475323180806135414961069)
                  ·
                    refine ⟨2053246192802300780610401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5475323180806135414961069 2053246192802300780610401)
                    ·
                      refine ⟨1539934644601725585457801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2053246192802300780610401 1539934644601725585457801)
                      ·
                        rfl

theorem cell23_2999012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 3, 3, 2].length) (baseStart_2999012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999012 prefixEnd_2999012 := by exact prefixLift 2999012
  have htrace : WordTrace (prefixWord ++ tailWord_2999012) baseStart_2999012 baseEnd_2999012 := by
    simpa [prefixWord, tailWord_2999012, baseEnd_2999012] using wordTrace_append hprefix tailTrace_2999012
  have hstable : (prefixWord ++ tailWord_2999012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999012).length < 2 ^ (prefixWord ++ tailWord_2999012).sum := by decide
  have hdescent : baseEnd_2999012 < baseStart_2999012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999018 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 4, 6]
def baseStart_2999018 : Nat := 118140960795 + 2999018 * 2 ^ 59
def prefixEnd_2999018 : Nat := 4983230072969 + 3 ^ 40 * 2999018 * 2
def baseEnd_2999018 : Nat := 513312575161884187327591

theorem tailTrace_2999018 : CollatzResearch.WordTrace tailWord_2999018 prefixEnd_2999018 513312575161884187327591 := by
  unfold tailWord_2999018
  simp only [CollatzResearch.WordTrace]
  refine ⟨27345793162269363085465427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72922115099384968227907805 27345793162269363085465427)
  ·
    refine ⟨41018689743404044628198141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27345793162269363085465427 41018689743404044628198141)
    ·
      refine ⟨15382008653776516735574303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41018689743404044628198141 15382008653776516735574303)
      ·
        refine ⟨23073012980664775103361455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15382008653776516735574303 23073012980664775103361455)
        ·
          refine ⟨34609519470997162655042183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23073012980664775103361455 34609519470997162655042183)
          ·
            refine ⟨51914279206495743982563275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34609519470997162655042183 51914279206495743982563275)
            ·
              refine ⟨77871418809743615973844913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51914279206495743982563275 77871418809743615973844913)
              ·
                refine ⟨58403564107307711980383685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77871418809743615973844913 58403564107307711980383685)
                ·
                  refine ⟨10950668270120195996321941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58403564107307711980383685 10950668270120195996321941)
                  ·
                    refine ⟨513312575161884187327591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10950668270120195996321941 513312575161884187327591)
                    ·
                      rfl

theorem cell23_2999018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_2999018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999018 prefixEnd_2999018 := by exact prefixLift 2999018
  have htrace : WordTrace (prefixWord ++ tailWord_2999018) baseStart_2999018 baseEnd_2999018 := by
    simpa [prefixWord, tailWord_2999018, baseEnd_2999018] using wordTrace_append hprefix tailTrace_2999018
  have hstable : (prefixWord ++ tailWord_2999018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999018).length < 2 ^ (prefixWord ++ tailWord_2999018).sum := by decide
  have hdescent : baseEnd_2999018 < baseStart_2999018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999088 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 5]
def baseStart_2999088 : Nat := 118140960795 + 2999088 * 2 ^ 59
def prefixEnd_2999088 : Nat := 4983230072969 + 3 ^ 40 * 2999088 * 2
def baseEnd_2999088 : Nat := 1539973669131467288107451

theorem tailTrace_2999088 : CollatzResearch.WordTrace tailWord_2999088 prefixEnd_2999088 1539973669131467288107451 := by
  unfold tailWord_2999088
  simp only [CollatzResearch.WordTrace]
  refine ⟨54692862879411927148454959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72923817172549236197939945 54692862879411927148454959)
  ·
    refine ⟨82039294319117890722682439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54692862879411927148454959 82039294319117890722682439)
    ·
      refine ⟨123058941478676836084023659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82039294319117890722682439 123058941478676836084023659)
      ·
        refine ⟨184588412218015254126035489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123058941478676836084023659 184588412218015254126035489)
        ·
          refine ⟨138441309163511440594526617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184588412218015254126035489 138441309163511440594526617)
          ·
            refine ⟨103830981872633580445894963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138441309163511440594526617 103830981872633580445894963)
            ·
              refine ⟨155746472808950370668842445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103830981872633580445894963 155746472808950370668842445)
              ·
                refine ⟨58404927303356389000815917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155746472808950370668842445 58404927303356389000815917)
                ·
                  refine ⟨21901847738758645875305969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58404927303356389000815917 21901847738758645875305969)
                  ·
                    refine ⟨16426385804068984406479477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21901847738758645875305969 16426385804068984406479477)
                    ·
                      refine ⟨1539973669131467288107451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16426385804068984406479477 1539973669131467288107451)
                      ·
                        rfl

theorem cell23_2999088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 5].length) (baseStart_2999088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999088 prefixEnd_2999088 := by exact prefixLift 2999088
  have htrace : WordTrace (prefixWord ++ tailWord_2999088) baseStart_2999088 baseEnd_2999088 := by
    simpa [prefixWord, tailWord_2999088, baseEnd_2999088] using wordTrace_append hprefix tailTrace_2999088
  have hstable : (prefixWord ++ tailWord_2999088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999088).length < 2 ^ (prefixWord ++ tailWord_2999088).sum := by decide
  have hdescent : baseEnd_2999088 < baseStart_2999088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999110 : List Nat := [6, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2]
def baseStart_2999110 : Nat := 118140960795 + 2999110 * 2 ^ 59
def prefixEnd_2999110 : Nat := 4983230072969 + 3 ^ 40 * 2999110 * 2
def baseEnd_2999110 : Nat := 1539984965705866202032351

theorem tailTrace_2999110 : CollatzResearch.WordTrace tailWord_2999110 prefixEnd_2999110 1539984965705866202032351 := by
  unfold tailWord_2999110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3418329005148254751694087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 72924352109829434702807189 3418329005148254751694087)
  ·
    refine ⟨5127493507722382127541131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3418329005148254751694087 5127493507722382127541131)
    ·
      refine ⟨7691240261583573191311697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5127493507722382127541131 7691240261583573191311697)
      ·
        refine ⟨5768430196187679893483773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7691240261583573191311697 5768430196187679893483773)
        ·
          refine ⟨2163161323570379960056415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5768430196187679893483773 2163161323570379960056415)
          ·
            refine ⟨3244741985355569940084623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2163161323570379960056415 3244741985355569940084623)
            ·
              refine ⟨4867112978033354910126935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3244741985355569940084623 4867112978033354910126935)
              ·
                refine ⟨7300669467050032365190403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4867112978033354910126935 7300669467050032365190403)
                ·
                  refine ⟨10951004200575048547785605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7300669467050032365190403 10951004200575048547785605)
                  ·
                    refine ⟨2053313287607821602709801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10951004200575048547785605 2053313287607821602709801)
                    ·
                      refine ⟨1539984965705866202032351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2053313287607821602709801 1539984965705866202032351)
                      ·
                        rfl

theorem cell23_2999110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_2999110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999110 prefixEnd_2999110 := by exact prefixLift 2999110
  have htrace : WordTrace (prefixWord ++ tailWord_2999110) baseStart_2999110 baseEnd_2999110 := by
    simpa [prefixWord, tailWord_2999110, baseEnd_2999110] using wordTrace_append hprefix tailTrace_2999110
  have hstable : (prefixWord ++ tailWord_2999110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999110).length < 2 ^ (prefixWord ++ tailWord_2999110).sum := by decide
  have hdescent : baseEnd_2999110 < baseStart_2999110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999132 : List Nat := [2, 2, 4, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_2999132 : Nat := 118140960795 + 2999132 * 2 ^ 59
def prefixEnd_2999132 : Nat := 4983230072969 + 3 ^ 40 * 2999132 * 2
def baseEnd_2999132 : Nat := 1539996262280265115957249

theorem tailTrace_2999132 : CollatzResearch.WordTrace tailWord_2999132 prefixEnd_2999132 1539996262280265115957249 := by
  unfold tailWord_2999132
  simp only [CollatzResearch.WordTrace]
  refine ⟨54693665285332224905755825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72924887047109633207674433 54693665285332224905755825)
  ·
    refine ⟨41020248963999168679316869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54693665285332224905755825 41020248963999168679316869)
    ·
      refine ⟨7691296680749844127371913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41020248963999168679316869 7691296680749844127371913)
      ·
        refine ⟨5768472510562383095528935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7691296680749844127371913 5768472510562383095528935)
        ·
          refine ⟨8652708765843574643293403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5768472510562383095528935 8652708765843574643293403)
          ·
            refine ⟨12979063148765361964940105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8652708765843574643293403 12979063148765361964940105)
            ·
              refine ⟨9734297361574021473705079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12979063148765361964940105 9734297361574021473705079)
              ·
                refine ⟨14601446042361032210557619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9734297361574021473705079 14601446042361032210557619)
                ·
                  refine ⟨21902169063541548315836429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14601446042361032210557619 21902169063541548315836429)
                  ·
                    refine ⟨8213313398828080618438661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21902169063541548315836429 8213313398828080618438661)
                    ·
                      refine ⟨1539996262280265115957249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8213313398828080618438661 1539996262280265115957249)
                      ·
                        rfl

theorem cell23_2999132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_2999132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999132 prefixEnd_2999132 := by exact prefixLift 2999132
  have htrace : WordTrace (prefixWord ++ tailWord_2999132) baseStart_2999132 baseEnd_2999132 := by
    simpa [prefixWord, tailWord_2999132, baseEnd_2999132] using wordTrace_append hprefix tailTrace_2999132
  have hstable : (prefixWord ++ tailWord_2999132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999132).length < 2 ^ (prefixWord ++ tailWord_2999132).sum := by decide
  have hdescent : baseEnd_2999132 < baseStart_2999132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999135 : List Nat := [1, 1, 2, 3, 1, 3, 1, 3, 1, 4, 3]
def baseStart_2999135 : Nat := 118140960795 + 2999135 * 2 ^ 59
def prefixEnd_2999135 : Nat := 4983230072969 + 3 ^ 40 * 2999135 * 2
def baseEnd_2999135 : Nat := 1539997802722228604219735

theorem tailTrace_2999135 : CollatzResearch.WordTrace tailWord_2999135 prefixEnd_2999135 1539997802722228604219735 := by
  unfold tailWord_2999135
  simp only [CollatzResearch.WordTrace]
  refine ⟨109387439989653581323870859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72924959993102387549247239 109387439989653581323870859)
  ·
    refine ⟨164081159984480371985806289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109387439989653581323870859 164081159984480371985806289)
    ·
      refine ⟨123060869988360278989354717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164081159984480371985806289 123060869988360278989354717)
      ·
        refine ⟨46147826245635104621008019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123060869988360278989354717 46147826245635104621008019)
        ·
          refine ⟨69221739368452656931512029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46147826245635104621008019 69221739368452656931512029)
          ·
            refine ⟨25958152263169746349317011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69221739368452656931512029 25958152263169746349317011)
            ·
              refine ⟨38937228394754619523975517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25958152263169746349317011 38937228394754619523975517)
              ·
                refine ⟨14601460648032982321490819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38937228394754619523975517 14601460648032982321490819)
                ·
                  refine ⟨21902190972049473482236229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14601460648032982321490819 21902190972049473482236229)
                  ·
                    refine ⟨4106660807259276277919293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21902190972049473482236229 4106660807259276277919293)
                    ·
                      refine ⟨1539997802722228604219735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4106660807259276277919293 1539997802722228604219735)
                      ·
                        rfl

theorem cell23_2999135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_2999135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999135 prefixEnd_2999135 := by exact prefixLift 2999135
  have htrace : WordTrace (prefixWord ++ tailWord_2999135) baseStart_2999135 baseEnd_2999135 := by
    simpa [prefixWord, tailWord_2999135, baseEnd_2999135] using wordTrace_append hprefix tailTrace_2999135
  have hstable : (prefixWord ++ tailWord_2999135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999135).length < 2 ^ (prefixWord ++ tailWord_2999135).sum := by decide
  have hdescent : baseEnd_2999135 < baseStart_2999135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999186 : List Nat := [3, 2, 3, 2, 2, 1, 2, 1, 2, 2, 3]
def baseStart_2999186 : Nat := 118140960795 + 2999186 * 2 ^ 59
def prefixEnd_2999186 : Nat := 4983230072969 + 3 ^ 40 * 2999186 * 2
def baseEnd_2999186 : Nat := 1540023990235607904682001

theorem tailTrace_2999186 : CollatzResearch.WordTrace tailWord_2999186 prefixEnd_2999186 1540023990235607904682001 := by
  unfold tailWord_2999186
  simp only [CollatzResearch.WordTrace]
  refine ⟨27347325028117204258494353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72926200074979211355984941 27347325028117204258494353)
  ·
    refine ⟨20510493771087903193870765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27347325028117204258494353 20510493771087903193870765)
    ·
      refine ⟨7691435164157963697701537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20510493771087903193870765 7691435164157963697701537)
      ·
        refine ⟨5768576373118472773276153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7691435164157963697701537 5768576373118472773276153)
        ·
          refine ⟨4326432279838854579957115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5768576373118472773276153 4326432279838854579957115)
          ·
            refine ⟨6489648419758281869935673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4326432279838854579957115 6489648419758281869935673)
            ·
              refine ⟨4867236314818711402451755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6489648419758281869935673 4867236314818711402451755)
              ·
                refine ⟨7300854472228067103677633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4867236314818711402451755 7300854472228067103677633)
                ·
                  refine ⟨5475640854171050327758225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7300854472228067103677633 5475640854171050327758225)
                  ·
                    refine ⟨4106730640628287745818669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5475640854171050327758225 4106730640628287745818669)
                    ·
                      refine ⟨1540023990235607904682001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4106730640628287745818669 1540023990235607904682001)
                      ·
                        rfl

theorem cell23_2999186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_2999186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999186 prefixEnd_2999186 := by exact prefixLift 2999186
  have htrace : WordTrace (prefixWord ++ tailWord_2999186) baseStart_2999186 baseEnd_2999186 := by
    simpa [prefixWord, tailWord_2999186, baseEnd_2999186] using wordTrace_append hprefix tailTrace_2999186
  have hstable : (prefixWord ++ tailWord_2999186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999186).length < 2 ^ (prefixWord ++ tailWord_2999186).sum := by decide
  have hdescent : baseEnd_2999186 < baseStart_2999186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999232 : List Nat := [2, 1, 1, 2, 3, 4, 2, 1, 1, 6]
def baseStart_2999232 : Nat := 118140960795 + 2999232 * 2 ^ 59
def prefixEnd_2999232 : Nat := 4983230072969 + 3 ^ 40 * 2999232 * 2
def baseEnd_2999232 : Nat := 513349203448571574902263

theorem tailTrace_2999232 : CollatzResearch.WordTrace tailWord_2999232 prefixEnd_2999232 513349203448571574902263 := by
  unfold tailWord_2999232
  simp only [CollatzResearch.WordTrace]
  refine ⟨54695488935151083445075975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72927318580201444593434633 54695488935151083445075975)
  ·
    refine ⟨82043233402726625167613963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54695488935151083445075975 82043233402726625167613963)
    ·
      refine ⟨123064850104089937751420945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82043233402726625167613963 123064850104089937751420945)
      ·
        refine ⟨92298637578067453313565709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123064850104089937751420945 92298637578067453313565709)
        ·
          refine ⟨34611989091775294992587141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92298637578067453313565709 34611989091775294992587141)
          ·
            refine ⟨6489747954707867811110089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34611989091775294992587141 6489747954707867811110089)
            ·
              refine ⟨4867310966030900858332567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6489747954707867811110089 4867310966030900858332567)
              ·
                refine ⟨7300966449046351287498851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4867310966030900858332567 7300966449046351287498851)
                ·
                  refine ⟨10951449673569526931248277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7300966449046351287498851 10951449673569526931248277)
                  ·
                    refine ⟨513349203448571574902263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10951449673569526931248277 513349203448571574902263)
                    ·
                      rfl

theorem cell23_2999232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 1, 6].length) (baseStart_2999232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999232 prefixEnd_2999232 := by exact prefixLift 2999232
  have htrace : WordTrace (prefixWord ++ tailWord_2999232) baseStart_2999232 baseEnd_2999232 := by
    simpa [prefixWord, tailWord_2999232, baseEnd_2999232] using wordTrace_append hprefix tailTrace_2999232
  have hstable : (prefixWord ++ tailWord_2999232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999232).length < 2 ^ (prefixWord ++ tailWord_2999232).sum := by decide
  have hdescent : baseEnd_2999232 < baseStart_2999232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999235 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 4]
def baseStart_2999235 : Nat := 118140960795 + 2999235 * 2 ^ 59
def prefixEnd_2999235 : Nat := 4983230072969 + 3 ^ 40 * 2999235 * 2
def baseEnd_2999235 : Nat := 1540049150787678212969275

theorem tailTrace_2999235 : CollatzResearch.WordTrace tailWord_2999235 prefixEnd_2999235 1540049150787678212969275 := by
  unfold tailWord_2999235
  simp only [CollatzResearch.WordTrace]
  refine ⟨109391087289291298402511159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72927391526194198935007439 109391087289291298402511159)
  ·
    refine ⟨164086630933936947603766739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109391087289291298402511159 164086630933936947603766739)
    ·
      refine ⟨246129946400905421405650109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164086630933936947603766739 246129946400905421405650109)
      ·
        refine ⟨92298729900339533027118791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246129946400905421405650109 92298729900339533027118791)
        ·
          refine ⟨138448094850509299540678187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92298729900339533027118791 138448094850509299540678187)
          ·
            refine ⟨207672142275763949311017281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138448094850509299540678187 207672142275763949311017281)
            ·
              refine ⟨155754106706822961983262961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207672142275763949311017281 155754106706822961983262961)
              ·
                refine ⟨116815580030117221487447221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155754106706822961983262961 116815580030117221487447221)
                ·
                  refine ⟨10951460627823489514448177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116815580030117221487447221 10951460627823489514448177)
                  ·
                    refine ⟨8213595470867617135836133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10951460627823489514448177 8213595470867617135836133)
                    ·
                      refine ⟨1540049150787678212969275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8213595470867617135836133 1540049150787678212969275)
                      ·
                        rfl

theorem cell23_2999235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_2999235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999235 prefixEnd_2999235 := by exact prefixLift 2999235
  have htrace : WordTrace (prefixWord ++ tailWord_2999235) baseStart_2999235 baseEnd_2999235 := by
    simpa [prefixWord, tailWord_2999235, baseEnd_2999235] using wordTrace_append hprefix tailTrace_2999235
  have hstable : (prefixWord ++ tailWord_2999235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999235).length < 2 ^ (prefixWord ++ tailWord_2999235).sum := by decide
  have hdescent : baseEnd_2999235 < baseStart_2999235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999239 : List Nat := [1, 1, 4, 1, 1, 2, 3, 1, 5, 2, 2]
def baseStart_2999239 : Nat := 118140960795 + 2999239 * 2 ^ 59
def prefixEnd_2999239 : Nat := 4983230072969 + 3 ^ 40 * 2999239 * 2
def baseEnd_2999239 : Nat := 1540051204710296197319257

theorem tailTrace_2999239 : CollatzResearch.WordTrace tailWord_2999239 prefixEnd_2999239 1540051204710296197319257 := by
  unfold tailWord_2999239
  simp only [CollatzResearch.WordTrace]
  refine ⟨109391233181276807085656771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72927488787517871390437847 109391233181276807085656771)
  ·
    refine ⟨164086849771915210628485157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109391233181276807085656771 164086849771915210628485157)
    ·
      refine ⟨30766284332234101992840967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164086849771915210628485157 30766284332234101992840967)
      ·
        refine ⟨46149426498351152989261451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30766284332234101992840967 46149426498351152989261451)
        ·
          refine ⟨69224139747526729483892177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46149426498351152989261451 69224139747526729483892177)
          ·
            refine ⟨51918104810645047112919133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69224139747526729483892177 51918104810645047112919133)
            ·
              refine ⟨19469289303991892667344675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51918104810645047112919133 19469289303991892667344675)
              ·
                refine ⟨29203933955987839001017013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19469289303991892667344675 29203933955987839001017013)
                ·
                  refine ⟨2737868808373859906345345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29203933955987839001017013 2737868808373859906345345)
                  ·
                    refine ⟨2053401606280394929759009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2737868808373859906345345 2053401606280394929759009)
                    ·
                      refine ⟨1540051204710296197319257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2053401606280394929759009 1540051204710296197319257)
                      ·
                        rfl

theorem cell23_2999239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 5, 2, 2].length) (baseStart_2999239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999239 prefixEnd_2999239 := by exact prefixLift 2999239
  have htrace : WordTrace (prefixWord ++ tailWord_2999239) baseStart_2999239 baseEnd_2999239 := by
    simpa [prefixWord, tailWord_2999239, baseEnd_2999239] using wordTrace_append hprefix tailTrace_2999239
  have hstable : (prefixWord ++ tailWord_2999239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999239).length < 2 ^ (prefixWord ++ tailWord_2999239).sum := by decide
  have hdescent : baseEnd_2999239 < baseStart_2999239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999253 : List Nat := [1, 3, 2, 3, 4, 1, 2, 1, 1, 5]
def baseStart_2999253 : Nat := 118140960795 + 2999253 * 2 ^ 59
def prefixEnd_2999253 : Nat := 4983230072969 + 3 ^ 40 * 2999253 * 2
def baseEnd_2999253 : Nat := 513352797813153047514731

theorem tailTrace_2999253 : CollatzResearch.WordTrace tailWord_2999253 prefixEnd_2999253 513352797813153047514731 := by
  unfold tailWord_2999253
  simp only [CollatzResearch.WordTrace]
  refine ⟨109391743803226087476666413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72927829202150724984444275 109391743803226087476666413)
  ·
    refine ⟨41021903926209782803749905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109391743803226087476666413 41021903926209782803749905)
    ·
      refine ⟨30766427944657337102812429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41021903926209782803749905 30766427944657337102812429)
      ·
        refine ⟨11537410479246501413554661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30766427944657337102812429 11537410479246501413554661)
        ·
          refine ⟨2163264464858719015041499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11537410479246501413554661 2163264464858719015041499)
          ·
            refine ⟨3244896697288078522562249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2163264464858719015041499 3244896697288078522562249)
            ·
              refine ⟨2433672522966058891921687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3244896697288078522562249 2433672522966058891921687)
              ·
                refine ⟨3650508784449088337882531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2433672522966058891921687 3650508784449088337882531)
                ·
                  refine ⟨5475763176673632506823797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3650508784449088337882531 5475763176673632506823797)
                  ·
                    refine ⟨513352797813153047514731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5475763176673632506823797 513352797813153047514731)
                    ·
                      rfl

theorem cell23_2999253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 1, 5].length) (baseStart_2999253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999253 prefixEnd_2999253 := by exact prefixLift 2999253
  have htrace : WordTrace (prefixWord ++ tailWord_2999253) baseStart_2999253 baseEnd_2999253 := by
    simpa [prefixWord, tailWord_2999253, baseEnd_2999253] using wordTrace_append hprefix tailTrace_2999253
  have hstable : (prefixWord ++ tailWord_2999253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999253).length < 2 ^ (prefixWord ++ tailWord_2999253).sum := by decide
  have hdescent : baseEnd_2999253 < baseStart_2999253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999256 : List Nat := [2, 1, 2, 2, 2, 5, 2, 1, 1, 1, 4]
def baseStart_2999256 : Nat := 118140960795 + 2999256 * 2 ^ 59
def prefixEnd_2999256 : Nat := 4983230072969 + 3 ^ 40 * 2999256 * 2
def baseEnd_2999256 : Nat := 1540059933881422630806679

theorem tailTrace_2999256 : CollatzResearch.WordTrace tailWord_2999256 prefixEnd_2999256 1540059933881422630806679 := by
  unfold tailWord_2999256
  simp only [CollatzResearch.WordTrace]
  refine ⟨54695926611107609494512811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72927902148143479326017081 54695926611107609494512811)
  ·
    refine ⟨82043889916661414241769217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54695926611107609494512811 82043889916661414241769217)
    ·
      refine ⟨61532917437496060681326913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82043889916661414241769217 61532917437496060681326913)
      ·
        refine ⟨46149688078122045510995185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61532917437496060681326913 46149688078122045510995185)
        ·
          refine ⟨34612266058591534133246389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46149688078122045510995185 34612266058591534133246389)
          ·
            refine ⟨3244899942992956324991849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34612266058591534133246389 3244899942992956324991849)
            ·
              refine ⟨2433674957244717243743887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3244899942992956324991849 2433674957244717243743887)
              ·
                refine ⟨3650512435867075865615831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2433674957244717243743887 3650512435867075865615831)
                ·
                  refine ⟨5475768653800613798423747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3650512435867075865615831 5475768653800613798423747)
                  ·
                    refine ⟨8213652980700920697635621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5475768653800613798423747 8213652980700920697635621)
                    ·
                      refine ⟨1540059933881422630806679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8213652980700920697635621 1540059933881422630806679)
                      ·
                        rfl

theorem cell23_2999256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 1, 1, 4].length) (baseStart_2999256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999256 prefixEnd_2999256 := by exact prefixLift 2999256
  have htrace : WordTrace (prefixWord ++ tailWord_2999256) baseStart_2999256 baseEnd_2999256 := by
    simpa [prefixWord, tailWord_2999256, baseEnd_2999256] using wordTrace_append hprefix tailTrace_2999256
  have hstable : (prefixWord ++ tailWord_2999256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999256).length < 2 ^ (prefixWord ++ tailWord_2999256).sum := by decide
  have hdescent : baseEnd_2999256 < baseStart_2999256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999265 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 2, 2, 6]
def baseStart_2999265 : Nat := 118140960795 + 2999265 * 2 ^ 59
def prefixEnd_2999265 : Nat := 4983230072969 + 3 ^ 40 * 2999265 * 2
def baseEnd_2999265 : Nat := 1540064555207313095594137

theorem tailTrace_2999265 : CollatzResearch.WordTrace tailWord_2999265 prefixEnd_2999265 1540064555207313095594137 := by
  unfold tailWord_2999265
  simp only [CollatzResearch.WordTrace]
  refine ⟨109392181479182613526103249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72928120986121742350735499 109392181479182613526103249)
  ·
    refine ⟨82044136109386960144577437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109392181479182613526103249 82044136109386960144577437)
    ·
      refine ⟨30766551041020110054216539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82044136109386960144577437 30766551041020110054216539)
      ·
        refine ⟨46149826561530165081324809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30766551041020110054216539 46149826561530165081324809)
        ·
          refine ⟨34612369921147623810993607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46149826561530165081324809 34612369921147623810993607)
          ·
            refine ⟨51918554881721435716490411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34612369921147623810993607 51918554881721435716490411)
            ·
              refine ⟨77877832322582153574735617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51918554881721435716490411 77877832322582153574735617)
              ·
                refine ⟨58408374241936615181051713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77877832322582153574735617 58408374241936615181051713)
                ·
                  refine ⟨43806280681452461385788785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58408374241936615181051713 43806280681452461385788785)
                  ·
                    refine ⟨32854710511089346039341589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43806280681452461385788785 32854710511089346039341589)
                    ·
                      refine ⟨1540064555207313095594137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32854710511089346039341589 1540064555207313095594137)
                      ·
                        rfl

theorem cell23_2999265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_2999265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999265 prefixEnd_2999265 := by exact prefixLift 2999265
  have htrace : WordTrace (prefixWord ++ tailWord_2999265) baseStart_2999265 baseEnd_2999265 := by
    simpa [prefixWord, tailWord_2999265, baseEnd_2999265] using wordTrace_append hprefix tailTrace_2999265
  have hstable : (prefixWord ++ tailWord_2999265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999265).length < 2 ^ (prefixWord ++ tailWord_2999265).sum := by decide
  have hdescent : baseEnd_2999265 < baseStart_2999265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999266 : List Nat := [3, 3, 3, 1, 1, 2, 1, 1, 4, 4]
def baseStart_2999266 : Nat := 118140960795 + 2999266 * 2 ^ 59
def prefixEnd_2999266 : Nat := 4983230072969 + 3 ^ 40 * 2999266 * 2
def baseEnd_2999266 : Nat := 513355022895989197227211

theorem tailTrace_2999266 : CollatzResearch.WordTrace tailWord_2999266 prefixEnd_2999266 513355022895989197227211 := by
  unfold tailWord_2999266
  simp only [CollatzResearch.WordTrace]
  refine ⟨27348054488044747674222413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72928145301452660464593101 27348054488044747674222413)
  ·
    refine ⟨10255520433016780377833405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27348054488044747674222413 10255520433016780377833405)
    ·
      refine ⟨3845820162381292641687527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10255520433016780377833405 3845820162381292641687527)
      ·
        refine ⟨5768730243571938962531291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3845820162381292641687527 5768730243571938962531291)
        ·
          refine ⟨8653095365357908443796937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5768730243571938962531291 8653095365357908443796937)
          ·
            refine ⟨6489821524018431332847703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8653095365357908443796937 6489821524018431332847703)
            ·
              refine ⟨9734732286027646999271555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6489821524018431332847703 9734732286027646999271555)
              ·
                refine ⟨14602098429041470498907333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9734732286027646999271555 14602098429041470498907333)
                ·
                  refine ⟨2737893455445275718545125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14602098429041470498907333 2737893455445275718545125)
                  ·
                    refine ⟨513355022895989197227211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2737893455445275718545125 513355022895989197227211)
                    ·
                      rfl

theorem cell23_2999266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_2999266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999266 prefixEnd_2999266 := by exact prefixLift 2999266
  have htrace : WordTrace (prefixWord ++ tailWord_2999266) baseStart_2999266 baseEnd_2999266 := by
    simpa [prefixWord, tailWord_2999266, baseEnd_2999266] using wordTrace_append hprefix tailTrace_2999266
  have hstable : (prefixWord ++ tailWord_2999266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999266).length < 2 ^ (prefixWord ++ tailWord_2999266).sum := by decide
  have hdescent : baseEnd_2999266 < baseStart_2999266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999272 : List Nat := [2, 1, 4, 1, 1, 1, 2, 2, 3, 3, 3]
def baseStart_2999272 : Nat := 118140960795 + 2999272 * 2 ^ 59
def prefixEnd_2999272 : Nat := 4983230072969 + 3 ^ 40 * 2999272 * 2
def baseEnd_2999272 : Nat := 1540068149571894568206605

theorem tailTrace_2999272 : CollatzResearch.WordTrace tailWord_2999272 prefixEnd_2999272 1540068149571894568206605 := by
  unfold tailWord_2999272
  simp only [CollatzResearch.WordTrace]
  refine ⟨54696218395078626860804035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72928291193438169147738713 54696218395078626860804035)
  ·
    refine ⟨82044327592617940291206053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54696218395078626860804035 82044327592617940291206053)
    ·
      refine ⟨15383311423615863804601135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82044327592617940291206053 15383311423615863804601135)
      ·
        refine ⟨23074967135423795706901703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15383311423615863804601135 23074967135423795706901703)
        ·
          refine ⟨34612450703135693560352555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23074967135423795706901703 34612450703135693560352555)
          ·
            refine ⟨51918676054703540340528833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34612450703135693560352555 51918676054703540340528833)
            ·
              refine ⟨38939007041027655255396625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51918676054703540340528833 38939007041027655255396625)
              ·
                refine ⟨29204255280770741441547469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38939007041027655255396625 29204255280770741441547469)
                ·
                  refine ⟨10951595730289028040580301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29204255280770741441547469 10951595730289028040580301)
                  ·
                    refine ⟨4106848398858385515217613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10951595730289028040580301 4106848398858385515217613)
                    ·
                      refine ⟨1540068149571894568206605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4106848398858385515217613 1540068149571894568206605)
                      ·
                        rfl

theorem cell23_2999272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_2999272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999272 prefixEnd_2999272 := by exact prefixLift 2999272
  have htrace : WordTrace (prefixWord ++ tailWord_2999272) baseStart_2999272 baseEnd_2999272 := by
    simpa [prefixWord, tailWord_2999272, baseEnd_2999272] using wordTrace_append hprefix tailTrace_2999272
  have hstable : (prefixWord ++ tailWord_2999272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999272).length < 2 ^ (prefixWord ++ tailWord_2999272).sum := by decide
  have hdescent : baseEnd_2999272 < baseStart_2999272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999286 : List Nat := [5, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4]
def baseStart_2999286 : Nat := 118140960795 + 2999286 * 2 ^ 59
def prefixEnd_2999286 : Nat := 4983230072969 + 3 ^ 40 * 2999286 * 2
def baseEnd_2999286 : Nat := 1540075338301057513431541

theorem tailTrace_2999286 : CollatzResearch.WordTrace tailWord_2999286 prefixEnd_2999286 1540075338301057513431541 := by
  unfold tailWord_2999286
  simp only [CollatzResearch.WordTrace]
  refine ⟨6837059213256658382038607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72928631608071022741745141 6837059213256658382038607)
  ·
    refine ⟨10255588819884987573057911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6837059213256658382038607 10255588819884987573057911)
    ·
      refine ⟨15383383229827481359586867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10255588819884987573057911 15383383229827481359586867)
      ·
        refine ⟨23075074844741222039380301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15383383229827481359586867 23075074844741222039380301)
        ·
          refine ⟨8653153066777958264767613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23075074844741222039380301 8653153066777958264767613)
          ·
            refine ⟨3244932400041734349287855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8653153066777958264767613 3244932400041734349287855)
            ·
              refine ⟨4867398600062601523931783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3244932400041734349287855 4867398600062601523931783)
              ·
                refine ⟨7301097900093902285897675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4867398600062601523931783 7301097900093902285897675)
                ·
                  refine ⟨10951646850140853428846513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7301097900093902285897675 10951646850140853428846513)
                  ·
                    refine ⟨8213735137605640071634885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10951646850140853428846513 8213735137605640071634885)
                    ·
                      refine ⟨1540075338301057513431541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8213735137605640071634885 1540075338301057513431541)
                      ·
                        rfl

theorem cell23_2999286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_2999286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999286 prefixEnd_2999286 := by exact prefixLift 2999286
  have htrace : WordTrace (prefixWord ++ tailWord_2999286) baseStart_2999286 baseEnd_2999286 := by
    simpa [prefixWord, tailWord_2999286, baseEnd_2999286] using wordTrace_append hprefix tailTrace_2999286
  have hstable : (prefixWord ++ tailWord_2999286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999286).length < 2 ^ (prefixWord ++ tailWord_2999286).sum := by decide
  have hdescent : baseEnd_2999286 < baseStart_2999286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999305 : List Nat := [1, 2, 1, 1, 3, 1, 1, 4, 1, 8]
def baseStart_2999305 : Nat := 118140960795 + 2999305 * 2 ^ 59
def prefixEnd_2999305 : Nat := 4983230072969 + 3 ^ 40 * 2999305 * 2
def baseEnd_2999305 : Nat := 513361698144497646364651

theorem tailTrace_2999305 : CollatzResearch.WordTrace tailWord_2999305 prefixEnd_2999305 513361698144497646364651 := by
  unfold tailWord_2999305
  simp only [CollatzResearch.WordTrace]
  refine ⟨109393640399037700357559369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72929093599358466905039579 109393640399037700357559369)
  ·
    refine ⟨82045230299278275268169527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109393640399037700357559369 82045230299278275268169527)
    ·
      refine ⟨123067845448917412902254291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82045230299278275268169527 123067845448917412902254291)
      ·
        refine ⟨184601768173376119353381437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123067845448917412902254291 184601768173376119353381437)
        ·
          refine ⟨69225663065016044757518039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184601768173376119353381437 69225663065016044757518039)
          ·
            refine ⟨103838494597524067136277059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69225663065016044757518039 103838494597524067136277059)
            ·
              refine ⟨155757741896286100704415589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103838494597524067136277059 155757741896286100704415589)
              ·
                refine ⟨29204576605553643882077923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155757741896286100704415589 29204576605553643882077923)
                ·
                  refine ⟨43806864908330465823116885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29204576605553643882077923 43806864908330465823116885)
                  ·
                    refine ⟨513361698144497646364651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 43806864908330465823116885 513361698144497646364651)
                    ·
                      rfl

theorem cell23_2999305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 8].length) (baseStart_2999305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999305 prefixEnd_2999305 := by exact prefixLift 2999305
  have htrace : WordTrace (prefixWord ++ tailWord_2999305) baseStart_2999305 baseEnd_2999305 := by
    simpa [prefixWord, tailWord_2999305, baseEnd_2999305] using wordTrace_append hprefix tailTrace_2999305
  have hstable : (prefixWord ++ tailWord_2999305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999305).length < 2 ^ (prefixWord ++ tailWord_2999305).sum := by decide
  have hdescent : baseEnd_2999305 < baseStart_2999305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999350 : List Nat := [5, 1, 2, 1, 1, 4, 1, 2, 1, 3, 2]
def baseStart_2999350 : Nat := 118140960795 + 2999350 * 2 ^ 59
def prefixEnd_2999350 : Nat := 4983230072969 + 3 ^ 40 * 2999350 * 2
def baseEnd_2999350 : Nat := 1540108201062945263031247

theorem tailTrace_2999350 : CollatzResearch.WordTrace tailWord_2999350 prefixEnd_2999350 1540108201062945263031247 := by
  unfold tailWord_2999350
  simp only [CollatzResearch.WordTrace]
  refine ⟨6837205105242167065184219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72930187789249782028631669 6837205105242167065184219)
  ·
    refine ⟨10255807657863250597776329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6837205105242167065184219 10255807657863250597776329)
    ·
      refine ⟨7691855743397437948332247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10255807657863250597776329 7691855743397437948332247)
      ·
        refine ⟨11537783615096156922498371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7691855743397437948332247 11537783615096156922498371)
        ·
          refine ⟨17306675422644235383747557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11537783615096156922498371 17306675422644235383747557)
          ·
            refine ⟨3245001641745794134452667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17306675422644235383747557 3245001641745794134452667)
            ·
              refine ⟨4867502462618691201679001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3245001641745794134452667 4867502462618691201679001)
              ·
                refine ⟨3650626846964018401259251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4867502462618691201679001 3650626846964018401259251)
                ·
                  refine ⟨5475940270446027601888877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3650626846964018401259251 5475940270446027601888877)
                  ·
                    refine ⟨2053477601417260350708329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5475940270446027601888877 2053477601417260350708329)
                    ·
                      refine ⟨1540108201062945263031247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2053477601417260350708329 1540108201062945263031247)
                      ·
                        rfl

theorem cell23_2999350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_2999350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999350 prefixEnd_2999350 := by exact prefixLift 2999350
  have htrace : WordTrace (prefixWord ++ tailWord_2999350) baseStart_2999350 baseEnd_2999350 := by
    simpa [prefixWord, tailWord_2999350, baseEnd_2999350] using wordTrace_append hprefix tailTrace_2999350
  have hstable : (prefixWord ++ tailWord_2999350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999350).length < 2 ^ (prefixWord ++ tailWord_2999350).sum := by decide
  have hdescent : baseEnd_2999350 < baseStart_2999350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999366 : List Nat := [6, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_2999366 : Nat := 118140960795 + 2999366 * 2 ^ 59
def prefixEnd_2999366 : Nat := 4983230072969 + 3 ^ 40 * 2999366 * 2
def baseEnd_2999366 : Nat := 1540116416753417200431173

theorem tailTrace_2999366 : CollatzResearch.WordTrace tailWord_2999366 prefixEnd_2999366 1540116416753417200431173 := by
  unfold tailWord_2999366
  simp only [CollatzResearch.WordTrace]
  refine ⟨3418620789119272117985311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 72930576834544471850353301 3418620789119272117985311)
  ·
    refine ⟨5127931183678908176977967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3418620789119272117985311 5127931183678908176977967)
    ·
      refine ⟨7691896775518362265466951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5127931183678908176977967 7691896775518362265466951)
      ·
        refine ⟨11537845163277543398200427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7691896775518362265466951 11537845163277543398200427)
        ·
          refine ⟨17306767744916315097300641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11537845163277543398200427 17306767744916315097300641)
          ·
            refine ⟨12980075808687236322975481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17306767744916315097300641 12980075808687236322975481)
            ·
              refine ⟨9735056856515427242231611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12980075808687236322975481 9735056856515427242231611)
              ·
                refine ⟨14602585284773140863347417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9735056856515427242231611 14602585284773140863347417)
                ·
                  refine ⟨10951938963579855647510563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14602585284773140863347417 10951938963579855647510563)
                  ·
                    refine ⟨16427908445369783471265845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10951938963579855647510563 16427908445369783471265845)
                    ·
                      refine ⟨1540116416753417200431173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16427908445369783471265845 1540116416753417200431173)
                      ·
                        rfl

theorem cell23_2999366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_2999366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999366 prefixEnd_2999366 := by exact prefixLift 2999366
  have htrace : WordTrace (prefixWord ++ tailWord_2999366) baseStart_2999366 baseEnd_2999366 := by
    simpa [prefixWord, tailWord_2999366, baseEnd_2999366] using wordTrace_append hprefix tailTrace_2999366
  have hstable : (prefixWord ++ tailWord_2999366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999366).length < 2 ^ (prefixWord ++ tailWord_2999366).sum := by decide
  have hdescent : baseEnd_2999366 < baseStart_2999366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999392 : List Nat := [2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 5]
def baseStart_2999392 : Nat := 118140960795 + 2999392 * 2 ^ 59
def prefixEnd_2999392 : Nat := 4983230072969 + 3 ^ 40 * 2999392 * 2
def baseEnd_2999392 : Nat := 1540129767250434098706053

theorem tailTrace_2999392 : CollatzResearch.WordTrace tailWord_2999392 prefixEnd_2999392 1540129767250434098706053 := by
  unfold tailWord_2999392
  simp only [CollatzResearch.WordTrace]
  refine ⟨54698406774861257107988215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72931209033148342810650953 54698406774861257107988215)
  ·
    refine ⟨82047610162291885661982323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54698406774861257107988215 82047610162291885661982323)
    ·
      refine ⟨123071415243437828492973485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82047610162291885661982323 123071415243437828492973485)
      ·
        refine ⟨46151780716289185684865057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123071415243437828492973485 46151780716289185684865057)
        ·
          refine ⟨34613835537216889263648793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46151780716289185684865057 34613835537216889263648793)
          ·
            refine ⟨25960376652912666947736595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34613835537216889263648793 25960376652912666947736595)
            ·
              refine ⟨38940564979369000421604893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25960376652912666947736595 38940564979369000421604893)
              ·
                refine ⟨14602711867263375158101835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38940564979369000421604893 14602711867263375158101835)
                ·
                  refine ⟨21904067800895062737152753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14602711867263375158101835 21904067800895062737152753)
                  ·
                    refine ⟨16428050850671297052864565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21904067800895062737152753 16428050850671297052864565)
                    ·
                      refine ⟨1540129767250434098706053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16428050850671297052864565 1540129767250434098706053)
                      ·
                        rfl

theorem cell23_2999392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_2999392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999392 prefixEnd_2999392 := by exact prefixLift 2999392
  have htrace : WordTrace (prefixWord ++ tailWord_2999392) baseStart_2999392 baseEnd_2999392 := by
    simpa [prefixWord, tailWord_2999392, baseEnd_2999392] using wordTrace_append hprefix tailTrace_2999392
  have hstable : (prefixWord ++ tailWord_2999392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999392).length < 2 ^ (prefixWord ++ tailWord_2999392).sum := by decide
  have hdescent : baseEnd_2999392 < baseStart_2999392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999496 : List Nat := [2, 1, 3, 1, 2, 1, 3, 1, 4, 3, 2]
def baseStart_2999496 : Nat := 118140960795 + 2999496 * 2 ^ 59
def prefixEnd_2999496 : Nat := 4983230072969 + 3 ^ 40 * 2999496 * 2
def baseEnd_2999496 : Nat := 1540183169238501691805575

theorem tailTrace_2999496 : CollatzResearch.WordTrace tailWord_2999496 prefixEnd_2999496 1540183169238501691805575 := by
  unfold tailWord_2999496
  simp only [CollatzResearch.WordTrace]
  refine ⟨54700303370672869988881171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72933737827563826651841561 54700303370672869988881171)
  ·
    refine ⟨82050455056009304983321757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54700303370672869988881171 82050455056009304983321757)
    ·
      refine ⟨30768920646003489368745659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82050455056009304983321757 30768920646003489368745659)
      ·
        refine ⟨46153380969005234053118489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30768920646003489368745659 46153380969005234053118489)
        ·
          refine ⟨34615035726753925539838867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46153380969005234053118489 34615035726753925539838867)
          ·
            refine ⟨51922553590130888309758301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34615035726753925539838867 51922553590130888309758301)
            ·
              refine ⟨19470957596299083116159363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51922553590130888309758301 19470957596299083116159363)
              ·
                refine ⟨29206436394448624674239045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19470957596299083116159363 29206436394448624674239045)
                ·
                  refine ⟨5476206823959117126419821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29206436394448624674239045 5476206823959117126419821)
                  ·
                    refine ⟨2053577558984668922407433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5476206823959117126419821 2053577558984668922407433)
                    ·
                      refine ⟨1540183169238501691805575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2053577558984668922407433 1540183169238501691805575)
                      ·
                        rfl

theorem cell23_2999496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 4, 3, 2].length) (baseStart_2999496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999496 prefixEnd_2999496 := by exact prefixLift 2999496
  have htrace : WordTrace (prefixWord ++ tailWord_2999496) baseStart_2999496 baseEnd_2999496 := by
    simpa [prefixWord, tailWord_2999496, baseEnd_2999496] using wordTrace_append hprefix tailTrace_2999496
  have hstable : (prefixWord ++ tailWord_2999496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999496).length < 2 ^ (prefixWord ++ tailWord_2999496).sum := by decide
  have hdescent : baseEnd_2999496 < baseStart_2999496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999539 : List Nat := [1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 4]
def baseStart_2999539 : Nat := 118140960795 + 2999539 * 2 ^ 59
def prefixEnd_2999539 : Nat := 4983230072969 + 3 ^ 40 * 2999539 * 2
def baseEnd_2999539 : Nat := 1540205248906645023567877

theorem tailTrace_2999539 : CollatzResearch.WordTrace tailWord_2999539 prefixEnd_2999539 1540205248906645023567877 := by
  unfold tailWord_2999539
  simp only [CollatzResearch.WordTrace]
  refine ⟨109402175080189958321577671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72934783386793305547718447 109402175080189958321577671)
  ·
    refine ⟨164103262620284937482366507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109402175080189958321577671 164103262620284937482366507)
    ·
      refine ⟨246154893930427406223549761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164103262620284937482366507 246154893930427406223549761)
      ·
        refine ⟨184616170447820554667662321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246154893930427406223549761 184616170447820554667662321)
        ·
          refine ⟨138462127835865416000746741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184616170447820554667662321 138462127835865416000746741)
          ·
            refine ⟨12980824484612382750070007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 138462127835865416000746741 12980824484612382750070007)
            ·
              refine ⟨19471236726918574125105011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12980824484612382750070007 19471236726918574125105011)
              ·
                refine ⟨29206855090377861187657517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19471236726918574125105011 29206855090377861187657517)
                ·
                  refine ⟨10952570658891697945371569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29206855090377861187657517 10952570658891697945371569)
                  ·
                    refine ⟨8214427994168773459028677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10952570658891697945371569 8214427994168773459028677)
                    ·
                      refine ⟨1540205248906645023567877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8214427994168773459028677 1540205248906645023567877)
                      ·
                        rfl

theorem cell23_2999539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 4].length) (baseStart_2999539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999539 prefixEnd_2999539 := by exact prefixLift 2999539
  have htrace : WordTrace (prefixWord ++ tailWord_2999539) baseStart_2999539 baseEnd_2999539 := by
    simpa [prefixWord, tailWord_2999539, baseEnd_2999539] using wordTrace_append hprefix tailTrace_2999539
  have hstable : (prefixWord ++ tailWord_2999539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999539).length < 2 ^ (prefixWord ++ tailWord_2999539).sum := by decide
  have hdescent : baseEnd_2999539 < baseStart_2999539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999553 : List Nat := [1, 2, 4, 1, 1, 4, 2, 2, 2, 4]
def baseStart_2999553 : Nat := 118140960795 + 2999553 * 2 ^ 59
def prefixEnd_2999553 : Nat := 4983230072969 + 3 ^ 40 * 2999553 * 2
def baseEnd_2999553 : Nat := 513404145878602656264271

theorem tailTrace_2999553 : CollatzResearch.WordTrace tailWord_2999553 prefixEnd_2999553 513404145878602656264271 := by
  unfold tailWord_2999553
  simp only [CollatzResearch.WordTrace]
  refine ⟨109402685702139238712587313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72935123801426159141724875 109402685702139238712587313)
  ·
    refine ⟨82052014276604429034440485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109402685702139238712587313 82052014276604429034440485)
    ·
      refine ⟨15384752676863330443957591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82052014276604429034440485 15384752676863330443957591)
      ·
        refine ⟨23077129015294995665936387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15384752676863330443957591 23077129015294995665936387)
        ·
          refine ⟨34615693522942493498904581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23077129015294995665936387 34615693522942493498904581)
          ·
            refine ⟨6490442535551717531044609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34615693522942493498904581 6490442535551717531044609)
            ·
              refine ⟨4867831901663788148283457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6490442535551717531044609 4867831901663788148283457)
              ·
                refine ⟨3650873926247841111212593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4867831901663788148283457 3650873926247841111212593)
                ·
                  refine ⟨2738155444685880833409445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3650873926247841111212593 2738155444685880833409445)
                  ·
                    refine ⟨513404145878602656264271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2738155444685880833409445 513404145878602656264271)
                    ·
                      rfl

theorem cell23_2999553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_2999553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999553 prefixEnd_2999553 := by exact prefixLift 2999553
  have htrace : WordTrace (prefixWord ++ tailWord_2999553) baseStart_2999553 baseEnd_2999553 := by
    simpa [prefixWord, tailWord_2999553, baseEnd_2999553] using wordTrace_append hprefix tailTrace_2999553
  have hstable : (prefixWord ++ tailWord_2999553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999553).length < 2 ^ (prefixWord ++ tailWord_2999553).sum := by decide
  have hdescent : baseEnd_2999553 < baseStart_2999553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999566 : List Nat := [4, 1, 1, 2, 1, 5, 1, 8]
def baseStart_2999566 : Nat := 118140960795 + 2999566 * 2 ^ 59
def prefixEnd_2999566 : Nat := 4983230072969 + 3 ^ 40 * 2999566 * 2
def baseEnd_2999566 : Nat := 57045152329048756219639

theorem tailTrace_2999566 : CollatzResearch.WordTrace tailWord_2999566 prefixEnd_2999566 57045152329048756219639 := by
  unfold tailWord_2999566
  simp only [CollatzResearch.WordTrace]
  refine ⟨13675394981386517741601319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72935439900728094621873701 13675394981386517741601319)
  ·
    refine ⟨20513092472079776612401979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13675394981386517741601319 20513092472079776612401979)
    ·
      refine ⟨30769638708119664918602969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20513092472079776612401979 30769638708119664918602969)
      ·
        refine ⟨23077229031089748688952227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30769638708119664918602969 23077229031089748688952227)
        ·
          refine ⟨34615843546634623033428341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23077229031089748688952227 34615843546634623033428341)
          ·
            refine ⟨3245235332496995909383907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34615843546634623033428341 3245235332496995909383907)
            ·
              refine ⟨4867852998745493864075861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3245235332496995909383907 4867852998745493864075861)
              ·
                refine ⟨57045152329048756219639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4867852998745493864075861 57045152329048756219639)
                ·
                  rfl

theorem cell23_2999566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 8].length) (baseStart_2999566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999566 prefixEnd_2999566 := by exact prefixLift 2999566
  have htrace : WordTrace (prefixWord ++ tailWord_2999566) baseStart_2999566 baseEnd_2999566 := by
    simpa [prefixWord, tailWord_2999566, baseEnd_2999566] using wordTrace_append hprefix tailTrace_2999566
  have hstable : (prefixWord ++ tailWord_2999566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999566).length < 2 ^ (prefixWord ++ tailWord_2999566).sum := by decide
  have hdescent : baseEnd_2999566 < baseStart_2999566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999570 : List Nat := [3, 2, 4, 2, 1, 1, 2, 1, 1, 6]
def baseStart_2999570 : Nat := 118140960795 + 2999570 * 2 ^ 59
def prefixEnd_2999570 : Nat := 4983230072969 + 3 ^ 40 * 2999570 * 2
def baseEnd_2999570 : Nat := 513407055602311467426745

theorem tailTrace_2999570 : CollatzResearch.WordTrace tailWord_2999570 prefixEnd_2999570 513407055602311467426745 := by
  unfold tailWord_2999570
  simp only [CollatzResearch.WordTrace]
  refine ⟨27350826435769412653989041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72935537162051767077304109 27350826435769412653989041)
  ·
    refine ⟨20513119826827059490491781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27350826435769412653989041 20513119826827059490491781)
    ·
      refine ⟨3846209967530073654467209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20513119826827059490491781 3846209967530073654467209)
      ·
        refine ⟨2884657475647555240850407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3846209967530073654467209 2884657475647555240850407)
        ·
          refine ⟨4326986213471332861275611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2884657475647555240850407 4326986213471332861275611)
          ·
            refine ⟨6490479320206999291913417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4326986213471332861275611 6490479320206999291913417)
            ·
              refine ⟨4867859490155249468935063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6490479320206999291913417 4867859490155249468935063)
              ·
                refine ⟨7301789235232874203402595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4867859490155249468935063 7301789235232874203402595)
                ·
                  refine ⟨10952683852849311305103893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7301789235232874203402595 10952683852849311305103893)
                  ·
                    refine ⟨513407055602311467426745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10952683852849311305103893 513407055602311467426745)
                    ·
                      rfl

theorem cell23_2999570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_2999570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999570 prefixEnd_2999570 := by exact prefixLift 2999570
  have htrace : WordTrace (prefixWord ++ tailWord_2999570) baseStart_2999570 baseEnd_2999570 := by
    simpa [prefixWord, tailWord_2999570, baseEnd_2999570] using wordTrace_append hprefix tailTrace_2999570
  have hstable : (prefixWord ++ tailWord_2999570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999570).length < 2 ^ (prefixWord ++ tailWord_2999570).sum := by decide
  have hdescent : baseEnd_2999570 < baseStart_2999570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999576 : List Nat := [2, 1, 2, 3, 1, 3, 1, 3, 1, 3, 3]
def baseStart_2999576 : Nat := 118140960795 + 2999576 * 2 ^ 59
def prefixEnd_2999576 : Nat := 4983230072969 + 3 ^ 40 * 2999576 * 2
def baseEnd_2999576 : Nat := 1540224247690861378805207

theorem tailTrace_2999576 : CollatzResearch.WordTrace tailWord_2999576 prefixEnd_2999576 1540224247690861378805207 := by
  unfold tailWord_2999576
  simp only [CollatzResearch.WordTrace]
  refine ⟨54701762290527956820337291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72935683054037275760449721 54701762290527956820337291)
  ·
    refine ⟨82052643435791935230505937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54701762290527956820337291 82052643435791935230505937)
    ·
      refine ⟨61539482576843951422879453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82052643435791935230505937 61539482576843951422879453)
      ·
        refine ⟨23077305966316481783579795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61539482576843951422879453 23077305966316481783579795)
        ·
          refine ⟨34615958949474722675369693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23077305966316481783579795 34615958949474722675369693)
          ·
            refine ⟨12980984606053021003263635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34615958949474722675369693 12980984606053021003263635)
            ·
              refine ⟨19471476909079531504895453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12980984606053021003263635 19471476909079531504895453)
              ·
                refine ⟨7301803840904824314335795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19471476909079531504895453 7301803840904824314335795)
                ·
                  refine ⟨10952705761357236471503693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7301803840904824314335795 10952705761357236471503693)
                  ·
                    refine ⟨4107264660508963676813885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10952705761357236471503693 4107264660508963676813885)
                    ·
                      refine ⟨1540224247690861378805207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4107264660508963676813885 1540224247690861378805207)
                      ·
                        rfl

theorem cell23_2999576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_2999576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999576 prefixEnd_2999576 := by exact prefixLift 2999576
  have htrace : WordTrace (prefixWord ++ tailWord_2999576) baseStart_2999576 baseEnd_2999576 := by
    simpa [prefixWord, tailWord_2999576, baseEnd_2999576] using wordTrace_append hprefix tailTrace_2999576
  have hstable : (prefixWord ++ tailWord_2999576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999576).length < 2 ^ (prefixWord ++ tailWord_2999576).sum := by decide
  have hdescent : baseEnd_2999576 < baseStart_2999576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999594 : List Nat := [3, 1, 4, 2, 1, 2, 2, 3, 1, 2, 2]
def baseStart_2999594 : Nat := 118140960795 + 2999594 * 2 ^ 59
def prefixEnd_2999594 : Nat := 4983230072969 + 3 ^ 40 * 2999594 * 2
def baseEnd_2999594 : Nat := 1540233490342642308380125

theorem tailTrace_2999594 : CollatzResearch.WordTrace tailWord_2999594 prefixEnd_2999594 1540233490342642308380125 := by
  unfold tailWord_2999594
  simp only [CollatzResearch.WordTrace]
  refine ⟨27351045273747675678707459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72936120729993801809886557 27351045273747675678707459)
  ·
    refine ⟨41026567910621513518061189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27351045273747675678707459 41026567910621513518061189)
    ·
      refine ⟨7692481483241533784636473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41026567910621513518061189 7692481483241533784636473)
      ·
        refine ⟨5769361112431150338477355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7692481483241533784636473 5769361112431150338477355)
        ·
          refine ⟨8654041668646725507716033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5769361112431150338477355 8654041668646725507716033)
          ·
            refine ⟨6490531251485044130787025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8654041668646725507716033 6490531251485044130787025)
            ·
              refine ⟨4867898438613783098090269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6490531251485044130787025 4867898438613783098090269)
              ·
                refine ⟨1825461914480168661783851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4867898438613783098090269 1825461914480168661783851)
                ·
                  refine ⟨2738192871720252992675777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1825461914480168661783851 2738192871720252992675777)
                  ·
                    refine ⟨2053644653790189744506833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2738192871720252992675777 2053644653790189744506833)
                    ·
                      refine ⟨1540233490342642308380125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2053644653790189744506833 1540233490342642308380125)
                      ·
                        rfl

theorem cell23_2999594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_2999594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999594 prefixEnd_2999594 := by exact prefixLift 2999594
  have htrace : WordTrace (prefixWord ++ tailWord_2999594) baseStart_2999594 baseEnd_2999594 := by
    simpa [prefixWord, tailWord_2999594, baseEnd_2999594] using wordTrace_append hprefix tailTrace_2999594
  have hstable : (prefixWord ++ tailWord_2999594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999594).length < 2 ^ (prefixWord ++ tailWord_2999594).sum := by decide
  have hdescent : baseEnd_2999594 < baseStart_2999594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999597 : List Nat := [1, 5, 3, 1, 1, 1, 4, 1, 1, 2, 3]
def baseStart_2999597 : Nat := 118140960795 + 2999597 * 2 ^ 59
def prefixEnd_2999597 : Nat := 4983230072969 + 3 ^ 40 * 2999597 * 2
def baseEnd_2999597 : Nat := 1540235030784605796642611

theorem tailTrace_2999597 : CollatzResearch.WordTrace tailWord_2999597 prefixEnd_2999597 1540235030784605796642611 := by
  unfold tailWord_2999597
  simp only [CollatzResearch.WordTrace]
  refine ⟨109404290513979834227189045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72936193675986556151459363 109404290513979834227189045)
  ·
    refine ⟨10256652235685609458798973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109404290513979834227189045 10256652235685609458798973)
    ·
      refine ⟨3846244588382103547049615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10256652235685609458798973 3846244588382103547049615)
      ·
        refine ⟨5769366882573155320574423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3846244588382103547049615 5769366882573155320574423)
        ·
          refine ⟨8654050323859732980861635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5769366882573155320574423 8654050323859732980861635)
          ·
            refine ⟨12981075485789599471292453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8654050323859732980861635 12981075485789599471292453)
            ·
              refine ⟨2433951653585549900867335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12981075485789599471292453 2433951653585549900867335)
              ·
                refine ⟨3650927480378324851301003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2433951653585549900867335 3650927480378324851301003)
                ·
                  refine ⟨5476391220567487276951505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3650927480378324851301003 5476391220567487276951505)
                  ·
                    refine ⟨4107293415425615457713629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5476391220567487276951505 4107293415425615457713629)
                    ·
                      refine ⟨1540235030784605796642611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4107293415425615457713629 1540235030784605796642611)
                      ·
                        rfl

theorem cell23_2999597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_2999597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999597 prefixEnd_2999597 := by exact prefixLift 2999597
  have htrace : WordTrace (prefixWord ++ tailWord_2999597) baseStart_2999597 baseEnd_2999597 := by
    simpa [prefixWord, tailWord_2999597, baseEnd_2999597] using wordTrace_append hprefix tailTrace_2999597
  have hstable : (prefixWord ++ tailWord_2999597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999597).length < 2 ^ (prefixWord ++ tailWord_2999597).sum := by decide
  have hdescent : baseEnd_2999597 < baseStart_2999597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999619 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 5]
def baseStart_2999619 : Nat := 118140960795 + 2999619 * 2 ^ 59
def prefixEnd_2999619 : Nat := 4983230072969 + 3 ^ 40 * 2999619 * 2
def baseEnd_2999619 : Nat := 1540246327359004710567509

theorem tailTrace_2999619 : CollatzResearch.WordTrace tailWord_2999619 prefixEnd_2999619 1540246327359004710567509 := by
  unfold tailWord_2999619
  simp only [CollatzResearch.WordTrace]
  refine ⟨109405092919900131984489911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72936728613266754656326607 109405092919900131984489911)
  ·
    refine ⟨164107639379850197976734867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109405092919900131984489911 164107639379850197976734867)
    ·
      refine ⟨246161459069775296965102301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164107639379850197976734867 246161459069775296965102301)
      ·
        refine ⟨92310547151165736361913363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246161459069775296965102301 92310547151165736361913363)
        ·
          refine ⟨138465820726748604542870045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92310547151165736361913363 138465820726748604542870045)
          ·
            refine ⟨51924682772530726703576267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138465820726748604542870045 51924682772530726703576267)
            ·
              refine ⟨77887024158796090055364401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51924682772530726703576267 77887024158796090055364401)
              ·
                refine ⟨58415268119097067541523301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77887024158796090055364401 58415268119097067541523301)
                ·
                  refine ⟨10952862772330700164035619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58415268119097067541523301 10952862772330700164035619)
                  ·
                    refine ⟨16429294158496050246053429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10952862772330700164035619 16429294158496050246053429)
                    ·
                      refine ⟨1540246327359004710567509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16429294158496050246053429 1540246327359004710567509)
                      ·
                        rfl

theorem cell23_2999619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_2999619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999619 prefixEnd_2999619 := by exact prefixLift 2999619
  have htrace : WordTrace (prefixWord ++ tailWord_2999619) baseStart_2999619 baseEnd_2999619 := by
    simpa [prefixWord, tailWord_2999619, baseEnd_2999619] using wordTrace_append hprefix tailTrace_2999619
  have hstable : (prefixWord ++ tailWord_2999619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999619).length < 2 ^ (prefixWord ++ tailWord_2999619).sum := by decide
  have hdescent : baseEnd_2999619 < baseStart_2999619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999636 : List Nat := [2, 4, 1, 1, 2, 1, 2, 2, 2, 1, 5]
def baseStart_2999636 : Nat := 118140960795 + 2999636 * 2 ^ 59
def prefixEnd_2999636 : Nat := 4983230072969 + 3 ^ 40 * 2999636 * 2
def baseEnd_2999636 : Nat := 1540255056530131144054931

theorem tailTrace_2999636 : CollatzResearch.WordTrace tailWord_2999636 prefixEnd_2999636 1540255056530131144054931 := by
  unfold tailWord_2999636
  simp only [CollatzResearch.WordTrace]
  refine ⟨54702856480419271943929381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72937141973892362591905841 54702856480419271943929381)
  ·
    refine ⟨10256785590078613489486759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54702856480419271943929381 10256785590078613489486759)
    ·
      refine ⟨15385178385117920234230139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10256785590078613489486759 15385178385117920234230139)
      ·
        refine ⟨23077767577676880351345209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15385178385117920234230139 23077767577676880351345209)
        ·
          refine ⟨17308325683257660263508907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23077767577676880351345209 17308325683257660263508907)
          ·
            refine ⟨25962488524886490395263361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17308325683257660263508907 25962488524886490395263361)
            ·
              refine ⟨19471866393664867796447521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25962488524886490395263361 19471866393664867796447521)
              ·
                refine ⟨14603899795248650847335641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19471866393664867796447521 14603899795248650847335641)
                ·
                  refine ⟨10952924846436488135501731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14603899795248650847335641 10952924846436488135501731)
                  ·
                    refine ⟨16429387269654732203252597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10952924846436488135501731 16429387269654732203252597)
                    ·
                      refine ⟨1540255056530131144054931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16429387269654732203252597 1540255056530131144054931)
                      ·
                        rfl

theorem cell23_2999636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_2999636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999636 prefixEnd_2999636 := by exact prefixLift 2999636
  have htrace : WordTrace (prefixWord ++ tailWord_2999636) baseStart_2999636 baseEnd_2999636 := by
    simpa [prefixWord, tailWord_2999636, baseEnd_2999636] using wordTrace_append hprefix tailTrace_2999636
  have hstable : (prefixWord ++ tailWord_2999636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999636).length < 2 ^ (prefixWord ++ tailWord_2999636).sum := by decide
  have hdescent : baseEnd_2999636 < baseStart_2999636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999645 : List Nat := [1, 4, 5, 1, 2, 1, 1, 3, 1, 2, 2]
def baseStart_2999645 : Nat := 118140960795 + 2999645 * 2 ^ 59
def prefixEnd_2999645 : Nat := 4983230072969 + 3 ^ 40 * 2999645 * 2
def baseEnd_2999645 : Nat := 1540259677856021608842391

theorem tailTrace_2999645 : CollatzResearch.WordTrace tailWord_2999645 prefixEnd_2999645 1540259677856021608842391 := by
  unfold tailWord_2999645
  simp only [CollatzResearch.WordTrace]
  refine ⟨109406041217805938424936389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72937360811870625616624259 109406041217805938424936389)
  ·
    refine ⟨20513632728338613454675573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109406041217805938424936389 20513632728338613454675573)
    ·
      refine ⟨1923153068281745011375835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20513632728338613454675573 1923153068281745011375835)
      ·
        refine ⟨2884729602422617517063753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1923153068281745011375835 2884729602422617517063753)
        ·
          refine ⟨2163547201816963137797815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2884729602422617517063753 2163547201816963137797815)
          ·
            refine ⟨3245320802725444706696723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2163547201816963137797815 3245320802725444706696723)
            ·
              refine ⟨4867981204088167060045085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3245320802725444706696723 4867981204088167060045085)
              ·
                refine ⟨1825492951533062647516907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4867981204088167060045085 1825492951533062647516907)
                ·
                  refine ⟨2738239427299593971275361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1825492951533062647516907 2738239427299593971275361)
                  ·
                    refine ⟨2053679570474695478456521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2738239427299593971275361 2053679570474695478456521)
                    ·
                      refine ⟨1540259677856021608842391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2053679570474695478456521 1540259677856021608842391)
                      ·
                        rfl

theorem cell23_2999645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_2999645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999645 prefixEnd_2999645 := by exact prefixLift 2999645
  have htrace : WordTrace (prefixWord ++ tailWord_2999645) baseStart_2999645 baseEnd_2999645 := by
    simpa [prefixWord, tailWord_2999645, baseEnd_2999645] using wordTrace_append hprefix tailTrace_2999645
  have hstable : (prefixWord ++ tailWord_2999645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999645).length < 2 ^ (prefixWord ++ tailWord_2999645).sum := by decide
  have hdescent : baseEnd_2999645 < baseStart_2999645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999650 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 6, 2, 2]
def baseStart_2999650 : Nat := 118140960795 + 2999650 * 2 ^ 59
def prefixEnd_2999650 : Nat := 4983230072969 + 3 ^ 40 * 2999650 * 2
def baseEnd_2999650 : Nat := 1540262245259294089279867

theorem tailTrace_2999650 : CollatzResearch.WordTrace tailWord_2999650 prefixEnd_2999650 1540262245259294089279867 := by
  unfold tailWord_2999650
  simp only [CollatzResearch.WordTrace]
  refine ⟨27351555895696956069717101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72937482388525216185912269 27351555895696956069717101)
  ·
    refine ⟨10256833460886358526143913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27351555895696956069717101 10256833460886358526143913)
    ·
      refine ⟨7692625095664768894607935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10256833460886358526143913 7692625095664768894607935)
      ·
        refine ⟨11538937643497153341911903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7692625095664768894607935 11538937643497153341911903)
        ·
          refine ⟨17308406465245730012867855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11538937643497153341911903 17308406465245730012867855)
          ·
            refine ⟨25962609697868595019301783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17308406465245730012867855 25962609697868595019301783)
            ·
              refine ⟨38943914546802892528952675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25962609697868595019301783 38943914546802892528952675)
              ·
                refine ⟨58415871820204338793429013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38943914546802892528952675 58415871820204338793429013)
                ·
                  refine ⟨2738243991572078380941985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58415871820204338793429013 2738243991572078380941985)
                  ·
                    refine ⟨2053682993679058785706489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2738243991572078380941985 2053682993679058785706489)
                    ·
                      refine ⟨1540262245259294089279867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2053682993679058785706489 1540262245259294089279867)
                      ·
                        rfl

theorem cell23_2999650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_2999650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999650 prefixEnd_2999650 := by exact prefixLift 2999650
  have htrace : WordTrace (prefixWord ++ tailWord_2999650) baseStart_2999650 baseEnd_2999650 := by
    simpa [prefixWord, tailWord_2999650, baseEnd_2999650] using wordTrace_append hprefix tailTrace_2999650
  have hstable : (prefixWord ++ tailWord_2999650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999650).length < 2 ^ (prefixWord ++ tailWord_2999650).sum := by decide
  have hdescent : baseEnd_2999650 < baseStart_2999650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999678 : List Nat := [4, 2, 3, 2, 2, 1, 2, 1, 2, 1, 3]
def baseStart_2999678 : Nat := 118140960795 + 2999678 * 2 ^ 59
def prefixEnd_2999678 : Nat := 4983230072969 + 3 ^ 40 * 2999678 * 2
def baseEnd_2999678 : Nat := 1540276622717619979729739

theorem tailTrace_2999678 : CollatzResearch.WordTrace tailWord_2999678 prefixEnd_2999678 1540276622717619979729739 := by
  unfold tailWord_2999678
  simp only [CollatzResearch.WordTrace]
  refine ⟨13675905603335798132610961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72938163217790923373925125 13675905603335798132610961)
  ·
    refine ⟨10256929202501848599458221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13675905603335798132610961 10256929202501848599458221)
    ·
      refine ⟨3846348450938193224796833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10256929202501848599458221 3846348450938193224796833)
      ·
        refine ⟨2884761338203644918597625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3846348450938193224796833 2884761338203644918597625)
        ·
          refine ⟨2163571003652733688948219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2884761338203644918597625 2163571003652733688948219)
          ·
            refine ⟨3245356505479100533422329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2163571003652733688948219 3245356505479100533422329)
            ·
              refine ⟨2434017379109325400066747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3245356505479100533422329 2434017379109325400066747)
              ·
                refine ⟨3651026068663988100100121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2434017379109325400066747 3651026068663988100100121)
                ·
                  refine ⟨2738269551497991075075091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3651026068663988100100121 2738269551497991075075091)
                  ·
                    refine ⟨4107404327246986612612637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2738269551497991075075091 4107404327246986612612637)
                    ·
                      refine ⟨1540276622717619979729739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4107404327246986612612637 1540276622717619979729739)
                      ·
                        rfl

theorem cell23_2999678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_2999678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999678 prefixEnd_2999678 := by exact prefixLift 2999678
  have htrace : WordTrace (prefixWord ++ tailWord_2999678) baseStart_2999678 baseEnd_2999678 := by
    simpa [prefixWord, tailWord_2999678, baseEnd_2999678] using wordTrace_append hprefix tailTrace_2999678
  have hstable : (prefixWord ++ tailWord_2999678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999678).length < 2 ^ (prefixWord ++ tailWord_2999678).sum := by decide
  have hdescent : baseEnd_2999678 < baseStart_2999678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999684 : List Nat := [2, 3, 2, 1, 1, 5, 2, 1, 2, 2, 2]
def baseStart_2999684 : Nat := 118140960795 + 2999684 * 2 ^ 59
def prefixEnd_2999684 : Nat := 4983230072969 + 3 ^ 40 * 2999684 * 2
def baseEnd_2999684 : Nat := 1540279703601546956254711

theorem tailTrace_2999684 : CollatzResearch.WordTrace tailWord_2999684 prefixEnd_2999684 1540279703601546956254711 := by
  unfold tailWord_2999684
  simp only [CollatzResearch.WordTrace]
  refine ⟨54703731832332324042803053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72938309109776432057070737 54703731832332324042803053)
  ·
    refine ⟨20513899437124621516051145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54703731832332324042803053 20513899437124621516051145)
    ·
      refine ⟨15385424577843466137038359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20513899437124621516051145 15385424577843466137038359)
      ·
        refine ⟨23078136866765199205557539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15385424577843466137038359 23078136866765199205557539)
        ·
          refine ⟨34617205300147798808336309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23078136866765199205557539 34617205300147798808336309)
          ·
            refine ⟨3245362996888856138281529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34617205300147798808336309 3245362996888856138281529)
            ·
              refine ⟨2434022247666642103711147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3245362996888856138281529 2434022247666642103711147)
              ·
                refine ⟨3651033371499963155566721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2434022247666642103711147 3651033371499963155566721)
                ·
                  refine ⟨2738275028624972366675041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3651033371499963155566721 2738275028624972366675041)
                  ·
                    refine ⟨2053706271468729275006281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2738275028624972366675041 2053706271468729275006281)
                    ·
                      refine ⟨1540279703601546956254711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2053706271468729275006281 1540279703601546956254711)
                      ·
                        rfl

theorem cell23_2999684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_2999684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999684 prefixEnd_2999684 := by exact prefixLift 2999684
  have htrace : WordTrace (prefixWord ++ tailWord_2999684) baseStart_2999684 baseEnd_2999684 := by
    simpa [prefixWord, tailWord_2999684, baseEnd_2999684] using wordTrace_append hprefix tailTrace_2999684
  have hstable : (prefixWord ++ tailWord_2999684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999684).length < 2 ^ (prefixWord ++ tailWord_2999684).sum := by decide
  have hdescent : baseEnd_2999684 < baseStart_2999684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999776 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 5, 5]
def baseStart_2999776 : Nat := 118140960795 + 2999776 * 2 ^ 59
def prefixEnd_2999776 : Nat := 4983230072969 + 3 ^ 40 * 2999776 * 2
def baseEnd_2999776 : Nat := 513442314607253532101429

theorem tailTrace_2999776 : CollatzResearch.WordTrace tailWord_2999776 prefixEnd_2999776 513442314607253532101429 := by
  unfold tailWord_2999776
  simp only [CollatzResearch.WordTrace]
  refine ⟨54705409590165673898977591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72940546120220898531970121 54705409590165673898977591)
  ·
    refine ⟨82058114385248510848466387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54705409590165673898977591 82058114385248510848466387)
    ·
      refine ⟨123087171577872766272699581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82058114385248510848466387 123087171577872766272699581)
      ·
        refine ⟨46157689341702287352262343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123087171577872766272699581 46157689341702287352262343)
        ·
          refine ⟨69236534012553431028393515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46157689341702287352262343 69236534012553431028393515)
          ·
            refine ⟨103854801018830146542590273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69236534012553431028393515 103854801018830146542590273)
            ·
              refine ⟨77891100764122609906942705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103854801018830146542590273 77891100764122609906942705)
              ·
                refine ⟨58418325573091957430207029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77891100764122609906942705 58418325573091957430207029)
                ·
                  refine ⟨5476718022477371009081909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58418325573091957430207029 5476718022477371009081909)
                  ·
                    refine ⟨513442314607253532101429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5476718022477371009081909 513442314607253532101429)
                    ·
                      rfl

theorem cell23_2999776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 5, 5].length) (baseStart_2999776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999776 prefixEnd_2999776 := by exact prefixLift 2999776
  have htrace : WordTrace (prefixWord ++ tailWord_2999776) baseStart_2999776 baseEnd_2999776 := by
    simpa [prefixWord, tailWord_2999776, baseEnd_2999776] using wordTrace_append hprefix tailTrace_2999776
  have hstable : (prefixWord ++ tailWord_2999776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999776).length < 2 ^ (prefixWord ++ tailWord_2999776).sum := by decide
  have hdescent : baseEnd_2999776 < baseStart_2999776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999797 : List Nat := [1, 3, 5, 1, 1, 2, 3, 1, 6]
def baseStart_2999797 : Nat := 118140960795 + 2999797 * 2 ^ 59
def prefixEnd_2999797 : Nat := 4983230072969 + 3 ^ 40 * 2999797 * 2
def baseEnd_2999797 : Nat := 171148636323945001571299

theorem tailTrace_2999797 : CollatzResearch.WordTrace tailWord_2999797 prefixEnd_2999797 171148636323945001571299 := by
  unfold tailWord_2999797
  simp only [CollatzResearch.WordTrace]
  refine ⟨109411585113255268384469645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72941056742170178922979763 109411585113255268384469645)
  ·
    refine ⟨41029344417470725644176117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109411585113255268384469645 41029344417470725644176117)
    ·
      refine ⟨3846501039137880529141511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41029344417470725644176117 3846501039137880529141511)
      ·
        refine ⟨5769751558706820793712267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3846501039137880529141511 5769751558706820793712267)
        ·
          refine ⟨8654627338060231190568401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5769751558706820793712267 8654627338060231190568401)
          ·
            refine ⟨6490970503545173392926301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8654627338060231190568401 6490970503545173392926301)
            ·
              refine ⟨2434113938829440022347363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6490970503545173392926301 2434113938829440022347363)
              ·
                refine ⟨3651170908244160033521045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2434113938829440022347363 3651170908244160033521045)
                ·
                  refine ⟨171148636323945001571299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3651170908244160033521045 171148636323945001571299)
                  ·
                    rfl

theorem cell23_2999797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 6].length) (baseStart_2999797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999797 prefixEnd_2999797 := by exact prefixLift 2999797
  have htrace : WordTrace (prefixWord ++ tailWord_2999797) baseStart_2999797 baseEnd_2999797 := by
    simpa [prefixWord, tailWord_2999797, baseEnd_2999797] using wordTrace_append hprefix tailTrace_2999797
  have hstable : (prefixWord ++ tailWord_2999797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999797).length < 2 ^ (prefixWord ++ tailWord_2999797).sum := by decide
  have hdescent : baseEnd_2999797 < baseStart_2999797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999813 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 1, 8, 2]
def baseStart_2999813 : Nat := 118140960795 + 2999813 * 2 ^ 59
def prefixEnd_2999813 : Nat := 4983230072969 + 3 ^ 40 * 2999813 * 2
def baseEnd_2999813 : Nat := 1540345942605976951541617

theorem tailTrace_2999813 : CollatzResearch.WordTrace tailWord_2999813 prefixEnd_2999813 1540345942605976951541617 := by
  unfold tailWord_2999813
  simp only [CollatzResearch.WordTrace]
  refine ⟨109412168681197303117052093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72941445787464868744701395 109412168681197303117052093)
  ·
    refine ⟨41029563255448988668894535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109412168681197303117052093 41029563255448988668894535)
    ·
      refine ⟨61544344883173483003341803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41029563255448988668894535 61544344883173483003341803)
      ·
        refine ⟨92316517324760224505012705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61544344883173483003341803 92316517324760224505012705)
        ·
          refine ⟨69237387993570168378759529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92316517324760224505012705 69237387993570168378759529)
          ·
            refine ⟨51928040995177626284069647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69237387993570168378759529 51928040995177626284069647)
            ·
              refine ⟨77892061492766439426104471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51928040995177626284069647 77892061492766439426104471)
              ·
                refine ⟨116838092239149659139156707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77892061492766439426104471 116838092239149659139156707)
                ·
                  refine ⟨175257138358724488708735061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116838092239149659139156707 175257138358724488708735061)
                  ·
                    refine ⟨2053794590141302602055489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 175257138358724488708735061 2053794590141302602055489)
                    ·
                      refine ⟨1540345942605976951541617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2053794590141302602055489 1540345942605976951541617)
                      ·
                        rfl

theorem cell23_2999813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 8, 2].length) (baseStart_2999813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999813 prefixEnd_2999813 := by exact prefixLift 2999813
  have htrace : WordTrace (prefixWord ++ tailWord_2999813) baseStart_2999813 baseEnd_2999813 := by
    simpa [prefixWord, tailWord_2999813, baseEnd_2999813] using wordTrace_append hprefix tailTrace_2999813
  have hstable : (prefixWord ++ tailWord_2999813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999813).length < 2 ^ (prefixWord ++ tailWord_2999813).sum := by decide
  have hdescent : baseEnd_2999813 < baseStart_2999813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999840 : List Nat := [2, 1, 1, 6, 1, 1, 2, 1, 4, 4]
def baseStart_2999840 : Nat := 118140960795 + 2999840 * 2 ^ 59
def prefixEnd_2999840 : Nat := 4983230072969 + 3 ^ 40 * 2999840 * 2
def baseEnd_2999840 : Nat := 513453268861216115301331

theorem tailTrace_2999840 : CollatzResearch.WordTrace tailWord_2999840 prefixEnd_2999840 513453268861216115301331 := by
  unfold tailWord_2999840
  simp only [CollatzResearch.WordTrace]
  refine ⟨54706576726049743364142487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72942102301399657818856649 54706576726049743364142487)
  ·
    refine ⟨82059865089074615046213731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54706576726049743364142487 82059865089074615046213731)
    ·
      refine ⟨123089797633611922569320597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82059865089074615046213731 123089797633611922569320597)
      ·
        refine ⟨5769834264075558870436903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 123089797633611922569320597 5769834264075558870436903)
        ·
          refine ⟨8654751396113338305655355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5769834264075558870436903 8654751396113338305655355)
          ·
            refine ⟨12982127094170007458483033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8654751396113338305655355 12982127094170007458483033)
            ·
              refine ⟨9736595320627505593862275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12982127094170007458483033 9736595320627505593862275)
              ·
                refine ⟨14604892980941258390793413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9736595320627505593862275 14604892980941258390793413)
                ·
                  refine ⟨2738417433926485948273765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14604892980941258390793413 2738417433926485948273765)
                  ·
                    refine ⟨513453268861216115301331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2738417433926485948273765 513453268861216115301331)
                    ·
                      rfl

theorem cell23_2999840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 4, 4].length) (baseStart_2999840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999840 prefixEnd_2999840 := by exact prefixLift 2999840
  have htrace : WordTrace (prefixWord ++ tailWord_2999840) baseStart_2999840 baseEnd_2999840 := by
    simpa [prefixWord, tailWord_2999840, baseEnd_2999840] using wordTrace_append hprefix tailTrace_2999840
  have hstable : (prefixWord ++ tailWord_2999840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999840).length < 2 ^ (prefixWord ++ tailWord_2999840).sum := by decide
  have hdescent : baseEnd_2999840 < baseStart_2999840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999850 : List Nat := [3, 1, 4, 1, 1, 1, 2, 2, 3, 2, 3]
def baseStart_2999850 : Nat := 118140960795 + 2999850 * 2 ^ 59
def prefixEnd_2999850 : Nat := 4983230072969 + 3 ^ 40 * 2999850 * 2
def baseEnd_2999850 : Nat := 1540364941390193306778947

theorem tailTrace_2999850 : CollatzResearch.WordTrace tailWord_2999850 prefixEnd_2999850 1540364941390193306778947 := by
  unfold tailWord_2999850
  simp only [CollatzResearch.WordTrace]
  refine ⟨27353379545515814609037251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72942345454708838957432669 27353379545515814609037251)
  ·
    refine ⟨41030069318273721913555877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27353379545515814609037251 41030069318273721913555877)
    ·
      refine ⟨7693137997176322858791727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41030069318273721913555877 7693137997176322858791727)
      ·
        refine ⟨11539706995764484288187591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7693137997176322858791727 11539706995764484288187591)
        ·
          refine ⟨17309560493646726432281387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11539706995764484288187591 17309560493646726432281387)
          ·
            refine ⟨25964340740470089648422081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17309560493646726432281387 25964340740470089648422081)
            ·
              refine ⟨19473255555352567236316561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25964340740470089648422081 19473255555352567236316561)
              ·
                refine ⟨14604941666514425427237421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19473255555352567236316561 14604941666514425427237421)
                ·
                  refine ⟨5476853124942909535214033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14604941666514425427237421 5476853124942909535214033)
                  ·
                    refine ⟨4107639843707182151410525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5476853124942909535214033 4107639843707182151410525)
                    ·
                      refine ⟨1540364941390193306778947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4107639843707182151410525 1540364941390193306778947)
                      ·
                        rfl

theorem cell23_2999850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_2999850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999850 prefixEnd_2999850 := by exact prefixLift 2999850
  have htrace : WordTrace (prefixWord ++ tailWord_2999850) baseStart_2999850 baseEnd_2999850 := by
    simpa [prefixWord, tailWord_2999850, baseEnd_2999850] using wordTrace_append hprefix tailTrace_2999850
  have hstable : (prefixWord ++ tailWord_2999850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999850).length < 2 ^ (prefixWord ++ tailWord_2999850).sum := by decide
  have hdescent : baseEnd_2999850 < baseStart_2999850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999856 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 6]
def baseStart_2999856 : Nat := 118140960795 + 2999856 * 2 ^ 59
def prefixEnd_2999856 : Nat := 4983230072969 + 3 ^ 40 * 2999856 * 2
def baseEnd_2999856 : Nat := 1540368022274120283303919

theorem tailTrace_2999856 : CollatzResearch.WordTrace tailWord_2999856 prefixEnd_2999856 1540368022274120283303919 := by
  unfold tailWord_2999856
  simp only [CollatzResearch.WordTrace]
  refine ⟨54706868510020760730433711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72942491346694347640578281 54706868510020760730433711)
  ·
    refine ⟨82060302765031141095650567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54706868510020760730433711 82060302765031141095650567)
    ·
      refine ⟨123090454147546711643475851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82060302765031141095650567 123090454147546711643475851)
      ·
        refine ⟨184635681221320067465213777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123090454147546711643475851 184635681221320067465213777)
        ·
          refine ⟨138476760915990050598910333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184635681221320067465213777 138476760915990050598910333)
          ·
            refine ⟨51928785343496268974591375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138476760915990050598910333 51928785343496268974591375)
            ·
              refine ⟨77893178015244403461887063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51928785343496268974591375 77893178015244403461887063)
              ·
                refine ⟨116839767022866605192830595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77893178015244403461887063 116839767022866605192830595)
                ·
                  refine ⟨175259650534299907789245893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116839767022866605192830595 175259650534299907789245893)
                  ·
                    refine ⟨32861184475181232710483605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 175259650534299907789245893 32861184475181232710483605)
                    ·
                      refine ⟨1540368022274120283303919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32861184475181232710483605 1540368022274120283303919)
                      ·
                        rfl

theorem cell23_2999856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 6].length) (baseStart_2999856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999856 prefixEnd_2999856 := by exact prefixLift 2999856
  have htrace : WordTrace (prefixWord ++ tailWord_2999856) baseStart_2999856 baseEnd_2999856 := by
    simpa [prefixWord, tailWord_2999856, baseEnd_2999856] using wordTrace_append hprefix tailTrace_2999856
  have hstable : (prefixWord ++ tailWord_2999856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999856).length < 2 ^ (prefixWord ++ tailWord_2999856).sum := by decide
  have hdescent : baseEnd_2999856 < baseStart_2999856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999937 : List Nat := [1, 2, 4, 2, 1, 2, 2, 2, 1, 4, 2]
def baseStart_2999937 : Nat := 118140960795 + 2999937 * 2 ^ 59
def prefixEnd_2999937 : Nat := 4983230072969 + 3 ^ 40 * 2999937 * 2
def baseEnd_2999937 : Nat := 1540409614207134466391047

theorem tailTrace_2999937 : CollatzResearch.WordTrace tailWord_2999937 prefixEnd_2999937 1540409614207134466391047 := by
  unfold tailWord_2999937
  simp only [CollatzResearch.WordTrace]
  refine ⟨109416691332748072294566065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72944460888498714863044043 109416691332748072294566065)
  ·
    refine ⟨82062518499561054220924549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109416691332748072294566065 82062518499561054220924549)
    ·
      refine ⟨15386722218667697666423353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82062518499561054220924549 15386722218667697666423353)
      ·
        refine ⟨11540041664000773249817515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15386722218667697666423353 11540041664000773249817515)
        ·
          refine ⟨17310062496001159874726273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11540041664000773249817515 17310062496001159874726273)
          ·
            refine ⟨12982546872000869906044705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17310062496001159874726273 12982546872000869906044705)
            ·
              refine ⟨9736910154000652429533529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12982546872000869906044705 9736910154000652429533529)
              ·
                refine ⟨7302682615500489322150147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9736910154000652429533529 7302682615500489322150147)
                ·
                  refine ⟨10954023923250733983225221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7302682615500489322150147 10954023923250733983225221)
                  ·
                    refine ⟨2053879485609512621854729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10954023923250733983225221 2053879485609512621854729)
                    ·
                      refine ⟨1540409614207134466391047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2053879485609512621854729 1540409614207134466391047)
                      ·
                        rfl

theorem cell23_2999937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_2999937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999937 prefixEnd_2999937 := by exact prefixLift 2999937
  have htrace : WordTrace (prefixWord ++ tailWord_2999937) baseStart_2999937 baseEnd_2999937 := by
    simpa [prefixWord, tailWord_2999937, baseEnd_2999937] using wordTrace_append hprefix tailTrace_2999937
  have hstable : (prefixWord ++ tailWord_2999937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999937).length < 2 ^ (prefixWord ++ tailWord_2999937).sum := by decide
  have hdescent : baseEnd_2999937 < baseStart_2999937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999950 : List Nat := [4, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4]
def baseStart_2999950 : Nat := 118140960795 + 2999950 * 2 ^ 59
def prefixEnd_2999950 : Nat := 4983230072969 + 3 ^ 40 * 2999950 * 2
def baseEnd_2999950 : Nat := 1540416289455642915528487

theorem tailTrace_2999950 : CollatzResearch.WordTrace tailWord_2999950 prefixEnd_2999950 1540416289455642915528487 := by
  unfold tailWord_2999950
  simp only [CollatzResearch.WordTrace]
  refine ⟨13677145685212621939348663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72944776987800650343192869 13677145685212621939348663)
  ·
    refine ⟨20515718527818932909022995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13677145685212621939348663 20515718527818932909022995)
    ·
      refine ⟨30773577791728399363534493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20515718527818932909022995 30773577791728399363534493)
      ·
        refine ⟨11540091671898149761325435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30773577791728399363534493 11540091671898149761325435)
        ·
          refine ⟨17310137507847224641988153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11540091671898149761325435 17310137507847224641988153)
          ·
            refine ⟨12982603130885418481491115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17310137507847224641988153 12982603130885418481491115)
            ·
              refine ⟨19473904696328127722236673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12982603130885418481491115 19473904696328127722236673)
              ·
                refine ⟨14605428522246095791677505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19473904696328127722236673 14605428522246095791677505)
                ·
                  refine ⟨10954071391684571843758129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14605428522246095791677505 10954071391684571843758129)
                  ·
                    refine ⟨8215553543763428882818597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10954071391684571843758129 8215553543763428882818597)
                    ·
                      refine ⟨1540416289455642915528487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8215553543763428882818597 1540416289455642915528487)
                      ·
                        rfl

theorem cell23_2999950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_2999950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999950 prefixEnd_2999950 := by exact prefixLift 2999950
  have htrace : WordTrace (prefixWord ++ tailWord_2999950) baseStart_2999950 baseEnd_2999950 := by
    simpa [prefixWord, tailWord_2999950, baseEnd_2999950] using wordTrace_append hprefix tailTrace_2999950
  have hstable : (prefixWord ++ tailWord_2999950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999950).length < 2 ^ (prefixWord ++ tailWord_2999950).sum := by decide
  have hdescent : baseEnd_2999950 < baseStart_2999950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999960 : List Nat := [2, 1, 2, 4, 1, 3, 2, 1, 7]
def baseStart_2999960 : Nat := 118140960795 + 2999960 * 2 ^ 59
def prefixEnd_2999960 : Nat := 4983230072969 + 3 ^ 40 * 2999960 * 2
def baseEnd_2999960 : Nat := 171157936029131986267049

theorem tailTrace_2999960 : CollatzResearch.WordTrace tailWord_2999960 prefixEnd_2999960 171157936029131986267049 := by
  unfold tailWord_2999960
  simp only [CollatzResearch.WordTrace]
  refine ⟨54708765105832373611326667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72945020141109831481768889 54708765105832373611326667)
  ·
    refine ⟨82063147658748560416990001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54708765105832373611326667 82063147658748560416990001)
    ·
      refine ⟨61547360744061420312742501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82063147658748560416990001 61547360744061420312742501)
      ·
        refine ⟨11540130139511516308639219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61547360744061420312742501 11540130139511516308639219)
        ·
          refine ⟨17310195209267274462958829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11540130139511516308639219 17310195209267274462958829)
          ·
            refine ⟨6491323203475227923609561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17310195209267274462958829 6491323203475227923609561)
            ·
              refine ⟨4868492402606420942707171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6491323203475227923609561 4868492402606420942707171)
              ·
                refine ⟨7302738603909631414060757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4868492402606420942707171 7302738603909631414060757)
                ·
                  refine ⟨171157936029131986267049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7302738603909631414060757 171157936029131986267049)
                  ·
                    rfl

theorem cell23_2999960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 7].length) (baseStart_2999960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999960 prefixEnd_2999960 := by exact prefixLift 2999960
  have htrace : WordTrace (prefixWord ++ tailWord_2999960) baseStart_2999960 baseEnd_2999960 := by
    simpa [prefixWord, tailWord_2999960, baseEnd_2999960] using wordTrace_append hprefix tailTrace_2999960
  have hstable : (prefixWord ++ tailWord_2999960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999960).length < 2 ^ (prefixWord ++ tailWord_2999960).sum := by decide
  have hdescent : baseEnd_2999960 < baseStart_2999960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999973 : List Nat := [1, 3, 1, 2, 1, 2, 3, 2, 1, 7]
def baseStart_2999973 : Nat := 118140960795 + 2999973 * 2 ^ 59
def prefixEnd_2999973 : Nat := 4983230072969 + 3 ^ 40 * 2999973 * 2
def baseEnd_2999973 : Nat := 513476033170232108513627

theorem tailTrace_2999973 : CollatzResearch.WordTrace tailWord_2999973 prefixEnd_2999973 513476033170232108513627 := by
  unfold tailWord_2999973
  simp only [CollatzResearch.WordTrace]
  refine ⟨109418004360617650442876573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72945336240411766961917715 109418004360617650442876573)
  ·
    refine ⟨41031751635231618916078715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109418004360617650442876573 41031751635231618916078715)
    ·
      refine ⟨61547627452847428374118073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41031751635231618916078715 61547627452847428374118073)
      ·
        refine ⟨46160720589635571280588555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61547627452847428374118073 46160720589635571280588555)
        ·
          refine ⟨69241080884453356920882833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46160720589635571280588555 69241080884453356920882833)
          ·
            refine ⟨51930810663340017690662125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69241080884453356920882833 51930810663340017690662125)
            ·
              refine ⟨19474053998752506633998297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51930810663340017690662125 19474053998752506633998297)
              ·
                refine ⟨14605540499064379975498723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19474053998752506633998297 14605540499064379975498723)
                ·
                  refine ⟨21908310748596569963248085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14605540499064379975498723 21908310748596569963248085)
                  ·
                    refine ⟨513476033170232108513627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21908310748596569963248085 513476033170232108513627)
                    ·
                      rfl

theorem cell23_2999973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 7].length) (baseStart_2999973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2999973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2999973 prefixEnd_2999973 := by exact prefixLift 2999973
  have htrace : WordTrace (prefixWord ++ tailWord_2999973) baseStart_2999973 baseEnd_2999973 := by
    simpa [prefixWord, tailWord_2999973, baseEnd_2999973] using wordTrace_append hprefix tailTrace_2999973
  have hstable : (prefixWord ++ tailWord_2999973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999973).length < 2 ^ (prefixWord ++ tailWord_2999973).sum := by decide
  have hdescent : baseEnd_2999973 < baseStart_2999973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000022 : List Nat := [5, 2, 1, 3, 1, 2, 2, 1, 2, 2, 2]
def baseStart_3000022 : Nat := 118140960795 + 3000022 * 2 ^ 59
def prefixEnd_3000022 : Nat := 4983230072969 + 3 ^ 40 * 3000022 * 2
def baseEnd_3000022 : Nat := 1540453260062766633828157

theorem tailTrace_3000022 : CollatzResearch.WordTrace tailWord_3000022 prefixEnd_3000022 1540453260062766633828157 := by
  unfold tailWord_3000022
  simp only [CollatzResearch.WordTrace]
  refine ⟨6838736971090008238213145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72946527691626754540940213 6838736971090008238213145)
  ·
    refine ⟨5129052728317506178659859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6838736971090008238213145 5129052728317506178659859)
    ·
      refine ⟨7693579092476259267989789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5129052728317506178659859 7693579092476259267989789)
      ·
        refine ⟨2885092159678597225496171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7693579092476259267989789 2885092159678597225496171)
        ·
          refine ⟨4327638239517895838244257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2885092159678597225496171 4327638239517895838244257)
          ·
            refine ⟨3245728679638421878683193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4327638239517895838244257 3245728679638421878683193)
            ·
              refine ⟨2434296509728816409012395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3245728679638421878683193 2434296509728816409012395)
              ·
                refine ⟨3651444764593224613518593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2434296509728816409012395 3651444764593224613518593)
                ·
                  refine ⟨2738583573444918460138945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3651444764593224613518593 2738583573444918460138945)
                  ·
                    refine ⟨2053937680083688845104209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2738583573444918460138945 2053937680083688845104209)
                    ·
                      refine ⟨1540453260062766633828157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2053937680083688845104209 1540453260062766633828157)
                      ·
                        rfl

theorem cell23_3000022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_3000022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000022 prefixEnd_3000022 := by exact prefixLift 3000022
  have htrace : WordTrace (prefixWord ++ tailWord_3000022) baseStart_3000022 baseEnd_3000022 := by
    simpa [prefixWord, tailWord_3000022, baseEnd_3000022] using wordTrace_append hprefix tailTrace_3000022
  have hstable : (prefixWord ++ tailWord_3000022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000022).length < 2 ^ (prefixWord ++ tailWord_3000022).sum := by decide
  have hdescent : baseEnd_3000022 < baseStart_3000022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000047 : List Nat := [1, 1, 2, 1, 5, 1, 4, 1, 2, 2, 3]
def baseStart_3000047 : Nat := 118140960795 + 3000047 * 2 ^ 59
def prefixEnd_3000047 : Nat := 4983230072969 + 3 ^ 40 * 3000047 * 2
def baseEnd_3000047 : Nat := 1540466097079129036015541

theorem tailTrace_3000047 : CollatzResearch.WordTrace tailWord_3000047 prefixEnd_3000047 1540466097079129036015541 := by
  unfold tailWord_3000047
  simp only [CollatzResearch.WordTrace]
  refine ⟨109420703362349561081070395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72947135574899707387380263 109420703362349561081070395)
  ·
    refine ⟨164131055043524341621605593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109420703362349561081070395 164131055043524341621605593)
    ·
      refine ⟨123098291282643256216204195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164131055043524341621605593 123098291282643256216204195)
      ·
        refine ⟨184647436923964884324306293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123098291282643256216204195 184647436923964884324306293)
        ·
          refine ⟨17310697211621707905403715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 184647436923964884324306293 17310697211621707905403715)
          ·
            refine ⟨25966045817432561858105573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17310697211621707905403715 25966045817432561858105573)
            ·
              refine ⟨4868633590768605348394795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25966045817432561858105573 4868633590768605348394795)
              ·
                refine ⟨7302950386152908022592193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4868633590768605348394795 7302950386152908022592193)
                ·
                  refine ⟨5477212789614681016944145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7302950386152908022592193 5477212789614681016944145)
                  ·
                    refine ⟨4107909592211010762708109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5477212789614681016944145 4107909592211010762708109)
                    ·
                      refine ⟨1540466097079129036015541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4107909592211010762708109 1540466097079129036015541)
                      ·
                        rfl

theorem cell23_3000047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 2, 3].length) (baseStart_3000047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000047 prefixEnd_3000047 := by exact prefixLift 3000047
  have htrace : WordTrace (prefixWord ++ tailWord_3000047) baseStart_3000047 baseEnd_3000047 := by
    simpa [prefixWord, tailWord_3000047, baseEnd_3000047] using wordTrace_append hprefix tailTrace_3000047
  have hstable : (prefixWord ++ tailWord_3000047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000047).length < 2 ^ (prefixWord ++ tailWord_3000047).sum := by decide
  have hdescent : baseEnd_3000047 < baseStart_3000047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000071 : List Nat := [1, 1, 4, 4, 2, 1, 1, 4, 1, 4]
def baseStart_3000071 : Nat := 118140960795 + 3000071 * 2 ^ 59
def prefixEnd_3000071 : Nat := 4983230072969 + 3 ^ 40 * 3000071 * 2
def baseEnd_3000071 : Nat := 513492806871612314038477

theorem tailTrace_3000071 : CollatzResearch.WordTrace tailWord_3000071 prefixEnd_3000071 513492806871612314038477 := by
  unfold tailWord_3000071
  simp only [CollatzResearch.WordTrace]
  refine ⟨109421578714262613179944067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72947719142841742119962711 109421578714262613179944067)
  ·
    refine ⟨164132368071393919769916101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109421578714262613179944067 164132368071393919769916101)
    ·
      refine ⟨30774819013386359956859269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164132368071393919769916101 30774819013386359956859269)
      ·
        refine ⟨5770278565009942491911113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30774819013386359956859269 5770278565009942491911113)
        ·
          refine ⟨4327708923757456868933335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5770278565009942491911113 4327708923757456868933335)
          ·
            refine ⟨6491563385636185303400003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4327708923757456868933335 6491563385636185303400003)
            ·
              refine ⟨9737345078454277955100005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6491563385636185303400003 9737345078454277955100005)
              ·
                refine ⟨1825752202210177116581251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9737345078454277955100005 1825752202210177116581251)
                ·
                  refine ⟨2738628303315265674871877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1825752202210177116581251 2738628303315265674871877)
                  ·
                    refine ⟨513492806871612314038477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2738628303315265674871877 513492806871612314038477)
                    ·
                      rfl

theorem cell23_3000071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 4, 1, 4].length) (baseStart_3000071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000071 prefixEnd_3000071 := by exact prefixLift 3000071
  have htrace : WordTrace (prefixWord ++ tailWord_3000071) baseStart_3000071 baseEnd_3000071 := by
    simpa [prefixWord, tailWord_3000071, baseEnd_3000071] using wordTrace_append hprefix tailTrace_3000071
  have hstable : (prefixWord ++ tailWord_3000071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000071).length < 2 ^ (prefixWord ++ tailWord_3000071).sum := by decide
  have hdescent : baseEnd_3000071 < baseStart_3000071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000104 : List Nat := [2, 1, 5, 1, 1, 3, 1, 1, 1, 5, 2]
def baseStart_3000104 : Nat := 118140960795 + 3000104 * 2 ^ 59
def prefixEnd_3000104 : Nat := 4983230072969 + 3 ^ 40 * 3000104 * 2
def baseEnd_3000104 : Nat := 1540495365476435313002779

theorem tailTrace_3000104 : CollatzResearch.WordTrace tailWord_3000104 prefixEnd_3000104 1540495365476435313002779 := by
  unfold tailWord_3000104
  simp only [CollatzResearch.WordTrace]
  refine ⟨54711391161571529907947683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72948521548762039877263577 54711391161571529907947683)
  ·
    refine ⟨82067086742357294861921525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54711391161571529907947683 82067086742357294861921525)
    ·
      refine ⟨7693789382095996393305143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82067086742357294861921525 7693789382095996393305143)
      ·
        refine ⟨11540684073143994589957715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7693789382095996393305143 11540684073143994589957715)
        ·
          refine ⟨17311026109715991884936573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11540684073143994589957715 17311026109715991884936573)
          ·
            refine ⟨6491634791143496956851215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17311026109715991884936573 6491634791143496956851215)
            ·
              refine ⟨9737452186715245435276823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6491634791143496956851215 9737452186715245435276823)
              ·
                refine ⟨14606178280072868152915235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9737452186715245435276823 14606178280072868152915235)
                ·
                  refine ⟨21909267420109302229372853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14606178280072868152915235 21909267420109302229372853)
                  ·
                    refine ⟨2053993820635247084003705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21909267420109302229372853 2053993820635247084003705)
                    ·
                      refine ⟨1540495365476435313002779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2053993820635247084003705 1540495365476435313002779)
                      ·
                        rfl

theorem cell23_3000104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_3000104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000104 prefixEnd_3000104 := by exact prefixLift 3000104
  have htrace : WordTrace (prefixWord ++ tailWord_3000104) baseStart_3000104 baseEnd_3000104 := by
    simpa [prefixWord, tailWord_3000104, baseEnd_3000104] using wordTrace_append hprefix tailTrace_3000104
  have hstable : (prefixWord ++ tailWord_3000104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000104).length < 2 ^ (prefixWord ++ tailWord_3000104).sum := by decide
  have hdescent : baseEnd_3000104 < baseStart_3000104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000114 : List Nat := [3, 2, 1, 1, 3, 2, 4, 1, 1, 5]
def baseStart_3000114 : Nat := 118140960795 + 3000114 * 2 ^ 59
def prefixEnd_3000114 : Nat := 4983230072969 + 3 ^ 40 * 3000114 * 2
def baseEnd_3000114 : Nat := 513500166760993424625911

theorem tailTrace_3000114 : CollatzResearch.WordTrace tailWord_3000114 prefixEnd_3000114 513500166760993424625911 := by
  unfold tailWord_3000114
  simp only [CollatzResearch.WordTrace]
  refine ⟨27355786763276707880939849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72948764702071221015839597 27355786763276707880939849)
  ·
    refine ⟨20516840072457530910704887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27355786763276707880939849 20516840072457530910704887)
    ·
      refine ⟨30775260108686296366057331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20516840072457530910704887 30775260108686296366057331)
      ·
        refine ⟨46162890163029444549085997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30775260108686296366057331 46162890163029444549085997)
        ·
          refine ⟨17311083811136041705907249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46162890163029444549085997 17311083811136041705907249)
          ·
            refine ⟨12983312858352031279430437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17311083811136041705907249 12983312858352031279430437)
            ·
              refine ⟨2434371160941005864893207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12983312858352031279430437 2434371160941005864893207)
              ·
                refine ⟨3651556741411508797339811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2434371160941005864893207 3651556741411508797339811)
                ·
                  refine ⟨5477335112117263196009717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3651556741411508797339811 5477335112117263196009717)
                  ·
                    refine ⟨513500166760993424625911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5477335112117263196009717 513500166760993424625911)
                    ·
                      rfl

theorem cell23_3000114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 1, 5].length) (baseStart_3000114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000114 prefixEnd_3000114 := by exact prefixLift 3000114
  have htrace : WordTrace (prefixWord ++ tailWord_3000114) baseStart_3000114 baseEnd_3000114 := by
    simpa [prefixWord, tailWord_3000114, baseEnd_3000114] using wordTrace_append hprefix tailTrace_3000114
  have hstable : (prefixWord ++ tailWord_3000114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000114).length < 2 ^ (prefixWord ++ tailWord_3000114).sum := by decide
  have hdescent : baseEnd_3000114 < baseStart_3000114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000154 : List Nat := [3, 1, 1, 2, 1, 3, 4, 2, 1, 2, 3]
def baseStart_3000154 : Nat := 118140960795 + 3000154 * 2 ^ 59
def prefixEnd_3000154 : Nat := 4983230072969 + 3 ^ 40 * 3000154 * 2
def baseEnd_3000154 : Nat := 1540521039509160117377549

theorem tailTrace_3000154 : CollatzResearch.WordTrace tailWord_3000154 prefixEnd_3000154 1540521039509160117377549 := by
  unfold tailWord_3000154
  simp only [CollatzResearch.WordTrace]
  refine ⟨27356151493240479588803879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72949737315307945570143677 27356151493240479588803879)
  ·
    refine ⟨41034227239860719383205819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27356151493240479588803879 41034227239860719383205819)
    ·
      refine ⟨61551340859791079074808729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41034227239860719383205819 61551340859791079074808729)
      ·
        refine ⟨46163505644843309306106547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61551340859791079074808729 46163505644843309306106547)
        ·
          refine ⟨69245258467264963959159821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46163505644843309306106547 69245258467264963959159821)
          ·
            refine ⟨25966971925224361484684933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69245258467264963959159821 25966971925224361484684933)
            ·
              refine ⟨4868807235979567778378425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25966971925224361484684933 4868807235979567778378425)
              ·
                refine ⟨3651605426984675833783819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4868807235979567778378425 3651605426984675833783819)
                ·
                  refine ⟨5477408140477013750675729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3651605426984675833783819 5477408140477013750675729)
                  ·
                    refine ⟨4108056105357760313006797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5477408140477013750675729 4108056105357760313006797)
                    ·
                      refine ⟨1540521039509160117377549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4108056105357760313006797 1540521039509160117377549)
                      ·
                        rfl

theorem cell23_3000154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 1, 2, 3].length) (baseStart_3000154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000154 prefixEnd_3000154 := by exact prefixLift 3000154
  have htrace : WordTrace (prefixWord ++ tailWord_3000154) baseStart_3000154 baseEnd_3000154 := by
    simpa [prefixWord, tailWord_3000154, baseEnd_3000154] using wordTrace_append hprefix tailTrace_3000154
  have hstable : (prefixWord ++ tailWord_3000154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000154).length < 2 ^ (prefixWord ++ tailWord_3000154).sum := by decide
  have hdescent : baseEnd_3000154 < baseStart_3000154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000167 : List Nat := [1, 1, 5, 1, 2, 1, 2, 1, 3, 3, 3]
def baseStart_3000167 : Nat := 118140960795 + 3000167 * 2 ^ 59
def prefixEnd_3000167 : Nat := 4983230072969 + 3 ^ 40 * 3000167 * 2
def baseEnd_3000167 : Nat := 1540527714757668566514989

theorem tailTrace_3000167 : CollatzResearch.WordTrace tailWord_3000167 prefixEnd_3000167 1540527714757668566514989 := by
  unfold tailWord_3000167
  simp only [CollatzResearch.WordTrace]
  refine ⟨109425080121914821575438755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72950053414609881050292503 109425080121914821575438755)
  ·
    refine ⟨164137620182872232363158133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109425080121914821575438755 164137620182872232363158133)
    ·
      refine ⟨15387901892144271784046075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 164137620182872232363158133 15387901892144271784046075)
      ·
        refine ⟨23081852838216407676069113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15387901892144271784046075 23081852838216407676069113)
        ·
          refine ⟨17311389628662305757051835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23081852838216407676069113 17311389628662305757051835)
          ·
            refine ⟨25967084442993458635577753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17311389628662305757051835 25967084442993458635577753)
            ·
              refine ⟨19475313332245093976683315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25967084442993458635577753 19475313332245093976683315)
              ·
                refine ⟨29212969998367640965024973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19475313332245093976683315 29212969998367640965024973)
                ·
                  refine ⟨10954863749387865361884365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29212969998367640965024973 10954863749387865361884365)
                  ·
                    refine ⟨4108073906020449510706637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10954863749387865361884365 4108073906020449510706637)
                    ·
                      refine ⟨1540527714757668566514989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4108073906020449510706637 1540527714757668566514989)
                      ·
                        rfl

theorem cell23_3000167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_3000167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000167 prefixEnd_3000167 := by exact prefixLift 3000167
  have htrace : WordTrace (prefixWord ++ tailWord_3000167) baseStart_3000167 baseEnd_3000167 := by
    simpa [prefixWord, tailWord_3000167, baseEnd_3000167] using wordTrace_append hprefix tailTrace_3000167
  have hstable : (prefixWord ++ tailWord_3000167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000167).length < 2 ^ (prefixWord ++ tailWord_3000167).sum := by decide
  have hdescent : baseEnd_3000167 < baseStart_3000167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000228 : List Nat := [2, 3, 1, 2, 1, 4, 3, 1, 1, 3, 2]
def baseStart_3000228 : Nat := 118140960795 + 3000228 * 2 ^ 59
def prefixEnd_3000228 : Nat := 4983230072969 + 3 ^ 40 * 3000228 * 2
def baseEnd_3000228 : Nat := 1540559037077592827852209

theorem tailTrace_3000228 : CollatzResearch.WordTrace tailWord_3000228 prefixEnd_3000228 1540559037077592827852209 := by
  unfold tailWord_3000228
  simp only [CollatzResearch.WordTrace]
  refine ⟨54713652487346914496704669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72951536649795885995606225 54713652487346914496704669)
  ·
    refine ⟨20517619682755092936264251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54713652487346914496704669 20517619682755092936264251)
    ·
      refine ⟨30776429524132639404396377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20517619682755092936264251 30776429524132639404396377)
      ·
        refine ⟨23082322143099479553297283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30776429524132639404396377 23082322143099479553297283)
        ·
          refine ⟨34623483214649219329945925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23082322143099479553297283 34623483214649219329945925)
          ·
            refine ⟨6491903102746728624364861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34623483214649219329945925 6491903102746728624364861)
            ·
              refine ⟨2434463663530023234136823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6491903102746728624364861 2434463663530023234136823)
              ·
                refine ⟨3651695495295034851205235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2434463663530023234136823 3651695495295034851205235)
                ·
                  refine ⟨5477543242942552276807853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3651695495295034851205235 5477543242942552276807853)
                  ·
                    refine ⟨2054078716103457103802945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5477543242942552276807853 2054078716103457103802945)
                    ·
                      refine ⟨1540559037077592827852209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2054078716103457103802945 1540559037077592827852209)
                      ·
                        rfl

theorem cell23_3000228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_3000228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000228 prefixEnd_3000228 := by exact prefixLift 3000228
  have htrace : WordTrace (prefixWord ++ tailWord_3000228) baseStart_3000228 baseEnd_3000228 := by
    simpa [prefixWord, tailWord_3000228, baseEnd_3000228] using wordTrace_append hprefix tailTrace_3000228
  have hstable : (prefixWord ++ tailWord_3000228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000228).length < 2 ^ (prefixWord ++ tailWord_3000228).sum := by decide
  have hdescent : baseEnd_3000228 < baseStart_3000228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000254 : List Nat := [4, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4]
def baseStart_3000254 : Nat := 118140960795 + 3000254 * 2 ^ 59
def prefixEnd_3000254 : Nat := 4983230072969 + 3 ^ 40 * 3000254 * 2
def baseEnd_3000254 : Nat := 1540572387574609726127089

theorem tailTrace_3000254 : CollatzResearch.WordTrace tailWord_3000254 prefixEnd_3000254 1540572387574609726127089 := by
  unfold tailWord_3000254
  simp only [CollatzResearch.WordTrace]
  refine ⟨13678531659074954429231977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72952168848399756955903877 13678531659074954429231977)
  ·
    refine ⟨10258898744306215821923983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13678531659074954429231977 10258898744306215821923983)
    ·
      refine ⟨15388348116459323732885975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10258898744306215821923983 15388348116459323732885975)
      ·
        refine ⟨23082522174688985599328963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15388348116459323732885975 23082522174688985599328963)
        ·
          refine ⟨34623783262033478398993445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23082522174688985599328963 34623783262033478398993445)
          ·
            refine ⟨6491959361631277199811271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34623783262033478398993445 6491959361631277199811271)
            ·
              refine ⟨9737939042446915799716907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6491959361631277199811271 9737939042446915799716907)
              ·
                refine ⟨14606908563670373699575361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9737939042446915799716907 14606908563670373699575361)
                ·
                  refine ⟨10955181422752780274681521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14606908563670373699575361 10955181422752780274681521)
                  ·
                    refine ⟨8216386067064585206011141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10955181422752780274681521 8216386067064585206011141)
                    ·
                      refine ⟨1540572387574609726127089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8216386067064585206011141 1540572387574609726127089)
                      ·
                        rfl

theorem cell23_3000254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_3000254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000254 prefixEnd_3000254 := by exact prefixLift 3000254
  have htrace : WordTrace (prefixWord ++ tailWord_3000254) baseStart_3000254 baseEnd_3000254 := by
    simpa [prefixWord, tailWord_3000254, baseEnd_3000254] using wordTrace_append hprefix tailTrace_3000254
  have hstable : (prefixWord ++ tailWord_3000254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000254).length < 2 ^ (prefixWord ++ tailWord_3000254).sum := by decide
  have hdescent : baseEnd_3000254 < baseStart_3000254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000281 : List Nat := [1, 2, 1, 2, 6, 1, 2, 3, 5]
def baseStart_3000281 : Nat := 118140960795 + 3000281 * 2 ^ 59
def prefixEnd_3000281 : Nat := 4983230072969 + 3 ^ 40 * 3000281 * 2
def baseEnd_3000281 : Nat := 171176250172475680054385

theorem tailTrace_3000281 : CollatzResearch.WordTrace tailWord_3000281 prefixEnd_3000281 171176250172475680054385 := by
  unfold tailWord_3000281
  simp only [CollatzResearch.WordTrace]
  refine ⟨109429238043501819045088697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72952825362334546030059131 109429238043501819045088697)
  ·
    refine ⟨82071928532626364283816523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109429238043501819045088697 82071928532626364283816523)
    ·
      refine ⟨123107892798939546425724785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82071928532626364283816523 123107892798939546425724785)
      ·
        refine ⟨92330919599204659819293589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123107892798939546425724785 92330919599204659819293589)
        ·
          refine ⟨4328011856212718429029387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 92330919599204659819293589 4328011856212718429029387)
          ·
            refine ⟨6492017784319077643544081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4328011856212718429029387 6492017784319077643544081)
            ·
              refine ⟨4869013338239308232658061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6492017784319077643544081 4869013338239308232658061)
              ·
                refine ⟨1825880001839740587246773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4869013338239308232658061 1825880001839740587246773)
                ·
                  refine ⟨171176250172475680054385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1825880001839740587246773 171176250172475680054385)
                  ·
                    rfl

theorem cell23_3000281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 3, 5].length) (baseStart_3000281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000281 prefixEnd_3000281 := by exact prefixLift 3000281
  have htrace : WordTrace (prefixWord ++ tailWord_3000281) baseStart_3000281 baseEnd_3000281 := by
    simpa [prefixWord, tailWord_3000281, baseEnd_3000281] using wordTrace_append hprefix tailTrace_3000281
  have hstable : (prefixWord ++ tailWord_3000281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000281).length < 2 ^ (prefixWord ++ tailWord_3000281).sum := by decide
  have hdescent : baseEnd_3000281 < baseStart_3000281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000334 : List Nat := [4, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3]
def baseStart_3000334 : Nat := 118140960795 + 3000334 * 2 ^ 59
def prefixEnd_3000334 : Nat := 4983230072969 + 3 ^ 40 * 3000334 * 2
def baseEnd_3000334 : Nat := 1540613466026969413126721

theorem tailTrace_3000334 : CollatzResearch.WordTrace tailWord_3000334 prefixEnd_3000334 1540613466026969413126721 := by
  unfold tailWord_3000334
  simp only [CollatzResearch.WordTrace]
  refine ⟨13678896389038726137096007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72954114074873206064512037 13678896389038726137096007)
  ·
    refine ⟨20518344583558089205644011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13678896389038726137096007 20518344583558089205644011)
    ·
      refine ⟨30777516875337133808466017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20518344583558089205644011 30777516875337133808466017)
      ·
        refine ⟨23083137656502850356349513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30777516875337133808466017 23083137656502850356349513)
        ·
          refine ⟨17312353242377137767262135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23083137656502850356349513 17312353242377137767262135)
          ·
            refine ⟨25968529863565706650893203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17312353242377137767262135 25968529863565706650893203)
            ·
              refine ⟨38952794795348559976339805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25968529863565706650893203 38952794795348559976339805)
              ·
                refine ⟨14607298048255709991127427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38952794795348559976339805 14607298048255709991127427)
                ·
                  refine ⟨21910947072383564986691141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14607298048255709991127427 21910947072383564986691141)
                  ·
                    refine ⟨4108302576071918435004589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21910947072383564986691141 4108302576071918435004589)
                    ·
                      refine ⟨1540613466026969413126721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4108302576071918435004589 1540613466026969413126721)
                      ·
                        rfl

theorem cell23_3000334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_3000334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000334 prefixEnd_3000334 := by exact prefixLift 3000334
  have htrace : WordTrace (prefixWord ++ tailWord_3000334) baseStart_3000334 baseEnd_3000334 := by
    simpa [prefixWord, tailWord_3000334, baseEnd_3000334] using wordTrace_append hprefix tailTrace_3000334
  have hstable : (prefixWord ++ tailWord_3000334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000334).length < 2 ^ (prefixWord ++ tailWord_3000334).sum := by decide
  have hdescent : baseEnd_3000334 < baseStart_3000334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000354 : List Nat := [3, 3, 1, 1, 1, 2, 2, 4, 6]
def baseStart_3000354 : Nat := 118140960795 + 3000354 * 2 ^ 59
def prefixEnd_3000354 : Nat := 4983230072969 + 3 ^ 40 * 3000354 * 2
def baseEnd_3000354 : Nat := 171180415071117703875181

theorem tailTrace_3000354 : CollatzResearch.WordTrace tailWord_3000354 prefixEnd_3000354 171180415071117703875181 := by
  unfold tailWord_3000354
  simp only [CollatzResearch.WordTrace]
  refine ⟨27357975143059338128124029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72954600381491568341664077 27357975143059338128124029)
  ·
    refine ⟨10259240678647251798046511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27357975143059338128124029 10259240678647251798046511)
    ·
      refine ⟨15388861017970877697069767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10259240678647251798046511 15388861017970877697069767)
      ·
        refine ⟨23083291526956316545604651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15388861017970877697069767 23083291526956316545604651)
        ·
          refine ⟨34624937290434474818406977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23083291526956316545604651 34624937290434474818406977)
          ·
            refine ⟨25968702967825856113805233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34624937290434474818406977 25968702967825856113805233)
            ·
              refine ⟨19476527225869392085353925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25968702967825856113805233 19476527225869392085353925)
              ·
                refine ⟨3651848854850511016003861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19476527225869392085353925 3651848854850511016003861)
                ·
                  refine ⟨171180415071117703875181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3651848854850511016003861 171180415071117703875181)
                  ·
                    rfl

theorem cell23_3000354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_3000354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000354 prefixEnd_3000354 := by exact prefixLift 3000354
  have htrace : WordTrace (prefixWord ++ tailWord_3000354) baseStart_3000354 baseEnd_3000354 := by
    simpa [prefixWord, tailWord_3000354, baseEnd_3000354] using wordTrace_append hprefix tailTrace_3000354
  have hstable : (prefixWord ++ tailWord_3000354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000354).length < 2 ^ (prefixWord ++ tailWord_3000354).sum := by decide
  have hdescent : baseEnd_3000354 < baseStart_3000354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000381 : List Nat := [1, 4, 1, 3, 1, 1, 2, 1, 5, 1, 3]
def baseStart_3000381 : Nat := 118140960795 + 3000381 * 2 ^ 59
def prefixEnd_3000381 : Nat := 4983230072969 + 3 ^ 40 * 3000381 * 2
def baseEnd_3000381 : Nat := 1540637599617730729239005

theorem tailTrace_3000381 : CollatzResearch.WordTrace tailWord_3000381 prefixEnd_3000381 1540637599617730729239005 := by
  unfold tailWord_3000381
  simp only [CollatzResearch.WordTrace]
  refine ⟨109432885343139536123728997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72955256895426357415819331 109432885343139536123728997)
  ·
    refine ⟨20518666001838663023199187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109432885343139536123728997 20518666001838663023199187)
    ·
      refine ⟨30777999002757994534798781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20518666001838663023199187 30777999002757994534798781)
      ·
        refine ⟨11541749626034247950549543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30777999002757994534798781 11541749626034247950549543)
        ·
          refine ⟨17312624439051371925824315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11541749626034247950549543 17312624439051371925824315)
          ·
            refine ⟨25968936658577057888736473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17312624439051371925824315 25968936658577057888736473)
            ·
              refine ⟨19476702493932793416552355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25968936658577057888736473 19476702493932793416552355)
              ·
                refine ⟨29215053740899190124828533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19476702493932793416552355 29215053740899190124828533)
                ·
                  refine ⟨2738911288209299074202675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29215053740899190124828533 2738911288209299074202675)
                  ·
                    refine ⟨4108366932313948611304013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2738911288209299074202675 4108366932313948611304013)
                    ·
                      refine ⟨1540637599617730729239005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4108366932313948611304013 1540637599617730729239005)
                      ·
                        rfl

theorem cell23_3000381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_3000381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000381 prefixEnd_3000381 := by exact prefixLift 3000381
  have htrace : WordTrace (prefixWord ++ tailWord_3000381) baseStart_3000381 baseEnd_3000381 := by
    simpa [prefixWord, tailWord_3000381, baseEnd_3000381] using wordTrace_append hprefix tailTrace_3000381
  have hstable : (prefixWord ++ tailWord_3000381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000381).length < 2 ^ (prefixWord ++ tailWord_3000381).sum := by decide
  have hdescent : baseEnd_3000381 < baseStart_3000381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000384 : List Nat := [2, 1, 1, 2, 2, 5, 1, 1, 3, 5]
def baseStart_3000384 : Nat := 118140960795 + 3000384 * 2 ^ 59
def prefixEnd_3000384 : Nat := 4983230072969 + 3 ^ 40 * 3000384 * 2
def baseEnd_3000384 : Nat := 513546380019898072500497

theorem tailTrace_3000384 : CollatzResearch.WordTrace tailWord_3000384 prefixEnd_3000384 513546380019898072500497 := by
  unfold tailWord_3000384
  simp only [CollatzResearch.WordTrace]
  refine ⟨54716497381064333818044103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72955329841419111757392137 54716497381064333818044103)
  ·
    refine ⟨82074746071596500727066155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54716497381064333818044103 82074746071596500727066155)
    ·
      refine ⟨123112119107394751090599233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82074746071596500727066155 123112119107394751090599233)
      ·
        refine ⟨92334089330546063317949425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123112119107394751090599233 92334089330546063317949425)
        ·
          refine ⟨69250566997909547488462069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92334089330546063317949425 69250566997909547488462069)
          ·
            refine ⟨6492240656054020077043319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69250566997909547488462069 6492240656054020077043319)
            ·
              refine ⟨9738360984081030115564979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6492240656054020077043319 9738360984081030115564979)
              ·
                refine ⟨14607541476121545173347469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9738360984081030115564979 14607541476121545173347469)
                ·
                  refine ⟨5477828053545579440005301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14607541476121545173347469 5477828053545579440005301)
                  ·
                    refine ⟨513546380019898072500497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5477828053545579440005301 513546380019898072500497)
                    ·
                      rfl

theorem cell23_3000384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 3, 5].length) (baseStart_3000384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000384 prefixEnd_3000384 := by exact prefixLift 3000384
  have htrace : WordTrace (prefixWord ++ tailWord_3000384) baseStart_3000384 baseEnd_3000384 := by
    simpa [prefixWord, tailWord_3000384, baseEnd_3000384] using wordTrace_append hprefix tailTrace_3000384
  have hstable : (prefixWord ++ tailWord_3000384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000384).length < 2 ^ (prefixWord ++ tailWord_3000384).sum := by decide
  have hdescent : baseEnd_3000384 < baseStart_3000384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000431 : List Nat := [1, 1, 2, 1, 3, 4, 2, 3, 2, 4]
def baseStart_3000431 : Nat := 118140960795 + 3000431 * 2 ^ 59
def prefixEnd_3000431 : Nat := 4983230072969 + 3 ^ 40 * 3000431 * 2
def baseEnd_3000431 : Nat := 513554424550151844537925

theorem tailTrace_3000431 : CollatzResearch.WordTrace tailWord_3000431 prefixEnd_3000431 513554424550151844537925 := by
  unfold tailWord_3000431
  simp only [CollatzResearch.WordTrace]
  refine ⟨109434708992958394663049147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72956472661972263108699431 109434708992958394663049147)
  ·
    refine ⟨164152063489437591994573721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109434708992958394663049147 164152063489437591994573721)
    ·
      refine ⟨123114047617078193995930291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164152063489437591994573721 123114047617078193995930291)
      ·
        refine ⟨184671071425617290993895437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123114047617078193995930291 184671071425617290993895437)
        ·
          refine ⟨69251651784606484122710789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184671071425617290993895437 69251651784606484122710789)
          ·
            refine ⟨12984684709613715773008273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69251651784606484122710789 12984684709613715773008273)
            ·
              refine ⟨9738513532210286829756205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12984684709613715773008273 9738513532210286829756205)
              ·
                refine ⟨3651942574578857561158577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9738513532210286829756205 3651942574578857561158577)
                ·
                  refine ⟨2738956930934143170868933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3651942574578857561158577 2738956930934143170868933)
                  ·
                    refine ⟨513554424550151844537925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2738956930934143170868933 513554424550151844537925)
                    ·
                      rfl

theorem cell23_3000431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 2, 4].length) (baseStart_3000431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000431 prefixEnd_3000431 := by exact prefixLift 3000431
  have htrace : WordTrace (prefixWord ++ tailWord_3000431) baseStart_3000431 baseEnd_3000431 := by
    simpa [prefixWord, tailWord_3000431, baseEnd_3000431] using wordTrace_append hprefix tailTrace_3000431
  have hstable : (prefixWord ++ tailWord_3000431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000431).length < 2 ^ (prefixWord ++ tailWord_3000431).sum := by decide
  have hdescent : baseEnd_3000431 < baseStart_3000431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000441 : List Nat := [1, 2, 1, 3, 4, 1, 2, 1, 3, 2, 3]
def baseStart_3000441 : Nat := 118140960795 + 3000441 * 2 ^ 59
def prefixEnd_3000441 : Nat := 4983230072969 + 3 ^ 40 * 3000441 * 2
def baseEnd_3000441 : Nat := 1540668408457000494488729

theorem tailTrace_3000441 : CollatzResearch.WordTrace tailWord_3000441 prefixEnd_3000441 1540668408457000494488729 := by
  unfold tailWord_3000441
  simp only [CollatzResearch.WordTrace]
  refine ⟨109435073722922166370913177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72956715815281444247275451 109435073722922166370913177)
  ·
    refine ⟨82076305292191624778184883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109435073722922166370913177 82076305292191624778184883)
    ·
      refine ⟨123114457938287437167277325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82076305292191624778184883 123114457938287437167277325)
      ·
        refine ⟨46167921726857788937728997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123114457938287437167277325 46167921726857788937728997)
        ·
          refine ⟨8656485323785835425824187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46167921726857788937728997 8656485323785835425824187)
          ·
            refine ⟨12984727985678753138736281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8656485323785835425824187 12984727985678753138736281)
            ·
              refine ⟨9738545989259064854052211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12984727985678753138736281 9738545989259064854052211)
              ·
                refine ⟨14607818983888597281078317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9738545989259064854052211 14607818983888597281078317)
                ·
                  refine ⟨5477932118958223980404369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14607818983888597281078317 5477932118958223980404369)
                  ·
                    refine ⟨4108449089218667985303277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5477932118958223980404369 4108449089218667985303277)
                    ·
                      refine ⟨1540668408457000494488729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4108449089218667985303277 1540668408457000494488729)
                      ·
                        rfl

theorem cell23_3000441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_3000441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000441 prefixEnd_3000441 := by exact prefixLift 3000441
  have htrace : WordTrace (prefixWord ++ tailWord_3000441) baseStart_3000441 baseEnd_3000441 := by
    simpa [prefixWord, tailWord_3000441, baseEnd_3000441] using wordTrace_append hprefix tailTrace_3000441
  have hstable : (prefixWord ++ tailWord_3000441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000441).length < 2 ^ (prefixWord ++ tailWord_3000441).sum := by decide
  have hdescent : baseEnd_3000441 < baseStart_3000441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000455 : List Nat := [1, 1, 4, 2, 1, 1, 3, 5, 1, 2, 2]
def baseStart_3000455 : Nat := 118140960795 + 3000455 * 2 ^ 59
def prefixEnd_3000455 : Nat := 4983230072969 + 3 ^ 40 * 3000455 * 2
def baseEnd_3000455 : Nat := 1540675597186163439713665

theorem tailTrace_3000455 : CollatzResearch.WordTrace tailWord_3000455 prefixEnd_3000455 1540675597186163439713665 := by
  unfold tailWord_3000455
  simp only [CollatzResearch.WordTrace]
  refine ⟨109435584344871446761922819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72957056229914297841281879 109435584344871446761922819)
  ·
    refine ⟨164153376517307170142884229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109435584344871446761922819 164153376517307170142884229)
    ·
      refine ⟨30778758096995094401790793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164153376517307170142884229 30778758096995094401790793)
      ·
        refine ⟨23084068572746320801343095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30778758096995094401790793 23084068572746320801343095)
        ·
          refine ⟨34626102859119481202014643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23084068572746320801343095 34626102859119481202014643)
          ·
            refine ⟨51939154288679221803021965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34626102859119481202014643 51939154288679221803021965)
            ·
              refine ⟨19477182858254708176133237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51939154288679221803021965 19477182858254708176133237)
              ·
                refine ⟨1825985892961378891512491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19477182858254708176133237 1825985892961378891512491)
                ·
                  refine ⟨2738978839442068337268737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1825985892961378891512491 2738978839442068337268737)
                  ·
                    refine ⟨2054234129581551252951553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2738978839442068337268737 2054234129581551252951553)
                    ·
                      refine ⟨1540675597186163439713665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2054234129581551252951553 1540675597186163439713665)
                      ·
                        rfl

theorem cell23_3000455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_3000455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000455 prefixEnd_3000455 := by exact prefixLift 3000455
  have htrace : WordTrace (prefixWord ++ tailWord_3000455) baseStart_3000455 baseEnd_3000455 := by
    simpa [prefixWord, tailWord_3000455, baseEnd_3000455] using wordTrace_append hprefix tailTrace_3000455
  have hstable : (prefixWord ++ tailWord_3000455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000455).length < 2 ^ (prefixWord ++ tailWord_3000455).sum := by decide
  have hdescent : baseEnd_3000455 < baseStart_3000455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000458 : List Nat := [3, 1, 2, 3, 1, 3, 1, 3, 1, 2, 3]
def baseStart_3000458 : Nat := 118140960795 + 3000458 * 2 ^ 59
def prefixEnd_3000458 : Nat := 4983230072969 + 3 ^ 40 * 3000458 * 2
def baseEnd_3000458 : Nat := 1540677137628126927976151

theorem tailTrace_3000458 : CollatzResearch.WordTrace tailWord_3000458 prefixEnd_3000458 1540677137628126927976151 := by
  unfold tailWord_3000458
  simp only [CollatzResearch.WordTrace]
  refine ⟨27358923440965144568570507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72957129175907052182854685 27358923440965144568570507)
  ·
    refine ⟨41038385161447716852855761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27358923440965144568570507 41038385161447716852855761)
    ·
      refine ⟨30778788871085787639641821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41038385161447716852855761 30778788871085787639641821)
      ·
        refine ⟨11542045826657170364865683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30778788871085787639641821 11542045826657170364865683)
        ·
          refine ⟨17313068739985755547298525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11542045826657170364865683 17313068739985755547298525)
          ·
            refine ⟨6492400777494658330236947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17313068739985755547298525 6492400777494658330236947)
            ·
              refine ⟨9738601166241987495355421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6492400777494658330236947 9738601166241987495355421)
              ·
                refine ⟨3651975437340745310758283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9738601166241987495355421 3651975437340745310758283)
                ·
                  refine ⟨5477963156011117966137425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3651975437340745310758283 5477963156011117966137425)
                  ·
                    refine ⟨4108472367008338474603069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5477963156011117966137425 4108472367008338474603069)
                    ·
                      refine ⟨1540677137628126927976151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4108472367008338474603069 1540677137628126927976151)
                      ·
                        rfl

theorem cell23_3000458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_3000458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000458 prefixEnd_3000458 := by exact prefixLift 3000458
  have htrace : WordTrace (prefixWord ++ tailWord_3000458) baseStart_3000458 baseEnd_3000458 := by
    simpa [prefixWord, tailWord_3000458, baseEnd_3000458] using wordTrace_append hprefix tailTrace_3000458
  have hstable : (prefixWord ++ tailWord_3000458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000458).length < 2 ^ (prefixWord ++ tailWord_3000458).sum := by decide
  have hdescent : baseEnd_3000458 < baseStart_3000458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000511 : List Nat := [1, 1, 2, 2, 2, 2, 1, 3, 3, 4, 2]
def baseStart_3000511 : Nat := 118140960795 + 3000511 * 2 ^ 59
def prefixEnd_3000511 : Nat := 4983230072969 + 3 ^ 40 * 3000511 * 2
def baseEnd_3000511 : Nat := 1540704352102815220613407

theorem tailTrace_3000511 : CollatzResearch.WordTrace tailWord_3000511 prefixEnd_3000511 1540704352102815220613407 := by
  unfold tailWord_3000511
  simp only [CollatzResearch.WordTrace]
  refine ⟨109437626832668568325961387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72958417888445712217307591 109437626832668568325961387)
  ·
    refine ⟨164156440249002852488942081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109437626832668568325961387 164156440249002852488942081)
    ·
      refine ⟨123117330186752139366706561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164156440249002852488942081 123117330186752139366706561)
      ·
        refine ⟨92337997640064104525029921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123117330186752139366706561 92337997640064104525029921)
        ·
          refine ⟨69253498230048078393772441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92337997640064104525029921 69253498230048078393772441)
          ·
            refine ⟨51940123672536058795329331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69253498230048078393772441 51940123672536058795329331)
            ·
              refine ⟨77910185508804088192993997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51940123672536058795329331 77910185508804088192993997)
              ·
                refine ⟨29216319565801533072372749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77910185508804088192993997 29216319565801533072372749)
                ·
                  refine ⟨10956119837175574902139781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29216319565801533072372749 10956119837175574902139781)
                  ·
                    refine ⟨2054272469470420294151209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10956119837175574902139781 2054272469470420294151209)
                    ·
                      refine ⟨1540704352102815220613407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2054272469470420294151209 1540704352102815220613407)
                      ·
                        rfl

theorem cell23_3000511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 4, 2].length) (baseStart_3000511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000511 prefixEnd_3000511 := by exact prefixLift 3000511
  have htrace : WordTrace (prefixWord ++ tailWord_3000511) baseStart_3000511 baseEnd_3000511 := by
    simpa [prefixWord, tailWord_3000511, baseEnd_3000511] using wordTrace_append hprefix tailTrace_3000511
  have hstable : (prefixWord ++ tailWord_3000511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000511).length < 2 ^ (prefixWord ++ tailWord_3000511).sum := by decide
  have hdescent : baseEnd_3000511 < baseStart_3000511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000545 : List Nat := [1, 2, 3, 1, 3, 1, 3, 3, 2, 2, 2]
def baseStart_3000545 : Nat := 118140960795 + 3000545 * 2 ^ 59
def prefixEnd_3000545 : Nat := 4983230072969 + 3 ^ 40 * 3000545 * 2
def baseEnd_3000545 : Nat := 1540721810445068087588251

theorem tailTrace_3000545 : CollatzResearch.WordTrace tailWord_3000545 prefixEnd_3000545 1540721810445068087588251 := by
  unfold tailWord_3000545
  simp only [CollatzResearch.WordTrace]
  refine ⟨109438866914545392132699089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72959244609696928088466059 109438866914545392132699089)
  ·
    refine ⟨82079150185909044099524317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109438866914545392132699089 82079150185909044099524317)
    ·
      refine ⟨30779681319715891537321619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82079150185909044099524317 30779681319715891537321619)
      ·
        refine ⟨46169521979573837305982429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30779681319715891537321619 46169521979573837305982429)
        ·
          refine ⟨17313570742340188989743411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46169521979573837305982429 17313570742340188989743411)
          ·
            refine ⟨25970356113510283484615117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17313570742340188989743411 25970356113510283484615117)
            ·
              refine ⟨9738883542566356306730669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25970356113510283484615117 9738883542566356306730669)
              ·
                refine ⟨3652081328462383615024001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9738883542566356306730669 3652081328462383615024001)
                ·
                  refine ⟨2739060996346787711268001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3652081328462383615024001 2739060996346787711268001)
                  ·
                    refine ⟨2054295747260090783451001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2739060996346787711268001 2054295747260090783451001)
                    ·
                      refine ⟨1540721810445068087588251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2054295747260090783451001 1540721810445068087588251)
                      ·
                        rfl

theorem cell23_3000545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 2, 2, 2].length) (baseStart_3000545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000545 prefixEnd_3000545 := by exact prefixLift 3000545
  have htrace : WordTrace (prefixWord ++ tailWord_3000545) baseStart_3000545 baseEnd_3000545 := by
    simpa [prefixWord, tailWord_3000545, baseEnd_3000545] using wordTrace_append hprefix tailTrace_3000545
  have hstable : (prefixWord ++ tailWord_3000545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000545).length < 2 ^ (prefixWord ++ tailWord_3000545).sum := by decide
  have hdescent : baseEnd_3000545 < baseStart_3000545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000571 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 6, 5, 2]
def baseStart_3000571 : Nat := 118140960795 + 3000571 * 2 ^ 59
def prefixEnd_3000571 : Nat := 4983230072969 + 3 ^ 40 * 3000571 * 2
def baseEnd_3000571 : Nat := 1540735160942084985863131

theorem tailTrace_3000571 : CollatzResearch.WordTrace tailWord_3000571 prefixEnd_3000571 1540735160942084985863131 := by
  unfold tailWord_3000571
  simp only [CollatzResearch.WordTrace]
  refine ⟨109439815212451198573145567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72959876808300799048763711 109439815212451198573145567)
  ·
    refine ⟨164159722818676797859718351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109439815212451198573145567 164159722818676797859718351)
    ·
      refine ⟨246239584228015196789577527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164159722818676797859718351 246239584228015196789577527)
      ·
        refine ⟨369359376342022795184366291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246239584228015196789577527 369359376342022795184366291)
        ·
          refine ⟨554039064513034192776549437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369359376342022795184366291 554039064513034192776549437)
          ·
            refine ⟨207764649192387822291206039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 554039064513034192776549437 207764649192387822291206039)
            ·
              refine ⟨311646973788581733436809059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207764649192387822291206039 311646973788581733436809059)
              ·
                refine ⟨467470460682872600155213589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 311646973788581733436809059 467470460682872600155213589)
                ·
                  refine ⟨21912677844509653132275637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 467470460682872600155213589 21912677844509653132275637)
                  ·
                    refine ⟨2054313547922779981150841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21912677844509653132275637 2054313547922779981150841)
                    ·
                      refine ⟨1540735160942084985863131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2054313547922779981150841 1540735160942084985863131)
                      ·
                        rfl

theorem cell23_3000571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 5, 2].length) (baseStart_3000571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000571 prefixEnd_3000571 := by exact prefixLift 3000571
  have htrace : WordTrace (prefixWord ++ tailWord_3000571) baseStart_3000571 baseEnd_3000571 := by
    simpa [prefixWord, tailWord_3000571, baseEnd_3000571] using wordTrace_append hprefix tailTrace_3000571
  have hstable : (prefixWord ++ tailWord_3000571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000571).length < 2 ^ (prefixWord ++ tailWord_3000571).sum := by decide
  have hdescent : baseEnd_3000571 < baseStart_3000571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000585 : List Nat := [1, 2, 1, 1, 3, 6, 2, 2, 5]
def baseStart_3000585 : Nat := 118140960795 + 3000585 * 2 ^ 59
def prefixEnd_3000585 : Nat := 4983230072969 + 3 ^ 40 * 3000585 * 2
def baseEnd_3000585 : Nat := 171193594407916436787563

theorem tailTrace_3000585 : CollatzResearch.WordTrace tailWord_3000585 prefixEnd_3000585 171193594407916436787563 := by
  unfold tailWord_3000585
  simp only [CollatzResearch.WordTrace]
  refine ⟨109440325834400478964155209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72960217222933652642770139 109440325834400478964155209)
  ·
    refine ⟨82080244375800359223116407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109440325834400478964155209 82080244375800359223116407)
    ·
      refine ⟨123120366563700538834674611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82080244375800359223116407 123120366563700538834674611)
      ·
        refine ⟨184680549845550808252011917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123120366563700538834674611 184680549845550808252011917)
        ·
          refine ⟨69255206192081553094504469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184680549845550808252011917 69255206192081553094504469)
          ·
            refine ⟨3246337790253822801304897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 69255206192081553094504469 3246337790253822801304897)
            ·
              refine ⟨2434753342690367100978673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3246337790253822801304897 2434753342690367100978673)
              ·
                refine ⟨1826065007017775325734005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2434753342690367100978673 1826065007017775325734005)
                ·
                  refine ⟨171193594407916436787563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1826065007017775325734005 171193594407916436787563)
                  ·
                    rfl

theorem cell23_3000585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 2, 5].length) (baseStart_3000585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000585 prefixEnd_3000585 := by exact prefixLift 3000585
  have htrace : WordTrace (prefixWord ++ tailWord_3000585) baseStart_3000585 baseEnd_3000585 := by
    simpa [prefixWord, tailWord_3000585, baseEnd_3000585] using wordTrace_append hprefix tailTrace_3000585
  have hstable : (prefixWord ++ tailWord_3000585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000585).length < 2 ^ (prefixWord ++ tailWord_3000585).sum := by decide
  have hdescent : baseEnd_3000585 < baseStart_3000585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000671 : List Nat := [1, 1, 2, 3, 1, 2, 2, 3, 3, 5]
def baseStart_3000671 : Nat := 118140960795 + 3000671 * 2 ^ 59
def prefixEnd_3000671 : Nat := 4983230072969 + 3 ^ 40 * 3000671 * 2
def baseEnd_3000671 : Nat := 513595503002511531537557

theorem tailTrace_3000671 : CollatzResearch.WordTrace tailWord_3000671 prefixEnd_3000671 513595503002511531537557 := by
  unfold tailWord_3000671
  simp only [CollatzResearch.WordTrace]
  refine ⟨109443462512088915651785867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72962308341392610434523911 109443462512088915651785867)
  ·
    refine ⟨164165193768133373477678801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109443462512088915651785867 164165193768133373477678801)
    ·
      refine ⟨123123895326100030108259101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164165193768133373477678801 123123895326100030108259101)
      ·
        refine ⟨46171460747287511290597163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123123895326100030108259101 46171460747287511290597163)
        ·
          refine ⟨69257191120931266935895745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46171460747287511290597163 69257191120931266935895745)
          ·
            refine ⟨51942893340698450201921809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69257191120931266935895745 51942893340698450201921809)
            ·
              refine ⟨38957170005523837651441357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51942893340698450201921809 38957170005523837651441357)
              ·
                refine ⟨14608938752071439119290509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38957170005523837651441357 14608938752071439119290509)
                ·
                  refine ⟨5478352032026789669733941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14608938752071439119290509 5478352032026789669733941)
                  ·
                    refine ⟨513595503002511531537557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5478352032026789669733941 513595503002511531537557)
                    ·
                      rfl

theorem cell23_3000671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 5].length) (baseStart_3000671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000671 prefixEnd_3000671 := by exact prefixLift 3000671
  have htrace : WordTrace (prefixWord ++ tailWord_3000671) baseStart_3000671 baseEnd_3000671 := by
    simpa [prefixWord, tailWord_3000671, baseEnd_3000671] using wordTrace_append hprefix tailTrace_3000671
  have hstable : (prefixWord ++ tailWord_3000671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000671).length < 2 ^ (prefixWord ++ tailWord_3000671).sum := by decide
  have hdescent : baseEnd_3000671 < baseStart_3000671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000688 : List Nat := [2, 1, 1, 1, 4, 3, 2, 3, 1, 5]
def baseStart_3000688 : Nat := 118140960795 + 3000688 * 2 ^ 59
def prefixEnd_3000688 : Nat := 4983230072969 + 3 ^ 40 * 3000688 * 2
def baseEnd_3000688 : Nat := 513598412726220342700031

theorem tailTrace_3000688 : CollatzResearch.WordTrace tailWord_3000688 prefixEnd_3000688 513598412726220342700031 := by
  unfold tailWord_3000688
  simp only [CollatzResearch.WordTrace]
  refine ⟨54722041276513663777577359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72962721702018218370103145 54722041276513663777577359)
  ·
    refine ⟨82083061914770495666366039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54722041276513663777577359 82083061914770495666366039)
    ·
      refine ⟨123124592872155743499549059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82083061914770495666366039 123124592872155743499549059)
      ·
        refine ⟨184686889308233615249323589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123124592872155743499549059 184686889308233615249323589)
        ·
          refine ⟨34628791745293802859248173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 184686889308233615249323589 34628791745293802859248173)
          ·
            refine ⟨12985796904485176072218065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34628791745293802859248173 12985796904485176072218065)
            ·
              refine ⟨9739347678363882054163549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12985796904485176072218065 9739347678363882054163549)
              ·
                refine ⟨3652255379386455770311331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9739347678363882054163549 3652255379386455770311331)
                ·
                  refine ⟨5478383069079683655466997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3652255379386455770311331 5478383069079683655466997)
                  ·
                    refine ⟨513598412726220342700031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5478383069079683655466997 513598412726220342700031)
                    ·
                      rfl

theorem cell23_3000688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 1, 5].length) (baseStart_3000688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000688 prefixEnd_3000688 := by exact prefixLift 3000688
  have htrace : WordTrace (prefixWord ++ tailWord_3000688) baseStart_3000688 baseEnd_3000688 := by
    simpa [prefixWord, tailWord_3000688, baseEnd_3000688] using wordTrace_append hprefix tailTrace_3000688
  have hstable : (prefixWord ++ tailWord_3000688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000688).length < 2 ^ (prefixWord ++ tailWord_3000688).sum := by decide
  have hdescent : baseEnd_3000688 < baseStart_3000688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000708 : List Nat := [2, 3, 2, 1, 1, 2, 2, 2, 3, 1, 4]
def baseStart_3000708 : Nat := 118140960795 + 3000708 * 2 ^ 59
def prefixEnd_3000708 : Nat := 4983230072969 + 3 ^ 40 * 3000708 * 2
def baseEnd_3000708 : Nat := 1540805507791750949850001

theorem tailTrace_3000708 : CollatzResearch.WordTrace tailWord_3000708 prefixEnd_3000708 1540805507791750949850001 := by
  unfold tailWord_3000708
  simp only [CollatzResearch.WordTrace]
  refine ⟨54722406006477435485441389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72963208008636580647255185 54722406006477435485441389)
  ·
    refine ⟨20520902252429038307040521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54722406006477435485441389 20520902252429038307040521)
    ·
      refine ⟨15390676689321778730280391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20520902252429038307040521 15390676689321778730280391)
      ·
        refine ⟨23086015033982668095420587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15390676689321778730280391 23086015033982668095420587)
        ·
          refine ⟨34629022550974002143130881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23086015033982668095420587 34629022550974002143130881)
          ·
            refine ⟨25971766913230501607348161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34629022550974002143130881 25971766913230501607348161)
            ·
              refine ⟨19478825184922876205511121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25971766913230501607348161 19478825184922876205511121)
              ·
                refine ⟨14609118888692157154133341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19478825184922876205511121 14609118888692157154133341)
                ·
                  refine ⟨5478419583259558932800003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14609118888692157154133341 5478419583259558932800003)
                  ·
                    refine ⟨8217629374889338399200005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5478419583259558932800003 8217629374889338399200005)
                    ·
                      refine ⟨1540805507791750949850001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8217629374889338399200005 1540805507791750949850001)
                      ·
                        rfl

theorem cell23_3000708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_3000708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000708 prefixEnd_3000708 := by exact prefixLift 3000708
  have htrace : WordTrace (prefixWord ++ tailWord_3000708) baseStart_3000708 baseEnd_3000708 := by
    simpa [prefixWord, tailWord_3000708, baseEnd_3000708] using wordTrace_append hprefix tailTrace_3000708
  have hstable : (prefixWord ++ tailWord_3000708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000708).length < 2 ^ (prefixWord ++ tailWord_3000708).sum := by decide
  have hdescent : baseEnd_3000708 < baseStart_3000708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000725 : List Nat := [1, 3, 2, 1, 1, 2, 1, 3, 5, 2, 2]
def baseStart_3000725 : Nat := 118140960795 + 3000725 * 2 ^ 59
def prefixEnd_3000725 : Nat := 4983230072969 + 3 ^ 40 * 3000725 * 2
def baseEnd_3000725 : Nat := 1540814236962877383337423

theorem tailTrace_3000725 : CollatzResearch.WordTrace tailWord_3000725 prefixEnd_3000725 1540814236962877383337423 := by
  unfold tailWord_3000725
  simp only [CollatzResearch.WordTrace]
  refine ⟨109445432053893282874251629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72963621369262188582834419 109445432053893282874251629)
  ·
    refine ⟨41042037020209981077844361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109445432053893282874251629 41042037020209981077844361)
    ·
      refine ⟨30781527765157485808383271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41042037020209981077844361 30781527765157485808383271)
      ·
        refine ⟨46172291647736228712574907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30781527765157485808383271 46172291647736228712574907)
        ·
          refine ⟨69258437471604343068862361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46172291647736228712574907 69258437471604343068862361)
          ·
            refine ⟨51943828103703257301646771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69258437471604343068862361 51943828103703257301646771)
            ·
              refine ⟨77915742155554885952470157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51943828103703257301646771 77915742155554885952470157)
              ·
                refine ⟨29218403308333082232176309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77915742155554885952470157 29218403308333082232176309)
                ·
                  refine ⟨2739225310156226459266529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29218403308333082232176309 2739225310156226459266529)
                  ·
                    refine ⟨2054418982617169844449897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2739225310156226459266529 2054418982617169844449897)
                    ·
                      refine ⟨1540814236962877383337423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2054418982617169844449897 1540814236962877383337423)
                      ·
                        rfl

theorem cell23_3000725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 5, 2, 2].length) (baseStart_3000725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000725 prefixEnd_3000725 := by exact prefixLift 3000725
  have htrace : WordTrace (prefixWord ++ tailWord_3000725) baseStart_3000725 baseEnd_3000725 := by
    simpa [prefixWord, tailWord_3000725, baseEnd_3000725] using wordTrace_append hprefix tailTrace_3000725
  have hstable : (prefixWord ++ tailWord_3000725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000725).length < 2 ^ (prefixWord ++ tailWord_3000725).sum := by decide
  have hdescent : baseEnd_3000725 < baseStart_3000725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000759 : List Nat := [1, 1, 3, 1, 3, 4, 1, 4, 1, 2, 2]
def baseStart_3000759 : Nat := 118140960795 + 3000759 * 2 ^ 59
def prefixEnd_3000759 : Nat := 4983230072969 + 3 ^ 40 * 3000759 * 2
def baseEnd_3000759 : Nat := 1540831695305130250312267

theorem tailTrace_3000759 : CollatzResearch.WordTrace tailWord_3000759 prefixEnd_3000759 1540831695305130250312267 := by
  unfold tailWord_3000759
  simp only [CollatzResearch.WordTrace]
  refine ⟨109446672135770106680989331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72964448090513404453992887 109446672135770106680989331)
  ·
    refine ⟨164170008203655160021483997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109446672135770106680989331 164170008203655160021483997)
    ·
      refine ⟨61563753076370685008056499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164170008203655160021483997 61563753076370685008056499)
      ·
        refine ⟨92345629614556027512084749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61563753076370685008056499 92345629614556027512084749)
        ·
          refine ⟨34629611105458510317031781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92345629614556027512084749 34629611105458510317031781)
          ·
            refine ⟨6493052082273470684443459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34629611105458510317031781 6493052082273470684443459)
            ·
              refine ⟨9739578123410206026665189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6493052082273470684443459 9739578123410206026665189)
              ·
                refine ⟨1826170898139413629999723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9739578123410206026665189 1826170898139413629999723)
                ·
                  refine ⟨2739256347209120444999585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1826170898139413629999723 2739256347209120444999585)
                  ·
                    refine ⟨2054442260406840333749689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2739256347209120444999585 2054442260406840333749689)
                    ·
                      refine ⟨1540831695305130250312267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2054442260406840333749689 1540831695305130250312267)
                      ·
                        rfl

theorem cell23_3000759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 4, 1, 2, 2].length) (baseStart_3000759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000759 prefixEnd_3000759 := by exact prefixLift 3000759
  have htrace : WordTrace (prefixWord ++ tailWord_3000759) baseStart_3000759 baseEnd_3000759 := by
    simpa [prefixWord, tailWord_3000759, baseEnd_3000759] using wordTrace_append hprefix tailTrace_3000759
  have hstable : (prefixWord ++ tailWord_3000759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000759).length < 2 ^ (prefixWord ++ tailWord_3000759).sum := by decide
  have hdescent : baseEnd_3000759 < baseStart_3000759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000769 : List Nat := [1, 2, 7, 1, 1, 1, 2, 1, 1, 6]
def baseStart_3000769 : Nat := 118140960795 + 3000769 * 2 ^ 59
def prefixEnd_3000769 : Nat := 4983230072969 + 3 ^ 40 * 3000769 * 2
def baseEnd_3000769 : Nat := 513612276703891737062407

theorem tailTrace_3000769 : CollatzResearch.WordTrace tailWord_3000769 prefixEnd_3000769 513612276703891737062407 := by
  unfold tailWord_3000769
  simp only [CollatzResearch.WordTrace]
  refine ⟨109447036865733878388853361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72964691243822585592568907 109447036865733878388853361)
  ·
    refine ⟨82085277649300408791640021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109447036865733878388853361 82085277649300408791640021)
    ·
      refine ⟨1923873694905478331054063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 82085277649300408791640021 1923873694905478331054063)
      ·
        refine ⟨2885810542358217496581095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1923873694905478331054063 2885810542358217496581095)
        ·
          refine ⟨4328715813537326244871643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2885810542358217496581095 4328715813537326244871643)
          ·
            refine ⟨6493073720305989367307465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4328715813537326244871643 6493073720305989367307465)
            ·
              refine ⟨4869805290229492025480599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6493073720305989367307465 4869805290229492025480599)
              ·
                refine ⟨7304707935344238038220899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4869805290229492025480599 7304707935344238038220899)
                ·
                  refine ⟨10957061903016357057331349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7304707935344238038220899 10957061903016357057331349)
                  ·
                    refine ⟨513612276703891737062407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10957061903016357057331349 513612276703891737062407)
                    ·
                      rfl

theorem cell23_3000769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_3000769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000769 prefixEnd_3000769 := by exact prefixLift 3000769
  have htrace : WordTrace (prefixWord ++ tailWord_3000769) baseStart_3000769 baseEnd_3000769 := by
    simpa [prefixWord, tailWord_3000769, baseEnd_3000769] using wordTrace_append hprefix tailTrace_3000769
  have hstable : (prefixWord ++ tailWord_3000769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000769).length < 2 ^ (prefixWord ++ tailWord_3000769).sum := by decide
  have hdescent : baseEnd_3000769 < baseStart_3000769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000771 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 5]
def baseStart_3000771 : Nat := 118140960795 + 3000771 * 2 ^ 59
def prefixEnd_3000771 : Nat := 4983230072969 + 3 ^ 40 * 3000771 * 2
def baseEnd_3000771 : Nat := 1540837857072984203362211

theorem tailTrace_3000771 : CollatzResearch.WordTrace tailWord_3000771 prefixEnd_3000771 1540837857072984203362211 := by
  unfold tailWord_3000771
  simp only [CollatzResearch.WordTrace]
  refine ⟨109447109811726632730426167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72964739874484421820284111 109447109811726632730426167)
  ·
    refine ⟨164170664717589949095639251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109447109811726632730426167 164170664717589949095639251)
    ·
      refine ⟨246255997076384923643458877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164170664717589949095639251 246255997076384923643458877)
      ·
        refine ⟨92345998903644346366297079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246255997076384923643458877 92345998903644346366297079)
        ·
          refine ⟨138518998355466519549445619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92345998903644346366297079 138518998355466519549445619)
          ·
            refine ⟨207778497533199779324168429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138518998355466519549445619 207778497533199779324168429)
            ·
              refine ⟨77916936574949917246563161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 207778497533199779324168429 77916936574949917246563161)
              ·
                refine ⟨58437702431212437934922371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77916936574949917246563161 58437702431212437934922371)
                ·
                  refine ⟨87656553646818656902383557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58437702431212437934922371 87656553646818656902383557)
                  ·
                    refine ⟨16435603808778498169196917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87656553646818656902383557 16435603808778498169196917)
                    ·
                      refine ⟨1540837857072984203362211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16435603808778498169196917 1540837857072984203362211)
                      ·
                        rfl

theorem cell23_3000771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_3000771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000771 prefixEnd_3000771 := by exact prefixLift 3000771
  have htrace : WordTrace (prefixWord ++ tailWord_3000771) baseStart_3000771 baseEnd_3000771 := by
    simpa [prefixWord, tailWord_3000771, baseEnd_3000771] using wordTrace_append hprefix tailTrace_3000771
  have hstable : (prefixWord ++ tailWord_3000771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000771).length < 2 ^ (prefixWord ++ tailWord_3000771).sum := by decide
  have hdescent : baseEnd_3000771 < baseStart_3000771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000772 : List Nat := [2, 3, 3, 2, 2, 1, 2, 1, 1, 2, 4]
def baseStart_3000772 : Nat := 118140960795 + 3000772 * 2 ^ 59
def prefixEnd_3000772 : Nat := 4983230072969 + 3 ^ 40 * 3000772 * 2
def baseEnd_3000772 : Nat := 1540838370553638699449707

theorem tailTrace_3000772 : CollatzResearch.WordTrace tailWord_3000772 prefixEnd_3000772 1540838370553638699449707 := by
  unfold tailWord_3000772
  simp only [CollatzResearch.WordTrace]
  refine ⟨54723573142361504950606285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72964764189815339934141713 54723573142361504950606285)
  ·
    refine ⟨20521339928385564356477357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54723573142361504950606285 20521339928385564356477357)
    ·
      refine ⟨7695502473144586633679009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20521339928385564356477357 7695502473144586633679009)
      ·
        refine ⟨5771626854858439975259257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7695502473144586633679009 5771626854858439975259257)
        ·
          refine ⟨4328720141143829981444443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5771626854858439975259257 4328720141143829981444443)
          ·
            refine ⟨6493080211715744972166665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4328720141143829981444443 6493080211715744972166665)
            ·
              refine ⟨4869810158786808729124999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6493080211715744972166665 4869810158786808729124999)
              ·
                refine ⟨7304715238180213093687499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4869810158786808729124999 7304715238180213093687499)
                ·
                  refine ⟨10957072857270319640531249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7304715238180213093687499 10957072857270319640531249)
                  ·
                    refine ⟨8217804642952739730398437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10957072857270319640531249 8217804642952739730398437)
                    ·
                      refine ⟨1540838370553638699449707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8217804642952739730398437 1540838370553638699449707)
                      ·
                        rfl

theorem cell23_3000772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_3000772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000772 prefixEnd_3000772 := by exact prefixLift 3000772
  have htrace : WordTrace (prefixWord ++ tailWord_3000772) baseStart_3000772 baseEnd_3000772 := by
    simpa [prefixWord, tailWord_3000772, baseEnd_3000772] using wordTrace_append hprefix tailTrace_3000772
  have hstable : (prefixWord ++ tailWord_3000772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000772).length < 2 ^ (prefixWord ++ tailWord_3000772).sum := by decide
  have hdescent : baseEnd_3000772 < baseStart_3000772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000775 : List Nat := [1, 1, 4, 1, 1, 5, 2, 1, 1, 3, 3]
def baseStart_3000775 : Nat := 118140960795 + 3000775 * 2 ^ 59
def prefixEnd_3000775 : Nat := 4983230072969 + 3 ^ 40 * 3000775 * 2
def baseEnd_3000775 : Nat := 1540839910995602187712193

theorem tailTrace_3000775 : CollatzResearch.WordTrace tailWord_3000775 prefixEnd_3000775 1540839910995602187712193 := by
  unfold tailWord_3000775
  simp only [CollatzResearch.WordTrace]
  refine ⟨109447255703712141413571779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72964837135808094275714519 109447255703712141413571779)
  ·
    refine ⟨164170883555568212120357669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109447255703712141413571779 164170883555568212120357669)
    ·
      refine ⟨30782040666669039772567063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164170883555568212120357669 30782040666669039772567063)
      ·
        refine ⟨46173061000003559658850595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30782040666669039772567063 46173061000003559658850595)
        ·
          refine ⟨69259591500005339488275893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46173061000003559658850595 69259591500005339488275893)
          ·
            refine ⟨6493086703125500577025865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69259591500005339488275893 6493086703125500577025865)
            ·
              refine ⟨4869815027344125432769399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6493086703125500577025865 4869815027344125432769399)
              ·
                refine ⟨7304722541016188149154099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4869815027344125432769399 7304722541016188149154099)
                ·
                  refine ⟨10957083811524282223731149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7304722541016188149154099 10957083811524282223731149)
                  ·
                    refine ⟨4108906429321605833899181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10957083811524282223731149 4108906429321605833899181)
                    ·
                      refine ⟨1540839910995602187712193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4108906429321605833899181 1540839910995602187712193)
                      ·
                        rfl

theorem cell23_3000775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_3000775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000775 prefixEnd_3000775 := by exact prefixLift 3000775
  have htrace : WordTrace (prefixWord ++ tailWord_3000775) baseStart_3000775 baseEnd_3000775 := by
    simpa [prefixWord, tailWord_3000775, baseEnd_3000775] using wordTrace_append hprefix tailTrace_3000775
  have hstable : (prefixWord ++ tailWord_3000775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000775).length < 2 ^ (prefixWord ++ tailWord_3000775).sum := by decide
  have hdescent : baseEnd_3000775 < baseStart_3000775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000808 : List Nat := [2, 1, 4, 1, 1, 3, 1, 2, 2, 6]
def baseStart_3000808 : Nat := 118140960795 + 3000808 * 2 ^ 59
def prefixEnd_3000808 : Nat := 4983230072969 + 3 ^ 40 * 3000808 * 2
def baseEnd_3000808 : Nat := 513618951952400186199847

theorem tailTrace_3000808 : CollatzResearch.WordTrace tailWord_3000808 prefixEnd_3000808 513618951952400186199847 := by
  unfold tailWord_3000808
  simp only [CollatzResearch.WordTrace]
  refine ⟨54724229656296294024761539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72965639541728392033015385 54724229656296294024761539)
  ·
    refine ⟨82086344484444441037142309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54724229656296294024761539 82086344484444441037142309)
    ·
      refine ⟨15391189590833332694464183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82086344484444441037142309 15391189590833332694464183)
      ·
        refine ⟨23086784386249999041696275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15391189590833332694464183 23086784386249999041696275)
        ·
          refine ⟨34630176579374998562544413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23086784386249999041696275 34630176579374998562544413)
          ·
            refine ⟨12986316217265624460954155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34630176579374998562544413 12986316217265624460954155)
            ·
              refine ⟨19479474325898436691431233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12986316217265624460954155 19479474325898436691431233)
              ·
                refine ⟨14609605744423827518573425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19479474325898436691431233 14609605744423827518573425)
                ·
                  refine ⟨10957204308317870638930069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14609605744423827518573425 10957204308317870638930069)
                  ·
                    refine ⟨513618951952400186199847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10957204308317870638930069 513618951952400186199847)
                    ·
                      rfl

theorem cell23_3000808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_3000808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000808 prefixEnd_3000808 := by exact prefixLift 3000808
  have htrace : WordTrace (prefixWord ++ tailWord_3000808) baseStart_3000808 baseEnd_3000808 := by
    simpa [prefixWord, tailWord_3000808, baseEnd_3000808] using wordTrace_append hprefix tailTrace_3000808
  have hstable : (prefixWord ++ tailWord_3000808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000808).length < 2 ^ (prefixWord ++ tailWord_3000808).sum := by decide
  have hdescent : baseEnd_3000808 < baseStart_3000808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000852 : List Nat := [2, 4, 3, 1, 1, 2, 1, 1, 2, 1, 5]
def baseStart_3000852 : Nat := 118140960795 + 3000852 * 2 ^ 59
def prefixEnd_3000852 : Nat := 4983230072969 + 3 ^ 40 * 3000852 * 2
def baseEnd_3000852 : Nat := 1540879449005998386449339

theorem tailTrace_3000852 : CollatzResearch.WordTrace tailWord_3000852 prefixEnd_3000852 1540879449005998386449339 := by
  unfold tailWord_3000852
  simp only [CollatzResearch.WordTrace]
  refine ⟨54725032062216591782062405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72966709416288789042749873 54725032062216591782062405)
  ·
    refine ⟨10260943511665610959136701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54725032062216591782062405 10260943511665610959136701)
    ·
      refine ⟨3847853816874604109676263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10260943511665610959136701 3847853816874604109676263)
      ·
        refine ⟨5771780725311906164514395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3847853816874604109676263 5771780725311906164514395)
        ·
          refine ⟨8657671087967859246771593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5771780725311906164514395 8657671087967859246771593)
          ·
            refine ⟨6493253315975894435078695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8657671087967859246771593 6493253315975894435078695)
            ·
              refine ⟨9739879973963841652618043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6493253315975894435078695 9739879973963841652618043)
              ·
                refine ⟨14609819960945762478927065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9739879973963841652618043 14609819960945762478927065)
                ·
                  refine ⟨10957364970709321859195299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14609819960945762478927065 10957364970709321859195299)
                  ·
                    refine ⟨16436047456063982788792949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10957364970709321859195299 16436047456063982788792949)
                    ·
                      refine ⟨1540879449005998386449339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16436047456063982788792949 1540879449005998386449339)
                      ·
                        rfl

theorem cell23_3000852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_3000852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000852 prefixEnd_3000852 := by exact prefixLift 3000852
  have htrace : WordTrace (prefixWord ++ tailWord_3000852) baseStart_3000852 baseEnd_3000852 := by
    simpa [prefixWord, tailWord_3000852, baseEnd_3000852] using wordTrace_append hprefix tailTrace_3000852
  have hstable : (prefixWord ++ tailWord_3000852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000852).length < 2 ^ (prefixWord ++ tailWord_3000852).sum := by decide
  have hdescent : baseEnd_3000852 < baseStart_3000852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000872 : List Nat := [2, 1, 5, 2, 1, 3, 1, 1, 7]
def baseStart_3000872 : Nat := 118140960795 + 3000872 * 2 ^ 59
def prefixEnd_3000872 : Nat := 4983230072969 + 3 ^ 40 * 3000872 * 2
def baseEnd_3000872 : Nat := 171209968735454256466583

theorem tailTrace_3000872 : CollatzResearch.WordTrace tailWord_3000872 prefixEnd_3000872 171209968735454256466583 := by
  unfold tailWord_3000872
  simp only [CollatzResearch.WordTrace]
  refine ⟨54725396792180363489926435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72967195722907151319901913 54725396792180363489926435)
  ·
    refine ⟨82088095188270545234889653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54725396792180363489926435 82088095188270545234889653)
    ·
      refine ⟨7695758923900363615770905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82088095188270545234889653 7695758923900363615770905)
      ·
        refine ⟨5771819192925272711828179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7695758923900363615770905 5771819192925272711828179)
        ·
          refine ⟨8657728789387909067742269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5771819192925272711828179 8657728789387909067742269)
          ·
            refine ⟨3246648296020465900403351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8657728789387909067742269 3246648296020465900403351)
            ·
              refine ⟨4869972444030698850605027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3246648296020465900403351 4869972444030698850605027)
              ·
                refine ⟨7304958666046048275907541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4869972444030698850605027 7304958666046048275907541)
                ·
                  refine ⟨171209968735454256466583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7304958666046048275907541 171209968735454256466583)
                  ·
                    rfl

theorem cell23_3000872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 7].length) (baseStart_3000872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000872 prefixEnd_3000872 := by exact prefixLift 3000872
  have htrace : WordTrace (prefixWord ++ tailWord_3000872) baseStart_3000872 baseEnd_3000872 := by
    simpa [prefixWord, tailWord_3000872, baseEnd_3000872] using wordTrace_append hprefix tailTrace_3000872
  have hstable : (prefixWord ++ tailWord_3000872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000872).length < 2 ^ (prefixWord ++ tailWord_3000872).sum := by decide
  have hdescent : baseEnd_3000872 < baseStart_3000872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000877 : List Nat := [1, 5, 4, 1, 2, 1, 2, 1, 2, 1, 3]
def baseStart_3000877 : Nat := 118140960795 + 3000877 * 2 ^ 59
def prefixEnd_3000877 : Nat := 4983230072969 + 3 ^ 40 * 3000877 * 2
def baseEnd_3000877 : Nat := 1540892286022360788636725

theorem tailTrace_3000877 : CollatzResearch.WordTrace tailWord_3000877 prefixEnd_3000877 1540892286022360788636725 := by
  unfold tailWord_3000877
  simp only [CollatzResearch.WordTrace]
  refine ⟨109450975949342612833784885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72967317299561741889189923 109450975949342612833784885)
  ·
    refine ⟨10261028995250869953167333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109450975949342612833784885 10261028995250869953167333)
    ·
      refine ⟨1923942936609538116218875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10261028995250869953167333 1923942936609538116218875)
      ·
        refine ⟨2885914404914307174328313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1923942936609538116218875 2885914404914307174328313)
        ·
          refine ⟨2164435803685730380746235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2885914404914307174328313 2164435803685730380746235)
          ·
            refine ⟨3246653705528595571119353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2164435803685730380746235 3246653705528595571119353)
            ·
              refine ⟨2434990279146446678339515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3246653705528595571119353 2434990279146446678339515)
              ·
                refine ⟨3652485418719670017509273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2434990279146446678339515 3652485418719670017509273)
                ·
                  refine ⟨2739364064039752513131955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3652485418719670017509273 2739364064039752513131955)
                  ·
                    refine ⟨4109046096059628769697933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2739364064039752513131955 4109046096059628769697933)
                    ·
                      refine ⟨1540892286022360788636725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4109046096059628769697933 1540892286022360788636725)
                      ·
                        rfl

theorem cell23_3000877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_3000877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000877 prefixEnd_3000877 := by exact prefixLift 3000877
  have htrace : WordTrace (prefixWord ++ tailWord_3000877) baseStart_3000877 baseEnd_3000877 := by
    simpa [prefixWord, tailWord_3000877, baseEnd_3000877] using wordTrace_append hprefix tailTrace_3000877
  have hstable : (prefixWord ++ tailWord_3000877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000877).length < 2 ^ (prefixWord ++ tailWord_3000877).sum := by decide
  have hdescent : baseEnd_3000877 < baseStart_3000877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000905 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 6, 4, 2]
def baseStart_3000905 : Nat := 118140960795 + 3000905 * 2 ^ 59
def prefixEnd_3000905 : Nat := 4983230072969 + 3 ^ 40 * 3000905 * 2
def baseEnd_3000905 : Nat := 1540906663480686679086595

theorem tailTrace_3000905 : CollatzResearch.WordTrace tailWord_3000905 prefixEnd_3000905 1540906663480686679086595 := by
  unfold tailWord_3000905
  simp only [CollatzResearch.WordTrace]
  refine ⟨109451997193241173615804169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72967998128827449077202779 109451997193241173615804169)
  ·
    refine ⟨82088997894930880211853127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109451997193241173615804169 82088997894930880211853127)
    ·
      refine ⟨123133496842396320317779691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82088997894930880211853127 123133496842396320317779691)
      ·
        refine ⟨184700245263594480476669537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123133496842396320317779691 184700245263594480476669537)
        ·
          refine ⟨138525183947695860357502153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184700245263594480476669537 138525183947695860357502153)
          ·
            refine ⟨103893887960771895268126615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138525183947695860357502153 103893887960771895268126615)
            ·
              refine ⟨155840831941157842902189923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103893887960771895268126615 155840831941157842902189923)
              ·
                refine ⟨233761247911736764353284885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155840831941157842902189923 233761247911736764353284885)
                ·
                  refine ⟨10957558495862660829060229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 233761247911736764353284885 10957558495862660829060229)
                  ·
                    refine ⟨2054542217974248905448793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10957558495862660829060229 2054542217974248905448793)
                    ·
                      refine ⟨1540906663480686679086595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2054542217974248905448793 1540906663480686679086595)
                      ·
                        rfl

theorem cell23_3000905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 4, 2].length) (baseStart_3000905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000905 prefixEnd_3000905 := by exact prefixLift 3000905
  have htrace : WordTrace (prefixWord ++ tailWord_3000905) baseStart_3000905 baseEnd_3000905 := by
    simpa [prefixWord, tailWord_3000905, baseEnd_3000905] using wordTrace_append hprefix tailTrace_3000905
  have hstable : (prefixWord ++ tailWord_3000905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000905).length < 2 ^ (prefixWord ++ tailWord_3000905).sum := by decide
  have hdescent : baseEnd_3000905 < baseStart_3000905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000928 : List Nat := [2, 1, 1, 3, 2, 1, 2, 3, 8]
def baseStart_3000928 : Nat := 118140960795 + 3000928 * 2 ^ 59
def prefixEnd_3000928 : Nat := 4983230072969 + 3 ^ 40 * 3000928 * 2
def baseEnd_3000928 : Nat := 171213163726193343233221

theorem tailTrace_3000928 : CollatzResearch.WordTrace tailWord_3000928 prefixEnd_3000928 171213163726193343233221 := by
  unfold tailWord_3000928
  simp only [CollatzResearch.WordTrace]
  refine ⟨54726418036078924271945719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72968557381438565695927625 54726418036078924271945719)
  ·
    refine ⟨82089627054118386407918579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54726418036078924271945719 82089627054118386407918579)
    ·
      refine ⟨123134440581177579611877869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82089627054118386407918579 123134440581177579611877869)
      ·
        refine ⟨46175415217941592354454201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123134440581177579611877869 46175415217941592354454201)
        ·
          refine ⟨34631561413456194265840651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46175415217941592354454201 34631561413456194265840651)
          ·
            refine ⟨51947342120184291398760977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34631561413456194265840651 51947342120184291398760977)
            ·
              refine ⟨38960506590138218549070733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51947342120184291398760977 38960506590138218549070733)
              ·
                refine ⟨14610189971301831955901525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38960506590138218549070733 14610189971301831955901525)
                ·
                  refine ⟨171213163726193343233221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14610189971301831955901525 171213163726193343233221)
                  ·
                    rfl

theorem cell23_3000928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 8].length) (baseStart_3000928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000928 prefixEnd_3000928 := by exact prefixLift 3000928
  have htrace : WordTrace (prefixWord ++ tailWord_3000928) baseStart_3000928 baseEnd_3000928 := by
    simpa [prefixWord, tailWord_3000928, baseEnd_3000928] using wordTrace_append hprefix tailTrace_3000928
  have hstable : (prefixWord ++ tailWord_3000928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000928).length < 2 ^ (prefixWord ++ tailWord_3000928).sum := by decide
  have hdescent : baseEnd_3000928 < baseStart_3000928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000949 : List Nat := [1, 3, 4, 2, 2, 1, 1, 2, 3, 4]
def baseStart_3000949 : Nat := 118140960795 + 3000949 * 2 ^ 59
def prefixEnd_3000949 : Nat := 4983230072969 + 3 ^ 40 * 3000949 * 2
def baseEnd_3000949 : Nat := 513643085543161502312131

theorem tailTrace_3000949 : CollatzResearch.WordTrace tailWord_3000949 prefixEnd_3000949 513643085543161502312131 := by
  unfold tailWord_3000949
  simp only [CollatzResearch.WordTrace]
  refine ⟨109453602005081769130405901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72969068003387846086937267 109453602005081769130405901)
  ·
    refine ⟨41045100751905663423902213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109453602005081769130405901 41045100751905663423902213)
    ·
      refine ⟨7695956390982311891981665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41045100751905663423902213 7695956390982311891981665)
      ·
        refine ⟨5771967293236733918986249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7695956390982311891981665 5771967293236733918986249)
        ·
          refine ⟨4328975469927550439239687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5771967293236733918986249 4328975469927550439239687)
          ·
            refine ⟨6493463204891325658859531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4328975469927550439239687 6493463204891325658859531)
            ·
              refine ⟨9740194807336988488289297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6493463204891325658859531 9740194807336988488289297)
              ·
                refine ⟨7305146105502741366216973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9740194807336988488289297 7305146105502741366216973)
                ·
                  refine ⟨2739429789563528012331365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7305146105502741366216973 2739429789563528012331365)
                  ·
                    refine ⟨513643085543161502312131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2739429789563528012331365 513643085543161502312131)
                    ·
                      rfl

theorem cell23_3000949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_3000949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000949 prefixEnd_3000949 := by exact prefixLift 3000949
  have htrace : WordTrace (prefixWord ++ tailWord_3000949) baseStart_3000949 baseEnd_3000949 := by
    simpa [prefixWord, tailWord_3000949, baseEnd_3000949] using wordTrace_append hprefix tailTrace_3000949
  have hstable : (prefixWord ++ tailWord_3000949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000949).length < 2 ^ (prefixWord ++ tailWord_3000949).sum := by decide
  have hdescent : baseEnd_3000949 < baseStart_3000949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000975 : List Nat := [1, 1, 2, 1, 1, 1, 1, 9, 1, 5]
def baseStart_3000975 : Nat := 118140960795 + 3000975 * 2 ^ 59
def prefixEnd_3000975 : Nat := 4983230072969 + 3 ^ 40 * 3000975 * 2
def baseEnd_3000975 : Nat := 513647535708833801737091

theorem tailTrace_3000975 : CollatzResearch.WordTrace tailWord_3000975 prefixEnd_3000975 513647535708833801737091 := by
  unfold tailWord_3000975
  simp only [CollatzResearch.WordTrace]
  refine ⟨109454550302987575570852379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72969700201991717047234919 109454550302987575570852379)
  ·
    refine ⟨164181825454481363356278569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109454550302987575570852379 164181825454481363356278569)
    ·
      refine ⟨123136369090861022517208927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164181825454481363356278569 123136369090861022517208927)
      ·
        refine ⟨184704553636291533775813391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123136369090861022517208927 184704553636291533775813391)
        ·
          refine ⟨277056830454437300663720087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184704553636291533775813391 277056830454437300663720087)
          ·
            refine ⟨415585245681655950995580131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277056830454437300663720087 415585245681655950995580131)
            ·
              refine ⟨623377868522483926493370197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415585245681655950995580131 623377868522483926493370197)
              ·
                refine ⟨3652604698373929256797091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 623377868522483926493370197 3652604698373929256797091)
                ·
                  refine ⟨5478907047560893885195637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3652604698373929256797091 5478907047560893885195637)
                  ·
                    refine ⟨513647535708833801737091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5478907047560893885195637 513647535708833801737091)
                    ·
                      rfl

theorem cell23_3000975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 5].length) (baseStart_3000975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000975 prefixEnd_3000975 := by exact prefixLift 3000975
  have htrace : WordTrace (prefixWord ++ tailWord_3000975) baseStart_3000975 baseEnd_3000975 := by
    simpa [prefixWord, tailWord_3000975, baseEnd_3000975] using wordTrace_append hprefix tailTrace_3000975
  have hstable : (prefixWord ++ tailWord_3000975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000975).length < 2 ^ (prefixWord ++ tailWord_3000975).sum := by decide
  have hdescent : baseEnd_3000975 < baseStart_3000975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000995 : List Nat := [1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 4]
def baseStart_3000995 : Nat := 118140960795 + 3000995 * 2 ^ 59
def prefixEnd_3000995 : Nat := 4983230072969 + 3 ^ 40 * 3000995 * 2
def baseEnd_3000995 : Nat := 1540952876739591326961181

theorem tailTrace_3000995 : CollatzResearch.WordTrace tailWord_3000995 prefixEnd_3000995 1540952876739591326961181 := by
  unfold tailWord_3000995
  simp only [CollatzResearch.WordTrace]
  refine ⟨109455279762915118986580439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72970186508610079324386959 109455279762915118986580439)
  ·
    refine ⟨164182919644372678479870659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109455279762915118986580439 164182919644372678479870659)
    ·
      refine ⟨246274379466559017719805989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164182919644372678479870659 246274379466559017719805989)
      ·
        refine ⟨46176446149979815822463623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 246274379466559017719805989 46176446149979815822463623)
        ·
          refine ⟨69264669224969723733695435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46176446149979815822463623 69264669224969723733695435)
          ·
            refine ⟨103897003837454585600543153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69264669224969723733695435 103897003837454585600543153)
            ·
              refine ⟨77922752878090939200407365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103897003837454585600543153 77922752878090939200407365)
              ·
                refine ⟨14610516164642051100076381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77922752878090939200407365 14610516164642051100076381)
                ·
                  refine ⟨5478943561740769162528643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14610516164642051100076381 5478943561740769162528643)
                  ·
                    refine ⟨8218415342611153743792965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5478943561740769162528643 8218415342611153743792965)
                    ·
                      refine ⟨1540952876739591326961181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8218415342611153743792965 1540952876739591326961181)
                      ·
                        rfl

theorem cell23_3000995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_3000995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3000995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3000995 prefixEnd_3000995 := by exact prefixLift 3000995
  have htrace : WordTrace (prefixWord ++ tailWord_3000995) baseStart_3000995 baseEnd_3000995 := by
    simpa [prefixWord, tailWord_3000995, baseEnd_3000995] using wordTrace_append hprefix tailTrace_3000995
  have hstable : (prefixWord ++ tailWord_3000995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000995).length < 2 ^ (prefixWord ++ tailWord_3000995).sum := by decide
  have hdescent : baseEnd_3000995 < baseStart_3000995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001006 : List Nat := [4, 1, 4, 1, 1, 1, 2, 2, 3, 1, 3]
def baseStart_3001006 : Nat := 118140960795 + 3001006 * 2 ^ 59
def prefixEnd_3001006 : Nat := 4983230072969 + 3 ^ 40 * 3001006 * 2
def baseEnd_3001006 : Nat := 1540958525026790783923631

theorem tailTrace_3001006 : CollatzResearch.WordTrace tailWord_3001006 prefixEnd_3001006 1540958525026790783923631 := by
  unfold tailWord_3001006
  simp only [CollatzResearch.WordTrace]
  refine ⟨13681960120734408483153859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72970453977250178576820581 13681960120734408483153859)
  ·
    refine ⟨20522940181101612724730789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13681960120734408483153859 20522940181101612724730789)
    ·
      refine ⟨3848051283956552385887023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20522940181101612724730789 3848051283956552385887023)
      ·
        refine ⟨5772076925934828578830535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3848051283956552385887023 5772076925934828578830535)
        ·
          refine ⟨8658115388902242868245803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5772076925934828578830535 8658115388902242868245803)
          ·
            refine ⟨12987173083353364302368705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8658115388902242868245803 12987173083353364302368705)
            ·
              refine ⟨9740379812515023226776529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12987173083353364302368705 9740379812515023226776529)
              ·
                refine ⟨7305284859386267420082397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9740379812515023226776529 7305284859386267420082397)
                ·
                  refine ⟨2739481822269850282530899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7305284859386267420082397 2739481822269850282530899)
                  ·
                    refine ⟨4109222733404775423796349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2739481822269850282530899 4109222733404775423796349)
                    ·
                      refine ⟨1540958525026790783923631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4109222733404775423796349 1540958525026790783923631)
                      ·
                        rfl

theorem cell23_3001006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_3001006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001006 prefixEnd_3001006 := by exact prefixLift 3001006
  have htrace : WordTrace (prefixWord ++ tailWord_3001006) baseStart_3001006 baseEnd_3001006 := by
    simpa [prefixWord, tailWord_3001006, baseEnd_3001006] using wordTrace_append hprefix tailTrace_3001006
  have hstable : (prefixWord ++ tailWord_3001006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001006).length < 2 ^ (prefixWord ++ tailWord_3001006).sum := by decide
  have hdescent : baseEnd_3001006 < baseStart_3001006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001022 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 6, 4]
def baseStart_3001022 : Nat := 118140960795 + 3001022 * 2 ^ 59
def prefixEnd_3001022 : Nat := 4983230072969 + 3 ^ 40 * 3001022 * 2
def baseEnd_3001022 : Nat := 513655580239087573774519

theorem tailTrace_3001022 : CollatzResearch.WordTrace tailWord_3001022 prefixEnd_3001022 513655580239087573774519 := by
  unfold tailWord_3001022
  simp only [CollatzResearch.WordTrace]
  refine ⟨13682033066727162824726665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72970843022544868398542213 13682033066727162824726665)
  ·
    refine ⟨10261524800045372118544999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13682033066727162824726665 10261524800045372118544999)
    ·
      refine ⟨15392287200068058177817499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10261524800045372118544999 15392287200068058177817499)
      ·
        refine ⟨23088430800102087266726249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15392287200068058177817499 23088430800102087266726249)
        ·
          refine ⟨17316323100076565450044687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23088430800102087266726249 17316323100076565450044687)
          ·
            refine ⟨25974484650114848175067031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17316323100076565450044687 25974484650114848175067031)
            ·
              refine ⟨38961726975172272262600547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25974484650114848175067031 38961726975172272262600547)
              ·
                refine ⟨58442590462758408393900821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38961726975172272262600547 58442590462758408393900821)
                ·
                  refine ⟨2739496427941800393464101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58442590462758408393900821 2739496427941800393464101)
                  ·
                    refine ⟨513655580239087573774519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2739496427941800393464101 513655580239087573774519)
                    ·
                      rfl

theorem cell23_3001022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_3001022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001022 prefixEnd_3001022 := by exact prefixLift 3001022
  have htrace : WordTrace (prefixWord ++ tailWord_3001022) baseStart_3001022 baseEnd_3001022 := by
    simpa [prefixWord, tailWord_3001022, baseEnd_3001022] using wordTrace_append hprefix tailTrace_3001022
  have hstable : (prefixWord ++ tailWord_3001022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001022).length < 2 ^ (prefixWord ++ tailWord_3001022).sum := by decide
  have hdescent : baseEnd_3001022 < baseStart_3001022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001032 : List Nat := [2, 1, 3, 1, 2, 4, 2, 1, 1, 1, 5]
def baseStart_3001032 : Nat := 118140960795 + 3001032 * 2 ^ 59
def prefixEnd_3001032 : Nat := 4983230072969 + 3 ^ 40 * 3001032 * 2
def baseEnd_3001032 : Nat := 1540971875523807682198511

theorem tailTrace_3001032 : CollatzResearch.WordTrace tailWord_3001032 prefixEnd_3001032 1540971875523807682198511 := by
  unfold tailWord_3001032
  simp only [CollatzResearch.WordTrace]
  refine ⟨54728314631890537152838675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72971086175854049537118233 54728314631890537152838675)
  ·
    refine ⟨82092471947835805729258013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54728314631890537152838675 82092471947835805729258013)
    ·
      refine ⟨30784676980438427148471755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82092471947835805729258013 30784676980438427148471755)
      ·
        refine ⟨46177015470657640722707633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30784676980438427148471755 46177015470657640722707633)
        ·
          refine ⟨34632761602993230542030725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46177015470657640722707633 34632761602993230542030725)
          ·
            refine ⟨6493642800561230726630761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34632761602993230542030725 6493642800561230726630761)
            ·
              refine ⟨4870232100420923044973071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6493642800561230726630761 4870232100420923044973071)
              ·
                refine ⟨7305348150631384567459607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4870232100420923044973071 7305348150631384567459607)
                ·
                  refine ⟨10958022225947076851189411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7305348150631384567459607 10958022225947076851189411)
                  ·
                    refine ⟨16437033338920615276784117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10958022225947076851189411 16437033338920615276784117)
                    ·
                      refine ⟨1540971875523807682198511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16437033338920615276784117 1540971875523807682198511)
                      ·
                        rfl

theorem cell23_3001032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_3001032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001032 prefixEnd_3001032 := by exact prefixLift 3001032
  have htrace : WordTrace (prefixWord ++ tailWord_3001032) baseStart_3001032 baseEnd_3001032 := by
    simpa [prefixWord, tailWord_3001032, baseEnd_3001032] using wordTrace_append hprefix tailTrace_3001032
  have hstable : (prefixWord ++ tailWord_3001032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001032).length < 2 ^ (prefixWord ++ tailWord_3001032).sum := by decide
  have hdescent : baseEnd_3001032 < baseStart_3001032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001052 : List Nat := [2, 2, 5, 1, 1, 1, 1, 10]
def baseStart_3001052 : Nat := 118140960795 + 3001052 * 2 ^ 59
def prefixEnd_3001052 : Nat := 4983230072969 + 3 ^ 40 * 3001052 * 2
def baseEnd_3001052 : Nat := 57073412782848059405497

theorem tailTrace_3001052 : CollatzResearch.WordTrace tailWord_3001052 prefixEnd_3001052 57073412782848059405497 := by
  unfold tailWord_3001052
  simp only [CollatzResearch.WordTrace]
  refine ⟨54728679361854308860702705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72971572482472411814270273 54728679361854308860702705)
  ·
    refine ⟨41046509521390731645527029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54728679361854308860702705 41046509521390731645527029)
    ·
      refine ⟨3848110267630381091768159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41046509521390731645527029 3848110267630381091768159)
      ·
        refine ⟨5772165401445571637652239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3848110267630381091768159 5772165401445571637652239)
        ·
          refine ⟨8658248102168357456478359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5772165401445571637652239 8658248102168357456478359)
          ·
            refine ⟨12987372153252536184717539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8658248102168357456478359 12987372153252536184717539)
            ·
              refine ⟨19481058229878804277076309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12987372153252536184717539 19481058229878804277076309)
              ·
                refine ⟨57073412782848059405497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 19481058229878804277076309 57073412782848059405497)
                ·
                  rfl

theorem cell23_3001052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 10].length) (baseStart_3001052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001052 prefixEnd_3001052 := by exact prefixLift 3001052
  have htrace : WordTrace (prefixWord ++ tailWord_3001052) baseStart_3001052 baseEnd_3001052 := by
    simpa [prefixWord, tailWord_3001052, baseEnd_3001052] using wordTrace_append hprefix tailTrace_3001052
  have hstable : (prefixWord ++ tailWord_3001052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001052).length < 2 ^ (prefixWord ++ tailWord_3001052).sum := by decide
  have hdescent : baseEnd_3001052 < baseStart_3001052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001096 : List Nat := [2, 1, 3, 2, 2, 3, 2, 2, 2, 1, 3]
def baseStart_3001096 : Nat := 118140960795 + 3001096 * 2 ^ 59
def prefixEnd_3001096 : Nat := 4983230072969 + 3 ^ 40 * 3001096 * 2
def baseEnd_3001096 : Nat := 1541004738285695431798217

theorem tailTrace_3001096 : CollatzResearch.WordTrace tailWord_3001096 prefixEnd_3001096 1541004738285695431798217 := by
  unfold tailWord_3001096
  simp only [CollatzResearch.WordTrace]
  refine ⟨54729481767774606618003571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72972642357032808824004761 54729481767774606618003571)
  ·
    refine ⟨82094222651661909927005357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54729481767774606618003571 82094222651661909927005357)
    ·
      refine ⟨30785333494373216222627009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82094222651661909927005357 30785333494373216222627009)
      ·
        refine ⟨23089000120779912166970257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30785333494373216222627009 23089000120779912166970257)
        ·
          refine ⟨17316750090584934125227693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23089000120779912166970257 17316750090584934125227693)
          ·
            refine ⟨6493781283969350296960385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17316750090584934125227693 6493781283969350296960385)
            ·
              refine ⟨4870335962977012722720289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6493781283969350296960385 4870335962977012722720289)
              ·
                refine ⟨3652751972232759542040217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4870335962977012722720289 3652751972232759542040217)
                ·
                  refine ⟨2739563979174569656530163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3652751972232759542040217 2739563979174569656530163)
                  ·
                    refine ⟨4109345968761854484795245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2739563979174569656530163 4109345968761854484795245)
                    ·
                      refine ⟨1541004738285695431798217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4109345968761854484795245 1541004738285695431798217)
                      ·
                        rfl

theorem cell23_3001096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_3001096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001096 prefixEnd_3001096 := by exact prefixLift 3001096
  have htrace : WordTrace (prefixWord ++ tailWord_3001096) baseStart_3001096 baseEnd_3001096 := by
    simpa [prefixWord, tailWord_3001096, baseEnd_3001096] using wordTrace_append hprefix tailTrace_3001096
  have hstable : (prefixWord ++ tailWord_3001096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001096).length < 2 ^ (prefixWord ++ tailWord_3001096).sum := by decide
  have hdescent : baseEnd_3001096 < baseStart_3001096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001105 : List Nat := [1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 5]
def baseStart_3001105 : Nat := 118140960795 + 3001105 * 2 ^ 59
def prefixEnd_3001105 : Nat := 4983230072969 + 3 ^ 40 * 3001105 * 2
def baseEnd_3001105 : Nat := 1541009359611585896585675

theorem tailTrace_3001105 : CollatzResearch.WordTrace tailWord_3001105 prefixEnd_3001105 1541009359611585896585675 := by
  unfold tailWord_3001105
  simp only [CollatzResearch.WordTrace]
  refine ⟨109459291792516607773084769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72972861195011071848723179 109459291792516607773084769)
  ·
    refine ⟨82094468844387455829813577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109459291792516607773084769 82094468844387455829813577)
    ·
      refine ⟨61570851633290591872360183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82094468844387455829813577 61570851633290591872360183)
      ·
        refine ⟨92356277449935887808540275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61570851633290591872360183 92356277449935887808540275)
        ·
          refine ⟨138534416174903831712810413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92356277449935887808540275 138534416174903831712810413)
          ·
            refine ⟨51950406065588936892303905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138534416174903831712810413 51950406065588936892303905)
            ·
              refine ⟨38962804549191702669227929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51950406065588936892303905 38962804549191702669227929)
              ·
                refine ⟨29222103411893777001920947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38962804549191702669227929 29222103411893777001920947)
                ·
                  refine ⟨43833155117840665502881421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29222103411893777001920947 43833155117840665502881421)
                  ·
                    refine ⟨16437433169190249563580533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43833155117840665502881421 16437433169190249563580533)
                    ·
                      refine ⟨1541009359611585896585675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16437433169190249563580533 1541009359611585896585675)
                      ·
                        rfl

theorem cell23_3001105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_3001105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001105 prefixEnd_3001105 := by exact prefixLift 3001105
  have htrace : WordTrace (prefixWord ++ tailWord_3001105) baseStart_3001105 baseEnd_3001105 := by
    simpa [prefixWord, tailWord_3001105, baseEnd_3001105] using wordTrace_append hprefix tailTrace_3001105
  have hstable : (prefixWord ++ tailWord_3001105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001105).length < 2 ^ (prefixWord ++ tailWord_3001105).sum := by decide
  have hdescent : baseEnd_3001105 < baseStart_3001105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001119 : List Nat := [1, 1, 2, 4, 2, 2, 1, 3, 1, 4, 2]
def baseStart_3001119 : Nat := 118140960795 + 3001119 * 2 ^ 59
def prefixEnd_3001119 : Nat := 4983230072969 + 3 ^ 40 * 3001119 * 2
def baseEnd_3001119 : Nat := 1541016548340748841810611

theorem tailTrace_3001119 : CollatzResearch.WordTrace tailWord_3001119 prefixEnd_3001119 1541016548340748841810611 := by
  unfold tailWord_3001119
  simp only [CollatzResearch.WordTrace]
  refine ⟨109459802414465888164094411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72973201609643925442729607 109459802414465888164094411)
  ·
    refine ⟨164189703621698832246141617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109459802414465888164094411 164189703621698832246141617)
    ·
      refine ⟨123142277716274124184606213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164189703621698832246141617 123142277716274124184606213)
      ·
        refine ⟨23089177071801398284613665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123142277716274124184606213 23089177071801398284613665)
        ·
          refine ⟨17316882803851048713460249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23089177071801398284613665 17316882803851048713460249)
          ·
            refine ⟨12987662102888286535095187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17316882803851048713460249 12987662102888286535095187)
            ·
              refine ⟨19481493154332429802642781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12987662102888286535095187 19481493154332429802642781)
              ·
                refine ⟨7305559932874661175991043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19481493154332429802642781 7305559932874661175991043)
                ·
                  refine ⟨10958339899311991763986565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7305559932874661175991043 10958339899311991763986565)
                  ·
                    refine ⟨2054688731120998455747481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10958339899311991763986565 2054688731120998455747481)
                    ·
                      refine ⟨1541016548340748841810611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2054688731120998455747481 1541016548340748841810611)
                      ·
                        rfl

theorem cell23_3001119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_3001119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001119 prefixEnd_3001119 := by exact prefixLift 3001119
  have htrace : WordTrace (prefixWord ++ tailWord_3001119) baseStart_3001119 baseEnd_3001119 := by
    simpa [prefixWord, tailWord_3001119, baseEnd_3001119] using wordTrace_append hprefix tailTrace_3001119
  have hstable : (prefixWord ++ tailWord_3001119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001119).length < 2 ^ (prefixWord ++ tailWord_3001119).sum := by decide
  have hdescent : baseEnd_3001119 < baseStart_3001119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001206 : List Nat := [5, 1, 1, 3, 1, 2, 1, 2, 2, 5]
def baseStart_3001206 : Nat := 118140960795 + 3001206 * 2 ^ 59
def prefixEnd_3001206 : Nat := 4983230072969 + 3 ^ 40 * 3001206 * 2
def baseEnd_3001206 : Nat := 513687073719230000474237

theorem tailTrace_3001206 : CollatzResearch.WordTrace tailWord_3001206 prefixEnd_3001206 513687073719230000474237 := by
  unfold tailWord_3001206
  simp only [CollatzResearch.WordTrace]
  refine ⟨6841435972821918876406967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72975317043433801348340981 6841435972821918876406967)
  ·
    refine ⟨10262153959232878314610451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6841435972821918876406967 10262153959232878314610451)
    ·
      refine ⟨15393230938849317471915677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10262153959232878314610451 15393230938849317471915677)
      ·
        refine ⟨5772461602068494051968379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15393230938849317471915677 5772461602068494051968379)
        ·
          refine ⟨8658692403102741077952569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5772461602068494051968379 8658692403102741077952569)
          ·
            refine ⟨6494019302327055808464427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8658692403102741077952569 6494019302327055808464427)
            ·
              refine ⟨9741028953490583712696641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6494019302327055808464427 9741028953490583712696641)
              ·
                refine ⟨7305771715117937784522481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9741028953490583712696641 7305771715117937784522481)
                ·
                  refine ⟨5479328786338453338391861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7305771715117937784522481 5479328786338453338391861)
                  ·
                    refine ⟨513687073719230000474237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5479328786338453338391861 513687073719230000474237)
                    ·
                      rfl

theorem cell23_3001206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_3001206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001206 prefixEnd_3001206 := by exact prefixLift 3001206
  have htrace : WordTrace (prefixWord ++ tailWord_3001206) baseStart_3001206 baseEnd_3001206 := by
    simpa [prefixWord, tailWord_3001206, baseEnd_3001206] using wordTrace_append hprefix tailTrace_3001206
  have hstable : (prefixWord ++ tailWord_3001206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001206).length < 2 ^ (prefixWord ++ tailWord_3001206).sum := by decide
  have hdescent : baseEnd_3001206 < baseStart_3001206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001209 : List Nat := [1, 2, 1, 3, 2, 4, 1, 2, 2, 1, 4]
def baseStart_3001209 : Nat := 118140960795 + 3001209 * 2 ^ 59
def prefixEnd_3001209 : Nat := 4983230072969 + 3 ^ 40 * 3001209 * 2
def baseEnd_3001209 : Nat := 1541062761599653489685197

theorem tailTrace_3001209 : CollatzResearch.WordTrace tailWord_3001209 prefixEnd_3001209 1541062761599653489685197 := by
  unfold tailWord_3001209
  simp only [CollatzResearch.WordTrace]
  refine ⟨109463084984139833534870681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72975389989426555689913787 109463084984139833534870681)
  ·
    refine ⟨82097313738104875151153011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109463084984139833534870681 82097313738104875151153011)
    ·
      refine ⟨123145970607157312726729517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82097313738104875151153011 123145970607157312726729517)
      ·
        refine ⟨46179738977683992272523569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123145970607157312726729517 46179738977683992272523569)
        ·
          refine ⟨34634804233262994204392677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46179738977683992272523569 34634804233262994204392677)
          ·
            refine ⟨6494025793736811413323627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34634804233262994204392677 6494025793736811413323627)
            ·
              refine ⟨9741038690605217119985441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6494025793736811413323627 9741038690605217119985441)
              ·
                refine ⟨7305779017953912839989081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9741038690605217119985441 7305779017953912839989081)
                ·
                  refine ⟨5479334263465434629991811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7305779017953912839989081 5479334263465434629991811)
                  ·
                    refine ⟨8219001395198151944987717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5479334263465434629991811 8219001395198151944987717)
                    ·
                      refine ⟨1541062761599653489685197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8219001395198151944987717 1541062761599653489685197)
                      ·
                        rfl

theorem cell23_3001209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_3001209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001209 prefixEnd_3001209 := by exact prefixLift 3001209
  have htrace : WordTrace (prefixWord ++ tailWord_3001209) baseStart_3001209 baseEnd_3001209 := by
    simpa [prefixWord, tailWord_3001209, baseEnd_3001209] using wordTrace_append hprefix tailTrace_3001209
  have hstable : (prefixWord ++ tailWord_3001209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001209).length < 2 ^ (prefixWord ++ tailWord_3001209).sum := by decide
  have hdescent : baseEnd_3001209 < baseStart_3001209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001259 : List Nat := [1, 1, 1, 1, 2, 1, 1, 6, 5, 1, 3]
def baseStart_3001259 : Nat := 118140960795 + 3001259 * 2 ^ 59
def prefixEnd_3001259 : Nat := 4983230072969 + 3 ^ 40 * 3001259 * 2
def baseEnd_3001259 : Nat := 1541088435632378294059967

theorem tailTrace_3001259 : CollatzResearch.WordTrace tailWord_3001259 prefixEnd_3001259 1541088435632378294059967 := by
  unfold tailWord_3001259
  simp only [CollatzResearch.WordTrace]
  refine ⟨109464908633958692074190831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72976605755972461382793887 109464908633958692074190831)
  ·
    refine ⟨164197362950938038111286247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109464908633958692074190831 164197362950938038111286247)
    ·
      refine ⟨246296044426407057166929371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164197362950938038111286247 246296044426407057166929371)
      ·
        refine ⟨369444066639610585750394057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246296044426407057166929371 369444066639610585750394057)
        ·
          refine ⟨277083049979707939312795543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 369444066639610585750394057 277083049979707939312795543)
          ·
            refine ⟨415624574969561908969193315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277083049979707939312795543 415624574969561908969193315)
            ·
              refine ⟨623436862454342863453789973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415624574969561908969193315 623436862454342863453789973)
              ·
                refine ⟨29223602927547321724396405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 623436862454342863453789973 29223602927547321724396405)
                ·
                  refine ⟨2739712774457561411662163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29223602927547321724396405 2739712774457561411662163)
                  ·
                    refine ⟨4109569161686342117493245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2739712774457561411662163 4109569161686342117493245)
                    ·
                      refine ⟨1541088435632378294059967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4109569161686342117493245 1541088435632378294059967)
                      ·
                        rfl

theorem cell23_3001259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 5, 1, 3].length) (baseStart_3001259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001259 prefixEnd_3001259 := by exact prefixLift 3001259
  have htrace : WordTrace (prefixWord ++ tailWord_3001259) baseStart_3001259 baseEnd_3001259 := by
    simpa [prefixWord, tailWord_3001259, baseEnd_3001259] using wordTrace_append hprefix tailTrace_3001259
  have hstable : (prefixWord ++ tailWord_3001259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001259).length < 2 ^ (prefixWord ++ tailWord_3001259).sum := by decide
  have hdescent : baseEnd_3001259 < baseStart_3001259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001312 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 6]
def baseStart_3001312 : Nat := 118140960795 + 3001312 * 2 ^ 59
def prefixEnd_3001312 : Nat := 4983230072969 + 3 ^ 40 * 3001312 * 2
def baseEnd_3001312 : Nat := 1541115650107066586697223

theorem tailTrace_3001312 : CollatzResearch.WordTrace tailWord_3001312 prefixEnd_3001312 1541115650107066586697223 := by
  unfold tailWord_3001312
  simp only [CollatzResearch.WordTrace]
  refine ⟨54733420851383341062935095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72977894468511121417246793 54733420851383341062935095)
  ·
    refine ⟨82100131277075011594402643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54733420851383341062935095 82100131277075011594402643)
    ·
      refine ⟨123150196915612517391603965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82100131277075011594402643 123150196915612517391603965)
      ·
        refine ⟨46181323843354694021851487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123150196915612517391603965 46181323843354694021851487)
        ·
          refine ⟨69271985765032041032777231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46181323843354694021851487 69271985765032041032777231)
          ·
            refine ⟨103907978647548061549165847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69271985765032041032777231 103907978647548061549165847)
            ·
              refine ⟨155861967971322092323748771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103907978647548061549165847 155861967971322092323748771)
              ·
                refine ⟨233792951956983138485623157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155861967971322092323748771 233792951956983138485623157)
                ·
                  refine ⟨21918089245967169233027171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 233792951956983138485623157 21918089245967169233027171)
                  ·
                    refine ⟨32877133868950753849540757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21918089245967169233027171 32877133868950753849540757)
                    ·
                      refine ⟨1541115650107066586697223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32877133868950753849540757 1541115650107066586697223)
                      ·
                        rfl

theorem cell23_3001312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_3001312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001312 prefixEnd_3001312 := by exact prefixLift 3001312
  have htrace : WordTrace (prefixWord ++ tailWord_3001312) baseStart_3001312 baseEnd_3001312 := by
    simpa [prefixWord, tailWord_3001312, baseEnd_3001312] using wordTrace_append hprefix tailTrace_3001312
  have hstable : (prefixWord ++ tailWord_3001312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001312).length < 2 ^ (prefixWord ++ tailWord_3001312).sum := by decide
  have hdescent : baseEnd_3001312 < baseStart_3001312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001356 : List Nat := [2, 2, 1, 2, 3, 4, 2, 7]
def baseStart_3001356 : Nat := 118140960795 + 3001356 * 2 ^ 59
def prefixEnd_3001356 : Nat := 4983230072969 + 3 ^ 40 * 3001356 * 2
def baseEnd_3001356 : Nat := 57079194194661644983223

theorem tailTrace_3001356 : CollatzResearch.WordTrace tailWord_3001356 prefixEnd_3001356 57079194194661644983223 := by
  unfold tailWord_3001356
  simp only [CollatzResearch.WordTrace]
  refine ⟨54734223257303638820235961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72978964343071518426981281 54734223257303638820235961)
  ·
    refine ⟨41050667442977729115176971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54734223257303638820235961 41050667442977729115176971)
    ·
      refine ⟨61576001164466593672765457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41050667442977729115176971 61576001164466593672765457)
      ·
        refine ⟨46182000873349945254574093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61576001164466593672765457 46182000873349945254574093)
        ·
          refine ⟨17318250327506229470465285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46182000873349945254574093 17318250327506229470465285)
          ·
            refine ⟨3247171936407418025712241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17318250327506229470465285 3247171936407418025712241)
            ·
              refine ⟨2435378952305563519284181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3247171936407418025712241 2435378952305563519284181)
              ·
                refine ⟨57079194194661644983223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2435378952305563519284181 57079194194661644983223)
                ·
                  rfl

theorem cell23_3001356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 7].length) (baseStart_3001356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001356 prefixEnd_3001356 := by exact prefixLift 3001356
  have htrace : WordTrace (prefixWord ++ tailWord_3001356) baseStart_3001356 baseEnd_3001356 := by
    simpa [prefixWord, tailWord_3001356, baseEnd_3001356] using wordTrace_append hprefix tailTrace_3001356
  have hstable : (prefixWord ++ tailWord_3001356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001356).length < 2 ^ (prefixWord ++ tailWord_3001356).sum := by decide
  have hdescent : baseEnd_3001356 < baseStart_3001356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001367 : List Nat := [1, 1, 3, 5, 1, 1, 3, 3, 1, 2, 2]
def baseStart_3001367 : Nat := 118140960795 + 3001367 * 2 ^ 59
def prefixEnd_3001367 : Nat := 4983230072969 + 3 ^ 40 * 3001367 * 2
def baseEnd_3001367 : Nat := 1541143891543063871509471

theorem tailTrace_3001367 : CollatzResearch.WordTrace tailWord_3001367 prefixEnd_3001367 1541143891543063871509471 := by
  unfold tailWord_3001367
  simp only [CollatzResearch.WordTrace]
  refine ⟨109468847717567426519122355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72979231811711617679414903 109468847717567426519122355)
  ·
    refine ⟨164203271576351139778683533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109468847717567426519122355 164203271576351139778683533)
    ·
      refine ⟨61576226841131677417006325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164203271576351139778683533 61576226841131677417006325)
      ·
        refine ⟨5772771266356094757844343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61576226841131677417006325 5772771266356094757844343)
        ·
          refine ⟨8659156899534142136766515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5772771266356094757844343 8659156899534142136766515)
          ·
            refine ⟨12988735349301213205149773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8659156899534142136766515 12988735349301213205149773)
            ·
              refine ⟨4870775755987954951931165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12988735349301213205149773 4870775755987954951931165)
              ·
                refine ⟨1826540908495483106974187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4870775755987954951931165 1826540908495483106974187)
                ·
                  refine ⟨2739811362743224660461281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1826540908495483106974187 2739811362743224660461281)
                  ·
                    refine ⟨2054858522057418495345961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2739811362743224660461281 2054858522057418495345961)
                    ·
                      refine ⟨1541143891543063871509471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2054858522057418495345961 1541143891543063871509471)
                      ·
                        rfl

theorem cell23_3001367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_3001367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001367 prefixEnd_3001367 := by exact prefixLift 3001367
  have htrace : WordTrace (prefixWord ++ tailWord_3001367) baseStart_3001367 baseEnd_3001367 := by
    simpa [prefixWord, tailWord_3001367, baseEnd_3001367] using wordTrace_append hprefix tailTrace_3001367
  have hstable : (prefixWord ++ tailWord_3001367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001367).length < 2 ^ (prefixWord ++ tailWord_3001367).sum := by decide
  have hdescent : baseEnd_3001367 < baseStart_3001367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001400 : List Nat := [2, 1, 2, 1, 5, 1, 4, 1, 2, 1, 3]
def baseStart_3001400 : Nat := 118140960795 + 3001400 * 2 ^ 59
def prefixEnd_3001400 : Nat := 4983230072969 + 3 ^ 40 * 3001400 * 2
def baseEnd_3001400 : Nat := 1541160836404662242396819

theorem tailTrace_3001400 : CollatzResearch.WordTrace tailWord_3001400 prefixEnd_3001400 1541160836404662242396819 := by
  unfold tailWord_3001400
  simp only [CollatzResearch.WordTrace]
  refine ⟨54735025663223936577536827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72980034217631915436715769 54735025663223936577536827)
  ·
    refine ⟨82102538494835904866305241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54735025663223936577536827 82102538494835904866305241)
    ·
      refine ⟨61576903871126928649728931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82102538494835904866305241 61576903871126928649728931)
      ·
        refine ⟨92365355806690392974593397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61576903871126928649728931 92365355806690392974593397)
        ·
          refine ⟨8659252106877224341368131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92365355806690392974593397 8659252106877224341368131)
          ·
            refine ⟨12988878160315836512052197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8659252106877224341368131 12988878160315836512052197)
            ·
              refine ⟨2435414655059219346009787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12988878160315836512052197 2435414655059219346009787)
              ·
                refine ⟨3653121982588829019014681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2435414655059219346009787 3653121982588829019014681)
                ·
                  refine ⟨2739841486941621764261011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3653121982588829019014681 2739841486941621764261011)
                  ·
                    refine ⟨4109762230412432646391517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2739841486941621764261011 4109762230412432646391517)
                    ·
                      refine ⟨1541160836404662242396819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4109762230412432646391517 1541160836404662242396819)
                      ·
                        rfl

theorem cell23_3001400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 2, 1, 3].length) (baseStart_3001400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001400 prefixEnd_3001400 := by exact prefixLift 3001400
  have htrace : WordTrace (prefixWord ++ tailWord_3001400) baseStart_3001400 baseEnd_3001400 := by
    simpa [prefixWord, tailWord_3001400, baseEnd_3001400] using wordTrace_append hprefix tailTrace_3001400
  have hstable : (prefixWord ++ tailWord_3001400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001400).length < 2 ^ (prefixWord ++ tailWord_3001400).sum := by decide
  have hdescent : baseEnd_3001400 < baseStart_3001400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001426 : List Nat := [3, 2, 2, 1, 3, 1, 2, 1, 2, 1, 5]
def baseStart_3001426 : Nat := 118140960795 + 3001426 * 2 ^ 59
def prefixEnd_3001426 : Nat := 4983230072969 + 3 ^ 40 * 3001426 * 2
def baseEnd_3001426 : Nat := 1541174186901679140671699

theorem tailTrace_3001426 : CollatzResearch.WordTrace tailWord_3001426 prefixEnd_3001426 1541174186901679140671699 := by
  unfold tailWord_3001426
  simp only [CollatzResearch.WordTrace]
  refine ⟨27367749906088419898880033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72980666416235786397013421 27367749906088419898880033)
  ·
    refine ⟨20525812429566314924160025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27367749906088419898880033 20525812429566314924160025)
    ·
      refine ⟨15394359322174736193120019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20525812429566314924160025 15394359322174736193120019)
      ·
        refine ⟨23091538983262104289680029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15394359322174736193120019 23091538983262104289680029)
        ·
          refine ⟨8659327118723289108630011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23091538983262104289680029 8659327118723289108630011)
          ·
            refine ⟨12988990678084933662945017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8659327118723289108630011 12988990678084933662945017)
            ·
              refine ⟨9741743008563700247208763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12988990678084933662945017 9741743008563700247208763)
              ·
                refine ⟨14612614512845550370813145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9741743008563700247208763 14612614512845550370813145)
                ·
                  refine ⟨10959460884634162778109859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14612614512845550370813145 10959460884634162778109859)
                  ·
                    refine ⟨16439191326951244167164789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10959460884634162778109859 16439191326951244167164789)
                    ·
                      refine ⟨1541174186901679140671699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16439191326951244167164789 1541174186901679140671699)
                      ·
                        rfl

theorem cell23_3001426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_3001426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001426 prefixEnd_3001426 := by exact prefixLift 3001426
  have htrace : WordTrace (prefixWord ++ tailWord_3001426) baseStart_3001426 baseEnd_3001426 := by
    simpa [prefixWord, tailWord_3001426, baseEnd_3001426] using wordTrace_append hprefix tailTrace_3001426
  have hstable : (prefixWord ++ tailWord_3001426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001426).length < 2 ^ (prefixWord ++ tailWord_3001426).sum := by decide
  have hdescent : baseEnd_3001426 < baseStart_3001426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001436 : List Nat := [2, 2, 4, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_3001436 : Nat := 118140960795 + 3001436 * 2 ^ 59
def prefixEnd_3001436 : Nat := 4983230072969 + 3 ^ 40 * 3001436 * 2
def baseEnd_3001436 : Nat := 1541179321708224101546653

theorem tailTrace_3001436 : CollatzResearch.WordTrace tailWord_3001436 prefixEnd_3001436 1541179321708224101546653 := by
  unfold tailWord_3001436
  simp only [CollatzResearch.WordTrace]
  refine ⟨54735682177158725651692081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72980909569544967535589441 54735682177158725651692081)
  ·
    refine ⟨41051761632869044238769061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54735682177158725651692081 41051761632869044238769061)
    ·
      refine ⟨7697205306162945794769199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41051761632869044238769061 7697205306162945794769199)
      ·
        refine ⟨11545807959244418692153799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7697205306162945794769199 11545807959244418692153799)
        ·
          refine ⟨17318711938866628038230699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11545807959244418692153799 17318711938866628038230699)
          ·
            refine ⟨25978067908299942057346049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17318711938866628038230699 25978067908299942057346049)
            ·
              refine ⟨19483550931224956543009537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25978067908299942057346049 19483550931224956543009537)
              ·
                refine ⟨14612663198418717407257153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19483550931224956543009537 14612663198418717407257153)
                ·
                  refine ⟨10959497398814038055442865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14612663198418717407257153 10959497398814038055442865)
                  ·
                    refine ⟨8219623049110528541582149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10959497398814038055442865 8219623049110528541582149)
                    ·
                      refine ⟨1541179321708224101546653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8219623049110528541582149 1541179321708224101546653)
                      ·
                        rfl

theorem cell23_3001436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_3001436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001436 prefixEnd_3001436 := by exact prefixLift 3001436
  have htrace : WordTrace (prefixWord ++ tailWord_3001436) baseStart_3001436 baseEnd_3001436 := by
    simpa [prefixWord, tailWord_3001436, baseEnd_3001436] using wordTrace_append hprefix tailTrace_3001436
  have hstable : (prefixWord ++ tailWord_3001436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001436).length < 2 ^ (prefixWord ++ tailWord_3001436).sum := by decide
  have hdescent : baseEnd_3001436 < baseStart_3001436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001440 : List Nat := [2, 1, 1, 3, 2, 2, 4, 2, 2, 2, 2]
def baseStart_3001440 : Nat := 118140960795 + 3001440 * 2 ^ 59
def prefixEnd_3001440 : Nat := 4983230072969 + 3 ^ 40 * 3001440 * 2
def baseEnd_3001440 : Nat := 1541181375630842085896635

theorem tailTrace_3001440 : CollatzResearch.WordTrace tailWord_3001440 prefixEnd_3001440 1541181375630842085896635 := by
  unfold tailWord_3001440
  simp only [CollatzResearch.WordTrace]
  refine ⟨54735755123151479993264887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72981006830868639991019849 54735755123151479993264887)
  ·
    refine ⟨82103632684727219989897331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54735755123151479993264887 82103632684727219989897331)
    ·
      refine ⟨123155449027090829984845997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82103632684727219989897331 123155449027090829984845997)
      ·
        refine ⟨46183293385159061244317249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123155449027090829984845997 46183293385159061244317249)
        ·
          refine ⟨34637470038869295933237937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46183293385159061244317249 34637470038869295933237937)
          ·
            refine ⟨25978102529151971949928453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34637470038869295933237937 25978102529151971949928453)
            ·
              refine ⟨4870894224215994740611585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25978102529151971949928453 4870894224215994740611585)
              ·
                refine ⟨3653170668161996055458689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4870894224215994740611585 3653170668161996055458689)
                ·
                  refine ⟨2739878001121497041594017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3653170668161996055458689 2739878001121497041594017)
                  ·
                    refine ⟨2054908500841122781195513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2739878001121497041594017 2054908500841122781195513)
                    ·
                      refine ⟨1541181375630842085896635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2054908500841122781195513 1541181375630842085896635)
                      ·
                        rfl

theorem cell23_3001440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 2, 2, 2].length) (baseStart_3001440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001440 prefixEnd_3001440 := by exact prefixLift 3001440
  have htrace : WordTrace (prefixWord ++ tailWord_3001440) baseStart_3001440 baseEnd_3001440 := by
    simpa [prefixWord, tailWord_3001440, baseEnd_3001440] using wordTrace_append hprefix tailTrace_3001440
  have hstable : (prefixWord ++ tailWord_3001440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001440).length < 2 ^ (prefixWord ++ tailWord_3001440).sum := by decide
  have hdescent : baseEnd_3001440 < baseStart_3001440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001456 : List Nat := [2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 3]
def baseStart_3001456 : Nat := 118140960795 + 3001456 * 2 ^ 59
def prefixEnd_3001456 : Nat := 4983230072969 + 3 ^ 40 * 3001456 * 2
def baseEnd_3001456 : Nat := 1541189591321314023296561

theorem tailTrace_3001456 : CollatzResearch.WordTrace tailWord_3001456 prefixEnd_3001456 1541189591321314023296561 := by
  unfold tailWord_3001456
  simp only [CollatzResearch.WordTrace]
  refine ⟨54736046907122497359556111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72981395876163329812741481 54736046907122497359556111)
  ·
    refine ⟨82104070360683746039334167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54736046907122497359556111 82104070360683746039334167)
    ·
      refine ⟨123156105541025619059001251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82104070360683746039334167 123156105541025619059001251)
      ·
        refine ⟨184734158311538428588501877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123156105541025619059001251 184734158311538428588501877)
        ·
          refine ⟨17318827341706727680172051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 184734158311538428588501877 17318827341706727680172051)
          ·
            refine ⟨25978241012560091520258077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17318827341706727680172051 25978241012560091520258077)
            ·
              refine ⟨9741840379710034320096779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25978241012560091520258077 9741840379710034320096779)
              ·
                refine ⟨14612760569565051480145169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9741840379710034320096779 14612760569565051480145169)
                ·
                  refine ⟨10959570427173788610108877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14612760569565051480145169 10959570427173788610108877)
                  ·
                    refine ⟨4109838910190170728790829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10959570427173788610108877 4109838910190170728790829)
                    ·
                      refine ⟨1541189591321314023296561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4109838910190170728790829 1541189591321314023296561)
                      ·
                        rfl

theorem cell23_3001456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 3].length) (baseStart_3001456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001456 prefixEnd_3001456 := by exact prefixLift 3001456
  have htrace : WordTrace (prefixWord ++ tailWord_3001456) baseStart_3001456 baseEnd_3001456 := by
    simpa [prefixWord, tailWord_3001456, baseEnd_3001456] using wordTrace_append hprefix tailTrace_3001456
  have hstable : (prefixWord ++ tailWord_3001456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001456).length < 2 ^ (prefixWord ++ tailWord_3001456).sum := by decide
  have hdescent : baseEnd_3001456 < baseStart_3001456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001476 : List Nat := [2, 3, 2, 1, 2, 3, 1, 1, 1, 7]
def baseStart_3001476 : Nat := 118140960795 + 3001476 * 2 ^ 59
def prefixEnd_3001476 : Nat := 4983230072969 + 3 ^ 40 * 3001476 * 2
def baseEnd_3001476 : Nat := 513733286978134648348823

theorem tailTrace_3001476 : CollatzResearch.WordTrace tailWord_3001476 prefixEnd_3001476 513733286978134648348823 := by
  unfold tailWord_3001476
  simp only [CollatzResearch.WordTrace]
  refine ⟨54736411637086269067420141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72981882182781692089893521 54736411637086269067420141)
  ·
    refine ⟨20526154363907350900282553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54736411637086269067420141 20526154363907350900282553)
    ·
      refine ⟨15394615772930513175211915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20526154363907350900282553 15394615772930513175211915)
      ·
        refine ⟨23091923659395769762817873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15394615772930513175211915 23091923659395769762817873)
        ·
          refine ⟨17318942744546827322113405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23091923659395769762817873 17318942744546827322113405)
          ·
            refine ⟨6494603529205060245792527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17318942744546827322113405 6494603529205060245792527)
            ·
              refine ⟨9741905293807590368688791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6494603529205060245792527 9741905293807590368688791)
              ·
                refine ⟨14612857940711385553033187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9741905293807590368688791 14612857940711385553033187)
                ·
                  refine ⟨21919286911067078329549781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14612857940711385553033187 21919286911067078329549781)
                  ·
                    refine ⟨513733286978134648348823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21919286911067078329549781 513733286978134648348823)
                    ·
                      rfl

theorem cell23_3001476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_3001476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001476 prefixEnd_3001476 := by exact prefixLift 3001476
  have htrace : WordTrace (prefixWord ++ tailWord_3001476) baseStart_3001476 baseEnd_3001476 := by
    simpa [prefixWord, tailWord_3001476, baseEnd_3001476] using wordTrace_append hprefix tailTrace_3001476
  have hstable : (prefixWord ++ tailWord_3001476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001476).length < 2 ^ (prefixWord ++ tailWord_3001476).sum := by decide
  have hdescent : baseEnd_3001476 < baseStart_3001476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001480 : List Nat := [2, 1, 3, 4, 2, 1, 2, 3, 5]
def baseStart_3001480 : Nat := 118140960795 + 3001480 * 2 ^ 59
def prefixEnd_3001480 : Nat := 4983230072969 + 3 ^ 40 * 3001480 * 2
def baseEnd_3001480 : Nat := 171244657206335769932939

theorem tailTrace_3001480 : CollatzResearch.WordTrace tailWord_3001480 prefixEnd_3001480 171244657206335769932939 := by
  unfold tailWord_3001480
  simp only [CollatzResearch.WordTrace]
  refine ⟨54736484583079023408992947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72981979444105364545323929 54736484583079023408992947)
  ·
    refine ⟨82104726874618535113489421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54736484583079023408992947 82104726874618535113489421)
    ·
      refine ⟨30789272577981950667558533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82104726874618535113489421 30789272577981950667558533)
      ·
        refine ⟨5772988608371615750167225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30789272577981950667558533 5772988608371615750167225)
        ·
          refine ⟨4329741456278711812625419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5772988608371615750167225 4329741456278711812625419)
          ·
            refine ⟨6494612184418067718938129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4329741456278711812625419 6494612184418067718938129)
            ·
              refine ⟨4870959138313550789203597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6494612184418067718938129 4870959138313550789203597)
              ·
                refine ⟨1826609676867581545951349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4870959138313550789203597 1826609676867581545951349)
                ·
                  refine ⟨171244657206335769932939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1826609676867581545951349 171244657206335769932939)
                  ·
                    rfl

theorem cell23_3001480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 3, 5].length) (baseStart_3001480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001480 prefixEnd_3001480 := by exact prefixLift 3001480
  have htrace : WordTrace (prefixWord ++ tailWord_3001480) baseStart_3001480 baseEnd_3001480 := by
    simpa [prefixWord, tailWord_3001480, baseEnd_3001480] using wordTrace_append hprefix tailTrace_3001480
  have hstable : (prefixWord ++ tailWord_3001480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001480).length < 2 ^ (prefixWord ++ tailWord_3001480).sum := by decide
  have hdescent : baseEnd_3001480 < baseStart_3001480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001516 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 3]
def baseStart_3001516 : Nat := 118140960795 + 3001516 * 2 ^ 59
def prefixEnd_3001516 : Nat := 4983230072969 + 3 ^ 40 * 3001516 * 2
def baseEnd_3001516 : Nat := 1541220400160583788546285

theorem tailTrace_3001516 : CollatzResearch.WordTrace tailWord_3001516 prefixEnd_3001516 1541220400160583788546285 := by
  unfold tailWord_3001516
  simp only [CollatzResearch.WordTrace]
  refine ⟨54737141097013812483148201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72982854796018416644197601 54737141097013812483148201)
  ·
    refine ⟨41052855822760359362361151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54737141097013812483148201 41052855822760359362361151)
    ·
      refine ⟨61579283734140539043541727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41052855822760359362361151 61579283734140539043541727)
      ·
        refine ⟨92368925601210808565312591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61579283734140539043541727 92368925601210808565312591)
        ·
          refine ⟨138553388401816212847968887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92368925601210808565312591 138553388401816212847968887)
          ·
            refine ⟨207830082602724319271953331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138553388401816212847968887 207830082602724319271953331)
            ·
              refine ⟨311745123904086478907929997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207830082602724319271953331 311745123904086478907929997)
              ·
                refine ⟨116904421464032429590473749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 311745123904086478907929997 116904421464032429590473749)
                ·
                  refine ⟨5479894756126520137053457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 116904421464032429590473749 5479894756126520137053457)
                  ·
                    refine ⟨4109921067094890102790093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5479894756126520137053457 4109921067094890102790093)
                    ·
                      refine ⟨1541220400160583788546285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4109921067094890102790093 1541220400160583788546285)
                      ·
                        rfl

theorem cell23_3001516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 3].length) (baseStart_3001516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001516 prefixEnd_3001516 := by exact prefixLift 3001516
  have htrace : WordTrace (prefixWord ++ tailWord_3001516) baseStart_3001516 baseEnd_3001516 := by
    simpa [prefixWord, tailWord_3001516, baseEnd_3001516] using wordTrace_append hprefix tailTrace_3001516
  have hstable : (prefixWord ++ tailWord_3001516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001516).length < 2 ^ (prefixWord ++ tailWord_3001516).sum := by decide
  have hdescent : baseEnd_3001516 < baseStart_3001516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001539 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 8]
def baseStart_3001539 : Nat := 118140960795 + 3001539 * 2 ^ 59
def prefixEnd_3001539 : Nat := 4983230072969 + 3 ^ 40 * 3001539 * 2
def baseEnd_3001539 : Nat := 1541232210215637198558679

theorem tailTrace_3001539 : CollatzResearch.WordTrace tailWord_3001539 prefixEnd_3001539 1541232210215637198558679 := by
  unfold tailWord_3001539
  simp only [CollatzResearch.WordTrace]
  refine ⟨109475121072944299894383671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72983414048629533262922447 109475121072944299894383671)
  ·
    refine ⟨164212681609416449841575507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109475121072944299894383671 164212681609416449841575507)
    ·
      refine ⟨246319022414124674762363261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164212681609416449841575507 246319022414124674762363261)
      ·
        refine ⟨92369633405296753035886223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246319022414124674762363261 92369633405296753035886223)
        ·
          refine ⟨138554450107945129553829335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92369633405296753035886223 138554450107945129553829335)
          ·
            refine ⟨207831675161917694330744003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138554450107945129553829335 207831675161917694330744003)
            ·
              refine ⟨311747512742876541496116005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207831675161917694330744003 311747512742876541496116005)
              ·
                refine ⟨58452658639289351530521751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 311747512742876541496116005 58452658639289351530521751)
                ·
                  refine ⟨87678987958934027295782627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58452658639289351530521751 87678987958934027295782627)
                  ·
                    refine ⟨131518481938401040943673941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 87678987958934027295782627 131518481938401040943673941)
                    ·
                      refine ⟨1541232210215637198558679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 131518481938401040943673941 1541232210215637198558679)
                      ·
                        rfl

theorem cell23_3001539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_3001539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001539 prefixEnd_3001539 := by exact prefixLift 3001539
  have htrace : WordTrace (prefixWord ++ tailWord_3001539) baseStart_3001539 baseEnd_3001539 := by
    simpa [prefixWord, tailWord_3001539, baseEnd_3001539] using wordTrace_append hprefix tailTrace_3001539
  have hstable : (prefixWord ++ tailWord_3001539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001539).length < 2 ^ (prefixWord ++ tailWord_3001539).sum := by decide
  have hdescent : baseEnd_3001539 < baseStart_3001539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001550 : List Nat := [4, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3]
def baseStart_3001550 : Nat := 118140960795 + 3001550 * 2 ^ 59
def prefixEnd_3001550 : Nat := 4983230072969 + 3 ^ 40 * 3001550 * 2
def baseEnd_3001550 : Nat := 1541237858502836655521129

theorem tailTrace_3001550 : CollatzResearch.WordTrace tailWord_3001550 prefixEnd_3001550 1541237858502836655521129 := by
  unfold tailWord_3001550
  simp only [CollatzResearch.WordTrace]
  refine ⟨13684440284488056096629263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72983681517269632515356069 13684440284488056096629263)
  ·
    refine ⟨20526660426732084144943895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13684440284488056096629263 20526660426732084144943895)
    ·
      refine ⟨30789990640098126217415843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20526660426732084144943895 30789990640098126217415843)
      ·
        refine ⟨46184985960147189326123765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30789990640098126217415843 46184985960147189326123765)
        ·
          refine ⟨4329842433763798999324103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46184985960147189326123765 4329842433763798999324103)
          ·
            refine ⟨6494763650645698498986155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4329842433763798999324103 6494763650645698498986155)
            ·
              refine ⟨9742145475968547748479233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6494763650645698498986155 9742145475968547748479233)
              ·
                refine ⟨7306609106976410811359425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9742145475968547748479233 7306609106976410811359425)
                ·
                  refine ⟨5479956830232308108519569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7306609106976410811359425 5479956830232308108519569)
                  ·
                    refine ⟨4109967622674231081389677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5479956830232308108519569 4109967622674231081389677)
                    ·
                      refine ⟨1541237858502836655521129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4109967622674231081389677 1541237858502836655521129)
                      ·
                        rfl

theorem cell23_3001550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_3001550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001550 prefixEnd_3001550 := by exact prefixLift 3001550
  have htrace : WordTrace (prefixWord ++ tailWord_3001550) baseStart_3001550 baseEnd_3001550 := by
    simpa [prefixWord, tailWord_3001550, baseEnd_3001550] using wordTrace_append hprefix tailTrace_3001550
  have hstable : (prefixWord ++ tailWord_3001550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001550).length < 2 ^ (prefixWord ++ tailWord_3001550).sum := by decide
  have hdescent : baseEnd_3001550 < baseStart_3001550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001583 : List Nat := [1, 1, 2, 1, 7, 1, 1, 1, 3, 5]
def baseStart_3001583 : Nat := 118140960795 + 3001583 * 2 ^ 59
def prefixEnd_3001583 : Nat := 4983230072969 + 3 ^ 40 * 3001583 * 2
def baseEnd_3001583 : Nat := 513751601121478342136159

theorem tailTrace_3001583 : CollatzResearch.WordTrace tailWord_3001583 prefixEnd_3001583 513751601121478342136159 := by
  unfold tailWord_3001583
  simp only [CollatzResearch.WordTrace]
  refine ⟨109476725884784895408985403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72984483923189930272656935 109476725884784895408985403)
  ·
    refine ⟨164215088827177343113478105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109476725884784895408985403 164215088827177343113478105)
    ·
      refine ⟨123161316620383007335108579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164215088827177343113478105 123161316620383007335108579)
      ·
        refine ⟨184741974930574511002662869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123161316620383007335108579 184741974930574511002662869)
        ·
          refine ⟨4329890037435340101624911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 184741974930574511002662869 4329890037435340101624911)
          ·
            refine ⟨6494835056153010152437367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4329890037435340101624911 6494835056153010152437367)
            ·
              refine ⟨9742252584229515228656051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6494835056153010152437367 9742252584229515228656051)
              ·
                refine ⟨14613378876344272842984077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9742252584229515228656051 14613378876344272842984077)
                ·
                  refine ⟨5480017078629102316119029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14613378876344272842984077 5480017078629102316119029)
                  ·
                    refine ⟨513751601121478342136159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5480017078629102316119029 513751601121478342136159)
                    ·
                      rfl

theorem cell23_3001583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 5].length) (baseStart_3001583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001583 prefixEnd_3001583 := by exact prefixLift 3001583
  have htrace : WordTrace (prefixWord ++ tailWord_3001583) baseStart_3001583 baseEnd_3001583 := by
    simpa [prefixWord, tailWord_3001583, baseEnd_3001583] using wordTrace_append hprefix tailTrace_3001583
  have hstable : (prefixWord ++ tailWord_3001583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001583).length < 2 ^ (prefixWord ++ tailWord_3001583).sum := by decide
  have hdescent : baseEnd_3001583 < baseStart_3001583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001614 : List Nat := [4, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3]
def baseStart_3001614 : Nat := 118140960795 + 3001614 * 2 ^ 59
def prefixEnd_3001614 : Nat := 4983230072969 + 3 ^ 40 * 3001614 * 2
def baseEnd_3001614 : Nat := 1541270721264724405120835

theorem tailTrace_3001614 : CollatzResearch.WordTrace tailWord_3001614 prefixEnd_3001614 1541270721264724405120835 := by
  unfold tailWord_3001614
  simp only [CollatzResearch.WordTrace]
  refine ⟨13684732068459073462920487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72985237698448391802242597 13684732068459073462920487)
  ·
    refine ⟨20527098102688610194380731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13684732068459073462920487 20527098102688610194380731)
    ·
      refine ⟨30790647154032915291571097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20527098102688610194380731 30790647154032915291571097)
      ·
        refine ⟨23092985365524686468678323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30790647154032915291571097 23092985365524686468678323)
        ·
          refine ⟨34639478048287029703017485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23092985365524686468678323 34639478048287029703017485)
          ·
            refine ⟨12989804268107636138631557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34639478048287029703017485 12989804268107636138631557)
            ·
              refine ⟨2435588300270181775993417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12989804268107636138631557 2435588300270181775993417)
              ·
                refine ⟨1826691225202636331995063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2435588300270181775993417 1826691225202636331995063)
                ·
                  refine ⟨2740036837803954497992595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1826691225202636331995063 2740036837803954497992595)
                  ·
                    refine ⟨4110055256705931746988893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2740036837803954497992595 4110055256705931746988893)
                    ·
                      refine ⟨1541270721264724405120835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4110055256705931746988893 1541270721264724405120835)
                      ·
                        rfl

theorem cell23_3001614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_3001614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001614 prefixEnd_3001614 := by exact prefixLift 3001614
  have htrace : WordTrace (prefixWord ++ tailWord_3001614) baseStart_3001614 baseEnd_3001614 := by
    simpa [prefixWord, tailWord_3001614, baseEnd_3001614] using wordTrace_append hprefix tailTrace_3001614
  have hstable : (prefixWord ++ tailWord_3001614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001614).length < 2 ^ (prefixWord ++ tailWord_3001614).sum := by decide
  have hdescent : baseEnd_3001614 < baseStart_3001614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001623 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 5, 2, 3]
def baseStart_3001623 : Nat := 118140960795 + 3001623 * 2 ^ 59
def prefixEnd_3001623 : Nat := 4983230072969 + 3 ^ 40 * 3001623 * 2
def baseEnd_3001623 : Nat := 1541275342590614869908293

theorem tailTrace_3001623 : CollatzResearch.WordTrace tailWord_3001623 prefixEnd_3001623 1541275342590614869908293 := by
  unfold tailWord_3001623
  simp only [CollatzResearch.WordTrace]
  refine ⟨109478184804639982240441523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72985456536426654826961015 109478184804639982240441523)
  ·
    refine ⟨164217277206959973360662285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109478184804639982240441523 164217277206959973360662285)
    ·
      refine ⟨61581478952609990010248357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164217277206959973360662285 61581478952609990010248357)
      ·
        refine ⟨11546527303614373126921567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61581478952609990010248357 11546527303614373126921567)
        ·
          refine ⟨17319790955421559690382351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11546527303614373126921567 17319790955421559690382351)
          ·
            refine ⟨25979686433132339535573527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17319790955421559690382351 25979686433132339535573527)
            ·
              refine ⟨38969529649698509303360291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25979686433132339535573527 38969529649698509303360291)
              ·
                refine ⟨58454294474547763955040437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38969529649698509303360291 58454294474547763955040437)
                ·
                  refine ⟨5480090106988852870785041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58454294474547763955040437 5480090106988852870785041)
                  ·
                    refine ⟨4110067580241639653088781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5480090106988852870785041 4110067580241639653088781)
                    ·
                      refine ⟨1541275342590614869908293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4110067580241639653088781 1541275342590614869908293)
                      ·
                        rfl

theorem cell23_3001623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_3001623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001623 prefixEnd_3001623 := by exact prefixLift 3001623
  have htrace : WordTrace (prefixWord ++ tailWord_3001623) baseStart_3001623 baseEnd_3001623 := by
    simpa [prefixWord, tailWord_3001623, baseEnd_3001623] using wordTrace_append hprefix tailTrace_3001623
  have hstable : (prefixWord ++ tailWord_3001623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001623).length < 2 ^ (prefixWord ++ tailWord_3001623).sum := by decide
  have hdescent : baseEnd_3001623 < baseStart_3001623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001637 : List Nat := [1, 3, 1, 2, 4, 2, 1, 2, 3, 2, 2]
def baseStart_3001637 : Nat := 118140960795 + 3001637 * 2 ^ 59
def prefixEnd_3001637 : Nat := 4983230072969 + 3 ^ 40 * 3001637 * 2
def baseEnd_3001637 : Nat := 1541282531319777815133229

theorem tailTrace_3001637 : CollatzResearch.WordTrace tailWord_3001637 prefixEnd_3001637 1541282531319777815133229 := by
  unfold tailWord_3001637
  simp only [CollatzResearch.WordTrace]
  refine ⟨109478695426589262631451165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72985796951059508420967443 109478695426589262631451165)
  ·
    refine ⟨41054510784970973486794187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109478695426589262631451165 41054510784970973486794187)
    ·
      refine ⟨61581766177456460230191281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41054510784970973486794187 61581766177456460230191281)
      ·
        refine ⟨46186324633092345172643461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61581766177456460230191281 46186324633092345172643461)
        ·
          refine ⟨8659935868704814719870649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46186324633092345172643461 8659935868704814719870649)
          ·
            refine ⟨6494951901528611039902987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8659935868704814719870649 6494951901528611039902987)
            ·
              refine ⟨9742427852292916559854481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6494951901528611039902987 9742427852292916559854481)
              ·
                refine ⟨7306820889219687419890861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9742427852292916559854481 7306820889219687419890861)
                ·
                  refine ⟨2740057833457382782459073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7306820889219687419890861 2740057833457382782459073)
                  ·
                    refine ⟨2055043375093037086844305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2740057833457382782459073 2055043375093037086844305)
                    ·
                      refine ⟨1541282531319777815133229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2055043375093037086844305 1541282531319777815133229)
                      ·
                        rfl

theorem cell23_3001637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 3, 2, 2].length) (baseStart_3001637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001637 prefixEnd_3001637 := by exact prefixLift 3001637
  have htrace : WordTrace (prefixWord ++ tailWord_3001637) baseStart_3001637 baseEnd_3001637 := by
    simpa [prefixWord, tailWord_3001637, baseEnd_3001637] using wordTrace_append hprefix tailTrace_3001637
  have hstable : (prefixWord ++ tailWord_3001637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001637).length < 2 ^ (prefixWord ++ tailWord_3001637).sum := by decide
  have hdescent : baseEnd_3001637 < baseStart_3001637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001640 : List Nat := [2, 1, 5, 1, 2, 1, 2, 1, 3, 2, 3]
def baseStart_3001640 : Nat := 118140960795 + 3001640 * 2 ^ 59
def prefixEnd_3001640 : Nat := 4983230072969 + 3 ^ 40 * 3001640 * 2
def baseEnd_3001640 : Nat := 1541284071761741303395715

theorem tailTrace_3001640 : CollatzResearch.WordTrace tailWord_3001640 prefixEnd_3001640 1541284071761741303395715 := by
  unfold tailWord_3001640
  simp only [CollatzResearch.WordTrace]
  refine ⟨54739402422789197071905187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72985869897052262762540249 54739402422789197071905187)
  ·
    refine ⟨82109103634183795607857781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54739402422789197071905187 82109103634183795607857781)
    ·
      refine ⟨7697728465704730838236667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82109103634183795607857781 7697728465704730838236667)
      ·
        refine ⟨11546592698557096257355001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7697728465704730838236667 11546592698557096257355001)
        ·
          refine ⟨8659944523917822193016251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11546592698557096257355001 8659944523917822193016251)
          ·
            refine ⟨12989916785876733289524377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8659944523917822193016251 12989916785876733289524377)
            ·
              refine ⟨9742437589407549967143283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12989916785876733289524377 9742437589407549967143283)
              ·
                refine ⟨14613656384111324950714925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9742437589407549967143283 14613656384111324950714925)
                ·
                  refine ⟨5480121144041746856518097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14613656384111324950714925 5480121144041746856518097)
                  ·
                    refine ⟨4110090858031310142388573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5480121144041746856518097 4110090858031310142388573)
                    ·
                      refine ⟨1541284071761741303395715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4110090858031310142388573 1541284071761741303395715)
                      ·
                        rfl

theorem cell23_3001640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_3001640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001640 prefixEnd_3001640 := by exact prefixLift 3001640
  have htrace : WordTrace (prefixWord ++ tailWord_3001640) baseStart_3001640 baseEnd_3001640 := by
    simpa [prefixWord, tailWord_3001640, baseEnd_3001640] using wordTrace_append hprefix tailTrace_3001640
  have hstable : (prefixWord ++ tailWord_3001640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001640).length < 2 ^ (prefixWord ++ tailWord_3001640).sum := by decide
  have hdescent : baseEnd_3001640 < baseStart_3001640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001654 : List Nat := [5, 1, 2, 3, 1, 1, 1, 3, 1, 1, 4]
def baseStart_3001654 : Nat := 118140960795 + 3001654 * 2 ^ 59
def prefixEnd_3001654 : Nat := 4983230072969 + 3 ^ 40 * 3001654 * 2
def baseEnd_3001654 : Nat := 1541291260490904248620651

theorem tailTrace_3001654 : CollatzResearch.WordTrace tailWord_3001654 prefixEnd_3001654 1541291260490904248620651 := by
  unfold tailWord_3001654
  simp only [CollatzResearch.WordTrace]
  refine ⟨6842457216720479658426251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72986210311685116356546677 6842457216720479658426251)
  ·
    refine ⟨10263685825080719487639377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6842457216720479658426251 10263685825080719487639377)
    ·
      refine ⟨7697764368810539615729533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10263685825080719487639377 7697764368810539615729533)
      ·
        refine ⟨2886661638303952355898575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7697764368810539615729533 2886661638303952355898575)
        ·
          refine ⟨4329992457455928533847863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2886661638303952355898575 4329992457455928533847863)
          ·
            refine ⟨6494988686183892800771795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4329992457455928533847863 6494988686183892800771795)
            ·
              refine ⟨9742483029275839201157693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6494988686183892800771795 9742483029275839201157693)
              ·
                refine ⟨3653431135978439700434135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9742483029275839201157693 3653431135978439700434135)
                ·
                  refine ⟨5480146703967659550651203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3653431135978439700434135 5480146703967659550651203)
                  ·
                    refine ⟨8220220055951489325976805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5480146703967659550651203 8220220055951489325976805)
                    ·
                      refine ⟨1541291260490904248620651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8220220055951489325976805 1541291260490904248620651)
                      ·
                        rfl

theorem cell23_3001654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_3001654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001654 prefixEnd_3001654 := by exact prefixLift 3001654
  have htrace : WordTrace (prefixWord ++ tailWord_3001654) baseStart_3001654 baseEnd_3001654 := by
    simpa [prefixWord, tailWord_3001654, baseEnd_3001654] using wordTrace_append hprefix tailTrace_3001654
  have hstable : (prefixWord ++ tailWord_3001654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001654).length < 2 ^ (prefixWord ++ tailWord_3001654).sum := by decide
  have hdescent : baseEnd_3001654 < baseStart_3001654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001657 : List Nat := [1, 2, 1, 6, 2, 1, 1, 3, 1, 2, 3]
def baseStart_3001657 : Nat := 118140960795 + 3001657 * 2 ^ 59
def prefixEnd_3001657 : Nat := 4983230072969 + 3 ^ 40 * 3001657 * 2
def baseEnd_3001657 : Nat := 1541292800932867736883137

theorem tailTrace_3001657 : CollatzResearch.WordTrace tailWord_3001657 prefixEnd_3001657 1541292800932867736883137 := by
  unfold tailWord_3001657
  simp only [CollatzResearch.WordTrace]
  refine ⟨109479424886516806047179225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72986283257677870698119483 109479424886516806047179225)
  ·
    refine ⟨82109568664887604535384419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109479424886516806047179225 82109568664887604535384419)
    ·
      refine ⟨123164352997331406803076629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82109568664887604535384419 123164352997331406803076629)
      ·
        refine ⟨5773329046749909693894217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 123164352997331406803076629 5773329046749909693894217)
        ·
          refine ⟨4329996785062432270420663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5773329046749909693894217 4329996785062432270420663)
          ·
            refine ⟨6494995177593648405630995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4329996785062432270420663 6494995177593648405630995)
            ·
              refine ⟨9742492766390472608446493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6494995177593648405630995 9742492766390472608446493)
              ·
                refine ⟨3653434787396427228167435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9742492766390472608446493 3653434787396427228167435)
                ·
                  refine ⟨5480152181094640842251153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3653434787396427228167435 5480152181094640842251153)
                  ·
                    refine ⟨4110114135820980631688365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5480152181094640842251153 4110114135820980631688365)
                    ·
                      refine ⟨1541292800932867736883137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4110114135820980631688365 1541292800932867736883137)
                      ·
                        rfl

theorem cell23_3001657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_3001657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001657 prefixEnd_3001657 := by exact prefixLift 3001657
  have htrace : WordTrace (prefixWord ++ tailWord_3001657) baseStart_3001657 baseEnd_3001657 := by
    simpa [prefixWord, tailWord_3001657, baseEnd_3001657] using wordTrace_append hprefix tailTrace_3001657
  have hstable : (prefixWord ++ tailWord_3001657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001657).length < 2 ^ (prefixWord ++ tailWord_3001657).sum := by decide
  have hdescent : baseEnd_3001657 < baseStart_3001657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001733 : List Nat := [1, 3, 1, 1, 3, 1, 5, 1, 7]
def baseStart_3001733 : Nat := 118140960795 + 3001733 * 2 ^ 59
def prefixEnd_3001733 : Nat := 4983230072969 + 3 ^ 40 * 3001733 * 2
def baseEnd_3001733 : Nat := 171259091718067715503643

theorem tailTrace_3001733 : CollatzResearch.WordTrace tailWord_3001733 prefixEnd_3001733 171259091718067715503643 := by
  unfold tailWord_3001733
  simp only [CollatzResearch.WordTrace]
  refine ⟨109482196834241471026945853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72988131222827647351297235 109482196834241471026945853)
  ·
    refine ⟨41055823812840551635104695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109482196834241471026945853 41055823812840551635104695)
    ·
      refine ⟨61583735719260827452657043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41055823812840551635104695 61583735719260827452657043)
      ·
        refine ⟨92375603578891241178985565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61583735719260827452657043 92375603578891241178985565)
        ·
          refine ⟨34640851342084215442119587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92375603578891241178985565 34640851342084215442119587)
          ·
            refine ⟨51961277013126323163179381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34640851342084215442119587 51961277013126323163179381)
            ·
              refine ⟨4871369719980592796548067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51961277013126323163179381 4871369719980592796548067)
              ·
                refine ⟨7307054579970889194822101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4871369719980592796548067 7307054579970889194822101)
                ·
                  refine ⟨171259091718067715503643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7307054579970889194822101 171259091718067715503643)
                  ·
                    rfl

theorem cell23_3001733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 7].length) (baseStart_3001733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001733 prefixEnd_3001733 := by exact prefixLift 3001733
  have htrace : WordTrace (prefixWord ++ tailWord_3001733) baseStart_3001733 baseEnd_3001733 := by
    simpa [prefixWord, tailWord_3001733, baseEnd_3001733] using wordTrace_append hprefix tailTrace_3001733
  have hstable : (prefixWord ++ tailWord_3001733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001733).length < 2 ^ (prefixWord ++ tailWord_3001733).sum := by decide
  have hdescent : baseEnd_3001733 < baseStart_3001733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001814 : List Nat := [5, 2, 1, 1, 1, 4, 1, 1, 2, 5]
def baseStart_3001814 : Nat := 118140960795 + 3001814 * 2 ^ 59
def prefixEnd_3001814 : Nat := 4983230072969 + 3 ^ 40 * 3001814 * 2
def baseEnd_3001814 : Nat := 513791139131874540873305

theorem tailTrace_3001814 : CollatzResearch.WordTrace tailWord_3001814 prefixEnd_3001814 513791139131874540873305 := by
  unfold tailWord_3001814
  simp only [CollatzResearch.WordTrace]
  refine ⟨6842821946684251366290281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72990100764632014573762997 6842821946684251366290281)
  ·
    refine ⟨5132116460013188524717711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6842821946684251366290281 5132116460013188524717711)
    ·
      refine ⟨7698174690019782787076567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5132116460013188524717711 7698174690019782787076567)
      ·
        refine ⟨11547262035029674180614851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7698174690019782787076567 11547262035029674180614851)
        ·
          refine ⟨17320893052544511270922277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11547262035029674180614851 17320893052544511270922277)
          ·
            refine ⟨3247667447352095863297927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17320893052544511270922277 3247667447352095863297927)
            ·
              refine ⟨4871501171028143794946891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3247667447352095863297927 4871501171028143794946891)
              ·
                refine ⟨7307251756542215692420337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4871501171028143794946891 7307251756542215692420337)
                ·
                  refine ⟨5480438817406661769315253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7307251756542215692420337 5480438817406661769315253)
                  ·
                    refine ⟨513791139131874540873305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5480438817406661769315253 513791139131874540873305)
                    ·
                      rfl

theorem cell23_3001814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_3001814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001814 prefixEnd_3001814 := by exact prefixLift 3001814
  have htrace : WordTrace (prefixWord ++ tailWord_3001814) baseStart_3001814 baseEnd_3001814 := by
    simpa [prefixWord, tailWord_3001814, baseEnd_3001814] using wordTrace_append hprefix tailTrace_3001814
  have hstable : (prefixWord ++ tailWord_3001814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001814).length < 2 ^ (prefixWord ++ tailWord_3001814).sum := by decide
  have hdescent : baseEnd_3001814 < baseStart_3001814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001817 : List Nat := [1, 2, 1, 2, 4, 4, 1, 1, 2, 1, 4]
def baseStart_3001817 : Nat := 118140960795 + 3001817 * 2 ^ 59
def prefixEnd_3001817 : Nat := 4983230072969 + 3 ^ 40 * 3001817 * 2
def baseEnd_3001817 : Nat := 1541374957837587110882401

theorem tailTrace_3001817 : CollatzResearch.WordTrace tailWord_3001817 prefixEnd_3001817 1541374957837587110882401 := by
  unfold tailWord_3001817
  simp only [CollatzResearch.WordTrace]
  refine ⟨109485260565937153373003705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72990173710624768915335803 109485260565937153373003705)
  ·
    refine ⟨82113945424452865029752779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109485260565937153373003705 82113945424452865029752779)
    ·
      refine ⟨123170918136679297544629169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82113945424452865029752779 123170918136679297544629169)
      ·
        refine ⟨92378188602509473158471877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123170918136679297544629169 92378188602509473158471877)
        ·
          refine ⟨17320910362970526217213477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92378188602509473158471877 17320910362970526217213477)
          ·
            refine ⟨3247670693056973665727527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17320910362970526217213477 3247670693056973665727527)
            ·
              refine ⟨4871506039585460498591291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3247670693056973665727527 4871506039585460498591291)
              ·
                refine ⟨7307259059378190747886937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4871506039585460498591291 7307259059378190747886937)
                ·
                  refine ⟨5480444294533643060915203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7307259059378190747886937 5480444294533643060915203)
                  ·
                    refine ⟨8220666441800464591372805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5480444294533643060915203 8220666441800464591372805)
                    ·
                      refine ⟨1541374957837587110882401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8220666441800464591372805 1541374957837587110882401)
                      ·
                        rfl

theorem cell23_3001817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 1, 4].length) (baseStart_3001817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001817 prefixEnd_3001817 := by exact prefixLift 3001817
  have htrace : WordTrace (prefixWord ++ tailWord_3001817) baseStart_3001817 baseEnd_3001817 := by
    simpa [prefixWord, tailWord_3001817, baseEnd_3001817] using wordTrace_append hprefix tailTrace_3001817
  have hstable : (prefixWord ++ tailWord_3001817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001817).length < 2 ^ (prefixWord ++ tailWord_3001817).sum := by decide
  have hdescent : baseEnd_3001817 < baseStart_3001817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001823 : List Nat := [1, 1, 2, 3, 3, 1, 2, 2, 8]
def baseStart_3001823 : Nat := 118140960795 + 3001823 * 2 ^ 59
def prefixEnd_3001823 : Nat := 4983230072969 + 3 ^ 40 * 3001823 * 2
def baseEnd_3001823 : Nat := 171264226524612676378597

theorem tailTrace_3001823 : CollatzResearch.WordTrace tailWord_3001823 prefixEnd_3001823 171264226524612676378597 := by
  unfold tailWord_3001823
  simp only [CollatzResearch.WordTrace]
  refine ⟨109485479403915416397722123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72990319602610277598481415 109485479403915416397722123)
  ·
    refine ⟨164228219105873124596583185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109485479403915416397722123 164228219105873124596583185)
    ·
      refine ⟨123171164329404843447437389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164228219105873124596583185 123171164329404843447437389)
      ·
        refine ⟨46189186623526816292789021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123171164329404843447437389 46189186623526816292789021)
        ·
          refine ⟨17320944983822556109795883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46189186623526816292789021 17320944983822556109795883)
          ·
            refine ⟨25981417475733834164693825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17320944983822556109795883 25981417475733834164693825)
            ·
              refine ⟨19486063106800375623520369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25981417475733834164693825 19486063106800375623520369)
              ·
                refine ⟨14614547330100281717640277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19486063106800375623520369 14614547330100281717640277)
                ·
                  refine ⟨171264226524612676378597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14614547330100281717640277 171264226524612676378597)
                  ·
                    rfl

theorem cell23_3001823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 8].length) (baseStart_3001823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001823 prefixEnd_3001823 := by exact prefixLift 3001823
  have htrace : WordTrace (prefixWord ++ tailWord_3001823) baseStart_3001823 baseEnd_3001823 := by
    simpa [prefixWord, tailWord_3001823, baseEnd_3001823] using wordTrace_append hprefix tailTrace_3001823
  have hstable : (prefixWord ++ tailWord_3001823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001823).length < 2 ^ (prefixWord ++ tailWord_3001823).sum := by decide
  have hdescent : baseEnd_3001823 < baseStart_3001823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001840 : List Nat := [2, 1, 1, 1, 3, 4, 3, 2, 6]
def baseStart_3001840 : Nat := 118140960795 + 3001840 * 2 ^ 59
def prefixEnd_3001840 : Nat := 4983230072969 + 3 ^ 40 * 3001840 * 2
def baseEnd_3001840 : Nat := 171265196432515613432755

theorem tailTrace_3001840 : CollatzResearch.WordTrace tailWord_3001840 prefixEnd_3001840 171265196432515613432755 := by
  unfold tailWord_3001840
  simp only [CollatzResearch.WordTrace]
  refine ⟨54743049722426914150545487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72990732963235885534060649 54743049722426914150545487)
  ·
    refine ⟨82114574583640371225818231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54743049722426914150545487 82114574583640371225818231)
    ·
      refine ⟨123171861875460556838727347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82114574583640371225818231 123171861875460556838727347)
      ·
        refine ⟨184757792813190835258091021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123171861875460556838727347 184757792813190835258091021)
        ·
          refine ⟨69284172304946563221784133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184757792813190835258091021 69284172304946563221784133)
          ·
            refine ⟨12990782307177480604084525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69284172304946563221784133 12990782307177480604084525)
            ·
              refine ⟨4871543365191555226531697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12990782307177480604084525 4871543365191555226531697)
              ·
                refine ⟨3653657523893666419898773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4871543365191555226531697 3653657523893666419898773)
                ·
                  refine ⟨171265196432515613432755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3653657523893666419898773 171265196432515613432755)
                  ·
                    rfl

theorem cell23_3001840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 6].length) (baseStart_3001840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001840 prefixEnd_3001840 := by exact prefixLift 3001840
  have htrace : WordTrace (prefixWord ++ tailWord_3001840) baseStart_3001840 baseEnd_3001840 := by
    simpa [prefixWord, tailWord_3001840, baseEnd_3001840] using wordTrace_append hprefix tailTrace_3001840
  have hstable : (prefixWord ++ tailWord_3001840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001840).length < 2 ^ (prefixWord ++ tailWord_3001840).sum := by decide
  have hdescent : baseEnd_3001840 < baseStart_3001840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001877 : List Nat := [1, 3, 2, 1, 3, 2, 2, 1, 1, 5, 2]
def baseStart_3001877 : Nat := 118140960795 + 3001877 * 2 ^ 59
def prefixEnd_3001877 : Nat := 4983230072969 + 3 ^ 40 * 3001877 * 2
def baseEnd_3001877 : Nat := 1541405766676856876132125

theorem tailTrace_3001877 : CollatzResearch.WordTrace tailWord_3001877 prefixEnd_3001877 1541405766676856876132125 := by
  unfold tailWord_3001877
  simp only [CollatzResearch.WordTrace]
  refine ⟨109487448945719783620187885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72991632630479855746791923 109487448945719783620187885)
  ·
    refine ⟨41057793354644918857570457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109487448945719783620187885 41057793354644918857570457)
    ·
      refine ⟨30793345015983689143177843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41057793354644918857570457 30793345015983689143177843)
      ·
        refine ⟨46190017523975533714766765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30793345015983689143177843 46190017523975533714766765)
        ·
          refine ⟨17321256571490825143037537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46190017523975533714766765 17321256571490825143037537)
          ·
            refine ⟨12990942428618118857278153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17321256571490825143037537 12990942428618118857278153)
            ·
              refine ⟨9743206821463589142958615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12990942428618118857278153 9743206821463589142958615)
              ·
                refine ⟨14614810232195383714437923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9743206821463589142958615 14614810232195383714437923)
                ·
                  refine ⟨21922215348293075571656885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14614810232195383714437923 21922215348293075571656885)
                  ·
                    refine ⟨2055207688902475834842833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21922215348293075571656885 2055207688902475834842833)
                    ·
                      refine ⟨1541405766676856876132125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2055207688902475834842833 1541405766676856876132125)
                      ·
                        rfl

theorem cell23_3001877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 5, 2].length) (baseStart_3001877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001877 prefixEnd_3001877 := by exact prefixLift 3001877
  have htrace : WordTrace (prefixWord ++ tailWord_3001877) baseStart_3001877 baseEnd_3001877 := by
    simpa [prefixWord, tailWord_3001877, baseEnd_3001877] using wordTrace_append hprefix tailTrace_3001877
  have hstable : (prefixWord ++ tailWord_3001877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001877).length < 2 ^ (prefixWord ++ tailWord_3001877).sum := by decide
  have hdescent : baseEnd_3001877 < baseStart_3001877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001920 : List Nat := [2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 4]
def baseStart_3001920 : Nat := 118140960795 + 3001920 * 2 ^ 59
def prefixEnd_3001920 : Nat := 4983230072969 + 3 ^ 40 * 3001920 * 2
def baseEnd_3001920 : Nat := 1541427846345000207894427

theorem tailTrace_3001920 : CollatzResearch.WordTrace tailWord_3001920 prefixEnd_3001920 1541427846345000207894427 := by
  unfold tailWord_3001920
  simp only [CollatzResearch.WordTrace]
  refine ⟨54744508642282000982001607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72992678189709334642668809 54744508642282000982001607)
  ·
    refine ⟨82116762963423001473002411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54744508642282000982001607 82116762963423001473002411)
    ·
      refine ⟨123175144445134502209503617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82116762963423001473002411 123175144445134502209503617)
      ·
        refine ⟨92381358333850876657127713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123175144445134502209503617 92381358333850876657127713)
        ·
          refine ⟨69286018750388157492845785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92381358333850876657127713 69286018750388157492845785)
          ·
            refine ⟨51964514062791118119634339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69286018750388157492845785 51964514062791118119634339)
            ·
              refine ⟨77946771094186677179451509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51964514062791118119634339 77946771094186677179451509)
              ·
                refine ⟨7307509790080000985573579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77946771094186677179451509 7307509790080000985573579)
                ·
                  refine ⟨10961264685120001478360369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7307509790080000985573579 10961264685120001478360369)
                  ·
                    refine ⟨8220948513840001108770277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10961264685120001478360369 8220948513840001108770277)
                    ·
                      refine ⟨1541427846345000207894427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8220948513840001108770277 1541427846345000207894427)
                      ·
                        rfl

theorem cell23_3001920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 4].length) (baseStart_3001920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001920 prefixEnd_3001920 := by exact prefixLift 3001920
  have htrace : WordTrace (prefixWord ++ tailWord_3001920) baseStart_3001920 baseEnd_3001920 := by
    simpa [prefixWord, tailWord_3001920, baseEnd_3001920] using wordTrace_append hprefix tailTrace_3001920
  have hstable : (prefixWord ++ tailWord_3001920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001920).length < 2 ^ (prefixWord ++ tailWord_3001920).sum := by decide
  have hdescent : baseEnd_3001920 < baseStart_3001920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001941 : List Nat := [1, 3, 2, 2, 1, 1, 1, 7, 1, 2, 2]
def baseStart_3001941 : Nat := 118140960795 + 3001941 * 2 ^ 59
def prefixEnd_3001941 : Nat := 4983230072969 + 3 ^ 40 * 3001941 * 2
def baseEnd_3001941 : Nat := 1541438629438744625731831

theorem tailTrace_3001941 : CollatzResearch.WordTrace tailWord_3001941 prefixEnd_3001941 1541438629438744625731831 := by
  unfold tailWord_3001941
  simp only [CollatzResearch.WordTrace]
  refine ⟨109489783217487922550517677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72993188811658615033678451 109489783217487922550517677)
  ·
    refine ⟨41058668706557970956444129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109489783217487922550517677 41058668706557970956444129)
    ·
      refine ⟨30794001529918478217333097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41058668706557970956444129 30794001529918478217333097)
      ·
        refine ⟨23095501147438858662999823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30794001529918478217333097 23095501147438858662999823)
        ·
          refine ⟨34643251721158287994499735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23095501147438858662999823 34643251721158287994499735)
          ·
            refine ⟨51964877581737431991749603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34643251721158287994499735 51964877581737431991749603)
            ·
              refine ⟨77947316372606147987624405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51964877581737431991749603 77947316372606147987624405)
              ·
                refine ⟨1826890227482956593459947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 77947316372606147987624405 1826890227482956593459947)
                ·
                  refine ⟨2740335341224434890189921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1826890227482956593459947 2740335341224434890189921)
                  ·
                    refine ⟨2055251505918326167642441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2740335341224434890189921 2055251505918326167642441)
                    ·
                      refine ⟨1541438629438744625731831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2055251505918326167642441 1541438629438744625731831)
                      ·
                        rfl

theorem cell23_3001941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_3001941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001941 prefixEnd_3001941 := by exact prefixLift 3001941
  have htrace : WordTrace (prefixWord ++ tailWord_3001941) baseStart_3001941 baseEnd_3001941 := by
    simpa [prefixWord, tailWord_3001941, baseEnd_3001941] using wordTrace_append hprefix tailTrace_3001941
  have hstable : (prefixWord ++ tailWord_3001941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001941).length < 2 ^ (prefixWord ++ tailWord_3001941).sum := by decide
  have hdescent : baseEnd_3001941 < baseStart_3001941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001974 : List Nat := [5, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3]
def baseStart_3001974 : Nat := 118140960795 + 3001974 * 2 ^ 59
def prefixEnd_3001974 : Nat := 4983230072969 + 3 ^ 40 * 3001974 * 2
def baseEnd_3001974 : Nat := 1541455574300342996619179

theorem tailTrace_3001974 : CollatzResearch.WordTrace tailWord_3001974 prefixEnd_3001974 1541455574300342996619179 := by
  unfold tailWord_3001974
  simp only [CollatzResearch.WordTrace]
  refine ⟨6843186676648023074154311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72993991217578912790979317 6843186676648023074154311)
  ·
    refine ⟨10264780014972034611231467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6843186676648023074154311 10264780014972034611231467)
    ·
      refine ⟨15397170022458051916847201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10264780014972034611231467 15397170022458051916847201)
      ·
        refine ⟨11547877516843538937635401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15397170022458051916847201 11547877516843538937635401)
        ·
          refine ⟨8660908137632654203226551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11547877516843538937635401 8660908137632654203226551)
          ·
            refine ⟨12991362206448981304839827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8660908137632654203226551 12991362206448981304839827)
            ·
              refine ⟨19487043309673471957259741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12991362206448981304839827 19487043309673471957259741)
              ·
                refine ⟨7307641241127551983972403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19487043309673471957259741 7307641241127551983972403)
                ·
                  refine ⟨10961461861691327975958605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7307641241127551983972403 10961461861691327975958605)
                  ·
                    refine ⟨4110548198134247990984477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10961461861691327975958605 4110548198134247990984477)
                    ·
                      refine ⟨1541455574300342996619179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4110548198134247990984477 1541455574300342996619179)
                      ·
                        rfl

theorem cell23_3001974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_3001974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001974 prefixEnd_3001974 := by exact prefixLift 3001974
  have htrace : WordTrace (prefixWord ++ tailWord_3001974) baseStart_3001974 baseEnd_3001974 := by
    simpa [prefixWord, tailWord_3001974, baseEnd_3001974] using wordTrace_append hprefix tailTrace_3001974
  have hstable : (prefixWord ++ tailWord_3001974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001974).length < 2 ^ (prefixWord ++ tailWord_3001974).sum := by decide
  have hdescent : baseEnd_3001974 < baseStart_3001974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001980 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 4, 3, 4]
def baseStart_3001980 : Nat := 118140960795 + 3001980 * 2 ^ 59
def prefixEnd_3001980 : Nat := 4983230072969 + 3 ^ 40 * 3001980 * 2
def baseEnd_3001980 : Nat := 1541458655184269973144151

theorem tailTrace_3001980 : CollatzResearch.WordTrace tailWord_3001980 prefixEnd_3001980 1541458655184269973144151 := by
  unfold tailWord_3001980
  simp only [CollatzResearch.WordTrace]
  refine ⟨54745602832173316105593697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72994137109564421474124929 54745602832173316105593697)
  ·
    refine ⟨41059202124129987079195273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54745602832173316105593697 41059202124129987079195273)
    ·
      refine ⟨30794401593097490309396455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41059202124129987079195273 30794401593097490309396455)
      ·
        refine ⟨46191602389646235464094683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30794401593097490309396455 46191602389646235464094683)
        ·
          refine ⟨69287403584469353196142025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46191602389646235464094683 69287403584469353196142025)
          ·
            refine ⟨51965552688352014897106519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69287403584469353196142025 51965552688352014897106519)
            ·
              refine ⟨77948329032528022345659779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51965552688352014897106519 77948329032528022345659779)
              ·
                refine ⟨116922493548792033518489669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77948329032528022345659779 116922493548792033518489669)
                ·
                  refine ⟨21922967540398506284716813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116922493548792033518489669 21922967540398506284716813)
                  ·
                    refine ⟨8221112827649439856768805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21922967540398506284716813 8221112827649439856768805)
                    ·
                      refine ⟨1541458655184269973144151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8221112827649439856768805 1541458655184269973144151)
                      ·
                        rfl

theorem cell23_3001980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_3001980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001980 prefixEnd_3001980 := by exact prefixLift 3001980
  have htrace : WordTrace (prefixWord ++ tailWord_3001980) baseStart_3001980 baseEnd_3001980 := by
    simpa [prefixWord, tailWord_3001980, baseEnd_3001980] using wordTrace_append hprefix tailTrace_3001980
  have hstable : (prefixWord ++ tailWord_3001980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001980).length < 2 ^ (prefixWord ++ tailWord_3001980).sum := by decide
  have hdescent : baseEnd_3001980 < baseStart_3001980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001984 : List Nat := [2, 1, 1, 2, 1, 4, 2, 4, 1, 3, 2]
def baseStart_3001984 : Nat := 118140960795 + 3001984 * 2 ^ 59
def prefixEnd_3001984 : Nat := 4983230072969 + 3 ^ 40 * 3001984 * 2
def baseEnd_3001984 : Nat := 1541460709106887957494133

theorem tailTrace_3001984 : CollatzResearch.WordTrace tailWord_3001984 prefixEnd_3001984 1541460709106887957494133 := by
  unfold tailWord_3001984
  simp only [CollatzResearch.WordTrace]
  refine ⟨54745675778166070447166503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72994234370888093929555337 54745675778166070447166503)
  ·
    refine ⟨82118513667249105670749755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54745675778166070447166503 82118513667249105670749755)
    ·
      refine ⟨123177770500873658506124633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82118513667249105670749755 123177770500873658506124633)
      ·
        refine ⟨92383327875655243879593475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123177770500873658506124633 92383327875655243879593475)
        ·
          refine ⟨138574991813482865819390213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92383327875655243879593475 138574991813482865819390213)
          ·
            refine ⟨25982810965028037341135665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138574991813482865819390213 25982810965028037341135665)
            ·
              refine ⟨19487108223771028005851749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25982810965028037341135665 19487108223771028005851749)
              ·
                refine ⟨3653832791957067751097203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19487108223771028005851749 3653832791957067751097203)
                ·
                  refine ⟨5480749187935601626645805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3653832791957067751097203 5480749187935601626645805)
                  ·
                    refine ⟨2055280945475850609992177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5480749187935601626645805 2055280945475850609992177)
                    ·
                      refine ⟨1541460709106887957494133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2055280945475850609992177 1541460709106887957494133)
                      ·
                        rfl

theorem cell23_3001984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 1, 3, 2].length) (baseStart_3001984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3001984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3001984 prefixEnd_3001984 := by exact prefixLift 3001984
  have htrace : WordTrace (prefixWord ++ tailWord_3001984) baseStart_3001984 baseEnd_3001984 := by
    simpa [prefixWord, tailWord_3001984, baseEnd_3001984] using wordTrace_append hprefix tailTrace_3001984
  have hstable : (prefixWord ++ tailWord_3001984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001984).length < 2 ^ (prefixWord ++ tailWord_3001984).sum := by decide
  have hdescent : baseEnd_3001984 < baseStart_3001984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002000 : List Nat := [2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 5]
def baseStart_3002000 : Nat := 118140960795 + 3002000 * 2 ^ 59
def prefixEnd_3002000 : Nat := 4983230072969 + 3 ^ 40 * 3002000 * 2
def baseEnd_3002000 : Nat := 1541468924797359894894059

theorem tailTrace_3002000 : CollatzResearch.WordTrace tailWord_3002000 prefixEnd_3002000 1541468924797359894894059 := by
  unfold tailWord_3002000
  simp only [CollatzResearch.WordTrace]
  refine ⟨54745967562137087813457727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72994623416182783751276969 54745967562137087813457727)
  ·
    refine ⟨82118951343205631720186591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54745967562137087813457727 82118951343205631720186591)
    ·
      refine ⟨123178427014808447580279887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82118951343205631720186591 123178427014808447580279887)
      ·
        refine ⟨184767640522212671370419831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123178427014808447580279887 184767640522212671370419831)
        ·
          refine ⟨277151460783319007055629747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184767640522212671370419831 277151460783319007055629747)
          ·
            refine ⟨415727191174978510583444621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277151460783319007055629747 415727191174978510583444621)
            ·
              refine ⟨155897696690616941468791733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 415727191174978510583444621 155897696690616941468791733)
              ·
                refine ⟨14615409064745338262699225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 155897696690616941468791733 14615409064745338262699225)
                ·
                  refine ⟨10961556798559003697024419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14615409064745338262699225 10961556798559003697024419)
                  ·
                    refine ⟨16442335197838505545536629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10961556798559003697024419 16442335197838505545536629)
                    ·
                      refine ⟨1541468924797359894894059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16442335197838505545536629 1541468924797359894894059)
                      ·
                        rfl

theorem cell23_3002000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 5].length) (baseStart_3002000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002000 prefixEnd_3002000 := by exact prefixLift 3002000
  have htrace : WordTrace (prefixWord ++ tailWord_3002000) baseStart_3002000 baseEnd_3002000 := by
    simpa [prefixWord, tailWord_3002000, baseEnd_3002000] using wordTrace_append hprefix tailTrace_3002000
  have hstable : (prefixWord ++ tailWord_3002000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002000).length < 2 ^ (prefixWord ++ tailWord_3002000).sum := by decide
  have hdescent : baseEnd_3002000 < baseStart_3002000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002124 : List Nat := [2, 2, 1, 2, 2, 1, 4, 2, 2, 2, 3]
def baseStart_3002124 : Nat := 118140960795 + 3002124 * 2 ^ 59
def prefixEnd_3002124 : Nat := 4983230072969 + 3 ^ 40 * 3002124 * 2
def baseEnd_3002124 : Nat := 1541532596398517409743489

theorem tailTrace_3002124 : CollatzResearch.WordTrace tailWord_3002124 prefixEnd_3002124 1541532596398517409743489 := by
  unfold tailWord_3002124
  simp only [CollatzResearch.WordTrace]
  refine ⟨54748228887912472402214713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72997638517216629869619617 54748228887912472402214713)
  ·
    refine ⟨41061171665934354301661035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54748228887912472402214713 41061171665934354301661035)
    ·
      refine ⟨61591757498901531452491553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41061171665934354301661035 61591757498901531452491553)
      ·
        refine ⟨46193818124176148589368665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61591757498901531452491553 46193818124176148589368665)
        ·
          refine ⟨34645363593132111442026499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46193818124176148589368665 34645363593132111442026499)
          ·
            refine ⟨51968045389698167163039749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34645363593132111442026499 51968045389698167163039749)
            ·
              refine ⟨9744008510568406343069953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51968045389698167163039749 9744008510568406343069953)
              ·
                refine ⟨7308006382926304757302465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9744008510568406343069953 7308006382926304757302465)
                ·
                  refine ⟨5481004787194728567976849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7308006382926304757302465 5481004787194728567976849)
                  ·
                    refine ⟨4110753590396046425982637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5481004787194728567976849 4110753590396046425982637)
                    ·
                      refine ⟨1541532596398517409743489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4110753590396046425982637 1541532596398517409743489)
                      ·
                        rfl

theorem cell23_3002124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_3002124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002124 prefixEnd_3002124 := by exact prefixLift 3002124
  have htrace : WordTrace (prefixWord ++ tailWord_3002124) baseStart_3002124 baseEnd_3002124 := by
    simpa [prefixWord, tailWord_3002124, baseEnd_3002124] using wordTrace_append hprefix tailTrace_3002124
  have hstable : (prefixWord ++ tailWord_3002124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002124).length < 2 ^ (prefixWord ++ tailWord_3002124).sum := by decide
  have hdescent : baseEnd_3002124 < baseStart_3002124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002188 : List Nat := [2, 2, 1, 3, 4, 1, 2, 1, 3, 1, 3]
def baseStart_3002188 : Nat := 118140960795 + 3002188 * 2 ^ 59
def prefixEnd_3002188 : Nat := 4983230072969 + 3 ^ 40 * 3002188 * 2
def baseEnd_3002188 : Nat := 1541565459160405159343195

theorem tailTrace_3002188 : CollatzResearch.WordTrace tailWord_3002188 prefixEnd_3002188 1541565459160405159343195 := by
  unfold tailWord_3002188
  simp only [CollatzResearch.WordTrace]
  refine ⟨54749396023796541867379609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72999194698395389156506145 54749396023796541867379609)
  ·
    refine ⟨41062047017847406400534707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54749396023796541867379609 41062047017847406400534707)
    ·
      refine ⟨61593070526771109600802061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41062047017847406400534707 61593070526771109600802061)
      ·
        refine ⟨23097401447539166100300773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61593070526771109600802061 23097401447539166100300773)
        ·
          refine ⟨4330762771413593643806395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23097401447539166100300773 4330762771413593643806395)
          ·
            refine ⟨6496144157120390465709593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4330762771413593643806395 6496144157120390465709593)
            ·
              refine ⟨4872108117840292849282195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6496144157120390465709593 4872108117840292849282195)
              ·
                refine ⟨7308162176760439273923293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4872108117840292849282195 7308162176760439273923293)
                ·
                  refine ⟨2740560816285164727721235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7308162176760439273923293 2740560816285164727721235)
                  ·
                    refine ⟨4110841224427747091581853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2740560816285164727721235 4110841224427747091581853)
                    ·
                      refine ⟨1541565459160405159343195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4110841224427747091581853 1541565459160405159343195)
                      ·
                        rfl

theorem cell23_3002188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_3002188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002188 prefixEnd_3002188 := by exact prefixLift 3002188
  have htrace : WordTrace (prefixWord ++ tailWord_3002188) baseStart_3002188 baseEnd_3002188 := by
    simpa [prefixWord, tailWord_3002188, baseEnd_3002188] using wordTrace_append hprefix tailTrace_3002188
  have hstable : (prefixWord ++ tailWord_3002188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002188).length < 2 ^ (prefixWord ++ tailWord_3002188).sum := by decide
  have hdescent : baseEnd_3002188 < baseStart_3002188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002222 : List Nat := [4, 1, 2, 3, 1, 3, 1, 3, 1, 1, 3]
def baseStart_3002222 : Nat := 118140960795 + 3002222 * 2 ^ 59
def prefixEnd_3002222 : Nat := 4983230072969 + 3 ^ 40 * 3002222 * 2
def baseEnd_3002222 : Nat := 1541582917502658026318039

theorem tailTrace_3002222 : CollatzResearch.WordTrace tailWord_3002222 prefixEnd_3002222 1541582917502658026318039 := by
  unfold tailWord_3002222
  simp only [CollatzResearch.WordTrace]
  refine ⟨13687504016183738442687115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73000021419646605027664613 13687504016183738442687115)
  ·
    refine ⟨20531256024275607664030673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13687504016183738442687115 20531256024275607664030673)
    ·
      refine ⟨15398442018206705748023005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20531256024275607664030673 15398442018206705748023005)
      ·
        refine ⟨5774415756827514655508627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15398442018206705748023005 5774415756827514655508627)
        ·
          refine ⟨8661623635241271983262941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5774415756827514655508627 8661623635241271983262941)
          ·
            refine ⟨3248108863215476993723603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8661623635241271983262941 3248108863215476993723603)
            ·
              refine ⟨4872163294823215490585405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3248108863215476993723603 4872163294823215490585405)
              ·
                refine ⟨1827061235558705808969527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4872163294823215490585405 1827061235558705808969527)
                ·
                  refine ⟨2740591853338058713454291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1827061235558705808969527 2740591853338058713454291)
                  ·
                    refine ⟨4110887780007088070181437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2740591853338058713454291 4110887780007088070181437)
                    ·
                      refine ⟨1541582917502658026318039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4110887780007088070181437 1541582917502658026318039)
                      ·
                        rfl

theorem cell23_3002222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_3002222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002222 prefixEnd_3002222 := by exact prefixLift 3002222
  have htrace : WordTrace (prefixWord ++ tailWord_3002222) baseStart_3002222 baseEnd_3002222 := by
    simpa [prefixWord, tailWord_3002222, baseEnd_3002222] using wordTrace_append hprefix tailTrace_3002222
  have hstable : (prefixWord ++ tailWord_3002222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002222).length < 2 ^ (prefixWord ++ tailWord_3002222).sum := by decide
  have hdescent : baseEnd_3002222 < baseStart_3002222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002238 : List Nat := [4, 2, 3, 1, 1, 1, 2, 1, 4, 4]
def baseStart_3002238 : Nat := 118140960795 + 3002238 * 2 ^ 59
def prefixEnd_3002238 : Nat := 4983230072969 + 3 ^ 40 * 3002238 * 2
def baseEnd_3002238 : Nat := 513863711064376654572655

theorem tailTrace_3002238 : CollatzResearch.WordTrace tailWord_3002238 prefixEnd_3002238 513863711064376654572655 := by
  unfold tailWord_3002238
  simp only [CollatzResearch.WordTrace]
  refine ⟨13687576962176492784259921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73000410464941294849386245 13687576962176492784259921)
  ·
    refine ⟨10265682721632369588194941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13687576962176492784259921 10265682721632369588194941)
    ·
      refine ⟨3849631020612138595573103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10265682721632369588194941 3849631020612138595573103)
      ·
        refine ⟨5774446530918207893359655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3849631020612138595573103 5774446530918207893359655)
        ·
          refine ⟨8661669796377311840039483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5774446530918207893359655 8661669796377311840039483)
          ·
            refine ⟨12992504694565967760059225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8661669796377311840039483 12992504694565967760059225)
            ·
              refine ⟨9744378520924475820044419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12992504694565967760059225 9744378520924475820044419)
              ·
                refine ⟨14616567781386713730066629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9744378520924475820044419 14616567781386713730066629)
                ·
                  refine ⟨2740606459010008824387493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14616567781386713730066629 2740606459010008824387493)
                  ·
                    refine ⟨513863711064376654572655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2740606459010008824387493 513863711064376654572655)
                    ·
                      rfl

theorem cell23_3002238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_3002238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002238 prefixEnd_3002238 := by exact prefixLift 3002238
  have htrace : WordTrace (prefixWord ++ tailWord_3002238) baseStart_3002238 baseEnd_3002238 := by
    simpa [prefixWord, tailWord_3002238, baseEnd_3002238] using wordTrace_append hprefix tailTrace_3002238
  have hstable : (prefixWord ++ tailWord_3002238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002238).length < 2 ^ (prefixWord ++ tailWord_3002238).sum := by decide
  have hdescent : baseEnd_3002238 < baseStart_3002238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002304 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 3]
def baseStart_3002304 : Nat := 118140960795 + 3002304 * 2 ^ 59
def prefixEnd_3002304 : Nat := 4983230072969 + 3 ^ 40 * 3002304 * 2
def baseEnd_3002304 : Nat := 1541625022916326705492661

theorem tailTrace_3002304 : CollatzResearch.WordTrace tailWord_3002304 prefixEnd_3002304 1541625022916326705492661 := by
  unfold tailWord_3002304
  simp only [CollatzResearch.WordTrace]
  refine ⟨54751511457586417772990983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73002015276781890363987977 54751511457586417772990983)
  ·
    refine ⟨82127267186379626659486475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54751511457586417772990983 82127267186379626659486475)
    ·
      refine ⟨123190900779569439989229713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82127267186379626659486475 123190900779569439989229713)
      ·
        refine ⟨92393175584677079991922285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123190900779569439989229713 92393175584677079991922285)
        ·
          refine ⟨34647440844253904996970857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92393175584677079991922285 34647440844253904996970857)
          ·
            refine ⟨25985580633190428747728143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34647440844253904996970857 25985580633190428747728143)
            ·
              refine ⟨38978370949785643121592215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25985580633190428747728143 38978370949785643121592215)
              ·
                refine ⟨58467556424678464682388323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38978370949785643121592215 58467556424678464682388323)
                ·
                  refine ⟨87701334637017697023582485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58467556424678464682388323 87701334637017697023582485)
                  ·
                    refine ⟨4111000061110204547980429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 87701334637017697023582485 4111000061110204547980429)
                    ·
                      refine ⟨1541625022916326705492661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4111000061110204547980429 1541625022916326705492661)
                      ·
                        rfl

theorem cell23_3002304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 3].length) (baseStart_3002304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002304 prefixEnd_3002304 := by exact prefixLift 3002304
  have htrace : WordTrace (prefixWord ++ tailWord_3002304) baseStart_3002304 baseEnd_3002304 := by
    simpa [prefixWord, tailWord_3002304, baseEnd_3002304] using wordTrace_append hprefix tailTrace_3002304
  have hstable : (prefixWord ++ tailWord_3002304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002304).length < 2 ^ (prefixWord ++ tailWord_3002304).sum := by decide
  have hdescent : baseEnd_3002304 < baseStart_3002304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002314 : List Nat := [3, 1, 2, 1, 2, 1, 3, 1, 1, 4, 4]
def baseStart_3002314 : Nat := 118140960795 + 3002314 * 2 ^ 59
def prefixEnd_3002314 : Nat := 4983230072969 + 3 ^ 40 * 3002314 * 2
def baseEnd_3002314 : Nat := 1541630157722871666367615

theorem tailTrace_3002314 : CollatzResearch.WordTrace tailWord_3002314 prefixEnd_3002314 1541630157722871666367615 := by
  unfold tailWord_3002314
  simp only [CollatzResearch.WordTrace]
  refine ⟨27375846911284151813461499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73002258430091071502563997 27375846911284151813461499)
  ·
    refine ⟨41063770366926227720192249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27375846911284151813461499 41063770366926227720192249)
    ·
      refine ⟨30797827775194670790144187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41063770366926227720192249 30797827775194670790144187)
      ·
        refine ⟨46196741662792006185216281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30797827775194670790144187 46196741662792006185216281)
        ·
          refine ⟨34647556247094004638912211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46196741662792006185216281 34647556247094004638912211)
          ·
            refine ⟨51971334370641006958368317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34647556247094004638912211 51971334370641006958368317)
            ·
              refine ⟨19489250388990377609388119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51971334370641006958368317 19489250388990377609388119)
              ·
                refine ⟨29233875583485566414082179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19489250388990377609388119 29233875583485566414082179)
                ·
                  refine ⟨43850813375228349621123269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29233875583485566414082179 43850813375228349621123269)
                  ·
                    refine ⟨8222027507855315553960613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43850813375228349621123269 8222027507855315553960613)
                    ·
                      refine ⟨1541630157722871666367615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8222027507855315553960613 1541630157722871666367615)
                      ·
                        rfl

theorem cell23_3002314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_3002314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002314 prefixEnd_3002314 := by exact prefixLift 3002314
  have htrace : WordTrace (prefixWord ++ tailWord_3002314) baseStart_3002314 baseEnd_3002314 := by
    simpa [prefixWord, tailWord_3002314, baseEnd_3002314] using wordTrace_append hprefix tailTrace_3002314
  have hstable : (prefixWord ++ tailWord_3002314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002314).length < 2 ^ (prefixWord ++ tailWord_3002314).sum := by decide
  have hdescent : baseEnd_3002314 < baseStart_3002314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002318 : List Nat := [4, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2]
def baseStart_3002318 : Nat := 118140960795 + 3002318 * 2 ^ 59
def prefixEnd_3002318 : Nat := 4983230072969 + 3 ^ 40 * 3002318 * 2
def baseEnd_3002318 : Nat := 1541632211645489650717597

theorem tailTrace_3002318 : CollatzResearch.WordTrace tailWord_3002318 prefixEnd_3002318 1541632211645489650717597 := by
  unfold tailWord_3002318
  simp only [CollatzResearch.WordTrace]
  refine ⟨13687941692140264492123951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73002355691414743957994405 13687941692140264492123951)
  ·
    refine ⟨20531912538210396738185927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13687941692140264492123951 20531912538210396738185927)
    ·
      refine ⟨30797868807315595107278891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20531912538210396738185927 30797868807315595107278891)
      ·
        refine ⟨46196803210973392660918337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30797868807315595107278891 46196803210973392660918337)
        ·
          refine ⟨34647602408230044495688753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46196803210973392660918337 34647602408230044495688753)
          ·
            refine ⟨25985701806172533371766565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34647602408230044495688753 25985701806172533371766565)
            ·
              refine ⟨4872319088657350007206231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25985701806172533371766565 4872319088657350007206231)
              ·
                refine ⟨7308478632986025010809347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4872319088657350007206231 7308478632986025010809347)
                ·
                  refine ⟨10962717949479037516214021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7308478632986025010809347 10962717949479037516214021)
                  ·
                    refine ⟨2055509615527319534290129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10962717949479037516214021 2055509615527319534290129)
                    ·
                      refine ⟨1541632211645489650717597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2055509615527319534290129 1541632211645489650717597)
                      ·
                        rfl

theorem cell23_3002318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2].length) (baseStart_3002318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002318 prefixEnd_3002318 := by exact prefixLift 3002318
  have htrace : WordTrace (prefixWord ++ tailWord_3002318) baseStart_3002318 baseEnd_3002318 := by
    simpa [prefixWord, tailWord_3002318, baseEnd_3002318] using wordTrace_append hprefix tailTrace_3002318
  have hstable : (prefixWord ++ tailWord_3002318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002318).length < 2 ^ (prefixWord ++ tailWord_3002318).sum := by decide
  have hdescent : baseEnd_3002318 < baseStart_3002318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002358 : List Nat := [5, 1, 1, 1, 4, 1, 2, 1, 7]
def baseStart_3002358 : Nat := 118140960795 + 3002358 * 2 ^ 59
def prefixEnd_3002358 : Nat := 4983230072969 + 3 ^ 40 * 3002358 * 2
def baseEnd_3002358 : Nat := 171294750096852166024157

theorem tailTrace_3002358 : CollatzResearch.WordTrace tailWord_3002358 prefixEnd_3002358 171294750096852166024157 := by
  unfold tailWord_3002358
  simp only [CollatzResearch.WordTrace]
  refine ⟨6844062028561075173027983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73003328304651468512298485 6844062028561075173027983)
  ·
    refine ⟨10266093042841612759541975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6844062028561075173027983 10266093042841612759541975)
    ·
      refine ⟨15399139564262419139312963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10266093042841612759541975 15399139564262419139312963)
      ·
        refine ⟨23098709346393628708969445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15399139564262419139312963 23098709346393628708969445)
        ·
          refine ⟨4331008002448805382931771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23098709346393628708969445 4331008002448805382931771)
          ·
            refine ⟨6496512003673208074397657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4331008002448805382931771 6496512003673208074397657)
            ·
              refine ⟨4872384002754906055798243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6496512003673208074397657 4872384002754906055798243)
              ·
                refine ⟨7308576004132359083697365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4872384002754906055798243 7308576004132359083697365)
                ·
                  refine ⟨171294750096852166024157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7308576004132359083697365 171294750096852166024157)
                  ·
                    rfl

theorem cell23_3002358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_3002358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002358 prefixEnd_3002358 := by exact prefixLift 3002358
  have htrace : WordTrace (prefixWord ++ tailWord_3002358) baseStart_3002358 baseEnd_3002358 := by
    simpa [prefixWord, tailWord_3002358, baseEnd_3002358] using wordTrace_append hprefix tailTrace_3002358
  have hstable : (prefixWord ++ tailWord_3002358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002358).length < 2 ^ (prefixWord ++ tailWord_3002358).sum := by decide
  have hdescent : baseEnd_3002358 < baseStart_3002358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002364 : List Nat := [2, 2, 2, 1, 2, 2, 2, 1, 1, 1, 7]
def baseStart_3002364 : Nat := 118140960795 + 3002364 * 2 ^ 59
def prefixEnd_3002364 : Nat := 4983230072969 + 3 ^ 40 * 3002364 * 2
def baseEnd_3002364 : Nat := 1541655831755596470742385

theorem tailTrace_3002364 : CollatzResearch.WordTrace tailWord_3002364 prefixEnd_3002364 1541655831755596470742385 := by
  unfold tailWord_3002364
  simp only [CollatzResearch.WordTrace]
  refine ⟨54752605647477732896583073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73003474196636977195444097 54752605647477732896583073)
  ·
    refine ⟨41064454235608299672437305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54752605647477732896583073 41064454235608299672437305)
    ·
      refine ⟨30798340676706224754327979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41064454235608299672437305 30798340676706224754327979)
      ·
        refine ⟨46197511015059337131491969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30798340676706224754327979 46197511015059337131491969)
        ·
          refine ⟨34648133261294502848618977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46197511015059337131491969 34648133261294502848618977)
          ·
            refine ⟨25986099945970877136464233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34648133261294502848618977 25986099945970877136464233)
            ·
              refine ⟨19489574959478157852348175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25986099945970877136464233 19489574959478157852348175)
              ·
                refine ⟨29234362439217236778522263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19489574959478157852348175 29234362439217236778522263)
                ·
                  refine ⟨43851543658825855167783395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29234362439217236778522263 43851543658825855167783395)
                  ·
                    refine ⟨65777315488238782751675093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43851543658825855167783395 65777315488238782751675093)
                    ·
                      refine ⟨1541655831755596470742385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 65777315488238782751675093 1541655831755596470742385)
                      ·
                        rfl

theorem cell23_3002364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_3002364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002364 prefixEnd_3002364 := by exact prefixLift 3002364
  have htrace : WordTrace (prefixWord ++ tailWord_3002364) baseStart_3002364 baseEnd_3002364 := by
    simpa [prefixWord, tailWord_3002364, baseEnd_3002364] using wordTrace_append hprefix tailTrace_3002364
  have hstable : (prefixWord ++ tailWord_3002364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002364).length < 2 ^ (prefixWord ++ tailWord_3002364).sum := by decide
  have hdescent : baseEnd_3002364 < baseStart_3002364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002418 : List Nat := [3, 2, 1, 1, 2, 3, 3, 1, 3, 4]
def baseStart_3002418 : Nat := 118140960795 + 3002418 * 2 ^ 59
def prefixEnd_3002418 : Nat := 4983230072969 + 3 ^ 40 * 3002418 * 2
def baseEnd_3002418 : Nat := 513894519903646419822379

theorem tailTrace_3002418 : CollatzResearch.WordTrace tailWord_3002418 prefixEnd_3002418 513894519903646419822379 := by
  unfold tailWord_3002418
  simp only [CollatzResearch.WordTrace]
  refine ⟨27376795209189958253907977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73004787224506555343754605 27376795209189958253907977)
  ·
    refine ⟨20532596406892468690430983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27376795209189958253907977 20532596406892468690430983)
    ·
      refine ⟨30798894610338703035646475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20532596406892468690430983 30798894610338703035646475)
      ·
        refine ⟨46198341915508054553469713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30798894610338703035646475 46198341915508054553469713)
        ·
          refine ⟨34648756436631040915102285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46198341915508054553469713 34648756436631040915102285)
          ·
            refine ⟨12993283663736640343163357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34648756436631040915102285 12993283663736640343163357)
            ·
              refine ⟨4872481373901240128686259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12993283663736640343163357 4872481373901240128686259)
              ·
                refine ⟨7308722060851860193029389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4872481373901240128686259 7308722060851860193029389)
                ·
                  refine ⟨2740770772819447572386021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7308722060851860193029389 2740770772819447572386021)
                  ·
                    refine ⟨513894519903646419822379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2740770772819447572386021 513894519903646419822379)
                    ·
                      rfl

theorem cell23_3002418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_3002418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002418 prefixEnd_3002418 := by exact prefixLift 3002418
  have htrace : WordTrace (prefixWord ++ tailWord_3002418) baseStart_3002418 baseEnd_3002418 := by
    simpa [prefixWord, tailWord_3002418, baseEnd_3002418] using wordTrace_append hprefix tailTrace_3002418
  have hstable : (prefixWord ++ tailWord_3002418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002418).length < 2 ^ (prefixWord ++ tailWord_3002418).sum := by decide
  have hdescent : baseEnd_3002418 < baseStart_3002418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002445 : List Nat := [1, 6, 1, 1, 1, 1, 4, 1, 2, 2, 3]
def baseStart_3002445 : Nat := 118140960795 + 3002445 * 2 ^ 59
def prefixEnd_3002445 : Nat := 4983230072969 + 3 ^ 40 * 3002445 * 2
def baseEnd_3002445 : Nat := 1541697423688610653829513

theorem tailTrace_3002445 : CollatzResearch.WordTrace tailWord_3002445 prefixEnd_3002445 1541697423688610653829513 := by
  unfold tailWord_3002445
  simp only [CollatzResearch.WordTrace]
  refine ⟨109508165607662016626864789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73005443738441344417909859 109508165607662016626864789)
  ·
    refine ⟨5133195262859157029384287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 109508165607662016626864789 5133195262859157029384287)
    ·
      refine ⟨7699792894288735544076431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5133195262859157029384287 7699792894288735544076431)
      ·
        refine ⟨11549689341433103316114647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7699792894288735544076431 11549689341433103316114647)
        ·
          refine ⟨17324534012149654974171971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11549689341433103316114647 17324534012149654974171971)
          ·
            refine ⟨25986801018224482461257957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17324534012149654974171971 25986801018224482461257957)
            ·
              refine ⟨4872525190917090461485867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25986801018224482461257957 4872525190917090461485867)
              ·
                refine ⟨7308787786375635692228801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4872525190917090461485867 7308787786375635692228801)
                ·
                  refine ⟨5481590839781726769171601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7308787786375635692228801 5481590839781726769171601)
                  ·
                    refine ⟨4111193129836295076878701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5481590839781726769171601 4111193129836295076878701)
                    ·
                      refine ⟨1541697423688610653829513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4111193129836295076878701 1541697423688610653829513)
                      ·
                        rfl

theorem cell23_3002445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_3002445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002445 prefixEnd_3002445 := by exact prefixLift 3002445
  have htrace : WordTrace (prefixWord ++ tailWord_3002445) baseStart_3002445 baseEnd_3002445 := by
    simpa [prefixWord, tailWord_3002445, baseEnd_3002445] using wordTrace_append hprefix tailTrace_3002445
  have hstable : (prefixWord ++ tailWord_3002445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002445).length < 2 ^ (prefixWord ++ tailWord_3002445).sum := by decide
  have hdescent : baseEnd_3002445 < baseStart_3002445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002481 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 5, 1, 4]
def baseStart_3002481 : Nat := 118140960795 + 3002481 * 2 ^ 59
def prefixEnd_3002481 : Nat := 4983230072969 + 3 ^ 40 * 3002481 * 2
def baseEnd_3002481 : Nat := 1541715908992172512979347

theorem tailTrace_3002481 : CollatzResearch.WordTrace tailWord_3002481 prefixEnd_3002481 1541715908992172512979347 := by
  unfold tailWord_3002481
  simp only [CollatzResearch.WordTrace]
  refine ⟨109509478635531594775175297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73006319090354396516783531 109509478635531594775175297)
  ·
    refine ⟨82132108976648696081381473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109509478635531594775175297 82132108976648696081381473)
    ·
      refine ⟨61599081732486522061036105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82132108976648696081381473 61599081732486522061036105)
      ·
        refine ⟨46199311299364891545777079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61599081732486522061036105 46199311299364891545777079)
        ·
          refine ⟨69298966949047337318665619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46199311299364891545777079 69298966949047337318665619)
          ·
            refine ⟨103948450423571005977998429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69298966949047337318665619 103948450423571005977998429)
            ·
              refine ⟨38980668908839127241749411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103948450423571005977998429 38980668908839127241749411)
              ·
                refine ⟨58471003363258690862624117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38980668908839127241749411 58471003363258690862624117)
                ·
                  refine ⟨5481656565305502268371011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58471003363258690862624117 5481656565305502268371011)
                  ·
                    refine ⟨8222484847958253402556517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5481656565305502268371011 8222484847958253402556517)
                    ·
                      refine ⟨1541715908992172512979347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8222484847958253402556517 1541715908992172512979347)
                      ·
                        rfl

theorem cell23_3002481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_3002481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002481 prefixEnd_3002481 := by exact prefixLift 3002481
  have htrace : WordTrace (prefixWord ++ tailWord_3002481) baseStart_3002481 baseEnd_3002481 := by
    simpa [prefixWord, tailWord_3002481, baseEnd_3002481] using wordTrace_append hprefix tailTrace_3002481
  have hstable : (prefixWord ++ tailWord_3002481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002481).length < 2 ^ (prefixWord ++ tailWord_3002481).sum := by decide
  have hdescent : baseEnd_3002481 < baseStart_3002481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002491 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 8, 4]
def baseStart_3002491 : Nat := 118140960795 + 3002491 * 2 ^ 59
def prefixEnd_3002491 : Nat := 4983230072969 + 3 ^ 40 * 3002491 * 2
def baseEnd_3002491 : Nat := 513907014599572491284767

theorem tailTrace_3002491 : CollatzResearch.WordTrace tailWord_3002491 prefixEnd_3002491 513907014599572491284767 := by
  unfold tailWord_3002491
  simp only [CollatzResearch.WordTrace]
  refine ⟨109509843365495366483039327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73006562243663577655359551 109509843365495366483039327)
  ·
    refine ⟨164264765048243049724558991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109509843365495366483039327 164264765048243049724558991)
    ·
      refine ⟨246397147572364574586838487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164264765048243049724558991 246397147572364574586838487)
      ·
        refine ⟨369595721358546861880257731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246397147572364574586838487 369595721358546861880257731)
        ·
          refine ⟨554393582037820292820386597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369595721358546861880257731 554393582037820292820386597)
          ·
            refine ⟨103948796632091304903822487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 554393582037820292820386597 103948796632091304903822487)
            ·
              refine ⟨155923194948136957355733731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103948796632091304903822487 155923194948136957355733731)
              ·
                refine ⟨233884792422205436033600597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155923194948136957355733731 233884792422205436033600597)
                ·
                  refine ⟨2740837411197719953518757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 233884792422205436033600597 2740837411197719953518757)
                  ·
                    refine ⟨513907014599572491284767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2740837411197719953518757 513907014599572491284767)
                    ·
                      rfl

theorem cell23_3002491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 8, 4].length) (baseStart_3002491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002491 prefixEnd_3002491 := by exact prefixLift 3002491
  have htrace : WordTrace (prefixWord ++ tailWord_3002491) baseStart_3002491 baseEnd_3002491 := by
    simpa [prefixWord, tailWord_3002491, baseEnd_3002491] using wordTrace_append hprefix tailTrace_3002491
  have hstable : (prefixWord ++ tailWord_3002491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002491).length < 2 ^ (prefixWord ++ tailWord_3002491).sum := by decide
  have hdescent : baseEnd_3002491 < baseStart_3002491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002525 : List Nat := [1, 4, 2, 1, 1, 3, 3, 2, 2, 4]
def baseStart_3002525 : Nat := 118140960795 + 3002525 * 2 ^ 59
def prefixEnd_3002525 : Nat := 4983230072969 + 3 ^ 40 * 3002525 * 2
def baseEnd_3002525 : Nat := 513912834046990113609715

theorem tailTrace_3002525 : CollatzResearch.WordTrace tailWord_3002525 prefixEnd_3002525 513912834046990113609715 := by
  unfold tailWord_3002525
  simp only [CollatzResearch.WordTrace]
  refine ⟨109511083447372190289777029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73007388964914793526518019 109511083447372190289777029)
  ·
    refine ⟨20533328146382285679333193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109511083447372190289777029 20533328146382285679333193)
    ·
      refine ⟨15399996109786714259499895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20533328146382285679333193 15399996109786714259499895)
      ·
        refine ⟨23099994164680071389249843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15399996109786714259499895 23099994164680071389249843)
        ·
          refine ⟨34649991247020107083874765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23099994164680071389249843 34649991247020107083874765)
          ·
            refine ⟨12993746717632540156453037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34649991247020107083874765 12993746717632540156453037)
            ·
              refine ⟨4872655019112202558669889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12993746717632540156453037 4872655019112202558669889)
              ·
                refine ⟨3654491264334151919002417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4872655019112202558669889 3654491264334151919002417)
                ·
                  refine ⟨2740868448250613939251813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3654491264334151919002417 2740868448250613939251813)
                  ·
                    refine ⟨513912834046990113609715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2740868448250613939251813 513912834046990113609715)
                    ·
                      rfl

theorem cell23_3002525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_3002525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002525 prefixEnd_3002525 := by exact prefixLift 3002525
  have htrace : WordTrace (prefixWord ++ tailWord_3002525) baseStart_3002525 baseEnd_3002525 := by
    simpa [prefixWord, tailWord_3002525, baseEnd_3002525] using wordTrace_append hprefix tailTrace_3002525
  have hstable : (prefixWord ++ tailWord_3002525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002525).length < 2 ^ (prefixWord ++ tailWord_3002525).sum := by decide
  have hdescent : baseEnd_3002525 < baseStart_3002525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002531 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 2, 7, 3]
def baseStart_3002531 : Nat := 118140960795 + 3002531 * 2 ^ 59
def prefixEnd_3002531 : Nat := 4983230072969 + 3 ^ 40 * 3002531 * 2
def baseEnd_3002531 : Nat := 1541741583024897317354117

theorem tailTrace_3002531 : CollatzResearch.WordTrace tailWord_3002531 prefixEnd_3002531 1541741583024897317354117 := by
  unfold tailWord_3002531
  simp only [CollatzResearch.WordTrace]
  refine ⟨109511302285350453314495447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73007534856900302209663631 109511302285350453314495447)
  ·
    refine ⟨164266953428025679971743171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109511302285350453314495447 164266953428025679971743171)
    ·
      refine ⟨246400430142038519957614757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164266953428025679971743171 246400430142038519957614757)
      ·
        refine ⟨46200080651632222492052767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 246400430142038519957614757 46200080651632222492052767)
        ·
          refine ⟨69300120977448333738079151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46200080651632222492052767 69300120977448333738079151)
          ·
            refine ⟨103950181466172500607118727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69300120977448333738079151 103950181466172500607118727)
            ·
              refine ⟨155925272199258750910678091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103950181466172500607118727 155925272199258750910678091)
              ·
                refine ⟨233887908298888126366017137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155925272199258750910678091 233887908298888126366017137)
                ·
                  refine ⟨175415931224166094774512853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233887908298888126366017137 175415931224166094774512853)
                  ·
                    refine ⟨4111310888066392846277645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 175415931224166094774512853 4111310888066392846277645)
                    ·
                      refine ⟨1541741583024897317354117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4111310888066392846277645 1541741583024897317354117)
                      ·
                        rfl

theorem cell23_3002531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_3002531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002531 prefixEnd_3002531 := by exact prefixLift 3002531
  have htrace : WordTrace (prefixWord ++ tailWord_3002531) baseStart_3002531 baseEnd_3002531 := by
    simpa [prefixWord, tailWord_3002531, baseEnd_3002531] using wordTrace_append hprefix tailTrace_3002531
  have hstable : (prefixWord ++ tailWord_3002531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002531).length < 2 ^ (prefixWord ++ tailWord_3002531).sum := by decide
  have hdescent : baseEnd_3002531 < baseStart_3002531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002535 : List Nat := [1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 5]
def baseStart_3002535 : Nat := 118140960795 + 3002535 * 2 ^ 59
def prefixEnd_3002535 : Nat := 4983230072969 + 3 ^ 40 * 3002535 * 2
def baseEnd_3002535 : Nat := 1541743636947515301704099

theorem tailTrace_3002535 : CollatzResearch.WordTrace tailWord_3002535 prefixEnd_3002535 1541743636947515301704099 := by
  unfold tailWord_3002535
  simp only [CollatzResearch.WordTrace]
  refine ⟨109511448177335961997641059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73007632118223974665094039 109511448177335961997641059)
  ·
    refine ⟨164267172266003942996461589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109511448177335961997641059 164267172266003942996461589)
    ·
      refine ⟨7700023699968934827959137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 164267172266003942996461589 7700023699968934827959137)
      ·
        refine ⟨5775017774976701120969353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7700023699968934827959137 5775017774976701120969353)
        ·
          refine ⟨4331263331232525840727015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5775017774976701120969353 4331263331232525840727015)
          ·
            refine ⟨6496894996848788761090523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4331263331232525840727015 6496894996848788761090523)
            ·
              refine ⟨9745342495273183141635785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6496894996848788761090523 9745342495273183141635785)
              ·
                refine ⟨7309006871454887356226839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9745342495273183141635785 7309006871454887356226839)
                ·
                  refine ⟨10963510307182331034340259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7309006871454887356226839 10963510307182331034340259)
                  ·
                    refine ⟨16445265460773496551510389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10963510307182331034340259 16445265460773496551510389)
                    ·
                      refine ⟨1541743636947515301704099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16445265460773496551510389 1541743636947515301704099)
                      ·
                        rfl

theorem cell23_3002535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_3002535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002535 prefixEnd_3002535 := by exact prefixLift 3002535
  have htrace : WordTrace (prefixWord ++ tailWord_3002535) baseStart_3002535 baseEnd_3002535 := by
    simpa [prefixWord, tailWord_3002535, baseEnd_3002535] using wordTrace_append hprefix tailTrace_3002535
  have hstable : (prefixWord ++ tailWord_3002535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002535).length < 2 ^ (prefixWord ++ tailWord_3002535).sum := by decide
  have hdescent : baseEnd_3002535 < baseStart_3002535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002575 : List Nat := [1, 1, 2, 1, 1, 3, 3, 5, 1, 3, 2]
def baseStart_3002575 : Nat := 118140960795 + 3002575 * 2 ^ 59
def prefixEnd_3002575 : Nat := 4983230072969 + 3 ^ 40 * 3002575 * 2
def baseEnd_3002575 : Nat := 1541764176173695145203915

theorem tailTrace_3002575 : CollatzResearch.WordTrace tailWord_3002575 prefixEnd_3002575 1541764176173695145203915 := by
  unfold tailWord_3002575
  simp only [CollatzResearch.WordTrace]
  refine ⟨109512907097191048829097179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73008604731460699219398119 109512907097191048829097179)
  ·
    refine ⟨164269360645786573243645769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109512907097191048829097179 164269360645786573243645769)
    ·
      refine ⟨123202020484339929932734327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164269360645786573243645769 123202020484339929932734327)
      ·
        refine ⟨184803030726509894899101491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123202020484339929932734327 184803030726509894899101491)
        ·
          refine ⟨277204546089764842348652237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184803030726509894899101491 277204546089764842348652237)
          ·
            refine ⟨103951704783661815880744589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 277204546089764842348652237 103951704783661815880744589)
            ·
              refine ⟨38981889293873180955279221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103951704783661815880744589 38981889293873180955279221)
              ·
                refine ⟨3654552121300610714557427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38981889293873180955279221 3654552121300610714557427)
                ·
                  refine ⟨5481828181950916071836141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3654552121300610714557427 5481828181950916071836141)
                  ·
                    refine ⟨2055685568231593526938553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5481828181950916071836141 2055685568231593526938553)
                    ·
                      refine ⟨1541764176173695145203915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2055685568231593526938553 1541764176173695145203915)
                      ·
                        rfl

theorem cell23_3002575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 3, 2].length) (baseStart_3002575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002575 prefixEnd_3002575 := by exact prefixLift 3002575
  have htrace : WordTrace (prefixWord ++ tailWord_3002575) baseStart_3002575 baseEnd_3002575 := by
    simpa [prefixWord, tailWord_3002575, baseEnd_3002575] using wordTrace_append hprefix tailTrace_3002575
  have hstable : (prefixWord ++ tailWord_3002575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002575).length < 2 ^ (prefixWord ++ tailWord_3002575).sum := by decide
  have hdescent : baseEnd_3002575 < baseStart_3002575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002591 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 5]
def baseStart_3002591 : Nat := 118140960795 + 3002591 * 2 ^ 59
def prefixEnd_3002591 : Nat := 4983230072969 + 3 ^ 40 * 3002591 * 2
def baseEnd_3002591 : Nat := 1541772391864167082603841

theorem tailTrace_3002591 : CollatzResearch.WordTrace tailWord_3002591 prefixEnd_3002591 1541772391864167082603841 := by
  unfold tailWord_3002591
  simp only [CollatzResearch.WordTrace]
  refine ⟨109513490665133083561679627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73008993776755389041119751 109513490665133083561679627)
  ·
    refine ⟨164270235997699625342519441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109513490665133083561679627 164270235997699625342519441)
    ·
      refine ⟨123202676998274719006889581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164270235997699625342519441 123202676998274719006889581)
      ·
        refine ⟨46201003874353019627583593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123202676998274719006889581 46201003874353019627583593)
        ·
          refine ⟨34650752905764764720687695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46201003874353019627583593 34650752905764764720687695)
          ·
            refine ⟨51976129358647147081031543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34650752905764764720687695 51976129358647147081031543)
            ·
              refine ⟨77964194037970720621547315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51976129358647147081031543 77964194037970720621547315)
              ·
                refine ⟨116946291056956080932320973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77964194037970720621547315 116946291056956080932320973)
                ·
                  refine ⟨43854859146358530349620365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116946291056956080932320973 43854859146358530349620365)
                  ·
                    refine ⟨16445572179884448881107637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43854859146358530349620365 16445572179884448881107637)
                    ·
                      refine ⟨1541772391864167082603841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16445572179884448881107637 1541772391864167082603841)
                      ·
                        rfl

theorem cell23_3002591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_3002591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002591 prefixEnd_3002591 := by exact prefixLift 3002591
  have htrace : WordTrace (prefixWord ++ tailWord_3002591) baseStart_3002591 baseEnd_3002591 := by
    simpa [prefixWord, tailWord_3002591, baseEnd_3002591] using wordTrace_append hprefix tailTrace_3002591
  have hstable : (prefixWord ++ tailWord_3002591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002591).length < 2 ^ (prefixWord ++ tailWord_3002591).sum := by decide
  have hdescent : baseEnd_3002591 < baseStart_3002591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002599 : List Nat := [1, 1, 5, 3, 1, 1, 4, 1, 2, 1, 3]
def baseStart_3002599 : Nat := 118140960795 + 3002599 * 2 ^ 59
def prefixEnd_3002599 : Nat := 4983230072969 + 3 ^ 40 * 3002599 * 2
def baseEnd_3002599 : Nat := 1541776499709403051303805

theorem tailTrace_3002599 : CollatzResearch.WordTrace tailWord_3002599 prefixEnd_3002599 1541776499709403051303805 := by
  unfold tailWord_3002599
  simp only [CollatzResearch.WordTrace]
  refine ⟨109513782449104100927970851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73009188299402733951980567 109513782449104100927970851)
  ·
    refine ⟨164270673673656151391956277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109513782449104100927970851 164270673673656151391956277)
    ·
      refine ⟨15400375656905264192995901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 164270673673656151391956277 15400375656905264192995901)
      ·
        refine ⟨5775140871339474072373463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15400375656905264192995901 5775140871339474072373463)
        ·
          refine ⟨8662711307009211108560195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5775140871339474072373463 8662711307009211108560195)
          ·
            refine ⟨12994066960513816662840293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8662711307009211108560195 12994066960513816662840293)
            ·
              refine ⟨2436387555096340624282555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12994066960513816662840293 2436387555096340624282555)
              ·
                refine ⟨3654581332644510936423833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2436387555096340624282555 3654581332644510936423833)
                ·
                  refine ⟨2740935999483383202317875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3654581332644510936423833 2740935999483383202317875)
                  ·
                    refine ⟨4111403999225074803476813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2740935999483383202317875 4111403999225074803476813)
                    ·
                      refine ⟨1541776499709403051303805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4111403999225074803476813 1541776499709403051303805)
                      ·
                        rfl

theorem cell23_3002599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_3002599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002599 prefixEnd_3002599 := by exact prefixLift 3002599
  have htrace : WordTrace (prefixWord ++ tailWord_3002599) baseStart_3002599 baseEnd_3002599 := by
    simpa [prefixWord, tailWord_3002599, baseEnd_3002599] using wordTrace_append hprefix tailTrace_3002599
  have hstable : (prefixWord ++ tailWord_3002599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002599).length < 2 ^ (prefixWord ++ tailWord_3002599).sum := by decide
  have hdescent : baseEnd_3002599 < baseStart_3002599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002611 : List Nat := [1, 1, 1, 2, 2, 4, 2, 1, 9]
def baseStart_3002611 : Nat := 118140960795 + 3002611 * 2 ^ 59
def prefixEnd_3002611 : Nat := 4983230072969 + 3 ^ 40 * 3002611 * 2
def baseEnd_3002611 : Nat := 171309184608584111594861

theorem tailTrace_3002611 : CollatzResearch.WordTrace tailWord_3002611 prefixEnd_3002611 171309184608584111594861 := by
  unfold tailWord_3002611
  simp only [CollatzResearch.WordTrace]
  refine ⟨109514220125060626977407687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73009480083373751318271791 109514220125060626977407687)
  ·
    refine ⟨164271330187590940466111531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109514220125060626977407687 164271330187590940466111531)
    ·
      refine ⟨246406995281386410699167297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164271330187590940466111531 246406995281386410699167297)
      ·
        refine ⟨184805246461039808024375473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246406995281386410699167297 184805246461039808024375473)
        ·
          refine ⟨138603934845779856018281605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184805246461039808024375473 138603934845779856018281605)
          ·
            refine ⟨25988237783583723003427801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138603934845779856018281605 25988237783583723003427801)
            ·
              refine ⟨19491178337687792252570851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25988237783583723003427801 19491178337687792252570851)
              ·
                refine ⟨29236767506531688378856277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19491178337687792252570851 29236767506531688378856277)
                ·
                  refine ⟨171309184608584111594861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29236767506531688378856277 171309184608584111594861)
                  ·
                    rfl

theorem cell23_3002611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 9].length) (baseStart_3002611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002611 prefixEnd_3002611 := by exact prefixLift 3002611
  have htrace : WordTrace (prefixWord ++ tailWord_3002611) baseStart_3002611 baseEnd_3002611 := by
    simpa [prefixWord, tailWord_3002611, baseEnd_3002611] using wordTrace_append hprefix tailTrace_3002611
  have hstable : (prefixWord ++ tailWord_3002611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002611).length < 2 ^ (prefixWord ++ tailWord_3002611).sum := by decide
  have hdescent : baseEnd_3002611 < baseStart_3002611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002622 : List Nat := [4, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2]
def baseStart_3002622 : Nat := 118140960795 + 3002622 * 2 ^ 59
def prefixEnd_3002622 : Nat := 4983230072969 + 3 ^ 40 * 3002622 * 2
def baseEnd_3002622 : Nat := 1541788309764456461316199

theorem tailTrace_3002622 : CollatzResearch.WordTrace tailWord_3002622 prefixEnd_3002622 1541788309764456461316199 := by
  unfold tailWord_3002622
  simp only [CollatzResearch.WordTrace]
  refine ⟨13689327666002596982007265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73009747552013850570705413 13689327666002596982007265)
  ·
    refine ⟨10266995749501947736505449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13689327666002596982007265 10266995749501947736505449)
    ·
      refine ⟨7700246812126460802379087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10266995749501947736505449 7700246812126460802379087)
      ·
        refine ⟨11550370218189691203568631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7700246812126460802379087 11550370218189691203568631)
        ·
          refine ⟨17325555327284536805352947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11550370218189691203568631 17325555327284536805352947)
          ·
            refine ⟨25988332990926805208029421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17325555327284536805352947 25988332990926805208029421)
            ·
              refine ⟨9745624871597551953011033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25988332990926805208029421 9745624871597551953011033)
              ·
                refine ⟨7309218653698163964758275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9745624871597551953011033 7309218653698163964758275)
                ·
                  refine ⟨10963827980547245947137413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7309218653698163964758275 10963827980547245947137413)
                  ·
                    refine ⟨2055717746352608615088265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10963827980547245947137413 2055717746352608615088265)
                    ·
                      refine ⟨1541788309764456461316199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2055717746352608615088265 1541788309764456461316199)
                      ·
                        rfl

theorem cell23_3002622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_3002622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002622 prefixEnd_3002622 := by exact prefixLift 3002622
  have htrace : WordTrace (prefixWord ++ tailWord_3002622) baseStart_3002622 baseEnd_3002622 := by
    simpa [prefixWord, tailWord_3002622, baseEnd_3002622] using wordTrace_append hprefix tailTrace_3002622
  have hstable : (prefixWord ++ tailWord_3002622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002622).length < 2 ^ (prefixWord ++ tailWord_3002622).sum := by decide
  have hdescent : baseEnd_3002622 < baseStart_3002622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002626 : List Nat := [3, 4, 1, 1, 2, 2, 3, 1, 1, 3, 2]
def baseStart_3002626 : Nat := 118140960795 + 3002626 * 2 ^ 59
def prefixEnd_3002626 : Nat := 4983230072969 + 3 ^ 40 * 3002626 * 2
def baseEnd_3002626 : Nat := 1541790363687074445666181

theorem tailTrace_3002626 : CollatzResearch.WordTrace tailWord_3002626 prefixEnd_3002626 1541790363687074445666181 := by
  unfold tailWord_3002626
  simp only [CollatzResearch.WordTrace]
  refine ⟨27378691805001571134800933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73009844813337523026135821 27378691805001571134800933)
  ·
    refine ⟨5133504713437794587775175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27378691805001571134800933 5133504713437794587775175)
    ·
      refine ⟨7700257070156691881662763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5133504713437794587775175 7700257070156691881662763)
      ·
        refine ⟨11550385605235037822494145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7700257070156691881662763 11550385605235037822494145)
        ·
          refine ⟨8662789203926278366870609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11550385605235037822494145 8662789203926278366870609)
          ·
            refine ⟨6497091902944708775152957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8662789203926278366870609 6497091902944708775152957)
            ·
              refine ⟨2436409463604265790682359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6497091902944708775152957 2436409463604265790682359)
              ·
                refine ⟨3654614195406398686023539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2436409463604265790682359 3654614195406398686023539)
                ·
                  refine ⟨5481921293109598029035309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3654614195406398686023539 5481921293109598029035309)
                  ·
                    refine ⟨2055720484916099260888241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5481921293109598029035309 2055720484916099260888241)
                    ·
                      refine ⟨1541790363687074445666181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2055720484916099260888241 1541790363687074445666181)
                      ·
                        rfl

theorem cell23_3002626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_3002626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002626 prefixEnd_3002626 := by exact prefixLift 3002626
  have htrace : WordTrace (prefixWord ++ tailWord_3002626) baseStart_3002626 baseEnd_3002626 := by
    simpa [prefixWord, tailWord_3002626, baseEnd_3002626] using wordTrace_append hprefix tailTrace_3002626
  have hstable : (prefixWord ++ tailWord_3002626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002626).length < 2 ^ (prefixWord ++ tailWord_3002626).sum := by decide
  have hdescent : baseEnd_3002626 < baseStart_3002626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002655 : List Nat := [1, 1, 2, 4, 3, 2, 1, 1, 2, 3, 3]
def baseStart_3002655 : Nat := 118140960795 + 3002655 * 2 ^ 59
def prefixEnd_3002655 : Nat := 4983230072969 + 3 ^ 40 * 3002655 * 2
def baseEnd_3002655 : Nat := 1541805254626054832203547

theorem tailTrace_3002655 : CollatzResearch.WordTrace tailWord_3002655 prefixEnd_3002655 1541805254626054832203547 := by
  unfold tailWord_3002655
  simp only [CollatzResearch.WordTrace]
  refine ⟨109515824936901222492009419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73010549957934148328006279 109515824936901222492009419)
  ·
    refine ⟨164273737405351833738014129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109515824936901222492009419 164273737405351833738014129)
    ·
      refine ⟨123205303054013875303510597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164273737405351833738014129 123205303054013875303510597)
      ·
        refine ⟨23100994322627601619408237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123205303054013875303510597 23100994322627601619408237)
        ·
          refine ⟨8662872870985350607278089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23100994322627601619408237 8662872870985350607278089)
          ·
            refine ⟨6497154653239012955458567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8662872870985350607278089 6497154653239012955458567)
            ·
              refine ⟨9745731979858519433187851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6497154653239012955458567 9745731979858519433187851)
              ·
                refine ⟨14618597969787779149781777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9745731979858519433187851 14618597969787779149781777)
                ·
                  refine ⟨10963948477340834362336333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14618597969787779149781777 10963948477340834362336333)
                  ·
                    refine ⟨4111480679002812885876125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10963948477340834362336333 4111480679002812885876125)
                    ·
                      refine ⟨1541805254626054832203547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4111480679002812885876125 1541805254626054832203547)
                      ·
                        rfl

theorem cell23_3002655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_3002655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002655 prefixEnd_3002655 := by exact prefixLift 3002655
  have htrace : WordTrace (prefixWord ++ tailWord_3002655) baseStart_3002655 baseEnd_3002655 := by
    simpa [prefixWord, tailWord_3002655, baseEnd_3002655] using wordTrace_append hprefix tailTrace_3002655
  have hstable : (prefixWord ++ tailWord_3002655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002655).length < 2 ^ (prefixWord ++ tailWord_3002655).sum := by decide
  have hdescent : baseEnd_3002655 < baseStart_3002655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002695 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 4, 4, 2]
def baseStart_3002695 : Nat := 118140960795 + 3002695 * 2 ^ 59
def prefixEnd_3002695 : Nat := 4983230072969 + 3 ^ 40 * 3002695 * 2
def baseEnd_3002695 : Nat := 1541825793852234675703363

theorem tailTrace_3002695 : CollatzResearch.WordTrace tailWord_3002695 prefixEnd_3002695 1541825793852234675703363 := by
  unfold tailWord_3002695
  simp only [CollatzResearch.WordTrace]
  refine ⟨109517283856756309323465539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73011522571170872882310359 109517283856756309323465539)
  ·
    refine ⟨164275925785134463985198309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109517283856756309323465539 164275925785134463985198309)
    ·
      refine ⟨30801736084712711997224683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164275925785134463985198309 30801736084712711997224683)
      ·
        refine ⟨46202604127069067995837025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30801736084712711997224683 46202604127069067995837025)
        ·
          refine ⟨34651953095301800996877769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46202604127069067995837025 34651953095301800996877769)
          ·
            refine ⟨25988964821476350747658327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34651953095301800996877769 25988964821476350747658327)
            ·
              refine ⟨38983447232214526121487491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25988964821476350747658327 38983447232214526121487491)
              ·
                refine ⟨58475170848321789182231237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38983447232214526121487491 58475170848321789182231237)
                ·
                  refine ⟨10964094534060335471668357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58475170848321789182231237 10964094534060335471668357)
                  ·
                    refine ⟨2055767725136312900937817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10964094534060335471668357 2055767725136312900937817)
                    ·
                      refine ⟨1541825793852234675703363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2055767725136312900937817 1541825793852234675703363)
                      ·
                        rfl

theorem cell23_3002695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 4, 2].length) (baseStart_3002695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002695 prefixEnd_3002695 := by exact prefixLift 3002695
  have htrace : WordTrace (prefixWord ++ tailWord_3002695) baseStart_3002695 baseEnd_3002695 := by
    simpa [prefixWord, tailWord_3002695, baseEnd_3002695] using wordTrace_append hprefix tailTrace_3002695
  have hstable : (prefixWord ++ tailWord_3002695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002695).length < 2 ^ (prefixWord ++ tailWord_3002695).sum := by decide
  have hdescent : baseEnd_3002695 < baseStart_3002695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002705 : List Nat := [1, 2, 2, 1, 4, 2, 1, 3, 3, 4]
def baseStart_3002705 : Nat := 118140960795 + 3002705 * 2 ^ 59
def prefixEnd_3002705 : Nat := 4983230072969 + 3 ^ 40 * 3002705 * 2
def baseEnd_3002705 : Nat := 513943642886259878859439

theorem tailTrace_3002705 : CollatzResearch.WordTrace tailWord_3002705 prefixEnd_3002705 513943642886259878859439 := by
  unfold tailWord_3002705
  simp only [CollatzResearch.WordTrace]
  refine ⟨109517648586720081031329569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73011765724480054020886379 109517648586720081031329569)
  ·
    refine ⟨82138236440040060773497177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109517648586720081031329569 82138236440040060773497177)
    ·
      refine ⟨61603677330030045580122883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82138236440040060773497177 61603677330030045580122883)
      ·
        refine ⟨92405515995045068370184325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61603677330030045580122883 92405515995045068370184325)
        ·
          refine ⟨17326034249070950319409561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92405515995045068370184325 17326034249070950319409561)
          ·
            refine ⟨12994525686803212739557171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17326034249070950319409561 12994525686803212739557171)
            ·
              refine ⟨19491788530204819109335757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12994525686803212739557171 19491788530204819109335757)
              ·
                refine ⟨7309420698826807166000909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19491788530204819109335757 7309420698826807166000909)
                ·
                  refine ⟨2741032762060052687250341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7309420698826807166000909 2741032762060052687250341)
                  ·
                    refine ⟨513943642886259878859439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2741032762060052687250341 513943642886259878859439)
                    ·
                      rfl

theorem cell23_3002705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 3, 4].length) (baseStart_3002705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002705 prefixEnd_3002705 := by exact prefixLift 3002705
  have htrace : WordTrace (prefixWord ++ tailWord_3002705) baseStart_3002705 baseEnd_3002705 := by
    simpa [prefixWord, tailWord_3002705, baseEnd_3002705] using wordTrace_append hprefix tailTrace_3002705
  have hstable : (prefixWord ++ tailWord_3002705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002705).length < 2 ^ (prefixWord ++ tailWord_3002705).sum := by decide
  have hdescent : baseEnd_3002705 < baseStart_3002705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002722 : List Nat := [3, 3, 2, 1, 1, 2, 2, 2, 3, 4]
def baseStart_3002722 : Nat := 118140960795 + 3002722 * 2 ^ 59
def prefixEnd_3002722 : Nat := 4983230072969 + 3 ^ 40 * 3002722 * 2
def baseEnd_3002722 : Nat := 513946552609968690021913

theorem tailTrace_3002722 : CollatzResearch.WordTrace tailWord_3002722 prefixEnd_3002722 513946552609968690021913 := by
  unfold tailWord_3002722
  simp only [CollatzResearch.WordTrace]
  refine ⟨27379567156914623233674605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73012179085105661956465613 27379567156914623233674605)
  ·
    refine ⟨10267337683842983712627977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27379567156914623233674605 10267337683842983712627977)
    ·
      refine ⟨7700503262882237784470983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10267337683842983712627977 7700503262882237784470983)
      ·
        refine ⟨11550754894323356676706475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7700503262882237784470983 11550754894323356676706475)
        ·
          refine ⟨17326132341485035015059713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11550754894323356676706475 17326132341485035015059713)
          ·
            refine ⟨12994599256113776261294785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17326132341485035015059713 12994599256113776261294785)
            ·
              refine ⟨9745949442085332195971089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12994599256113776261294785 9745949442085332195971089)
              ·
                refine ⟨7309462081563999146978317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9745949442085332195971089 7309462081563999146978317)
                ·
                  refine ⟨2741048280586499680116869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7309462081563999146978317 2741048280586499680116869)
                  ·
                    refine ⟨513946552609968690021913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2741048280586499680116869 513946552609968690021913)
                    ·
                      rfl

theorem cell23_3002722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_3002722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002722 prefixEnd_3002722 := by exact prefixLift 3002722
  have htrace : WordTrace (prefixWord ++ tailWord_3002722) baseStart_3002722 baseEnd_3002722 := by
    simpa [prefixWord, tailWord_3002722, baseEnd_3002722] using wordTrace_append hprefix tailTrace_3002722
  have hstable : (prefixWord ++ tailWord_3002722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002722).length < 2 ^ (prefixWord ++ tailWord_3002722).sum := by decide
  have hdescent : baseEnd_3002722 < baseStart_3002722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002813 : List Nat := [1, 4, 1, 2, 2, 4, 2, 2, 1, 1, 3]
def baseStart_3002813 : Nat := 118140960795 + 3002813 * 2 ^ 59
def prefixEnd_3002813 : Nat := 4983230072969 + 3 ^ 40 * 3002813 * 2
def baseEnd_3002813 : Nat := 1541886384569465214027821

theorem tailTrace_3002813 : CollatzResearch.WordTrace tailWord_3002813 prefixEnd_3002813 1541886384569465214027821 := by
  unfold tailWord_3002813
  simp only [CollatzResearch.WordTrace]
  refine ⟨109521587670328815476261093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73014391780219210317507395 109521587670328815476261093)
  ·
    refine ⟨20535297688186652901798955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109521587670328815476261093 20535297688186652901798955)
    ·
      refine ⟨30802946532279979352698433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20535297688186652901798955 30802946532279979352698433)
      ·
        refine ⟨23102209899209984514523825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30802946532279979352698433 23102209899209984514523825)
        ·
          refine ⟨17326657424407488385892869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23102209899209984514523825 17326657424407488385892869)
          ·
            refine ⟨3248748267076404072354913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17326657424407488385892869 3248748267076404072354913)
            ·
              refine ⟨2436561200307303054266185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3248748267076404072354913 2436561200307303054266185)
              ·
                refine ⟨1827420900230477290699639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2436561200307303054266185 1827420900230477290699639)
                ·
                  refine ⟨2741131350345715936049459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1827420900230477290699639 2741131350345715936049459)
                  ·
                    refine ⟨4111697025518573904074189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2741131350345715936049459 4111697025518573904074189)
                    ·
                      refine ⟨1541886384569465214027821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4111697025518573904074189 1541886384569465214027821)
                      ·
                        rfl

theorem cell23_3002813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_3002813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002813 prefixEnd_3002813 := by exact prefixLift 3002813
  have htrace : WordTrace (prefixWord ++ tailWord_3002813) baseStart_3002813 baseEnd_3002813 := by
    simpa [prefixWord, tailWord_3002813, baseEnd_3002813] using wordTrace_append hprefix tailTrace_3002813
  have hstable : (prefixWord ++ tailWord_3002813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002813).length < 2 ^ (prefixWord ++ tailWord_3002813).sum := by decide
  have hdescent : baseEnd_3002813 < baseStart_3002813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002836 : List Nat := [2, 4, 1, 2, 2, 2, 1, 2, 3, 2, 2]
def baseStart_3002836 : Nat := 118140960795 + 3002836 * 2 ^ 59
def prefixEnd_3002836 : Nat := 4983230072969 + 3 ^ 40 * 3002836 * 2
def baseEnd_3002836 : Nat := 1541898194624518624040215

theorem tailTrace_3002836 : CollatzResearch.WordTrace tailWord_3002836 prefixEnd_3002836 1541898194624518624040215 := by
  unfold tailWord_3002836
  simp only [CollatzResearch.WordTrace]
  refine ⟨54761213274622745202174181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73014951032830326936232241 54761213274622745202174181)
  ·
    refine ⟨10267727488991764725407659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54761213274622745202174181 10267727488991764725407659)
    ·
      refine ⟨15401591233487647088111489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10267727488991764725407659 15401591233487647088111489)
      ·
        refine ⟨11551193425115735316083617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15401591233487647088111489 11551193425115735316083617)
        ·
          refine ⟨8663395068836801487062713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11551193425115735316083617 8663395068836801487062713)
          ·
            refine ⟨6497546301627601115297035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8663395068836801487062713 6497546301627601115297035)
            ·
              refine ⟨9746319452441401672945553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6497546301627601115297035 9746319452441401672945553)
              ·
                refine ⟨7309739589331051254709165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9746319452441401672945553 7309739589331051254709165)
                ·
                  refine ⟨2741152345999144220515937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7309739589331051254709165 2741152345999144220515937)
                  ·
                    refine ⟨2055864259499358165386953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2741152345999144220515937 2055864259499358165386953)
                    ·
                      refine ⟨1541898194624518624040215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2055864259499358165386953 1541898194624518624040215)
                      ·
                        rfl

theorem cell23_3002836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_3002836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002836 prefixEnd_3002836 := by exact prefixLift 3002836
  have htrace : WordTrace (prefixWord ++ tailWord_3002836) baseStart_3002836 baseEnd_3002836 := by
    simpa [prefixWord, tailWord_3002836, baseEnd_3002836] using wordTrace_append hprefix tailTrace_3002836
  have hstable : (prefixWord ++ tailWord_3002836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002836).length < 2 ^ (prefixWord ++ tailWord_3002836).sum := by decide
  have hdescent : baseEnd_3002836 < baseStart_3002836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002850 : List Nat := [3, 3, 3, 2, 2, 1, 2, 1, 1, 5]
def baseStart_3002850 : Nat := 118140960795 + 3002850 * 2 ^ 59
def prefixEnd_3002850 : Nat := 4983230072969 + 3 ^ 40 * 3002850 * 2
def baseEnd_3002850 : Nat := 513968461117893856421717

theorem tailTrace_3002850 : CollatzResearch.WordTrace tailWord_3002850 prefixEnd_3002850 513968461117893856421717 := by
  unfold tailWord_3002850
  simp only [CollatzResearch.WordTrace]
  refine ⟨27380734292798692698839501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73015291447463180530238669 27380734292798692698839501)
  ·
    refine ⟨10267775359799509762064813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27380734292798692698839501 10267775359799509762064813)
    ·
      refine ⟨3850415759924816160774305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10267775359799509762064813 3850415759924816160774305)
      ·
        refine ⟨2887811819943612120580729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3850415759924816160774305 2887811819943612120580729)
        ·
          refine ⟨2165858864957709090435547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2887811819943612120580729 2165858864957709090435547)
          ·
            refine ⟨3248788297436563635653321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2165858864957709090435547 3248788297436563635653321)
            ·
              refine ⟨2436591223077422726739991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3248788297436563635653321 2436591223077422726739991)
              ·
                refine ⟨3654886834616134090109987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2436591223077422726739991 3654886834616134090109987)
                ·
                  refine ⟨5482330251924201135164981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3654886834616134090109987 5482330251924201135164981)
                  ·
                    refine ⟨513968461117893856421717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5482330251924201135164981 513968461117893856421717)
                    ·
                      rfl

theorem cell23_3002850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_3002850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002850 prefixEnd_3002850 := by exact prefixLift 3002850
  have htrace : WordTrace (prefixWord ++ tailWord_3002850) baseStart_3002850 baseEnd_3002850 := by
    simpa [prefixWord, tailWord_3002850, baseEnd_3002850] using wordTrace_append hprefix tailTrace_3002850
  have hstable : (prefixWord ++ tailWord_3002850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002850).length < 2 ^ (prefixWord ++ tailWord_3002850).sum := by decide
  have hdescent : baseEnd_3002850 < baseStart_3002850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002853 : List Nat := [1, 3, 1, 5, 3, 1, 2, 1, 1, 1, 4]
def baseStart_3002853 : Nat := 118140960795 + 3002853 * 2 ^ 59
def prefixEnd_3002853 : Nat := 4983230072969 + 3 ^ 40 * 3002853 * 2
def baseEnd_3002853 : Nat := 1541906923795645057527637

theorem tailTrace_3002853 : CollatzResearch.WordTrace tailWord_3002853 prefixEnd_3002853 1541906923795645057527637 := by
  unfold tailWord_3002853
  simp only [CollatzResearch.WordTrace]
  refine ⟨109523046590183902307717213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73015364393455934871811475 109523046590183902307717213)
  ·
    refine ⟨41071142471318963365393955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109523046590183902307717213 41071142471318963365393955)
    ·
      refine ⟨61606713706978445048090933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41071142471318963365393955 61606713706978445048090933)
      ·
        refine ⟨5775629410029229223258525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61606713706978445048090933 5775629410029229223258525)
        ·
          refine ⟨2165861028760960958721947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5775629410029229223258525 2165861028760960958721947)
          ·
            refine ⟨3248791543141441438082921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2165861028760960958721947 3248791543141441438082921)
            ·
              refine ⟨2436593657356081078562191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3248791543141441438082921 2436593657356081078562191)
              ·
                refine ⟨3654890486034121617843287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2436593657356081078562191 3654890486034121617843287)
                ·
                  refine ⟨5482335729051182426764931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3654890486034121617843287 5482335729051182426764931)
                  ·
                    refine ⟨8223503593576773640147397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5482335729051182426764931 8223503593576773640147397)
                    ·
                      refine ⟨1541906923795645057527637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8223503593576773640147397 1541906923795645057527637)
                      ·
                        rfl

theorem cell23_3002853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_3002853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002853 prefixEnd_3002853 := by exact prefixLift 3002853
  have htrace : WordTrace (prefixWord ++ tailWord_3002853) baseStart_3002853 baseEnd_3002853 := by
    simpa [prefixWord, tailWord_3002853, baseEnd_3002853] using wordTrace_append hprefix tailTrace_3002853
  have hstable : (prefixWord ++ tailWord_3002853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002853).length < 2 ^ (prefixWord ++ tailWord_3002853).sum := by decide
  have hdescent : baseEnd_3002853 < baseStart_3002853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002856 : List Nat := [2, 1, 4, 1, 1, 5, 2, 1, 1, 2, 3]
def baseStart_3002856 : Nat := 118140960795 + 3002856 * 2 ^ 59
def prefixEnd_3002856 : Nat := 4983230072969 + 3 ^ 40 * 3002856 * 2
def baseEnd_3002856 : Nat := 1541908464237608545790123

theorem tailTrace_3002856 : CollatzResearch.WordTrace tailWord_3002856 prefixEnd_3002856 1541908464237608545790123 := by
  unfold tailWord_3002856
  simp only [CollatzResearch.WordTrace]
  refine ⟨54761578004586516910038211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73015437339448689213384281 54761578004586516910038211)
  ·
    refine ⟨82142367006879775365057317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54761578004586516910038211 82142367006879775365057317)
    ·
      refine ⟨15401693813789957880948247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82142367006879775365057317 15401693813789957880948247)
      ·
        refine ⟨23102540720684936821422371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15401693813789957880948247 23102540720684936821422371)
        ·
          refine ⟨34653811081027405232133557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23102540720684936821422371 34653811081027405232133557)
          ·
            refine ⟨3248794788846319240512521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34653811081027405232133557 3248794788846319240512521)
            ·
              refine ⟨2436596091634739430384391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3248794788846319240512521 2436596091634739430384391)
              ·
                refine ⟨3654894137452109145576587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2436596091634739430384391 3654894137452109145576587)
                ·
                  refine ⟨5482341206178163718364881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3654894137452109145576587 5482341206178163718364881)
                  ·
                    refine ⟨4111755904633622788773661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5482341206178163718364881 4111755904633622788773661)
                    ·
                      refine ⟨1541908464237608545790123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4111755904633622788773661 1541908464237608545790123)
                      ·
                        rfl

theorem cell23_3002856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_3002856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002856 prefixEnd_3002856 := by exact prefixLift 3002856
  have htrace : WordTrace (prefixWord ++ tailWord_3002856) baseStart_3002856 baseEnd_3002856 := by
    simpa [prefixWord, tailWord_3002856, baseEnd_3002856] using wordTrace_append hprefix tailTrace_3002856
  have hstable : (prefixWord ++ tailWord_3002856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002856).length < 2 ^ (prefixWord ++ tailWord_3002856).sum := by decide
  have hdescent : baseEnd_3002856 < baseStart_3002856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002885 : List Nat := [1, 3, 1, 1, 2, 2, 4, 1, 2, 6]
def baseStart_3002885 : Nat := 118140960795 + 3002885 * 2 ^ 59
def prefixEnd_3002885 : Nat := 4983230072969 + 3 ^ 40 * 3002885 * 2
def baseEnd_3002885 : Nat := 513974451725529644109163

theorem tailTrace_3002885 : CollatzResearch.WordTrace tailWord_3002885 prefixEnd_3002885 513974451725529644109163 := by
  unfold tailWord_3002885
  simp only [CollatzResearch.WordTrace]
  refine ⟨109524213726067971772882109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73016142484045314515254739 109524213726067971772882109)
  ·
    refine ⟨41071580147275489414830791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109524213726067971772882109 41071580147275489414830791)
    ·
      refine ⟨61607370220913234122246187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41071580147275489414830791 61607370220913234122246187)
      ·
        refine ⟨92411055331369851183369281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61607370220913234122246187 92411055331369851183369281)
        ·
          refine ⟨69308291498527388387526961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92411055331369851183369281 69308291498527388387526961)
          ·
            refine ⟨51981218623895541290645221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69308291498527388387526961 51981218623895541290645221)
            ·
              refine ⟨9746478491980413991995979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51981218623895541290645221 9746478491980413991995979)
              ·
                refine ⟨14619717737970620987993969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9746478491980413991995979 14619717737970620987993969)
                ·
                  refine ⟨10964788303477965740995477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14619717737970620987993969 10964788303477965740995477)
                  ·
                    refine ⟨513974451725529644109163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10964788303477965740995477 513974451725529644109163)
                    ·
                      rfl

theorem cell23_3002885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 6].length) (baseStart_3002885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002885 prefixEnd_3002885 := by exact prefixLift 3002885
  have htrace : WordTrace (prefixWord ++ tailWord_3002885) baseStart_3002885 baseEnd_3002885 := by
    simpa [prefixWord, tailWord_3002885, baseEnd_3002885] using wordTrace_append hprefix tailTrace_3002885
  have hstable : (prefixWord ++ tailWord_3002885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002885).length < 2 ^ (prefixWord ++ tailWord_3002885).sum := by decide
  have hdescent : baseEnd_3002885 < baseStart_3002885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002895 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 4, 4, 3]
def baseStart_3002895 : Nat := 118140960795 + 3002895 * 2 ^ 59
def prefixEnd_3002895 : Nat := 4983230072969 + 3 ^ 40 * 3002895 * 2
def baseEnd_3002895 : Nat := 1541928489983133893202443

theorem tailTrace_3002895 : CollatzResearch.WordTrace tailWord_3002895 prefixEnd_3002895 1541928489983133893202443 := by
  unfold tailWord_3002895
  simp only [CollatzResearch.WordTrace]
  refine ⟨109524578456031743480746139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73016385637354495653830759 109524578456031743480746139)
  ·
    refine ⟨164286867684047615221119209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109524578456031743480746139 164286867684047615221119209)
    ·
      refine ⟨123215150763035711415839407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164286867684047615221119209 123215150763035711415839407)
      ·
        refine ⟨184822726144553567123759111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123215150763035711415839407 184822726144553567123759111)
        ·
          refine ⟨277234089216830350685638667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184822726144553567123759111 277234089216830350685638667)
          ·
            refine ⟨415851133825245526028458001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277234089216830350685638667 415851133825245526028458001)
            ·
              refine ⟨311888350368934144521343501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 415851133825245526028458001 311888350368934144521343501)
              ·
                refine ⟨116958131388350304195503813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 311888350368934144521343501 116958131388350304195503813)
                ·
                  refine ⟨21929649635315682036656965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116958131388350304195503813 21929649635315682036656965)
                  ·
                    refine ⟨4111809306621690381873181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21929649635315682036656965 4111809306621690381873181)
                    ·
                      refine ⟨1541928489983133893202443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4111809306621690381873181 1541928489983133893202443)
                      ·
                        rfl

theorem cell23_3002895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 4, 3].length) (baseStart_3002895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002895 prefixEnd_3002895 := by exact prefixLift 3002895
  have htrace : WordTrace (prefixWord ++ tailWord_3002895) baseStart_3002895 baseEnd_3002895 := by
    simpa [prefixWord, tailWord_3002895, baseEnd_3002895] using wordTrace_append hprefix tailTrace_3002895
  have hstable : (prefixWord ++ tailWord_3002895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002895).length < 2 ^ (prefixWord ++ tailWord_3002895).sum := by decide
  have hdescent : baseEnd_3002895 < baseStart_3002895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002985 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 1, 5, 5]
def baseStart_3002985 : Nat := 118140960795 + 3002985 * 2 ^ 59
def prefixEnd_3002985 : Nat := 4983230072969 + 3 ^ 40 * 3002985 * 2
def baseEnd_3002985 : Nat := 1541974703242038541077029

theorem tailTrace_3002985 : CollatzResearch.WordTrace tailWord_3002985 prefixEnd_3002985 1541974703242038541077029 := by
  unfold tailWord_3002985
  simp only [CollatzResearch.WordTrace]
  refine ⟨109527861025705688851522409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73018574017137125901014939 109527861025705688851522409)
  ·
    refine ⟨82145895769279266638641807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109527861025705688851522409 82145895769279266638641807)
    ·
      refine ⟨123218843653918899957962711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82145895769279266638641807 123218843653918899957962711)
      ·
        refine ⟨184828265480878349936944067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123218843653918899957962711 184828265480878349936944067)
        ·
          refine ⟨277242398221317524905416101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184828265480878349936944067 277242398221317524905416101)
          ·
            refine ⟨51982949666497035919765519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 277242398221317524905416101 51982949666497035919765519)
            ·
              refine ⟨77974424499745553879648279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51982949666497035919765519 77974424499745553879648279)
              ·
                refine ⟨116961636749618330819472419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77974424499745553879648279 116961636749618330819472419)
                ·
                  refine ⟨175442455124427496229208629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116961636749618330819472419 175442455124427496229208629)
                  ·
                    refine ⟨16447730167915077771488309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 175442455124427496229208629 16447730167915077771488309)
                    ·
                      refine ⟨1541974703242038541077029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16447730167915077771488309 1541974703242038541077029)
                      ·
                        rfl

theorem cell23_3002985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 5, 5].length) (baseStart_3002985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002985 prefixEnd_3002985 := by exact prefixLift 3002985
  have htrace : WordTrace (prefixWord ++ tailWord_3002985) baseStart_3002985 baseEnd_3002985 := by
    simpa [prefixWord, tailWord_3002985, baseEnd_3002985] using wordTrace_append hprefix tailTrace_3002985
  have hstable : (prefixWord ++ tailWord_3002985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002985).length < 2 ^ (prefixWord ++ tailWord_3002985).sum := by decide
  have hdescent : baseEnd_3002985 < baseStart_3002985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002995 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 6]
def baseStart_3002995 : Nat := 118140960795 + 3002995 * 2 ^ 59
def prefixEnd_3002995 : Nat := 4983230072969 + 3 ^ 40 * 3002995 * 2
def baseEnd_3002995 : Nat := 1541979838048583501951983

theorem tailTrace_3002995 : CollatzResearch.WordTrace tailWord_3002995 prefixEnd_3002995 1541979838048583501951983 := by
  unfold tailWord_3002995
  simp only [CollatzResearch.WordTrace]
  refine ⟨109528225755669460559386439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73018817170446307039590959 109528225755669460559386439)
  ·
    refine ⟨164292338633504190839079659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109528225755669460559386439 164292338633504190839079659)
    ·
      refine ⟨246438507950256286258619489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164292338633504190839079659 246438507950256286258619489)
      ·
        refine ⟨184828880962692214693964617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246438507950256286258619489 184828880962692214693964617)
        ·
          refine ⟨138621660722019161020473463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184828880962692214693964617 138621660722019161020473463)
          ·
            refine ⟨207932491083028741530710195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138621660722019161020473463 207932491083028741530710195)
            ·
              refine ⟨311898736624543112296065293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207932491083028741530710195 311898736624543112296065293)
              ·
                refine ⟨116962026234203667111024485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 311898736624543112296065293 116962026234203667111024485)
                ·
                  refine ⟨21930379918913187583317091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116962026234203667111024485 21930379918913187583317091)
                  ·
                    refine ⟨32895569878369781374975637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21930379918913187583317091 32895569878369781374975637)
                    ·
                      refine ⟨1541979838048583501951983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32895569878369781374975637 1541979838048583501951983)
                      ·
                        rfl

theorem cell23_3002995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 6].length) (baseStart_3002995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3002995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3002995 prefixEnd_3002995 := by exact prefixLift 3002995
  have htrace : WordTrace (prefixWord ++ tailWord_3002995) baseStart_3002995 baseEnd_3002995 := by
    simpa [prefixWord, tailWord_3002995, baseEnd_3002995] using wordTrace_append hprefix tailTrace_3002995
  have hstable : (prefixWord ++ tailWord_3002995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002995).length < 2 ^ (prefixWord ++ tailWord_3002995).sum := by decide
  have hdescent : baseEnd_3002995 < baseStart_3002995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003009 : List Nat := [1, 2, 4, 2, 1, 1, 3, 2, 3, 4]
def baseStart_3003009 : Nat := 118140960795 + 3003009 * 2 ^ 59
def prefixEnd_3003009 : Nat := 4983230072969 + 3 ^ 40 * 3003009 * 2
def baseEnd_3003009 : Nat := 513995675592582149058973

theorem tailTrace_3003009 : CollatzResearch.WordTrace tailWord_3003009 prefixEnd_3003009 513995675592582149058973 := by
  unfold tailWord_3003009
  simp only [CollatzResearch.WordTrace]
  refine ⟨109528736377618740950396081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73019157585079160633597387 109528736377618740950396081)
  ·
    refine ⟨82146552283214055712797061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109528736377618740950396081 82146552283214055712797061)
    ·
      refine ⟨15402478553102635446149449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82146552283214055712797061 15402478553102635446149449)
      ·
        refine ⟨11551858914826976584612087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15402478553102635446149449 11551858914826976584612087)
        ·
          refine ⟨17327788372240464876918131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11551858914826976584612087 17327788372240464876918131)
          ·
            refine ⟨25991682558360697315377197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17327788372240464876918131 25991682558360697315377197)
            ·
              refine ⟨9746880959385261493266449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25991682558360697315377197 9746880959385261493266449)
              ·
                refine ⟨7310160719538946119949837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9746880959385261493266449 7310160719538946119949837)
                ·
                  refine ⟨2741310269827104794981189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7310160719538946119949837 2741310269827104794981189)
                  ·
                    refine ⟨513995675592582149058973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2741310269827104794981189 513995675592582149058973)
                    ·
                      rfl

theorem cell23_3003009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_3003009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003009 prefixEnd_3003009 := by exact prefixLift 3003009
  have htrace : WordTrace (prefixWord ++ tailWord_3003009) baseStart_3003009 baseEnd_3003009 := by
    simpa [prefixWord, tailWord_3003009, baseEnd_3003009] using wordTrace_append hprefix tailTrace_3003009
  have hstable : (prefixWord ++ tailWord_3003009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003009).length < 2 ^ (prefixWord ++ tailWord_3003009).sum := by decide
  have hdescent : baseEnd_3003009 < baseStart_3003009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003022 : List Nat := [4, 1, 1, 3, 1, 1, 2, 2, 8]
def baseStart_3003022 : Nat := 118140960795 + 3003022 * 2 ^ 59
def prefixEnd_3003022 : Nat := 4983230072969 + 3 ^ 40 * 3003022 * 2
def baseEnd_3003022 : Nat := 171332633558472766257151

theorem tailTrace_3003022 : CollatzResearch.WordTrace tailWord_3003022 prefixEnd_3003022 171332633558472766257151 := by
  unfold tailWord_3003022
  simp only [CollatzResearch.WordTrace]
  refine ⟨13691151315821455521327415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73019473684381096113746213 13691151315821455521327415)
  ·
    refine ⟨20536726973732183281991123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13691151315821455521327415 20536726973732183281991123)
    ·
      refine ⟨30805090460598274922986685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20536726973732183281991123 30805090460598274922986685)
      ·
        refine ⟨11551908922724353096120007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30805090460598274922986685 11551908922724353096120007)
        ·
          refine ⟨17327863384086529644180011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11551908922724353096120007 17327863384086529644180011)
          ·
            refine ⟨25991795076129794466270017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17327863384086529644180011 25991795076129794466270017)
            ·
              refine ⟨19493846307097345849702513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25991795076129794466270017 19493846307097345849702513)
              ·
                refine ⟨14620384730323009387276885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19493846307097345849702513 14620384730323009387276885)
                ·
                  refine ⟨171332633558472766257151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14620384730323009387276885 171332633558472766257151)
                  ·
                    rfl

theorem cell23_3003022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 8].length) (baseStart_3003022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003022 prefixEnd_3003022 := by exact prefixLift 3003022
  have htrace : WordTrace (prefixWord ++ tailWord_3003022) baseStart_3003022 baseEnd_3003022 := by
    simpa [prefixWord, tailWord_3003022, baseEnd_3003022] using wordTrace_append hprefix tailTrace_3003022
  have hstable : (prefixWord ++ tailWord_3003022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003022).length < 2 ^ (prefixWord ++ tailWord_3003022).sum := by decide
  have hdescent : baseEnd_3003022 < baseStart_3003022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003035 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 4, 9]
def baseStart_3003035 : Nat := 118140960795 + 3003035 * 2 ^ 59
def prefixEnd_3003035 : Nat := 4983230072969 + 3 ^ 40 * 3003035 * 2
def baseEnd_3003035 : Nat := 514000125758254448483933

theorem tailTrace_3003035 : CollatzResearch.WordTrace tailWord_3003035 prefixEnd_3003035 514000125758254448483933 := by
  unfold tailWord_3003035
  simp only [CollatzResearch.WordTrace]
  refine ⟨109529684675524547390842559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73019789783683031593895039 109529684675524547390842559)
  ·
    refine ⟨164294527013286821086263839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109529684675524547390842559 164294527013286821086263839)
    ·
      refine ⟨246441790519930231629395759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164294527013286821086263839 246441790519930231629395759)
      ·
        refine ⟨369662685779895347444093639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246441790519930231629395759 369662685779895347444093639)
        ·
          refine ⟨554494028669843021166140459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369662685779895347444093639 554494028669843021166140459)
          ·
            refine ⟨831741043004764531749210689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554494028669843021166140459 831741043004764531749210689)
            ·
              refine ⟨623805782253573398811908017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 831741043004764531749210689 623805782253573398811908017)
              ·
                refine ⟨467854336690180049108931013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 623805782253573398811908017 467854336690180049108931013)
                ·
                  refine ⟨87722688129408759207924565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 467854336690180049108931013 87722688129408759207924565)
                  ·
                    refine ⟨514000125758254448483933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 87722688129408759207924565 514000125758254448483933)
                    ·
                      rfl

theorem cell23_3003035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 9].length) (baseStart_3003035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003035 prefixEnd_3003035 := by exact prefixLift 3003035
  have htrace : WordTrace (prefixWord ++ tailWord_3003035) baseStart_3003035 baseEnd_3003035 := by
    simpa [prefixWord, tailWord_3003035, baseEnd_3003035] using wordTrace_append hprefix tailTrace_3003035
  have hstable : (prefixWord ++ tailWord_3003035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003035).length < 2 ^ (prefixWord ++ tailWord_3003035).sum := by decide
  have hdescent : baseEnd_3003035 < baseStart_3003035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003049 : List Nat := [1, 2, 1, 1, 1, 1, 2, 7, 3, 1, 3]
def baseStart_3003049 : Nat := 118140960795 + 3003049 * 2 ^ 59
def prefixEnd_3003049 : Nat := 4983230072969 + 3 ^ 40 * 3003049 * 2
def baseEnd_3003049 : Nat := 1542007566003926290676735

theorem tailTrace_3003049 : CollatzResearch.WordTrace tailWord_3003049 prefixEnd_3003049 1542007566003926290676735 := by
  unfold tailWord_3003049
  simp only [CollatzResearch.WordTrace]
  refine ⟨109530195297473827781852201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73020130198315885187901467 109530195297473827781852201)
  ·
    refine ⟨82147646473105370836389151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109530195297473827781852201 82147646473105370836389151)
    ·
      refine ⟨123221469709658056254583727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82147646473105370836389151 123221469709658056254583727)
      ·
        refine ⟨184832204564487084381875591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123221469709658056254583727 184832204564487084381875591)
        ·
          refine ⟨277248306846730626572813387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184832204564487084381875591 277248306846730626572813387)
          ·
            refine ⟨415872460270095939859220081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277248306846730626572813387 415872460270095939859220081)
            ·
              refine ⟨311904345202571954894415061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 415872460270095939859220081 311904345202571954894415061)
              ·
                refine ⟨7310258090685280192837853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 311904345202571954894415061 7310258090685280192837853)
                ·
                  refine ⟨2741346784006980072314195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7310258090685280192837853 2741346784006980072314195)
                  ·
                    refine ⟨4112020176010470108471293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2741346784006980072314195 4112020176010470108471293)
                    ·
                      refine ⟨1542007566003926290676735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4112020176010470108471293 1542007566003926290676735)
                      ·
                        rfl

theorem cell23_3003049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 3, 1, 3].length) (baseStart_3003049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003049 prefixEnd_3003049 := by exact prefixLift 3003049
  have htrace : WordTrace (prefixWord ++ tailWord_3003049) baseStart_3003049 baseEnd_3003049 := by
    simpa [prefixWord, tailWord_3003049, baseEnd_3003049] using wordTrace_append hprefix tailTrace_3003049
  have hstable : (prefixWord ++ tailWord_3003049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003049).length < 2 ^ (prefixWord ++ tailWord_3003049).sum := by decide
  have hdescent : baseEnd_3003049 < baseStart_3003049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003059 : List Nat := [1, 1, 1, 2, 3, 4, 1, 2, 1, 5, 2]
def baseStart_3003059 : Nat := 118140960795 + 3003059 * 2 ^ 59
def prefixEnd_3003059 : Nat := 4983230072969 + 3 ^ 40 * 3003059 * 2
def baseEnd_3003059 : Nat := 1542012700810471251551689

theorem tailTrace_3003059 : CollatzResearch.WordTrace tailWord_3003059 prefixEnd_3003059 1542012700810471251551689 := by
  unfold tailWord_3003059
  simp only [CollatzResearch.WordTrace]
  refine ⟨109530560027437599489716231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73020373351625066326477487 109530560027437599489716231)
  ·
    refine ⟨164295840041156399234574347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109530560027437599489716231 164295840041156399234574347)
    ·
      refine ⟨246443760061734598851861521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164295840041156399234574347 246443760061734598851861521)
      ·
        refine ⟨184832820046300949138896141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246443760061734598851861521 184832820046300949138896141)
        ·
          refine ⟨69312307517362855927086053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184832820046300949138896141 69312307517362855927086053)
          ·
            refine ⟨12996057659505535486328635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69312307517362855927086053 12996057659505535486328635)
            ·
              refine ⟨19494086489258303229492953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12996057659505535486328635 19494086489258303229492953)
              ·
                refine ⟨14620564866943727422119715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19494086489258303229492953 14620564866943727422119715)
                ·
                  refine ⟨21930847300415591133179573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14620564866943727422119715 21930847300415591133179573)
                  ·
                    refine ⟨2056016934413961668735585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21930847300415591133179573 2056016934413961668735585)
                    ·
                      refine ⟨1542012700810471251551689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2056016934413961668735585 1542012700810471251551689)
                      ·
                        rfl

theorem cell23_3003059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 5, 2].length) (baseStart_3003059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003059 prefixEnd_3003059 := by exact prefixLift 3003059
  have htrace : WordTrace (prefixWord ++ tailWord_3003059) baseStart_3003059 baseEnd_3003059 := by
    simpa [prefixWord, tailWord_3003059, baseEnd_3003059] using wordTrace_append hprefix tailTrace_3003059
  have hstable : (prefixWord ++ tailWord_3003059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003059).length < 2 ^ (prefixWord ++ tailWord_3003059).sum := by decide
  have hdescent : baseEnd_3003059 < baseStart_3003059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003069 : List Nat := [1, 4, 1, 2, 1, 3, 1, 4, 1, 5]
def baseStart_3003069 : Nat := 118140960795 + 3003069 * 2 ^ 59
def prefixEnd_3003069 : Nat := 4983230072969 + 3 ^ 40 * 3003069 * 2
def baseEnd_3003069 : Nat := 514005945205672070808881

theorem tailTrace_3003069 : CollatzResearch.WordTrace tailWord_3003069 prefixEnd_3003069 514005945205672070808881 := by
  unfold tailWord_3003069
  simp only [CollatzResearch.WordTrace]
  refine ⟨109530924757401371197580261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73020616504934247465053507 109530924757401371197580261)
  ·
    refine ⟨20537048392012757099546299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109530924757401371197580261 20537048392012757099546299)
    ·
      refine ⟨30805572588019135649319449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20537048392012757099546299 30805572588019135649319449)
      ·
        refine ⟨23104179441014351736989587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30805572588019135649319449 23104179441014351736989587)
        ·
          refine ⟨34656269161521527605484381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23104179441014351736989587 34656269161521527605484381)
          ·
            refine ⟨12996100935570572852056643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34656269161521527605484381 12996100935570572852056643)
            ·
              refine ⟨19494151403355859278084965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12996100935570572852056643 19494151403355859278084965)
              ·
                refine ⟨3655153388129223614640931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19494151403355859278084965 3655153388129223614640931)
                ·
                  refine ⟨5482730082193835421961397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3655153388129223614640931 5482730082193835421961397)
                  ·
                    refine ⟨514005945205672070808881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5482730082193835421961397 514005945205672070808881)
                    ·
                      rfl

theorem cell23_3003069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_3003069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003069 prefixEnd_3003069 := by exact prefixLift 3003069
  have htrace : WordTrace (prefixWord ++ tailWord_3003069) baseStart_3003069 baseEnd_3003069 := by
    simpa [prefixWord, tailWord_3003069, baseEnd_3003069] using wordTrace_append hprefix tailTrace_3003069
  have hstable : (prefixWord ++ tailWord_3003069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003069).length < 2 ^ (prefixWord ++ tailWord_3003069).sum := by decide
  have hdescent : baseEnd_3003069 < baseStart_3003069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003076 : List Nat := [2, 3, 3, 1, 1, 2, 2, 1, 1, 5, 2]
def baseStart_3003076 : Nat := 118140960795 + 3003076 * 2 ^ 59
def prefixEnd_3003076 : Nat := 4983230072969 + 3 ^ 40 * 3003076 * 2
def baseEnd_3003076 : Nat := 1542021429981597685039111

theorem tailTrace_3003076 : CollatzResearch.WordTrace tailWord_3003076 prefixEnd_3003076 1542021429981597685039111 := by
  unfold tailWord_3003076
  simp only [CollatzResearch.WordTrace]
  refine ⟨54765590034188005696542541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73020786712250674262056721 54765590034188005696542541)
  ·
    refine ⟨20537096262820502136203453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54765590034188005696542541 20537096262820502136203453)
    ·
      refine ⟨7701411098557688301076295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20537096262820502136203453 7701411098557688301076295)
      ·
        refine ⟨11552116647836532451614443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7701411098557688301076295 11552116647836532451614443)
        ·
          refine ⟨17328174971754798677421665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11552116647836532451614443 17328174971754798677421665)
          ·
            refine ⟨12996131228816099008066249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17328174971754798677421665 12996131228816099008066249)
            ·
              refine ⟨9747098421612074256049687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12996131228816099008066249 9747098421612074256049687)
              ·
                refine ⟨14620647632418111384074531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9747098421612074256049687 14620647632418111384074531)
                ·
                  refine ⟨21930971448627167076111797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14620647632418111384074531 21930971448627167076111797)
                  ·
                    refine ⟨2056028573308796913385481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21930971448627167076111797 2056028573308796913385481)
                    ·
                      refine ⟨1542021429981597685039111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2056028573308796913385481 1542021429981597685039111)
                      ·
                        rfl

theorem cell23_3003076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_3003076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003076 prefixEnd_3003076 := by exact prefixLift 3003076
  have htrace : WordTrace (prefixWord ++ tailWord_3003076) baseStart_3003076 baseEnd_3003076 := by
    simpa [prefixWord, tailWord_3003076, baseEnd_3003076] using wordTrace_append hprefix tailTrace_3003076
  have hstable : (prefixWord ++ tailWord_3003076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003076).length < 2 ^ (prefixWord ++ tailWord_3003076).sum := by decide
  have hdescent : baseEnd_3003076 < baseStart_3003076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003089 : List Nat := [1, 2, 2, 1, 2, 3, 1, 5, 1, 1, 4]
def baseStart_3003089 : Nat := 118140960795 + 3003089 * 2 ^ 59
def prefixEnd_3003089 : Nat := 4983230072969 + 3 ^ 40 * 3003089 * 2
def baseEnd_3003089 : Nat := 1542028105230106134176551

theorem tailTrace_3003089 : CollatzResearch.WordTrace tailWord_3003089 prefixEnd_3003089 1542028105230106134176551 := by
  unfold tailWord_3003089
  simp only [CollatzResearch.WordTrace]
  refine ⟨109531654217328914613308321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73021102811552609742205547 109531654217328914613308321)
  ·
    refine ⟨82148740662996685959981241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109531654217328914613308321 82148740662996685959981241)
    ·
      refine ⟨61611555497247514469985931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82148740662996685959981241 61611555497247514469985931)
      ·
        refine ⟨92417333245871271704978897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61611555497247514469985931 92417333245871271704978897)
        ·
          refine ⟨69312999934403453778734173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92417333245871271704978897 69312999934403453778734173)
          ·
            refine ⟨25992374975401295167025315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69312999934403453778734173 25992374975401295167025315)
            ·
              refine ⟨38988562463101942750537973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25992374975401295167025315 38988562463101942750537973)
              ·
                refine ⟨3655177730915807132862935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38988562463101942750537973 3655177730915807132862935)
                ·
                  refine ⟨5482766596373710699294403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3655177730915807132862935 5482766596373710699294403)
                  ·
                    refine ⟨8224149894560566048941605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5482766596373710699294403 8224149894560566048941605)
                    ·
                      refine ⟨1542028105230106134176551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8224149894560566048941605 1542028105230106134176551)
                      ·
                        rfl

theorem cell23_3003089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 1, 4].length) (baseStart_3003089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003089 prefixEnd_3003089 := by exact prefixLift 3003089
  have htrace : WordTrace (prefixWord ++ tailWord_3003089) baseStart_3003089 baseEnd_3003089 := by
    simpa [prefixWord, tailWord_3003089, baseEnd_3003089] using wordTrace_append hprefix tailTrace_3003089
  have hstable : (prefixWord ++ tailWord_3003089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003089).length < 2 ^ (prefixWord ++ tailWord_3003089).sum := by decide
  have hdescent : baseEnd_3003089 < baseStart_3003089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003100 : List Nat := [2, 2, 5, 1, 1, 3, 1, 1, 3, 1, 3]
def baseStart_3003100 : Nat := 118140960795 + 3003100 * 2 ^ 59
def prefixEnd_3003100 : Nat := 4983230072969 + 3 ^ 40 * 3003100 * 2
def baseEnd_3003100 : Nat := 1542033753517305591139001

theorem tailTrace_3003100 : CollatzResearch.WordTrace tailWord_3003100 prefixEnd_3003100 1542033753517305591139001 := by
  unfold tailWord_3003100
  simp only [CollatzResearch.WordTrace]
  refine ⟨54766027710144531745979377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73021370280192708994639169 54766027710144531745979377)
  ·
    refine ⟨41074520782608398809484533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54766027710144531745979377 41074520782608398809484533)
    ·
      refine ⟨3850736323369537388389175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41074520782608398809484533 3850736323369537388389175)
      ·
        refine ⟨5776104485054306082583763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3850736323369537388389175 5776104485054306082583763)
        ·
          refine ⟨8664156727581459123875645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5776104485054306082583763 8664156727581459123875645)
          ·
            refine ⟨3249058772843047171453367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8664156727581459123875645 3249058772843047171453367)
            ·
              refine ⟨4873588159264570757180051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3249058772843047171453367 4873588159264570757180051)
              ·
                refine ⟨7310382238896856135770077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4873588159264570757180051 7310382238896856135770077)
                ·
                  refine ⟨2741393339586321050913779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7310382238896856135770077 2741393339586321050913779)
                  ·
                    refine ⟨4112090009379481576370669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2741393339586321050913779 4112090009379481576370669)
                    ·
                      refine ⟨1542033753517305591139001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4112090009379481576370669 1542033753517305591139001)
                      ·
                        rfl

theorem cell23_3003100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_3003100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003100 prefixEnd_3003100 := by exact prefixLift 3003100
  have htrace : WordTrace (prefixWord ++ tailWord_3003100) baseStart_3003100 baseEnd_3003100 := by
    simpa [prefixWord, tailWord_3003100, baseEnd_3003100] using wordTrace_append hprefix tailTrace_3003100
  have hstable : (prefixWord ++ tailWord_3003100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003100).length < 2 ^ (prefixWord ++ tailWord_3003100).sum := by decide
  have hdescent : baseEnd_3003100 < baseStart_3003100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003109 : List Nat := [1, 3, 1, 4, 1, 2, 2, 2, 1, 1, 5]
def baseStart_3003109 : Nat := 118140960795 + 3003109 * 2 ^ 59
def prefixEnd_3003109 : Nat := 4983230072969 + 3 ^ 40 * 3003109 * 2
def baseEnd_3003109 : Nat := 1542038374843196055926459

theorem tailTrace_3003109 : CollatzResearch.WordTrace tailWord_3003109 prefixEnd_3003109 1542038374843196055926459 := by
  unfold tailWord_3003109
  simp only [CollatzResearch.WordTrace]
  refine ⟨109532383677256458029036381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73021589118170972019357587 109532383677256458029036381)
  ·
    refine ⟨41074643878971171760888643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109532383677256458029036381 41074643878971171760888643)
    ·
      refine ⟨61611965818456757641332965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41074643878971171760888643 61611965818456757641332965)
      ·
        refine ⟨11552243590960642057749931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61611965818456757641332965 11552243590960642057749931)
        ·
          refine ⟨17328365386440963086624897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11552243590960642057749931 17328365386440963086624897)
          ·
            refine ⟨12996274039830722314968673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17328365386440963086624897 12996274039830722314968673)
            ·
              refine ⟨9747205529873041736226505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12996274039830722314968673 9747205529873041736226505)
              ·
                refine ⟨7310404147404781302169879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9747205529873041736226505 7310404147404781302169879)
                ·
                  refine ⟨10965606221107171953254819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7310404147404781302169879 10965606221107171953254819)
                  ·
                    refine ⟨16448409331660757929882229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10965606221107171953254819 16448409331660757929882229)
                    ·
                      refine ⟨1542038374843196055926459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16448409331660757929882229 1542038374843196055926459)
                      ·
                        rfl

theorem cell23_3003109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_3003109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003109 prefixEnd_3003109 := by exact prefixLift 3003109
  have htrace : WordTrace (prefixWord ++ tailWord_3003109) baseStart_3003109 baseEnd_3003109 := by
    simpa [prefixWord, tailWord_3003109, baseEnd_3003109] using wordTrace_append hprefix tailTrace_3003109
  have hstable : (prefixWord ++ tailWord_3003109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003109).length < 2 ^ (prefixWord ++ tailWord_3003109).sum := by decide
  have hdescent : baseEnd_3003109 < baseStart_3003109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003126 : List Nat := [5, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3]
def baseStart_3003126 : Nat := 118140960795 + 3003126 * 2 ^ 59
def prefixEnd_3003126 : Nat := 4983230072969 + 3 ^ 40 * 3003126 * 2
def baseEnd_3003126 : Nat := 1542047104014322489413881

theorem tailTrace_3003126 : CollatzResearch.WordTrace tailWord_3003126 prefixEnd_3003126 1542047104014322489413881 := by
  unfold tailWord_3003126
  simp only [CollatzResearch.WordTrace]
  refine ⟨6845812732387179370775327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73022002478796579954936821 6845812732387179370775327)
  ·
    refine ⟨10268719098580769056162991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6845812732387179370775327 10268719098580769056162991)
    ·
      refine ⟨15403078647871153584244487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10268719098580769056162991 15403078647871153584244487)
      ·
        refine ⟨23104617971806730376366731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15403078647871153584244487 23104617971806730376366731)
        ·
          refine ⟨34656926957710095564550097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23104617971806730376366731 34656926957710095564550097)
          ·
            refine ⟨25992695218282571673412573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34656926957710095564550097 25992695218282571673412573)
            ·
              refine ⟨9747260706855964377529715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25992695218282571673412573 9747260706855964377529715)
              ·
                refine ⟨14620891060283946566294573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9747260706855964377529715 14620891060283946566294573)
                ·
                  refine ⟨5482834147606479962360465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14620891060283946566294573 5482834147606479962360465)
                  ·
                    refine ⟨4112125610704859971770349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5482834147606479962360465 4112125610704859971770349)
                    ·
                      refine ⟨1542047104014322489413881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4112125610704859971770349 1542047104014322489413881)
                      ·
                        rfl

theorem cell23_3003126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_3003126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003126 prefixEnd_3003126 := by exact prefixLift 3003126
  have htrace : WordTrace (prefixWord ++ tailWord_3003126) baseStart_3003126 baseEnd_3003126 := by
    simpa [prefixWord, tailWord_3003126, baseEnd_3003126] using wordTrace_append hprefix tailTrace_3003126
  have hstable : (prefixWord ++ tailWord_3003126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003126).length < 2 ^ (prefixWord ++ tailWord_3003126).sum := by decide
  have hdescent : baseEnd_3003126 < baseStart_3003126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003140 : List Nat := [2, 3, 2, 2, 1, 1, 2, 5, 1, 2, 2]
def baseStart_3003140 : Nat := 118140960795 + 3003140 * 2 ^ 59
def prefixEnd_3003140 : Nat := 4983230072969 + 3 ^ 40 * 3003140 * 2
def baseEnd_3003140 : Nat := 1542054292743485434638817

theorem tailTrace_3003140 : CollatzResearch.WordTrace tailWord_3003140 prefixEnd_3003140 1542054292743485434638817 := by
  unfold tailWord_3003140
  simp only [CollatzResearch.WordTrace]
  refine ⟨54766757170072075161707437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73022342893429433548943249 54766757170072075161707437)
  ·
    refine ⟨20537533938777028185640289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54766757170072075161707437 20537533938777028185640289)
    ·
      refine ⟨15403150454082771139230217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20537533938777028185640289 15403150454082771139230217)
      ·
        refine ⟨11552362840562078354422663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15403150454082771139230217 11552362840562078354422663)
        ·
          refine ⟨17328544260843117531633995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11552362840562078354422663 17328544260843117531633995)
          ·
            refine ⟨25992816391264676297450993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17328544260843117531633995 25992816391264676297450993)
            ·
              refine ⟨19494612293448507223088245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25992816391264676297450993 19494612293448507223088245)
              ·
                refine ⟨1827619902510797552164523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19494612293448507223088245 1827619902510797552164523)
                ·
                  refine ⟨2741429853766196328246785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1827619902510797552164523 2741429853766196328246785)
                  ·
                    refine ⟨2056072390324647246185089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2741429853766196328246785 2056072390324647246185089)
                    ·
                      refine ⟨1542054292743485434638817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2056072390324647246185089 1542054292743485434638817)
                      ·
                        rfl

theorem cell23_3003140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_3003140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003140 prefixEnd_3003140 := by exact prefixLift 3003140
  have htrace : WordTrace (prefixWord ++ tailWord_3003140) baseStart_3003140 baseEnd_3003140 := by
    simpa [prefixWord, tailWord_3003140, baseEnd_3003140] using wordTrace_append hprefix tailTrace_3003140
  have hstable : (prefixWord ++ tailWord_3003140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003140).length < 2 ^ (prefixWord ++ tailWord_3003140).sum := by decide
  have hdescent : baseEnd_3003140 < baseStart_3003140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003209 : List Nat := [1, 2, 1, 1, 2, 5, 1, 2, 2, 2, 4]
def baseStart_3003209 : Nat := 118140960795 + 3003209 * 2 ^ 59
def prefixEnd_3003209 : Nat := 4983230072969 + 3 ^ 40 * 3003209 * 2
def baseEnd_3003209 : Nat := 1542089722908645664675999

theorem tailTrace_3003209 : CollatzResearch.WordTrace tailWord_3003209 prefixEnd_3003209 1542089722908645664675999 := by
  unfold tailWord_3003209
  simp only [CollatzResearch.WordTrace]
  refine ⟨109536030976894175107676681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73024020651262783405117787 109536030976894175107676681)
  ·
    refine ⟨82152023232670631330757511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109536030976894175107676681 82152023232670631330757511)
    ·
      refine ⟨123228034849005946996136267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82152023232670631330757511 123228034849005946996136267)
      ·
        refine ⟨184842052273508920494204401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123228034849005946996136267 184842052273508920494204401)
        ·
          refine ⟨138631539205131690370653301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184842052273508920494204401 138631539205131690370653301)
          ·
            refine ⟨12996706800481095972248747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 138631539205131690370653301 12996706800481095972248747)
            ·
              refine ⟨19495060200721643958373121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12996706800481095972248747 19495060200721643958373121)
              ·
                refine ⟨14621295150541232968779841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19495060200721643958373121 14621295150541232968779841)
                ·
                  refine ⟨10965971362905924726584881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14621295150541232968779841 10965971362905924726584881)
                  ·
                    refine ⟨8224478522179443544938661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10965971362905924726584881 8224478522179443544938661)
                    ·
                      refine ⟨1542089722908645664675999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8224478522179443544938661 1542089722908645664675999)
                      ·
                        rfl

theorem cell23_3003209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 2, 4].length) (baseStart_3003209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003209 prefixEnd_3003209 := by exact prefixLift 3003209
  have htrace : WordTrace (prefixWord ++ tailWord_3003209) baseStart_3003209 baseEnd_3003209 := by
    simpa [prefixWord, tailWord_3003209, baseEnd_3003209] using wordTrace_append hprefix tailTrace_3003209
  have hstable : (prefixWord ++ tailWord_3003209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003209).length < 2 ^ (prefixWord ++ tailWord_3003209).sum := by decide
  have hdescent : baseEnd_3003209 < baseStart_3003209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003249 : List Nat := [1, 2, 2, 2, 1, 4, 2, 1, 1, 7]
def baseStart_3003249 : Nat := 118140960795 + 3003249 * 2 ^ 59
def prefixEnd_3003249 : Nat := 4983230072969 + 3 ^ 40 * 3003249 * 2
def baseEnd_3003249 : Nat := 514036754044941836058605

theorem tailTrace_3003249 : CollatzResearch.WordTrace tailWord_3003249 prefixEnd_3003249 514036754044941836058605 := by
  unfold tailWord_3003249
  simp only [CollatzResearch.WordTrace]
  refine ⟨109537489896749261939132801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73024993264499507959421867 109537489896749261939132801)
  ·
    refine ⟨82153117422561946454349601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109537489896749261939132801 82153117422561946454349601)
    ·
      refine ⟨61614838066921459840762201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82153117422561946454349601 61614838066921459840762201)
      ·
        refine ⟨46211128550191094880571651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61614838066921459840762201 46211128550191094880571651)
        ·
          refine ⟨69316692825286642320857477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46211128550191094880571651 69316692825286642320857477)
          ·
            refine ⟨12996879904741245435160777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69316692825286642320857477 12996879904741245435160777)
            ·
              refine ⟨9747659928555934076370583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12996879904741245435160777 9747659928555934076370583)
              ·
                refine ⟨14621489892833901114555875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9747659928555934076370583 14621489892833901114555875)
                ·
                  refine ⟨21932234839250851671833813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14621489892833901114555875 21932234839250851671833813)
                  ·
                    refine ⟨514036754044941836058605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21932234839250851671833813 514036754044941836058605)
                    ·
                      rfl

theorem cell23_3003249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 7].length) (baseStart_3003249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003249 prefixEnd_3003249 := by exact prefixLift 3003249
  have htrace : WordTrace (prefixWord ++ tailWord_3003249) baseStart_3003249 baseEnd_3003249 := by
    simpa [prefixWord, tailWord_3003249, baseEnd_3003249] using wordTrace_append hprefix tailTrace_3003249
  have hstable : (prefixWord ++ tailWord_3003249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003249).length < 2 ^ (prefixWord ++ tailWord_3003249).sum := by decide
  have hdescent : baseEnd_3003249 < baseStart_3003249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003253 : List Nat := [1, 3, 4, 1, 1, 2, 3, 3, 5]
def baseStart_3003253 : Nat := 118140960795 + 3003253 * 2 ^ 59
def prefixEnd_3003253 : Nat := 4983230072969 + 3 ^ 40 * 3003253 * 2
def baseEnd_3003253 : Nat := 171345812895271499169533

theorem tailTrace_3003253 : CollatzResearch.WordTrace tailWord_3003253 prefixEnd_3003253 171345812895271499169533 := by
  unfold tailWord_3003253
  simp only [CollatzResearch.WordTrace]
  refine ⟨109537635788734770622278413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73025090525823180414852275 109537635788734770622278413)
  ·
    refine ⟨41076613420775538983354405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109537635788734770622278413 41076613420775538983354405)
    ·
      refine ⟨7701865016395413559378951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41076613420775538983354405 7701865016395413559378951)
      ·
        refine ⟨11552797524593120339068427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7701865016395413559378951 11552797524593120339068427)
        ·
          refine ⟨17329196286889680508602641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11552797524593120339068427 17329196286889680508602641)
          ·
            refine ⟨12996897215167260381451981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17329196286889680508602641 12996897215167260381451981)
            ·
              refine ⟨4873836455687722643044493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12996897215167260381451981 4873836455687722643044493)
              ·
                refine ⟨1827688670882895991141685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4873836455687722643044493 1827688670882895991141685)
                ·
                  refine ⟨171345812895271499169533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1827688670882895991141685 171345812895271499169533)
                  ·
                    rfl

theorem cell23_3003253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 3, 5].length) (baseStart_3003253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003253 prefixEnd_3003253 := by exact prefixLift 3003253
  have htrace : WordTrace (prefixWord ++ tailWord_3003253) baseStart_3003253 baseEnd_3003253 := by
    simpa [prefixWord, tailWord_3003253, baseEnd_3003253] using wordTrace_append hprefix tailTrace_3003253
  have hstable : (prefixWord ++ tailWord_3003253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003253).length < 2 ^ (prefixWord ++ tailWord_3003253).sum := by decide
  have hdescent : baseEnd_3003253 < baseStart_3003253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003296 : List Nat := [2, 1, 1, 4, 1, 1, 2, 4, 3, 4]
def baseStart_3003296 : Nat := 118140960795 + 3003296 * 2 ^ 59
def prefixEnd_3003296 : Nat := 4983230072969 + 3 ^ 40 * 3003296 * 2
def baseEnd_3003296 : Nat := 514044798575195608096033

theorem tailTrace_3003296 : CollatzResearch.WordTrace tailWord_3003296 prefixEnd_3003296 514044798575195608096033 := by
  unfold tailWord_3003296
  simp only [CollatzResearch.WordTrace]
  refine ⟨54769602063789494483046871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73026136085052659310729161 54769602063789494483046871)
  ·
    refine ⟨82154403095684241724570307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54769602063789494483046871 82154403095684241724570307)
    ·
      refine ⟨123231604643526362586855461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82154403095684241724570307 123231604643526362586855461)
      ·
        refine ⟨23105925870661192985035399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123231604643526362586855461 23105925870661192985035399)
        ·
          refine ⟨34658888805991789477553099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23105925870661192985035399 34658888805991789477553099)
          ·
            refine ⟨51988333208987684216329649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34658888805991789477553099 51988333208987684216329649)
            ·
              refine ⟨38991249906740763162247237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51988333208987684216329649 38991249906740763162247237)
              ·
                refine ⟨7310859357513893092921357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38991249906740763162247237 7310859357513893092921357)
                ·
                  refine ⟨2741572259067709909845509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7310859357513893092921357 2741572259067709909845509)
                  ·
                    refine ⟨514044798575195608096033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2741572259067709909845509 514044798575195608096033)
                    ·
                      rfl

theorem cell23_3003296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 3, 4].length) (baseStart_3003296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003296 prefixEnd_3003296 := by exact prefixLift 3003296
  have htrace : WordTrace (prefixWord ++ tailWord_3003296) baseStart_3003296 baseEnd_3003296 := by
    simpa [prefixWord, tailWord_3003296, baseEnd_3003296] using wordTrace_append hprefix tailTrace_3003296
  have hstable : (prefixWord ++ tailWord_3003296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003296).length < 2 ^ (prefixWord ++ tailWord_3003296).sum := by decide
  have hdescent : baseEnd_3003296 < baseStart_3003296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003299 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 4]
def baseStart_3003299 : Nat := 118140960795 + 3003299 * 2 ^ 59
def prefixEnd_3003299 : Nat := 4983230072969 + 3 ^ 40 * 3003299 * 2
def baseEnd_3003299 : Nat := 1542135936167550312550585

theorem tailTrace_3003299 : CollatzResearch.WordTrace tailWord_3003299 prefixEnd_3003299 1542135936167550312550585 := by
  unfold tailWord_3003299
  simp only [CollatzResearch.WordTrace]
  refine ⟨109539313546568120478452951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73026209031045413652301967 109539313546568120478452951)
  ·
    refine ⟨164308970319852180717679427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109539313546568120478452951 164308970319852180717679427)
    ·
      refine ⟨246463455479778271076519141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164308970319852180717679427 246463455479778271076519141)
      ·
        refine ⟨46211897902458425826847339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 246463455479778271076519141 46211897902458425826847339)
        ·
          refine ⟨69317846853687638740271009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46211897902458425826847339 69317846853687638740271009)
          ·
            refine ⟨51988385140265729055203257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69317846853687638740271009 51988385140265729055203257)
            ·
              refine ⟨38991288855199296791402443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51988385140265729055203257 38991288855199296791402443)
              ·
                refine ⟨58486933282798945187103665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38991288855199296791402443 58486933282798945187103665)
                ·
                  refine ⟨43865199962099208890327749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58486933282798945187103665 43865199962099208890327749)
                  ·
                    refine ⟨8224724992893601666936453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43865199962099208890327749 8224724992893601666936453)
                    ·
                      refine ⟨1542135936167550312550585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8224724992893601666936453 1542135936167550312550585)
                      ·
                        rfl

theorem cell23_3003299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_3003299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003299 prefixEnd_3003299 := by exact prefixLift 3003299
  have htrace : WordTrace (prefixWord ++ tailWord_3003299) baseStart_3003299 baseEnd_3003299 := by
    simpa [prefixWord, tailWord_3003299, baseEnd_3003299] using wordTrace_append hprefix tailTrace_3003299
  have hstable : (prefixWord ++ tailWord_3003299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003299).length < 2 ^ (prefixWord ++ tailWord_3003299).sum := by decide
  have hdescent : baseEnd_3003299 < baseStart_3003299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003353 : List Nat := [1, 2, 1, 2, 5, 1, 1, 1, 5, 1, 3]
def baseStart_3003353 : Nat := 118140960795 + 3003353 * 2 ^ 59
def prefixEnd_3003353 : Nat := 4983230072969 + 3 ^ 40 * 3003353 * 2
def baseEnd_3003353 : Nat := 1542163664122893101275337

theorem tailTrace_3003353 : CollatzResearch.WordTrace tailWord_3003353 prefixEnd_3003353 1542163664122893101275337 := by
  unfold tailWord_3003353
  simp only [CollatzResearch.WordTrace]
  refine ⟨109541283088372487700918713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73027522058914991800612475 109541283088372487700918713)
  ·
    refine ⟨82155962316279365775689035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109541283088372487700918713 82155962316279365775689035)
    ·
      refine ⟨123233943474419048663533553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82155962316279365775689035 123233943474419048663533553)
      ·
        refine ⟨92425457605814286497650165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123233943474419048663533553 92425457605814286497650165)
        ·
          refine ⟨8664886650545089359154703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92425457605814286497650165 8664886650545089359154703)
          ·
            refine ⟨12997329975817634038732055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8664886650545089359154703 12997329975817634038732055)
            ·
              refine ⟨19495994963726451058098083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12997329975817634038732055 19495994963726451058098083)
              ·
                refine ⟨29243992445589676587147125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19495994963726451058098083 29243992445589676587147125)
                ·
                  refine ⟨2741624291774032180045043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29243992445589676587147125 2741624291774032180045043)
                  ·
                    refine ⟨4112436437661048270067565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2741624291774032180045043 4112436437661048270067565)
                    ·
                      refine ⟨1542163664122893101275337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4112436437661048270067565 1542163664122893101275337)
                      ·
                        rfl

theorem cell23_3003353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 5, 1, 3].length) (baseStart_3003353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003353 prefixEnd_3003353 := by exact prefixLift 3003353
  have htrace : WordTrace (prefixWord ++ tailWord_3003353) baseStart_3003353 baseEnd_3003353 := by
    simpa [prefixWord, tailWord_3003353, baseEnd_3003353] using wordTrace_append hprefix tailTrace_3003353
  have hstable : (prefixWord ++ tailWord_3003353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003353).length < 2 ^ (prefixWord ++ tailWord_3003353).sum := by decide
  have hdescent : baseEnd_3003353 < baseStart_3003353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003363 : List Nat := [1, 1, 1, 6, 1, 1, 3, 1, 1, 5, 2]
def baseStart_3003363 : Nat := 118140960795 + 3003363 * 2 ^ 59
def prefixEnd_3003363 : Nat := 4983230072969 + 3 ^ 40 * 3003363 * 2
def baseEnd_3003363 : Nat := 1542168798929438062150291

theorem tailTrace_3003363 : CollatzResearch.WordTrace tailWord_3003363 prefixEnd_3003363 1542168798929438062150291 := by
  unfold tailWord_3003363
  simp only [CollatzResearch.WordTrace]
  refine ⟨109541647818336259408782743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73027765212224172939188495 109541647818336259408782743)
  ·
    refine ⟨164312471727504389113174115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109541647818336259408782743 164312471727504389113174115)
    ·
      refine ⟨246468707591256583669761173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164312471727504389113174115 246468707591256583669761173)
      ·
        refine ⟨11553220668340152359520055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 246468707591256583669761173 11553220668340152359520055)
        ·
          refine ⟨17329831002510228539280083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11553220668340152359520055 17329831002510228539280083)
          ·
            refine ⟨25994746503765342808920125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17329831002510228539280083 25994746503765342808920125)
            ·
              refine ⟨9748029938912003553345047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25994746503765342808920125 9748029938912003553345047)
              ·
                refine ⟨14622044908368005330017571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9748029938912003553345047 14622044908368005330017571)
                ·
                  refine ⟨21933067362552007995026357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14622044908368005330017571 21933067362552007995026357)
                  ·
                    refine ⟨2056225065239250749533721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21933067362552007995026357 2056225065239250749533721)
                    ·
                      refine ⟨1542168798929438062150291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2056225065239250749533721 1542168798929438062150291)
                      ·
                        rfl

theorem cell23_3003363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_3003363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003363 prefixEnd_3003363 := by exact prefixLift 3003363
  have htrace : WordTrace (prefixWord ++ tailWord_3003363) baseStart_3003363 baseEnd_3003363 := by
    simpa [prefixWord, tailWord_3003363, baseEnd_3003363] using wordTrace_append hprefix tailTrace_3003363
  have hstable : (prefixWord ++ tailWord_3003363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003363).length < 2 ^ (prefixWord ++ tailWord_3003363).sum := by decide
  have hdescent : baseEnd_3003363 < baseStart_3003363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003403 : List Nat := [1, 1, 1, 1, 6, 4, 1, 1, 1, 6]
def baseStart_3003403 : Nat := 118140960795 + 3003403 * 2 ^ 59
def prefixEnd_3003403 : Nat := 4983230072969 + 3 ^ 40 * 3003403 * 2
def baseEnd_3003403 : Nat := 514063112718539301883369

theorem tailTrace_3003403 : CollatzResearch.WordTrace tailWord_3003403 prefixEnd_3003403 514063112718539301883369 := by
  unfold tailWord_3003403
  simp only [CollatzResearch.WordTrace]
  refine ⟨109543106738191346240238863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73028737825460897493492575 109543106738191346240238863)
  ·
    refine ⟨164314660107287019360358295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109543106738191346240238863 164314660107287019360358295)
    ·
      refine ⟨246471990160930529040537443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164314660107287019360358295 246471990160930529040537443)
      ·
        refine ⟨369707985241395793560806165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246471990160930529040537443 369707985241395793560806165)
        ·
          refine ⟨17330061808190427823162789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 369707985241395793560806165 17330061808190427823162789)
          ·
            refine ⟨3249386589035705216843023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17330061808190427823162789 3249386589035705216843023)
            ·
              refine ⟨4874079883553557825264535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3249386589035705216843023 4874079883553557825264535)
              ·
                refine ⟨7311119825330336737896803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4874079883553557825264535 7311119825330336737896803)
                ·
                  refine ⟨10966679737995505106845205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7311119825330336737896803 10966679737995505106845205)
                  ·
                    refine ⟨514063112718539301883369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10966679737995505106845205 514063112718539301883369)
                    ·
                      rfl

theorem cell23_3003403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 6].length) (baseStart_3003403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003403 prefixEnd_3003403 := by exact prefixLift 3003403
  have htrace : WordTrace (prefixWord ++ tailWord_3003403) baseStart_3003403 baseEnd_3003403 := by
    simpa [prefixWord, tailWord_3003403, baseEnd_3003403] using wordTrace_append hprefix tailTrace_3003403
  have hstable : (prefixWord ++ tailWord_3003403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003403).length < 2 ^ (prefixWord ++ tailWord_3003403).sum := by decide
  have hdescent : baseEnd_3003403 < baseStart_3003403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003416 : List Nat := [2, 1, 2, 3, 2, 3, 1, 9]
def baseStart_3003416 : Nat := 118140960795 + 3003416 * 2 ^ 59
def prefixEnd_3003416 : Nat := 4983230072969 + 3 ^ 40 * 3003416 * 2
def baseEnd_3003416 : Nat := 57118370866819494621761

theorem tailTrace_3003416 : CollatzResearch.WordTrace tailWord_3003416 prefixEnd_3003416 57118370866819494621761 := by
  unfold tailWord_3003416
  simp only [CollatzResearch.WordTrace]
  refine ⟨54771790443572124730231051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73029053924762832973641401 54771790443572124730231051)
  ·
    refine ⟨82157685665358187095346577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54771790443572124730231051 82157685665358187095346577)
    ·
      refine ⟨61618264249018640321509933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82157685665358187095346577 61618264249018640321509933)
      ·
        refine ⟨23106849093381990120566225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61618264249018640321509933 23106849093381990120566225)
        ·
          refine ⟨17330136820036492590424669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23106849093381990120566225 17330136820036492590424669)
          ·
            refine ⟨6498801307513684721409251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17330136820036492590424669 6498801307513684721409251)
            ·
              refine ⟨9748201961270527082113877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6498801307513684721409251 9748201961270527082113877)
              ·
                refine ⟨57118370866819494621761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9748201961270527082113877 57118370866819494621761)
                ·
                  rfl

theorem cell23_3003416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 9].length) (baseStart_3003416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003416 prefixEnd_3003416 := by exact prefixLift 3003416
  have htrace : WordTrace (prefixWord ++ tailWord_3003416) baseStart_3003416 baseEnd_3003416 := by
    simpa [prefixWord, tailWord_3003416, baseEnd_3003416] using wordTrace_append hprefix tailTrace_3003416
  have hstable : (prefixWord ++ tailWord_3003416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003416).length < 2 ^ (prefixWord ++ tailWord_3003416).sum := by decide
  have hdescent : baseEnd_3003416 < baseStart_3003416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003421 : List Nat := [1, 4, 2, 2, 4, 1, 1, 3, 1, 1, 3]
def baseStart_3003421 : Nat := 118140960795 + 3003421 * 2 ^ 59
def prefixEnd_3003421 : Nat := 4983230072969 + 3 ^ 40 * 3003421 * 2
def baseEnd_3003421 : Nat := 1542198580807398835225025

theorem tailTrace_3003421 : CollatzResearch.WordTrace tailWord_3003421 prefixEnd_3003421 1542198580807398835225025 := by
  unfold tailWord_3003421
  simp only [CollatzResearch.WordTrace]
  refine ⟨109543763252126135314394117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73029175501417423542929411 109543763252126135314394117)
  ·
    refine ⟨20539455609773650371448897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109543763252126135314394117 20539455609773650371448897)
    ·
      refine ⟨15404591707330237778586673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20539455609773650371448897 15404591707330237778586673)
      ·
        refine ⟨11553443780497678333940005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15404591707330237778586673 11553443780497678333940005)
        ·
          refine ⟨2166270708843314687613751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11553443780497678333940005 2166270708843314687613751)
          ·
            refine ⟨3249406063264972031420627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2166270708843314687613751 3249406063264972031420627)
            ·
              refine ⟨4874109094897458047130941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3249406063264972031420627 4874109094897458047130941)
              ·
                refine ⟨1827790910586546767674103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4874109094897458047130941 1827790910586546767674103)
                ·
                  refine ⟨2741686365879820151511155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1827790910586546767674103 2741686365879820151511155)
                  ·
                    refine ⟨4112529548819730227266733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2741686365879820151511155 4112529548819730227266733)
                    ·
                      refine ⟨1542198580807398835225025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4112529548819730227266733 1542198580807398835225025)
                      ·
                        rfl

theorem cell23_3003421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_3003421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003421 prefixEnd_3003421 := by exact prefixLift 3003421
  have htrace : WordTrace (prefixWord ++ tailWord_3003421) baseStart_3003421 baseEnd_3003421 := by
    simpa [prefixWord, tailWord_3003421, baseEnd_3003421] using wordTrace_append hprefix tailTrace_3003421
  have hstable : (prefixWord ++ tailWord_3003421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003421).length < 2 ^ (prefixWord ++ tailWord_3003421).sum := by decide
  have hdescent : baseEnd_3003421 < baseStart_3003421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003444 : List Nat := [2, 5, 1, 2, 1, 1, 3, 1, 3, 2, 2]
def baseStart_3003444 : Nat := 118140960795 + 3003444 * 2 ^ 59
def prefixEnd_3003444 : Nat := 4983230072969 + 3 ^ 40 * 3003444 * 2
def baseEnd_3003444 : Nat := 1542210390862452245237419

theorem tailTrace_3003444 : CollatzResearch.WordTrace tailWord_3003444 prefixEnd_3003444 1542210390862452245237419 := by
  unfold tailWord_3003444
  simp only [CollatzResearch.WordTrace]
  refine ⟨54772301065521405121240693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73029734754028540161654257 54772301065521405121240693)
  ·
    refine ⟨5134903224892631730116315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54772301065521405121240693 5134903224892631730116315)
    ·
      refine ⟨7702354837338947595174473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5134903224892631730116315 7702354837338947595174473)
      ·
        refine ⟨5776766128004210696380855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7702354837338947595174473 5776766128004210696380855)
        ·
          refine ⟨8665149192006316044571283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5776766128004210696380855 8665149192006316044571283)
          ·
            refine ⟨12997723788009474066856925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8665149192006316044571283 12997723788009474066856925)
            ·
              refine ⟨4874146420503552775071347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12997723788009474066856925 4874146420503552775071347)
              ·
                refine ⟨7311219630755329162607021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4874146420503552775071347 7311219630755329162607021)
                ·
                  refine ⟨2741707361533248435977633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7311219630755329162607021 2741707361533248435977633)
                  ·
                    refine ⟨2056280521149936326983225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2741707361533248435977633 2056280521149936326983225)
                    ·
                      refine ⟨1542210390862452245237419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2056280521149936326983225 1542210390862452245237419)
                      ·
                        rfl

theorem cell23_3003444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_3003444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003444 prefixEnd_3003444 := by exact prefixLift 3003444
  have htrace : WordTrace (prefixWord ++ tailWord_3003444) baseStart_3003444 baseEnd_3003444 := by
    simpa [prefixWord, tailWord_3003444, baseEnd_3003444] using wordTrace_append hprefix tailTrace_3003444
  have hstable : (prefixWord ++ tailWord_3003444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003444).length < 2 ^ (prefixWord ++ tailWord_3003444).sum := by decide
  have hdescent : baseEnd_3003444 < baseStart_3003444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003454 : List Nat := [4, 2, 1, 3, 1, 3, 2, 1, 2, 4]
def baseStart_3003454 : Nat := 118140960795 + 3003454 * 2 ^ 59
def prefixEnd_3003454 : Nat := 4983230072969 + 3 ^ 40 * 3003454 * 2
def baseEnd_3003454 : Nat := 514071841889665735370791

theorem tailTrace_3003454 : CollatzResearch.WordTrace tailWord_3003454 prefixEnd_3003454 514071841889665735370791 := by
  unfold tailWord_3003454
  simp only [CollatzResearch.WordTrace]
  refine ⟨13693120857625822743793177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73029977907337721300230277 13693120857625822743793177)
  ·
    refine ⟨10269840643219367057844883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13693120857625822743793177 10269840643219367057844883)
    ·
      refine ⟨15404760964829050586767325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10269840643219367057844883 15404760964829050586767325)
      ·
        refine ⟨5776785361810893970037747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15404760964829050586767325 5776785361810893970037747)
        ·
          refine ⟨8665178042716340955056621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5776785361810893970037747 8665178042716340955056621)
          ·
            refine ⟨3249441766018627858146233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8665178042716340955056621 3249441766018627858146233)
            ·
              refine ⟨2437081324513970893609675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3249441766018627858146233 2437081324513970893609675)
              ·
                refine ⟨3655621986770956340414513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2437081324513970893609675 3655621986770956340414513)
                ·
                  refine ⟨2741716490078217255310885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3655621986770956340414513 2741716490078217255310885)
                  ·
                    refine ⟨514071841889665735370791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2741716490078217255310885 514071841889665735370791)
                    ·
                      rfl

theorem cell23_3003454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_3003454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003454 prefixEnd_3003454 := by exact prefixLift 3003454
  have htrace : WordTrace (prefixWord ++ tailWord_3003454) baseStart_3003454 baseEnd_3003454 := by
    simpa [prefixWord, tailWord_3003454, baseEnd_3003454] using wordTrace_append hprefix tailTrace_3003454
  have hstable : (prefixWord ++ tailWord_3003454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003454).length < 2 ^ (prefixWord ++ tailWord_3003454).sum := by decide
  have hdescent : baseEnd_3003454 < baseStart_3003454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003470 : List Nat := [4, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2]
def baseStart_3003470 : Nat := 118140960795 + 3003470 * 2 ^ 59
def prefixEnd_3003470 : Nat := 4983230072969 + 3 ^ 40 * 3003470 * 2
def baseEnd_3003470 : Nat := 1542223741359469143512299

theorem tailTrace_3003470 : CollatzResearch.WordTrace tailWord_3003470 prefixEnd_3003470 1542223741359469143512299 := by
  unfold tailWord_3003470
  simp only [CollatzResearch.WordTrace]
  refine ⟨13693193803618577085365983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73030366952632411121951909 13693193803618577085365983)
  ·
    refine ⟨20539790705427865628048975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13693193803618577085365983 20539790705427865628048975)
    ·
      refine ⟨30809686058141798442073463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20539790705427865628048975 30809686058141798442073463)
      ·
        refine ⟨46214529087212697663110195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30809686058141798442073463 46214529087212697663110195)
        ·
          refine ⟨69321793630819046494665293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46214529087212697663110195 69321793630819046494665293)
          ·
            refine ⟨25995672611557142435499485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69321793630819046494665293 25995672611557142435499485)
            ·
              refine ⟨9748377229333928413312307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25995672611557142435499485 9748377229333928413312307)
              ·
                refine ⟨14622565844000892619968461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9748377229333928413312307 14622565844000892619968461)
                ·
                  refine ⟨5483462191500334732488173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14622565844000892619968461 5483462191500334732488173)
                  ·
                    refine ⟨2056298321812625524683065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5483462191500334732488173 2056298321812625524683065)
                    ·
                      refine ⟨1542223741359469143512299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2056298321812625524683065 1542223741359469143512299)
                      ·
                        rfl

theorem cell23_3003470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2].length) (baseStart_3003470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003470 prefixEnd_3003470 := by exact prefixLift 3003470
  have htrace : WordTrace (prefixWord ++ tailWord_3003470) baseStart_3003470 baseEnd_3003470 := by
    simpa [prefixWord, tailWord_3003470, baseEnd_3003470] using wordTrace_append hprefix tailTrace_3003470
  have hstable : (prefixWord ++ tailWord_3003470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003470).length < 2 ^ (prefixWord ++ tailWord_3003470).sum := by decide
  have hdescent : baseEnd_3003470 < baseStart_3003470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003487 : List Nat := [1, 1, 2, 3, 1, 1, 7, 1, 1, 3, 2]
def baseStart_3003487 : Nat := 118140960795 + 3003487 * 2 ^ 59
def prefixEnd_3003487 : Nat := 4983230072969 + 3 ^ 40 * 3003487 * 2
def baseEnd_3003487 : Nat := 1542232470530595576999721

theorem tailTrace_3003487 : CollatzResearch.WordTrace tailWord_3003487 prefixEnd_3003487 1542232470530595576999721 := by
  unfold tailWord_3003487
  simp only [CollatzResearch.WordTrace]
  refine ⟨109546170469887028586296715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73030780313258019057531143 109546170469887028586296715)
  ·
    refine ⟨164319255704830542879445073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109546170469887028586296715 164319255704830542879445073)
    ·
      refine ⟨123239441778622907159583805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164319255704830542879445073 123239441778622907159583805)
      ·
        refine ⟨46214790666983590184843927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123239441778622907159583805 46214790666983590184843927)
        ·
          refine ⟨69322186000475385277265891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46214790666983590184843927 69322186000475385277265891)
          ·
            refine ⟨103983279000713077915898837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69322186000475385277265891 103983279000713077915898837)
            ·
              refine ⟨2437108101579212763653879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 103983279000713077915898837 2437108101579212763653879)
              ·
                refine ⟨3655662152368819145480819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2437108101579212763653879 3655662152368819145480819)
                ·
                  refine ⟨5483493228553228718221229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3655662152368819145480819 5483493228553228718221229)
                  ·
                    refine ⟨2056309960707460769332961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5483493228553228718221229 2056309960707460769332961)
                    ·
                      refine ⟨1542232470530595576999721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2056309960707460769332961 1542232470530595576999721)
                      ·
                        rfl

theorem cell23_3003487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 1, 3, 2].length) (baseStart_3003487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003487 prefixEnd_3003487 := by exact prefixLift 3003487
  have htrace : WordTrace (prefixWord ++ tailWord_3003487) baseStart_3003487 baseEnd_3003487 := by
    simpa [prefixWord, tailWord_3003487, baseEnd_3003487] using wordTrace_append hprefix tailTrace_3003487
  have hstable : (prefixWord ++ tailWord_3003487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003487).length < 2 ^ (prefixWord ++ tailWord_3003487).sum := by decide
  have hdescent : baseEnd_3003487 < baseStart_3003487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003517 : List Nat := [1, 4, 1, 1, 3, 1, 1, 5, 2, 2, 2]
def baseStart_3003517 : Nat := 118140960795 + 3003517 * 2 ^ 59
def prefixEnd_3003517 : Nat := 4983230072969 + 3 ^ 40 * 3003517 * 2
def baseEnd_3003517 : Nat := 1542247874950230459624583

theorem tailTrace_3003517 : CollatzResearch.WordTrace tailWord_3003517 prefixEnd_3003517 1542247874950230459624583 := by
  unfold tailWord_3003517
  simp only [CollatzResearch.WordTrace]
  refine ⟨109547264659778343709888805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73031509773185562473259203 109547264659778343709888805)
  ·
    refine ⟨20540112123708439445604151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109547264659778343709888805 20540112123708439445604151)
    ·
      refine ⟨30810168185562659168406227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20540112123708439445604151 30810168185562659168406227)
      ·
        refine ⟨46215252278343988752609341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30810168185562659168406227 46215252278343988752609341)
        ·
          refine ⟨17330719604378995782228503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46215252278343988752609341 17330719604378995782228503)
          ·
            refine ⟨25996079406568493673342755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17330719604378995782228503 25996079406568493673342755)
            ·
              refine ⟨38994119109852740510014133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25996079406568493673342755 38994119109852740510014133)
              ·
                refine ⟨3655698666548694422813825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38994119109852740510014133 3655698666548694422813825)
                ·
                  refine ⟨2741773999911520817110369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3655698666548694422813825 2741773999911520817110369)
                  ·
                    refine ⟨2056330499933640612832777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2741773999911520817110369 2056330499933640612832777)
                    ·
                      refine ⟨1542247874950230459624583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2056330499933640612832777 1542247874950230459624583)
                      ·
                        rfl

theorem cell23_3003517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 2, 2, 2].length) (baseStart_3003517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003517 prefixEnd_3003517 := by exact prefixLift 3003517
  have htrace : WordTrace (prefixWord ++ tailWord_3003517) baseStart_3003517 baseEnd_3003517 := by
    simpa [prefixWord, tailWord_3003517, baseEnd_3003517] using wordTrace_append hprefix tailTrace_3003517
  have hstable : (prefixWord ++ tailWord_3003517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003517).length < 2 ^ (prefixWord ++ tailWord_3003517).sum := by decide
  have hdescent : baseEnd_3003517 < baseStart_3003517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003551 : List Nat := [1, 1, 2, 6, 2, 2, 1, 2, 2, 2, 2]
def baseStart_3003551 : Nat := 118140960795 + 3003551 * 2 ^ 59
def prefixEnd_3003551 : Nat := 4983230072969 + 3 ^ 40 * 3003551 * 2
def baseEnd_3003551 : Nat := 1542265333292483326599427

theorem tailTrace_3003551 : CollatzResearch.WordTrace tailWord_3003551 prefixEnd_3003551 1542265333292483326599427 := by
  unfold tailWord_3003551
  simp only [CollatzResearch.WordTrace]
  refine ⟨109548504741655167516626507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73032336494436778344417671 109548504741655167516626507)
  ·
    refine ⟨164322757112482751274939761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109548504741655167516626507 164322757112482751274939761)
    ·
      refine ⟨123242067834362063456204821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164322757112482751274939761 123242067834362063456204821)
      ·
        refine ⟨5776971929735721724509601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 123242067834362063456204821 5776971929735721724509601)
        ·
          refine ⟨4332728947301791293382201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5776971929735721724509601 4332728947301791293382201)
          ·
            refine ⟨3249546710476343470036651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4332728947301791293382201 3249546710476343470036651)
            ·
              refine ⟨4874320065714515205054977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3249546710476343470036651 4874320065714515205054977)
              ·
                refine ⟨3655740049285886403791233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4874320065714515205054977 3655740049285886403791233)
                ·
                  refine ⟨2741805036964414802843425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3655740049285886403791233 2741805036964414802843425)
                  ·
                    refine ⟨2056353777723311102132569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2741805036964414802843425 2056353777723311102132569)
                    ·
                      refine ⟨1542265333292483326599427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2056353777723311102132569 1542265333292483326599427)
                      ·
                        rfl

theorem cell23_3003551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_3003551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003551 prefixEnd_3003551 := by exact prefixLift 3003551
  have htrace : WordTrace (prefixWord ++ tailWord_3003551) baseStart_3003551 baseEnd_3003551 := by
    simpa [prefixWord, tailWord_3003551, baseEnd_3003551] using wordTrace_append hprefix tailTrace_3003551
  have hstable : (prefixWord ++ tailWord_3003551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003551).length < 2 ^ (prefixWord ++ tailWord_3003551).sum := by decide
  have hdescent : baseEnd_3003551 < baseStart_3003551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003553 : List Nat := [1, 2, 3, 3, 1, 1, 2, 1, 4, 5]
def baseStart_3003553 : Nat := 118140960795 + 3003553 * 2 ^ 59
def prefixEnd_3003553 : Nat := 4983230072969 + 3 ^ 40 * 3003553 * 2
def baseEnd_3003553 : Nat := 514088786751264106258139

theorem tailTrace_3003553 : CollatzResearch.WordTrace tailWord_3003553 prefixEnd_3003553 514088786751264106258139 := by
  unfold tailWord_3003553
  simp only [CollatzResearch.WordTrace]
  refine ⟨109548577687647921858199313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73032385125098614572132875 109548577687647921858199313)
  ·
    refine ⟨82161433265735941393649485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109548577687647921858199313 82161433265735941393649485)
    ·
      refine ⟨30810537474650978022618557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82161433265735941393649485 30810537474650978022618557)
      ·
        refine ⟨11553951552994116758481959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30810537474650978022618557 11553951552994116758481959)
        ·
          refine ⟨17330927329491175137722939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11553951552994116758481959 17330927329491175137722939)
          ·
            refine ⟨25996390994236762706584409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17330927329491175137722939 25996390994236762706584409)
            ·
              refine ⟨19497293245677572029938307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25996390994236762706584409 19497293245677572029938307)
              ·
                refine ⟨29245939868516358044907461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19497293245677572029938307 29245939868516358044907461)
                ·
                  refine ⟨5483613725346817133420149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29245939868516358044907461 5483613725346817133420149)
                  ·
                    refine ⟨514088786751264106258139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5483613725346817133420149 514088786751264106258139)
                    ·
                      rfl

theorem cell23_3003553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_3003553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003553 prefixEnd_3003553 := by exact prefixLift 3003553
  have htrace : WordTrace (prefixWord ++ tailWord_3003553) baseStart_3003553 baseEnd_3003553 := by
    simpa [prefixWord, tailWord_3003553, baseEnd_3003553] using wordTrace_append hprefix tailTrace_3003553
  have hstable : (prefixWord ++ tailWord_3003553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003553).length < 2 ^ (prefixWord ++ tailWord_3003553).sum := by decide
  have hdescent : baseEnd_3003553 < baseStart_3003553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003617 : List Nat := [1, 2, 3, 1, 3, 4, 1, 1, 3, 4]
def baseStart_3003617 : Nat := 118140960795 + 3003617 * 2 ^ 59
def prefixEnd_3003617 : Nat := 4983230072969 + 3 ^ 40 * 3003617 * 2
def baseEnd_3003617 : Nat := 514099741005226689458041

theorem tailTrace_3003617 : CollatzResearch.WordTrace tailWord_3003617 prefixEnd_3003617 514099741005226689458041 := by
  unfold tailWord_3003617
  simp only [CollatzResearch.WordTrace]
  refine ⟨109550911959416060788529105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73033941306277373859019403 109550911959416060788529105)
  ·
    refine ⟨82163183969562045591396829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109550911959416060788529105 82163183969562045591396829)
    ·
      refine ⟨30811193988585767096773811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82163183969562045591396829 30811193988585767096773811)
      ·
        refine ⟨46216790982878650645160717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30811193988585767096773811 46216790982878650645160717)
        ·
          refine ⟨17331296618579493991935269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46216790982878650645160717 17331296618579493991935269)
          ·
            refine ⟨3249618115983655123487863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17331296618579493991935269 3249618115983655123487863)
            ·
              refine ⟨4874427173975482685231795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3249618115983655123487863 4874427173975482685231795)
              ·
                refine ⟨7311640760963224027847693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4874427173975482685231795 7311640760963224027847693)
                ·
                  refine ⟨2741865285361209010442885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7311640760963224027847693 2741865285361209010442885)
                  ·
                    refine ⟨514099741005226689458041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2741865285361209010442885 514099741005226689458041)
                    ·
                      rfl

theorem cell23_3003617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_3003617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003617 prefixEnd_3003617 := by exact prefixLift 3003617
  have htrace : WordTrace (prefixWord ++ tailWord_3003617) baseStart_3003617 baseEnd_3003617 := by
    simpa [prefixWord, tailWord_3003617, baseEnd_3003617] using wordTrace_append hprefix tailTrace_3003617
  have hstable : (prefixWord ++ tailWord_3003617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003617).length < 2 ^ (prefixWord ++ tailWord_3003617).sum := by decide
  have hdescent : baseEnd_3003617 < baseStart_3003617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003724 : List Nat := [2, 2, 1, 3, 2, 4, 1, 2, 2, 4]
def baseStart_3003724 : Nat := 118140960795 + 3003724 * 2 ^ 59
def prefixEnd_3003724 : Nat := 4983230072969 + 3 ^ 40 * 3003724 * 2
def baseEnd_3003724 : Nat := 514118055148570383245377

theorem tailTrace_3003724 : CollatzResearch.WordTrace tailWord_3003724 prefixEnd_3003724 514118055148570383245377 := by
  unfold tailWord_3003724
  simp only [CollatzResearch.WordTrace]
  refine ⟨54777407285014209031337113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73036543046685612041782817 54777407285014209031337113)
  ·
    refine ⟨41083055463760656773502835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54777407285014209031337113 41083055463760656773502835)
    ·
      refine ⟨61624583195640985160254253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41083055463760656773502835 61624583195640985160254253)
      ·
        refine ⟨23109218698365369435095345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61624583195640985160254253 23109218698365369435095345)
        ·
          refine ⟨17331914023774027076321509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23109218698365369435095345 17331914023774027076321509)
          ·
            refine ⟨3249733879457630076810283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17331914023774027076321509 3249733879457630076810283)
            ·
              refine ⟨4874600819186445115215425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3249733879457630076810283 4874600819186445115215425)
              ·
                refine ⟨3655950614389833836411569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4874600819186445115215425 3655950614389833836411569)
                ·
                  refine ⟨2741962960792375377308677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3655950614389833836411569 2741962960792375377308677)
                  ·
                    refine ⟨514118055148570383245377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2741962960792375377308677 514118055148570383245377)
                    ·
                      rfl

theorem cell23_3003724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 2, 4].length) (baseStart_3003724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003724 prefixEnd_3003724 := by exact prefixLift 3003724
  have htrace : WordTrace (prefixWord ++ tailWord_3003724) baseStart_3003724 baseEnd_3003724 := by
    simpa [prefixWord, tailWord_3003724, baseEnd_3003724] using wordTrace_append hprefix tailTrace_3003724
  have hstable : (prefixWord ++ tailWord_3003724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003724).length < 2 ^ (prefixWord ++ tailWord_3003724).sum := by decide
  have hdescent : baseEnd_3003724 < baseStart_3003724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003747 : List Nat := [1, 1, 1, 5, 2, 2, 3, 1, 1, 3, 3]
def baseStart_3003747 : Nat := 118140960795 + 3003747 * 2 ^ 59
def prefixEnd_3003747 : Nat := 4983230072969 + 3 ^ 40 * 3003747 * 2
def baseEnd_3003747 : Nat := 1542365975500764559748525

theorem tailTrace_3003747 : CollatzResearch.WordTrace tailWord_3003747 prefixEnd_3003747 1542365975500764559748525 := by
  unfold tailWord_3003747
  simp only [CollatzResearch.WordTrace]
  refine ⟨109555653448945092990761495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73037102299296728660507663 109555653448945092990761495)
  ·
    refine ⟨164333480173417639486142243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109555653448945092990761495 164333480173417639486142243)
    ·
      refine ⟨246500220260126459229213365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164333480173417639486142243 246500220260126459229213365)
      ·
        refine ⟨23109395649386855552738753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 246500220260126459229213365 23109395649386855552738753)
        ·
          refine ⟨17332046737040141664554065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23109395649386855552738753 17332046737040141664554065)
          ·
            refine ⟨12999035052780106248415549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17332046737040141664554065 12999035052780106248415549)
            ·
              refine ⟨4874638144792539843155831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12999035052780106248415549 4874638144792539843155831)
              ·
                refine ⟨7311957217188809764733747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4874638144792539843155831 7311957217188809764733747)
                ·
                  refine ⟨10967935825783214647100621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7311957217188809764733747 10967935825783214647100621)
                  ·
                    refine ⟨4112975934668705492662733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10967935825783214647100621 4112975934668705492662733)
                    ·
                      refine ⟨1542365975500764559748525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4112975934668705492662733 1542365975500764559748525)
                      ·
                        rfl

theorem cell23_3003747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_3003747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003747 prefixEnd_3003747 := by exact prefixLift 3003747
  have htrace : WordTrace (prefixWord ++ tailWord_3003747) baseStart_3003747 baseEnd_3003747 := by
    simpa [prefixWord, tailWord_3003747, baseEnd_3003747] using wordTrace_append hprefix tailTrace_3003747
  have hstable : (prefixWord ++ tailWord_3003747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003747).length < 2 ^ (prefixWord ++ tailWord_3003747).sum := by decide
  have hdescent : baseEnd_3003747 < baseStart_3003747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003753 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 1, 2, 8]
def baseStart_3003753 : Nat := 118140960795 + 3003753 * 2 ^ 59
def prefixEnd_3003753 : Nat := 4983230072969 + 3 ^ 40 * 3003753 * 2
def baseEnd_3003753 : Nat := 1542369056384691536273497

theorem tailTrace_3003753 : CollatzResearch.WordTrace tailWord_3003753 prefixEnd_3003753 1542369056384691536273497 := by
  unfold tailWord_3003753
  simp only [CollatzResearch.WordTrace]
  refine ⟨109555872286923356015479913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73037248191282237343653275 109555872286923356015479913)
  ·
    refine ⟨82166904215192517011609935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109555872286923356015479913 82166904215192517011609935)
    ·
      refine ⟨123250356322788775517414903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82166904215192517011609935 123250356322788775517414903)
      ·
        refine ⟨184875534484183163276122355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123250356322788775517414903 184875534484183163276122355)
        ·
          refine ⟨277313301726274744914183533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184875534484183163276122355 277313301726274744914183533)
          ·
            refine ⟨103992488147353029342818825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 277313301726274744914183533 103992488147353029342818825)
            ·
              refine ⟨77994366110514772007114119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103992488147353029342818825 77994366110514772007114119)
              ·
                refine ⟨116991549165772158010671179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77994366110514772007114119 116991549165772158010671179)
                ·
                  refine ⟨175487323748658237016006769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116991549165772158010671179 175487323748658237016006769)
                  ·
                    refine ⟨131615492811493677762005077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 175487323748658237016006769 131615492811493677762005077)
                    ·
                      refine ⟨1542369056384691536273497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 131615492811493677762005077 1542369056384691536273497)
                      ·
                        rfl

theorem cell23_3003753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 2, 8].length) (baseStart_3003753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003753 prefixEnd_3003753 := by exact prefixLift 3003753
  have htrace : WordTrace (prefixWord ++ tailWord_3003753) baseStart_3003753 baseEnd_3003753 := by
    simpa [prefixWord, tailWord_3003753, baseEnd_3003753] using wordTrace_append hprefix tailTrace_3003753
  have hstable : (prefixWord ++ tailWord_3003753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003753).length < 2 ^ (prefixWord ++ tailWord_3003753).sum := by decide
  have hdescent : baseEnd_3003753 < baseStart_3003753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003754 : List Nat := [3, 1, 3, 3, 2, 2, 2, 7]
def baseStart_3003754 : Nat := 118140960795 + 3003754 * 2 ^ 59
def prefixEnd_3003754 : Nat := 4983230072969 + 3 ^ 40 * 3003754 * 2
def baseEnd_3003754 : Nat := 57124798883901704902259

theorem tailTrace_3003754 : CollatzResearch.WordTrace tailWord_3003754 prefixEnd_3003754 57124798883901704902259 := by
  unfold tailWord_3003754
  simp only [CollatzResearch.WordTrace]
  refine ⟨27388977189979933296566579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73037272506613155457510877 27388977189979933296566579)
  ·
    refine ⟨41083465784969899944849869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27388977189979933296566579 41083465784969899944849869)
    ·
      refine ⟨15406299669363712479318701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41083465784969899944849869 15406299669363712479318701)
      ·
        refine ⟨5777362376011392179744513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15406299669363712479318701 5777362376011392179744513)
        ·
          refine ⟨4333021782008544134808385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5777362376011392179744513 4333021782008544134808385)
          ·
            refine ⟨3249766336506408101106289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4333021782008544134808385 3249766336506408101106289)
            ·
              refine ⟨2437324752379806075829717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3249766336506408101106289 2437324752379806075829717)
              ·
                refine ⟨57124798883901704902259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2437324752379806075829717 57124798883901704902259)
                ·
                  rfl

theorem cell23_3003754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 7].length) (baseStart_3003754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003754 prefixEnd_3003754 := by exact prefixLift 3003754
  have htrace : WordTrace (prefixWord ++ tailWord_3003754) baseStart_3003754 baseEnd_3003754 := by
    simpa [prefixWord, tailWord_3003754, baseEnd_3003754] using wordTrace_append hprefix tailTrace_3003754
  have hstable : (prefixWord ++ tailWord_3003754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003754).length < 2 ^ (prefixWord ++ tailWord_3003754).sum := by decide
  have hdescent : baseEnd_3003754 < baseStart_3003754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003765 : List Nat := [1, 3, 4, 1, 3, 2, 1, 3, 1, 2, 2]
def baseStart_3003765 : Nat := 118140960795 + 3003765 * 2 ^ 59
def prefixEnd_3003765 : Nat := 4983230072969 + 3 ^ 40 * 3003765 * 2
def baseEnd_3003765 : Nat := 1542375218152545489323443

theorem tailTrace_3003765 : CollatzResearch.WordTrace tailWord_3003765 prefixEnd_3003765 1542375218152545489323443 := by
  unfold tailWord_3003765
  simp only [CollatzResearch.WordTrace]
  refine ⟨109556309962879882064916749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73037539975253254709944499 109556309962879882064916749)
  ·
    refine ⟨41083616236079955774343781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109556309962879882064916749 41083616236079955774343781)
    ·
      refine ⟨7703178044264991707689459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41083616236079955774343781 7703178044264991707689459)
      ·
        refine ⟨11554767066397487561534189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7703178044264991707689459 11554767066397487561534189)
        ·
          refine ⟨4333037649899057835575321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11554767066397487561534189 4333037649899057835575321)
          ·
            refine ⟨3249778237424293376681491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4333037649899057835575321 3249778237424293376681491)
            ·
              refine ⟨4874667356136440065022237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3249778237424293376681491 4874667356136440065022237)
              ·
                refine ⟨1828000258551165024383339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4874667356136440065022237 1828000258551165024383339)
                ·
                  refine ⟨2742000387826747536575009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1828000258551165024383339 2742000387826747536575009)
                  ·
                    refine ⟨2056500290870060652431257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2742000387826747536575009 2056500290870060652431257)
                    ·
                      refine ⟨1542375218152545489323443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2056500290870060652431257 1542375218152545489323443)
                      ·
                        rfl

theorem cell23_3003765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_3003765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003765 prefixEnd_3003765 := by exact prefixLift 3003765
  have htrace : WordTrace (prefixWord ++ tailWord_3003765) baseStart_3003765 baseEnd_3003765 := by
    simpa [prefixWord, tailWord_3003765, baseEnd_3003765] using wordTrace_append hprefix tailTrace_3003765
  have hstable : (prefixWord ++ tailWord_3003765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003765).length < 2 ^ (prefixWord ++ tailWord_3003765).sum := by decide
  have hdescent : baseEnd_3003765 < baseStart_3003765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003821 : List Nat := [1, 5, 2, 2, 1, 2, 1, 2, 1, 4, 2]
def baseStart_3003821 : Nat := 118140960795 + 3003821 * 2 ^ 59
def prefixEnd_3003821 : Nat := 4983230072969 + 3 ^ 40 * 3003821 * 2
def baseEnd_3003821 : Nat := 1542403973069197270223185

theorem tailTrace_3003821 : CollatzResearch.WordTrace tailWord_3003821 prefixEnd_3003821 1542403973069197270223185 := by
  unfold tailWord_3003821
  simp only [CollatzResearch.WordTrace]
  refine ⟨109558352450677003628955317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73038901633784669085970211 109558352450677003628955317)
  ·
    refine ⟨10271095542250969090214561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109558352450677003628955317 10271095542250969090214561)
    ·
      refine ⟨7703321656688226817660921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10271095542250969090214561 7703321656688226817660921)
      ·
        refine ⟨5777491242516170113245691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7703321656688226817660921 5777491242516170113245691)
        ·
          refine ⟨8666236863774255169868537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5777491242516170113245691 8666236863774255169868537)
          ·
            refine ⟨6499677647830691377401403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8666236863774255169868537 6499677647830691377401403)
            ·
              refine ⟨9749516471746037066102105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6499677647830691377401403 9749516471746037066102105)
              ·
                refine ⟨7312137353809527799576579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9749516471746037066102105 7312137353809527799576579)
                ·
                  refine ⟨10968206030714291699364869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7312137353809527799576579 10968206030714291699364869)
                  ·
                    refine ⟨2056538630758929693630913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10968206030714291699364869 2056538630758929693630913)
                    ·
                      refine ⟨1542403973069197270223185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2056538630758929693630913 1542403973069197270223185)
                      ·
                        rfl

theorem cell23_3003821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_3003821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003821 prefixEnd_3003821 := by exact prefixLift 3003821
  have htrace : WordTrace (prefixWord ++ tailWord_3003821) baseStart_3003821 baseEnd_3003821 := by
    simpa [prefixWord, tailWord_3003821, baseEnd_3003821] using wordTrace_append hprefix tailTrace_3003821
  have hstable : (prefixWord ++ tailWord_3003821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003821).length < 2 ^ (prefixWord ++ tailWord_3003821).sum := by decide
  have hdescent : baseEnd_3003821 < baseStart_3003821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003837 : List Nat := [1, 4, 1, 2, 2, 1, 2, 2, 2, 3, 3]
def baseStart_3003837 : Nat := 118140960795 + 3003837 * 2 ^ 59
def prefixEnd_3003837 : Nat := 4983230072969 + 3 ^ 40 * 3003837 * 2
def baseEnd_3003837 : Nat := 1542412188759669207623111

theorem tailTrace_3003837 : CollatzResearch.WordTrace tailWord_3003837 prefixEnd_3003837 1542412188759669207623111 := by
  unfold tailWord_3003837
  simp only [CollatzResearch.WordTrace]
  refine ⟨109558936018619038361537765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73039290679079358907691843 109558936018619038361537765)
  ·
    refine ⟨20542300503491069692788331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109558936018619038361537765 20542300503491069692788331)
    ·
      refine ⟨30813450755236604539182497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20542300503491069692788331 30813450755236604539182497)
      ·
        refine ⟨23110088066427453404386873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30813450755236604539182497 23110088066427453404386873)
        ·
          refine ⟨17332566049820590053290155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23110088066427453404386873 17332566049820590053290155)
          ·
            refine ⟨25998849074730885079935233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17332566049820590053290155 25998849074730885079935233)
            ·
              refine ⟨19499136806048163809951425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25998849074730885079935233 19499136806048163809951425)
              ·
                refine ⟨14624352604536122857463569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19499136806048163809951425 14624352604536122857463569)
                ·
                  refine ⟨10968264453402092143097677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14624352604536122857463569 10968264453402092143097677)
                  ·
                    refine ⟨4113099170025784553661629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10968264453402092143097677 4113099170025784553661629)
                    ·
                      refine ⟨1542412188759669207623111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4113099170025784553661629 1542412188759669207623111)
                      ·
                        rfl

theorem cell23_3003837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_3003837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003837 prefixEnd_3003837 := by exact prefixLift 3003837
  have htrace : WordTrace (prefixWord ++ tailWord_3003837) baseStart_3003837 baseEnd_3003837 := by
    simpa [prefixWord, tailWord_3003837, baseEnd_3003837] using wordTrace_append hprefix tailTrace_3003837
  have hstable : (prefixWord ++ tailWord_3003837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003837).length < 2 ^ (prefixWord ++ tailWord_3003837).sum := by decide
  have hdescent : baseEnd_3003837 < baseStart_3003837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003847 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 1, 7, 2]
def baseStart_3003847 : Nat := 118140960795 + 3003847 * 2 ^ 59
def prefixEnd_3003847 : Nat := 4983230072969 + 3 ^ 40 * 3003847 * 2
def baseEnd_3003847 : Nat := 1542417323566214168498065

theorem tailTrace_3003847 : CollatzResearch.WordTrace tailWord_3003847 prefixEnd_3003847 1542417323566214168498065 := by
  unfold tailWord_3003847
  simp only [CollatzResearch.WordTrace]
  refine ⟨109559300748582810069401795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73039533832388540046267863 109559300748582810069401795)
  ·
    refine ⟨164338951122874215104102693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109559300748582810069401795 164338951122874215104102693)
    ·
      refine ⟨30813553335538915332019255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164338951122874215104102693 30813553335538915332019255)
      ·
        refine ⟨46220330003308372998028883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30813553335538915332019255 46220330003308372998028883)
        ·
          refine ⟨69330495004962559497043325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46220330003308372998028883 69330495004962559497043325)
          ·
            refine ⟨25998935626860959811391247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69330495004962559497043325 25998935626860959811391247)
            ·
              refine ⟨38998403440291439717086871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25998935626860959811391247 38998403440291439717086871)
              ·
                refine ⟨58497605160437159575630307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38998403440291439717086871 58497605160437159575630307)
                ·
                  refine ⟨87746407740655739363445461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58497605160437159575630307 87746407740655739363445461)
                  ·
                    refine ⟨2056556431421618891330753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 87746407740655739363445461 2056556431421618891330753)
                    ·
                      refine ⟨1542417323566214168498065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2056556431421618891330753 1542417323566214168498065)
                      ·
                        rfl

theorem cell23_3003847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 7, 2].length) (baseStart_3003847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003847 prefixEnd_3003847 := by exact prefixLift 3003847
  have htrace : WordTrace (prefixWord ++ tailWord_3003847) baseStart_3003847 baseEnd_3003847 := by
    simpa [prefixWord, tailWord_3003847, baseEnd_3003847] using wordTrace_append hprefix tailTrace_3003847
  have hstable : (prefixWord ++ tailWord_3003847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003847).length < 2 ^ (prefixWord ++ tailWord_3003847).sum := by decide
  have hdescent : baseEnd_3003847 < baseStart_3003847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003897 : List Nat := [1, 2, 1, 3, 1, 2, 1, 3, 4, 2, 3]
def baseStart_3003897 : Nat := 118140960795 + 3003897 * 2 ^ 59
def prefixEnd_3003897 : Nat := 4983230072969 + 3 ^ 40 * 3003897 * 2
def baseEnd_3003897 : Nat := 1542442997598938972872835

theorem tailTrace_3003897 : CollatzResearch.WordTrace tailWord_3003897 prefixEnd_3003897 1542442997598938972872835 := by
  unfold tailWord_3003897
  simp only [CollatzResearch.WordTrace]
  refine ⟨109561124398401668608721945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73040749598934445739147963 109561124398401668608721945)
  ·
    refine ⟨82170843298801251456541459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109561124398401668608721945 82170843298801251456541459)
    ·
      refine ⟨123256264948201877184812189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82170843298801251456541459 123256264948201877184812189)
      ·
        refine ⟨46221099355575703944304571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123256264948201877184812189 46221099355575703944304571)
        ·
          refine ⟨69331649033363555916456857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46221099355575703944304571 69331649033363555916456857)
          ·
            refine ⟨51998736775022666937342643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69331649033363555916456857 51998736775022666937342643)
            ·
              refine ⟨77998105162534000406013965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51998736775022666937342643 77998105162534000406013965)
              ·
                refine ⟨29249289435950250152255237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77998105162534000406013965 29249289435950250152255237)
                ·
                  refine ⟨5484241769240671903547857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29249289435950250152255237 5484241769240671903547857)
                  ·
                    refine ⟨4113181326930503927660893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5484241769240671903547857 4113181326930503927660893)
                    ·
                      refine ⟨1542442997598938972872835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4113181326930503927660893 1542442997598938972872835)
                      ·
                        rfl

theorem cell23_3003897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_3003897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003897 prefixEnd_3003897 := by exact prefixLift 3003897
  have htrace : WordTrace (prefixWord ++ tailWord_3003897) baseStart_3003897 baseEnd_3003897 := by
    simpa [prefixWord, tailWord_3003897, baseEnd_3003897] using wordTrace_append hprefix tailTrace_3003897
  have hstable : (prefixWord ++ tailWord_3003897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003897).length < 2 ^ (prefixWord ++ tailWord_3003897).sum := by decide
  have hdescent : baseEnd_3003897 < baseStart_3003897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003961 : List Nat := [1, 2, 1, 5, 1, 2, 3, 1, 3, 1, 3]
def baseStart_3003961 : Nat := 118140960795 + 3003961 * 2 ^ 59
def prefixEnd_3003961 : Nat := 4983230072969 + 3 ^ 40 * 3003961 * 2
def baseEnd_3003961 : Nat := 1542475860360826722472541

theorem tailTrace_3003961 : CollatzResearch.WordTrace tailWord_3003961 prefixEnd_3003961 1542475860360826722472541 := by
  unfold tailWord_3003961
  simp only [CollatzResearch.WordTrace]
  refine ⟨109563458670169807539051737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73042305780113205026034491 109563458670169807539051737)
  ·
    refine ⟨82172594002627355654288803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109563458670169807539051737 82172594002627355654288803)
    ·
      refine ⟨123258891003941033481433205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82172594002627355654288803 123258891003941033481433205)
      ·
        refine ⟨11555521031619471888884363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 123258891003941033481433205 11555521031619471888884363)
        ·
          refine ⟨17333281547429207833326545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11555521031619471888884363 17333281547429207833326545)
          ·
            refine ⟨12999961160571905874994909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17333281547429207833326545 12999961160571905874994909)
            ·
              refine ⟨4874985435214464703123091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12999961160571905874994909 4874985435214464703123091)
              ·
                refine ⟨7312478152821697054684637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4874985435214464703123091 7312478152821697054684637)
                ·
                  refine ⟨2742179307308136395506739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7312478152821697054684637 2742179307308136395506739)
                  ·
                    refine ⟨4113268960962204593260109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2742179307308136395506739 4113268960962204593260109)
                    ·
                      refine ⟨1542475860360826722472541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4113268960962204593260109 1542475860360826722472541)
                      ·
                        rfl

theorem cell23_3003961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_3003961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003961 prefixEnd_3003961 := by exact prefixLift 3003961
  have htrace : WordTrace (prefixWord ++ tailWord_3003961) baseStart_3003961 baseEnd_3003961 := by
    simpa [prefixWord, tailWord_3003961, baseEnd_3003961] using wordTrace_append hprefix tailTrace_3003961
  have hstable : (prefixWord ++ tailWord_3003961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003961).length < 2 ^ (prefixWord ++ tailWord_3003961).sum := by decide
  have hdescent : baseEnd_3003961 < baseStart_3003961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003981 : List Nat := [1, 6, 1, 1, 3, 1, 1, 1, 3, 5]
def baseStart_3003981 : Nat := 118140960795 + 3003981 * 2 ^ 59
def prefixEnd_3003981 : Nat := 4983230072969 + 3 ^ 40 * 3003981 * 2
def baseEnd_3003981 : Nat := 514162043324638881407483

theorem tailTrace_3003981 : CollatzResearch.WordTrace tailWord_3003981 prefixEnd_3003981 514162043324638881407483 := by
  unfold tailWord_3003981
  simp only [CollatzResearch.WordTrace]
  refine ⟨109564188130097350954779797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73042792086731567303186531 109564188130097350954779797)
  ·
    refine ⟨5135821318598313326005303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 109564188130097350954779797 5135821318598313326005303)
    ·
      refine ⟨7703731977897469989007955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5135821318598313326005303 7703731977897469989007955)
      ·
        refine ⟨11555597966846204983511933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7703731977897469989007955 11555597966846204983511933)
        ·
          refine ⟨4333349237567326868816975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11555597966846204983511933 4333349237567326868816975)
          ·
            refine ⟨6500023856350990303225463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4333349237567326868816975 6500023856350990303225463)
            ·
              refine ⟨9750035784526485454838195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6500023856350990303225463 9750035784526485454838195)
              ·
                refine ⟨14625053676789728182257293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9750035784526485454838195 14625053676789728182257293)
                ·
                  refine ⟨5484395128796148068346485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14625053676789728182257293 5484395128796148068346485)
                  ·
                    refine ⟨514162043324638881407483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5484395128796148068346485 514162043324638881407483)
                    ·
                      rfl

theorem cell23_3003981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_3003981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3003981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3003981 prefixEnd_3003981 := by exact prefixLift 3003981
  have htrace : WordTrace (prefixWord ++ tailWord_3003981) baseStart_3003981 baseEnd_3003981 := by
    simpa [prefixWord, tailWord_3003981, baseEnd_3003981] using wordTrace_append hprefix tailTrace_3003981
  have hstable : (prefixWord ++ tailWord_3003981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003981).length < 2 ^ (prefixWord ++ tailWord_3003981).sum := by decide
  have hdescent : baseEnd_3003981 < baseStart_3003981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004001 : List Nat := [1, 2, 3, 1, 1, 3, 5, 1, 1, 1, 4]
def baseStart_3004001 : Nat := 118140960795 + 3004001 * 2 ^ 59
def prefixEnd_3004001 : Nat := 4983230072969 + 3 ^ 40 * 3004001 * 2
def baseEnd_3004001 : Nat := 1542496399587006565972357

theorem tailTrace_3004001 : CollatzResearch.WordTrace tailWord_3004001 prefixEnd_3004001 1542496399587006565972357 := by
  unfold tailWord_3004001
  simp only [CollatzResearch.WordTrace]
  refine ⟨109564917590024894370507857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73043278393349929580338571 109564917590024894370507857)
  ·
    refine ⟨82173688192518670777880893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109564917590024894370507857 82173688192518670777880893)
    ·
      refine ⟨30815133072194501541705335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82173688192518670777880893 30815133072194501541705335)
      ·
        refine ⟨46222699608291752312558003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30815133072194501541705335 46222699608291752312558003)
        ·
          refine ⟨69334049412437628468837005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46222699608291752312558003 69334049412437628468837005)
          ·
            refine ⟨26000268529664110675813877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69334049412437628468837005 26000268529664110675813877)
            ·
              refine ⟨2437525174656010375857551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26000268529664110675813877 2437525174656010375857551)
              ·
                refine ⟨3656287761984015563786327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2437525174656010375857551 3656287761984015563786327)
                ·
                  refine ⟨5484431642976023345679491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3656287761984015563786327 5484431642976023345679491)
                  ·
                    refine ⟨8226647464464035018519237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5484431642976023345679491 8226647464464035018519237)
                    ·
                      refine ⟨1542496399587006565972357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8226647464464035018519237 1542496399587006565972357)
                      ·
                        rfl

theorem cell23_3004001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 1, 1, 4].length) (baseStart_3004001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004001 prefixEnd_3004001 := by exact prefixLift 3004001
  have htrace : WordTrace (prefixWord ++ tailWord_3004001) baseStart_3004001 baseEnd_3004001 := by
    simpa [prefixWord, tailWord_3004001, baseEnd_3004001] using wordTrace_append hprefix tailTrace_3004001
  have hstable : (prefixWord ++ tailWord_3004001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004001).length < 2 ^ (prefixWord ++ tailWord_3004001).sum := by decide
  have hdescent : baseEnd_3004001 < baseStart_3004001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004004 : List Nat := [2, 3, 1, 1, 2, 3, 3, 1, 1, 1, 5]
def baseStart_3004004 : Nat := 118140960795 + 3004004 * 2 ^ 59
def prefixEnd_3004004 : Nat := 4983230072969 + 3 ^ 40 * 3004004 * 2
def baseEnd_3004004 : Nat := 1542497940028970054234843

theorem tailTrace_3004004 : CollatzResearch.WordTrace tailWord_3004004 prefixEnd_3004004 1542497940028970054234843 := by
  unfold tailWord_3004004
  simp only [CollatzResearch.WordTrace]
  refine ⟨54782513504507012941433533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73043351339342683921911377 54782513504507012941433533)
  ·
    refine ⟨20543442564190129853037575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54782513504507012941433533 20543442564190129853037575)
    ·
      refine ⟨30815163846285194779556363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20543442564190129853037575 30815163846285194779556363)
      ·
        refine ⟨46222745769427792169334545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30815163846285194779556363 46222745769427792169334545)
        ·
          refine ⟨34667059327070844127000909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46222745769427792169334545 34667059327070844127000909)
          ·
            refine ⟨13000147247651566547625341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34667059327070844127000909 13000147247651566547625341)
            ·
              refine ⟨4875055217869337455359503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13000147247651566547625341 4875055217869337455359503)
              ·
                refine ⟨7312582826804006183039255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4875055217869337455359503 7312582826804006183039255)
                ·
                  refine ⟨10968874240206009274558883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7312582826804006183039255 10968874240206009274558883)
                  ·
                    refine ⟨16453311360309013911838325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10968874240206009274558883 16453311360309013911838325)
                    ·
                      refine ⟨1542497940028970054234843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16453311360309013911838325 1542497940028970054234843)
                      ·
                        rfl

theorem cell23_3004004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_3004004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004004 prefixEnd_3004004 := by exact prefixLift 3004004
  have htrace : WordTrace (prefixWord ++ tailWord_3004004) baseStart_3004004 baseEnd_3004004 := by
    simpa [prefixWord, tailWord_3004004, baseEnd_3004004] using wordTrace_append hprefix tailTrace_3004004
  have hstable : (prefixWord ++ tailWord_3004004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004004).length < 2 ^ (prefixWord ++ tailWord_3004004).sum := by decide
  have hdescent : baseEnd_3004004 < baseStart_3004004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004021 : List Nat := [1, 3, 4, 2, 1, 1, 1, 2, 3, 2, 3]
def baseStart_3004021 : Nat := 118140960795 + 3004021 * 2 ^ 59
def prefixEnd_3004021 : Nat := 4983230072969 + 3 ^ 40 * 3004021 * 2
def baseEnd_3004021 : Nat := 1542506669200096487722265

theorem tailTrace_3004021 : CollatzResearch.WordTrace tailWord_3004021 prefixEnd_3004021 1542506669200096487722265 := by
  unfold tailWord_3004021
  simp only [CollatzResearch.WordTrace]
  refine ⟨109565647049952437786235917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73043764699968291857490611 109565647049952437786235917)
  ·
    refine ⟨41087117643732164169838469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109565647049952437786235917 41087117643732164169838469)
    ·
      refine ⟨7703834558199780781844713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41087117643732164169838469 7703834558199780781844713)
      ·
        refine ⟨5777875918649835586383535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7703834558199780781844713 5777875918649835586383535)
        ·
          refine ⟨8666813877974753379575303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5777875918649835586383535 8666813877974753379575303)
          ·
            refine ⟨13000220816962130069362955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8666813877974753379575303 13000220816962130069362955)
            ·
              refine ⟨19500331225443195104044433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13000220816962130069362955 19500331225443195104044433)
              ·
                refine ⟨14625248419082396328033325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19500331225443195104044433 14625248419082396328033325)
                ·
                  refine ⟨5484468157155898623012497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14625248419082396328033325 5484468157155898623012497)
                  ·
                    refine ⟨4113351117866923967259373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5484468157155898623012497 4113351117866923967259373)
                    ·
                      refine ⟨1542506669200096487722265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4113351117866923967259373 1542506669200096487722265)
                      ·
                        rfl

theorem cell23_3004021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_3004021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004021 prefixEnd_3004021 := by exact prefixLift 3004021
  have htrace : WordTrace (prefixWord ++ tailWord_3004021) baseStart_3004021 baseEnd_3004021 := by
    simpa [prefixWord, tailWord_3004021, baseEnd_3004021] using wordTrace_append hprefix tailTrace_3004021
  have hstable : (prefixWord ++ tailWord_3004021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004021).length < 2 ^ (prefixWord ++ tailWord_3004021).sum := by decide
  have hdescent : baseEnd_3004021 < baseStart_3004021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004037 : List Nat := [1, 3, 1, 1, 4, 1, 1, 2, 2, 7]
def baseStart_3004037 : Nat := 118140960795 + 3004037 * 2 ^ 59
def prefixEnd_3004037 : Nat := 4983230072969 + 3 ^ 40 * 3004037 * 2
def baseEnd_3004037 : Nat := 514171628296856141707397

theorem tailTrace_3004037 : CollatzResearch.WordTrace tailWord_3004037 prefixEnd_3004037 514171628296856141707397 := by
  unfold tailWord_3004037
  simp only [CollatzResearch.WordTrace]
  refine ⟨109566230617894472518818365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73044153745262981679212243 109566230617894472518818365)
  ·
    refine ⟨41087336481710427194556887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109566230617894472518818365 41087336481710427194556887)
    ·
      refine ⟨61631004722565640791835331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41087336481710427194556887 61631004722565640791835331)
      ·
        refine ⟨92446507083848461187752997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61631004722565640791835331 92446507083848461187752997)
        ·
          refine ⟨17333720078221586472703687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92446507083848461187752997 17333720078221586472703687)
          ·
            refine ⟨26000580117332379709055531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17333720078221586472703687 26000580117332379709055531)
            ·
              refine ⟨39000870175998569563583297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26000580117332379709055531 39000870175998569563583297)
              ·
                refine ⟨29250652631998927172687473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39000870175998569563583297 29250652631998927172687473)
                ·
                  refine ⟨21937989473999195379515605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29250652631998927172687473 21937989473999195379515605)
                  ·
                    refine ⟨514171628296856141707397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21937989473999195379515605 514171628296856141707397)
                    ·
                      rfl

theorem cell23_3004037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 7].length) (baseStart_3004037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004037 prefixEnd_3004037 := by exact prefixLift 3004037
  have htrace : WordTrace (prefixWord ++ tailWord_3004037) baseStart_3004037 baseEnd_3004037 := by
    simpa [prefixWord, tailWord_3004037, baseEnd_3004037] using wordTrace_append hprefix tailTrace_3004037
  have hstable : (prefixWord ++ tailWord_3004037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004037).length < 2 ^ (prefixWord ++ tailWord_3004037).sum := by decide
  have hdescent : baseEnd_3004037 < baseStart_3004037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004052 : List Nat := [2, 4, 2, 2, 3, 1, 2, 1, 1, 1, 4]
def baseStart_3004052 : Nat := 118140960795 + 3004052 * 2 ^ 59
def prefixEnd_3004052 : Nat := 4983230072969 + 3 ^ 40 * 3004052 * 2
def baseEnd_3004052 : Nat := 1542522587100385866434623

theorem tailTrace_3004052 : CollatzResearch.WordTrace tailWord_3004052 prefixEnd_3004052 1542522587100385866434623 := by
  unfold tailWord_3004052
  simp only [CollatzResearch.WordTrace]
  refine ⟨54783388856420065040307205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73044518475226753387076273 54783388856420065040307205)
  ·
    refine ⟨10271885410578762195057601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54783388856420065040307205 10271885410578762195057601)
    ·
      refine ⟨7703914057934071646293201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10271885410578762195057601 7703914057934071646293201)
      ·
        refine ⟨5777935543450553734719901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7703914057934071646293201 5777935543450553734719901)
        ·
          refine ⟨2166725828793957650519963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5777935543450553734719901 2166725828793957650519963)
          ·
            refine ⟨3250088743190936475779945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2166725828793957650519963 3250088743190936475779945)
            ·
              refine ⟨2437566557393202356834959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3250088743190936475779945 2437566557393202356834959)
              ·
                refine ⟨3656349836089803535252439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2437566557393202356834959 3656349836089803535252439)
                ·
                  refine ⟨5484524754134705302878659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3656349836089803535252439 5484524754134705302878659)
                  ·
                    refine ⟨8226787131202057954317989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5484524754134705302878659 8226787131202057954317989)
                    ·
                      refine ⟨1542522587100385866434623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8226787131202057954317989 1542522587100385866434623)
                      ·
                        rfl

theorem cell23_3004052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_3004052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004052 prefixEnd_3004052 := by exact prefixLift 3004052
  have htrace : WordTrace (prefixWord ++ tailWord_3004052) baseStart_3004052 baseEnd_3004052 := by
    simpa [prefixWord, tailWord_3004052, baseEnd_3004052] using wordTrace_append hprefix tailTrace_3004052
  have hstable : (prefixWord ++ tailWord_3004052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004052).length < 2 ^ (prefixWord ++ tailWord_3004052).sum := by decide
  have hdescent : baseEnd_3004052 < baseStart_3004052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004057 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 1, 5, 4]
def baseStart_3004057 : Nat := 118140960795 + 3004057 * 2 ^ 59
def prefixEnd_3004057 : Nat := 4983230072969 + 3 ^ 40 * 3004057 * 2
def baseEnd_3004057 : Nat := 1542525154503658346872099

theorem tailTrace_3004057 : CollatzResearch.WordTrace tailWord_3004057 prefixEnd_3004057 1542525154503658346872099 := by
  unfold tailWord_3004057
  simp only [CollatzResearch.WordTrace]
  refine ⟨109566960077822015934546425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73044640051881343956364283 109566960077822015934546425)
  ·
    refine ⟨82175220058366511950909819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109566960077822015934546425 82175220058366511950909819)
    ·
      refine ⟨123262830087549767926364729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82175220058366511950909819 123262830087549767926364729)
      ·
        refine ⟨92447122565662325944773547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123262830087549767926364729 92447122565662325944773547)
        ·
          refine ⟨138670683848493488917160321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92447122565662325944773547 138670683848493488917160321)
          ·
            refine ⟨104003012886370116687870241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138670683848493488917160321 104003012886370116687870241)
            ·
              refine ⟨78002259664777587515902681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104003012886370116687870241 78002259664777587515902681)
              ·
                refine ⟨58501694748583190636927011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78002259664777587515902681 58501694748583190636927011)
                ·
                  refine ⟨87752542122874785955390517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58501694748583190636927011 87752542122874785955390517)
                  ·
                    refine ⟨8226800824019511183317861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87752542122874785955390517 8226800824019511183317861)
                    ·
                      refine ⟨1542525154503658346872099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8226800824019511183317861 1542525154503658346872099)
                      ·
                        rfl

theorem cell23_3004057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_3004057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004057 prefixEnd_3004057 := by exact prefixLift 3004057
  have htrace : WordTrace (prefixWord ++ tailWord_3004057) baseStart_3004057 baseEnd_3004057 := by
    simpa [prefixWord, tailWord_3004057, baseEnd_3004057] using wordTrace_append hprefix tailTrace_3004057
  have hstable : (prefixWord ++ tailWord_3004057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004057).length < 2 ^ (prefixWord ++ tailWord_3004057).sum := by decide
  have hdescent : baseEnd_3004057 < baseStart_3004057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004067 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 4, 6]
def baseStart_3004067 : Nat := 118140960795 + 3004067 * 2 ^ 59
def prefixEnd_3004067 : Nat := 4983230072969 + 3 ^ 40 * 3004067 * 2
def baseEnd_3004067 : Nat := 514176763103401102582351

theorem tailTrace_3004067 : CollatzResearch.WordTrace tailWord_3004067 prefixEnd_3004067 514176763103401102582351 := by
  unfold tailWord_3004067
  simp only [CollatzResearch.WordTrace]
  refine ⟨109567324807785787642410455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73044883205190525094940303 109567324807785787642410455)
  ·
    refine ⟨164350987211678681463615683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109567324807785787642410455 164350987211678681463615683)
    ·
      refine ⟨246526480817518022195423525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164350987211678681463615683 246526480817518022195423525)
      ·
        refine ⟨46223715153284629161641911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 246526480817518022195423525 46223715153284629161641911)
        ·
          refine ⟨69335572729926943742462867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46223715153284629161641911 69335572729926943742462867)
          ·
            refine ⟨104003359094890415613694301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69335572729926943742462867 104003359094890415613694301)
            ·
              refine ⟨39001259660583905855135363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104003359094890415613694301 39001259660583905855135363)
              ·
                refine ⟨58501889490875858782703045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39001259660583905855135363 58501889490875858782703045)
                ·
                  refine ⟨10969104279539223521756821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58501889490875858782703045 10969104279539223521756821)
                  ·
                    refine ⟨514176763103401102582351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10969104279539223521756821 514176763103401102582351)
                    ·
                      rfl

theorem cell23_3004067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 6].length) (baseStart_3004067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004067 prefixEnd_3004067 := by exact prefixLift 3004067
  have htrace : WordTrace (prefixWord ++ tailWord_3004067) baseStart_3004067 baseEnd_3004067 := by
    simpa [prefixWord, tailWord_3004067, baseEnd_3004067] using wordTrace_append hprefix tailTrace_3004067
  have hstable : (prefixWord ++ tailWord_3004067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004067).length < 2 ^ (prefixWord ++ tailWord_3004067).sum := by decide
  have hdescent : baseEnd_3004067 < baseStart_3004067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004068 : List Nat := [2, 3, 1, 2, 2, 2, 3, 2, 2, 1, 3]
def baseStart_3004068 : Nat := 118140960795 + 3004068 * 2 ^ 59
def prefixEnd_3004068 : Nat := 4983230072969 + 3 ^ 40 * 3004068 * 2
def baseEnd_3004068 : Nat := 1542530802790857803834549

theorem tailTrace_3004068 : CollatzResearch.WordTrace tailWord_3004068 prefixEnd_3004068 1542530802790857803834549 := by
  unfold tailWord_3004068
  simp only [CollatzResearch.WordTrace]
  refine ⟨54783680640391082406598429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73044907520521443208797905 54783680640391082406598429)
  ·
    refine ⟨20543880240146655902474411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54783680640391082406598429 20543880240146655902474411)
    ·
      refine ⟨30815820360219983853711617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20543880240146655902474411 30815820360219983853711617)
      ·
        refine ⟨23111865270164987890283713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30815820360219983853711617 23111865270164987890283713)
        ·
          refine ⟨17333898952623740917712785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23111865270164987890283713 17333898952623740917712785)
          ·
            refine ⟨13000424214467805688284589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17333898952623740917712785 13000424214467805688284589)
            ·
              refine ⟨4875159080425427133106721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13000424214467805688284589 4875159080425427133106721)
              ·
                refine ⟨3656369310319070349830041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4875159080425427133106721 3656369310319070349830041)
                ·
                  refine ⟨2742276982739302762372531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3656369310319070349830041 2742276982739302762372531)
                  ·
                    refine ⟨4113415474108954143558797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2742276982739302762372531 4113415474108954143558797)
                    ·
                      refine ⟨1542530802790857803834549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4113415474108954143558797 1542530802790857803834549)
                      ·
                        rfl

theorem cell23_3004068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_3004068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004068 prefixEnd_3004068 := by exact prefixLift 3004068
  have htrace : WordTrace (prefixWord ++ tailWord_3004068) baseStart_3004068 baseEnd_3004068 := by
    simpa [prefixWord, tailWord_3004068, baseEnd_3004068] using wordTrace_append hprefix tailTrace_3004068
  have hstable : (prefixWord ++ tailWord_3004068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004068).length < 2 ^ (prefixWord ++ tailWord_3004068).sum := by decide
  have hdescent : baseEnd_3004068 < baseStart_3004068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004085 : List Nat := [1, 3, 3, 3, 3, 1, 1, 1, 1, 3, 3]
def baseStart_3004085 : Nat := 118140960795 + 3004085 * 2 ^ 59
def prefixEnd_3004085 : Nat := 4983230072969 + 3 ^ 40 * 3004085 * 2
def baseEnd_3004085 : Nat := 1542539531961984237321971

theorem tailTrace_3004085 : CollatzResearch.WordTrace tailWord_3004085 prefixEnd_3004085 1542539531961984237321971 := by
  unfold tailWord_3004085
  simp only [CollatzResearch.WordTrace]
  refine ⟨109567981321720576716565709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73045320881147051144377139 109567981321720576716565709)
  ·
    refine ⟨41087992995645216268712141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109567981321720576716565709 41087992995645216268712141)
    ·
      refine ⟨15407997373366956100767053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41087992995645216268712141 15407997373366956100767053)
      ·
        refine ⟨5777999015012608537787645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15407997373366956100767053 5777999015012608537787645)
        ·
          refine ⟨2166749630629728201670367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5777999015012608537787645 2166749630629728201670367)
          ·
            refine ⟨3250124445944592302505551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2166749630629728201670367 3250124445944592302505551)
            ·
              refine ⟨4875186668916888453758327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3250124445944592302505551 4875186668916888453758327)
              ·
                refine ⟨7312780003375332680637491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4875186668916888453758327 7312780003375332680637491)
                ·
                  refine ⟨10969170005062999020956237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7312780003375332680637491 10969170005062999020956237)
                  ·
                    refine ⟨4113438751898624632858589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10969170005062999020956237 4113438751898624632858589)
                    ·
                      refine ⟨1542539531961984237321971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4113438751898624632858589 1542539531961984237321971)
                      ·
                        rfl

theorem cell23_3004085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_3004085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004085 prefixEnd_3004085 := by exact prefixLift 3004085
  have htrace : WordTrace (prefixWord ++ tailWord_3004085) baseStart_3004085 baseEnd_3004085 := by
    simpa [prefixWord, tailWord_3004085, baseEnd_3004085] using wordTrace_append hprefix tailTrace_3004085
  have hstable : (prefixWord ++ tailWord_3004085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004085).length < 2 ^ (prefixWord ++ tailWord_3004085).sum := by decide
  have hdescent : baseEnd_3004085 < baseStart_3004085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004178 : List Nat := [3, 2, 4, 1, 1, 1, 2, 2, 2, 5]
def baseStart_3004178 : Nat := 118140960795 + 3004178 * 2 ^ 59
def prefixEnd_3004178 : Nat := 4983230072969 + 3 ^ 40 * 3004178 * 2
def baseEnd_3004178 : Nat := 514195761887617457819681

theorem tailTrace_3004178 : CollatzResearch.WordTrace tailWord_3004178 prefixEnd_3004178 514195761887617457819681 := by
  unfold tailWord_3004178
  simp only [CollatzResearch.WordTrace]
  refine ⟨27392843327595913399925297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73047582206922435733134125 27392843327595913399925297)
  ·
    refine ⟨20544632495696935049943973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27392843327595913399925297 20544632495696935049943973)
    ·
      refine ⟨3852118592943175321864495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20544632495696935049943973 3852118592943175321864495)
      ·
        refine ⟨5778177889414762982796743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3852118592943175321864495 5778177889414762982796743)
        ·
          refine ⟨8667266834122144474195115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5778177889414762982796743 8667266834122144474195115)
          ·
            refine ⟨13000900251183216711292673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8667266834122144474195115 13000900251183216711292673)
            ·
              refine ⟨9750675188387412533469505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13000900251183216711292673 9750675188387412533469505)
              ·
                refine ⟨7313006391290559400102129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9750675188387412533469505 7313006391290559400102129)
                ·
                  refine ⟨5484754793467919550076597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7313006391290559400102129 5484754793467919550076597)
                  ·
                    refine ⟨514195761887617457819681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5484754793467919550076597 514195761887617457819681)
                    ·
                      rfl

theorem cell23_3004178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_3004178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004178 prefixEnd_3004178 := by exact prefixLift 3004178
  have htrace : WordTrace (prefixWord ++ tailWord_3004178) baseStart_3004178 baseEnd_3004178 := by
    simpa [prefixWord, tailWord_3004178, baseEnd_3004178] using wordTrace_append hprefix tailTrace_3004178
  have hstable : (prefixWord ++ tailWord_3004178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004178).length < 2 ^ (prefixWord ++ tailWord_3004178).sum := by decide
  have hdescent : baseEnd_3004178 < baseStart_3004178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004181 : List Nat := [1, 3, 2, 1, 2, 3, 2, 2, 2, 1, 4]
def baseStart_3004181 : Nat := 118140960795 + 3004181 * 2 ^ 59
def prefixEnd_3004181 : Nat := 4983230072969 + 3 ^ 40 * 3004181 * 2
def baseEnd_3004181 : Nat := 1542588826104815861721529

theorem tailTrace_3004181 : CollatzResearch.WordTrace tailWord_3004181 prefixEnd_3004181 1542588826104815861721529 := by
  unfold tailWord_3004181
  simp only [CollatzResearch.WordTrace]
  refine ⟨109571482729372785112060397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73047655152915190074706931 109571482729372785112060397)
  ·
    refine ⟨41089306023514794417022649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109571482729372785112060397 41089306023514794417022649)
    ·
      refine ⟨30816979517636095812766987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41089306023514794417022649 30816979517636095812766987)
      ·
        refine ⟨46225469276454143719150481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30816979517636095812766987 46225469276454143719150481)
        ·
          refine ⟨34669101957340607789362861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46225469276454143719150481 34669101957340607789362861)
          ·
            refine ⟨13000913234002727921011073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34669101957340607789362861 13000913234002727921011073)
            ·
              refine ⟨9750684925502045940758305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13000913234002727921011073 9750684925502045940758305)
              ·
                refine ⟨7313013694126534455568729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9750684925502045940758305 7313013694126534455568729)
                ·
                  refine ⟨5484760270594900841676547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7313013694126534455568729 5484760270594900841676547)
                  ·
                    refine ⟨8227140405892351262514821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5484760270594900841676547 8227140405892351262514821)
                    ·
                      refine ⟨1542588826104815861721529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8227140405892351262514821 1542588826104815861721529)
                      ·
                        rfl

theorem cell23_3004181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_3004181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004181 prefixEnd_3004181 := by exact prefixLift 3004181
  have htrace : WordTrace (prefixWord ++ tailWord_3004181) baseStart_3004181 baseEnd_3004181 := by
    simpa [prefixWord, tailWord_3004181, baseEnd_3004181] using wordTrace_append hprefix tailTrace_3004181
  have hstable : (prefixWord ++ tailWord_3004181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004181).length < 2 ^ (prefixWord ++ tailWord_3004181).sum := by decide
  have hdescent : baseEnd_3004181 < baseStart_3004181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004191 : List Nat := [1, 1, 2, 4, 2, 1, 2, 3, 3, 4]
def baseStart_3004191 : Nat := 118140960795 + 3004191 * 2 ^ 59
def prefixEnd_3004191 : Nat := 4983230072969 + 3 ^ 40 * 3004191 * 2
def baseEnd_3004191 : Nat := 514197986970453607532161

theorem tailTrace_3004191 : CollatzResearch.WordTrace tailWord_3004191 prefixEnd_3004191 514197986970453607532161 := by
  unfold tailWord_3004191
  simp only [CollatzResearch.WordTrace]
  refine ⟨109571847459336556819924427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73047898306224371213282951 109571847459336556819924427)
  ·
    refine ⟨164357771189004835229886641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109571847459336556819924427 164357771189004835229886641)
    ·
      refine ⟨123268328391753626422414981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164357771189004835229886641 123268328391753626422414981)
      ·
        refine ⟨23112811573453804954202809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123268328391753626422414981 23112811573453804954202809)
        ·
          refine ⟨17334608680090353715652107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23112811573453804954202809 17334608680090353715652107)
          ·
            refine ⟨26001913020135530573478161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17334608680090353715652107 26001913020135530573478161)
            ·
              refine ⟨19501434765101647930108621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26001913020135530573478161 19501434765101647930108621)
              ·
                refine ⟨7313038036913117973790733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19501434765101647930108621 7313038036913117973790733)
                ·
                  refine ⟨2742389263842419240171525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7313038036913117973790733 2742389263842419240171525)
                  ·
                    refine ⟨514197986970453607532161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2742389263842419240171525 514197986970453607532161)
                    ·
                      rfl

theorem cell23_3004191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 3, 4].length) (baseStart_3004191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004191 prefixEnd_3004191 := by exact prefixLift 3004191
  have htrace : WordTrace (prefixWord ++ tailWord_3004191) baseStart_3004191 baseEnd_3004191 := by
    simpa [prefixWord, tailWord_3004191, baseEnd_3004191] using wordTrace_append hprefix tailTrace_3004191
  have hstable : (prefixWord ++ tailWord_3004191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004191).length < 2 ^ (prefixWord ++ tailWord_3004191).sum := by decide
  have hdescent : baseEnd_3004191 < baseStart_3004191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004218 : List Nat := [3, 1, 1, 1, 5, 1, 3, 1, 2, 2, 3]
def baseStart_3004218 : Nat := 118140960795 + 3004218 * 2 ^ 59
def prefixEnd_3004218 : Nat := 4983230072969 + 3 ^ 40 * 3004218 * 2
def baseEnd_3004218 : Nat := 1542607824889032216958859

theorem tailTrace_3004218 : CollatzResearch.WordTrace tailWord_3004218 prefixEnd_3004218 1542607824889032216958859 := by
  unfold tailWord_3004218
  simp only [CollatzResearch.WordTrace]
  refine ⟨27393208057559685107789327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73048554820159160287438205 27393208057559685107789327)
  ·
    refine ⟨41089812086339527661683991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27393208057559685107789327 41089812086339527661683991)
    ·
      refine ⟨61634718129509291492525987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41089812086339527661683991 61634718129509291492525987)
      ·
        refine ⟨92452077194263937238788981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61634718129509291492525987 92452077194263937238788981)
        ·
          refine ⟨8667382236962244116136467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92452077194263937238788981 8667382236962244116136467)
          ·
            refine ⟨13001073355443366174204701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8667382236962244116136467 13001073355443366174204701)
            ·
              refine ⟨4875402508291262315326763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13001073355443366174204701 4875402508291262315326763)
              ·
                refine ⟨7313103762436893472990145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4875402508291262315326763 7313103762436893472990145)
                ·
                  refine ⟨5484827821827670104742609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7313103762436893472990145 5484827821827670104742609)
                  ·
                    refine ⟨4113620866370752578556957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5484827821827670104742609 4113620866370752578556957)
                    ·
                      refine ⟨1542607824889032216958859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4113620866370752578556957 1542607824889032216958859)
                      ·
                        rfl

theorem cell23_3004218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 2, 2, 3].length) (baseStart_3004218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004218 prefixEnd_3004218 := by exact prefixLift 3004218
  have htrace : WordTrace (prefixWord ++ tailWord_3004218) baseStart_3004218 baseEnd_3004218 := by
    simpa [prefixWord, tailWord_3004218, baseEnd_3004218] using wordTrace_append hprefix tailTrace_3004218
  have hstable : (prefixWord ++ tailWord_3004218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004218).length < 2 ^ (prefixWord ++ tailWord_3004218).sum := by decide
  have hdescent : baseEnd_3004218 < baseStart_3004218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004268 : List Nat := [2, 2, 1, 1, 4, 3, 2, 2, 1, 5]
def baseStart_3004268 : Nat := 118140960795 + 3004268 * 2 ^ 59
def prefixEnd_3004268 : Nat := 4983230072969 + 3 ^ 40 * 3004268 * 2
def baseEnd_3004268 : Nat := 514211166307252340444543

theorem tailTrace_3004268 : CollatzResearch.WordTrace tailWord_3004268 prefixEnd_3004268 514211166307252340444543 := by
  unfold tailWord_3004268
  simp only [CollatzResearch.WordTrace]
  refine ⟨54787327940028799485238729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73049770586705065980318305 54787327940028799485238729)
  ·
    refine ⟨41090495955021599613929047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54787327940028799485238729 41090495955021599613929047)
    ·
      refine ⟨61635743932532399420893571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41090495955021599613929047 61635743932532399420893571)
      ·
        refine ⟨92453615898798599131340357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61635743932532399420893571 92453615898798599131340357)
        ·
          refine ⟨17335052981024737337126317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92453615898798599131340357 17335052981024737337126317)
          ·
            refine ⟨6500644867884276501422369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17335052981024737337126317 6500644867884276501422369)
            ·
              refine ⟨4875483650913207376066777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6500644867884276501422369 4875483650913207376066777)
              ·
                refine ⟨3656612738184905532050083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4875483650913207376066777 3656612738184905532050083)
                ·
                  refine ⟨5484919107277358298075125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3656612738184905532050083 5484919107277358298075125)
                  ·
                    refine ⟨514211166307252340444543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5484919107277358298075125 514211166307252340444543)
                    ·
                      rfl

theorem cell23_3004268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 5].length) (baseStart_3004268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004268 prefixEnd_3004268 := by exact prefixLift 3004268
  have htrace : WordTrace (prefixWord ++ tailWord_3004268) baseStart_3004268 baseEnd_3004268 := by
    simpa [prefixWord, tailWord_3004268, baseEnd_3004268] using wordTrace_append hprefix tailTrace_3004268
  have hstable : (prefixWord ++ tailWord_3004268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004268).length < 2 ^ (prefixWord ++ tailWord_3004268).sum := by decide
  have hdescent : baseEnd_3004268 < baseStart_3004268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004281 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 6, 4]
def baseStart_3004281 : Nat := 118140960795 + 3004281 * 2 ^ 59
def prefixEnd_3004281 : Nat := 4983230072969 + 3 ^ 40 * 3004281 * 2
def baseEnd_3004281 : Nat := 514213391390088490157023

theorem tailTrace_3004281 : CollatzResearch.WordTrace tailWord_3004281 prefixEnd_3004281 514213391390088490157023 := by
  unfold tailWord_3004281
  simp only [CollatzResearch.WordTrace]
  refine ⟨109575130029010502190700697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73050086686007001460467131 109575130029010502190700697)
  ·
    refine ⟨82181347521757876643025523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109575130029010502190700697 82181347521757876643025523)
    ·
      refine ⟨123272021282636814964538285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82181347521757876643025523 123272021282636814964538285)
      ·
        refine ⟨46227007980988805611701857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123272021282636814964538285 46227007980988805611701857)
        ·
          refine ⟨34670255985741604208776393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46227007980988805611701857 34670255985741604208776393)
          ·
            refine ⟨26002691989306203156582295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34670255985741604208776393 26002691989306203156582295)
            ·
              refine ⟨39004037983959304734873443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26002691989306203156582295 39004037983959304734873443)
              ·
                refine ⟨58506056975938957102310165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39004037983959304734873443 58506056975938957102310165)
                ·
                  refine ⟨2742471420747138614170789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58506056975938957102310165 2742471420747138614170789)
                  ·
                    refine ⟨514213391390088490157023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2742471420747138614170789 514213391390088490157023)
                    ·
                      rfl

theorem cell23_3004281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 6, 4].length) (baseStart_3004281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004281 prefixEnd_3004281 := by exact prefixLift 3004281
  have htrace : WordTrace (prefixWord ++ tailWord_3004281) baseStart_3004281 baseEnd_3004281 := by
    simpa [prefixWord, tailWord_3004281, baseEnd_3004281] using wordTrace_append hprefix tailTrace_3004281
  have hstable : (prefixWord ++ tailWord_3004281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004281).length < 2 ^ (prefixWord ++ tailWord_3004281).sum := by decide
  have hdescent : baseEnd_3004281 < baseStart_3004281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004291 : List Nat := [1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 5]
def baseStart_3004291 : Nat := 118140960795 + 3004291 * 2 ^ 59
def prefixEnd_3004291 : Nat := 4983230072969 + 3 ^ 40 * 3004291 * 2
def baseEnd_3004291 : Nat := 1542645308976810431346023

theorem tailTrace_3004291 : CollatzResearch.WordTrace tailWord_3004291 prefixEnd_3004291 1542645308976810431346023 := by
  unfold tailWord_3004291
  simp only [CollatzResearch.WordTrace]
  refine ⟨109575494758974273898564727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73050329839316182599043151 109575494758974273898564727)
  ·
    refine ⟨164363242138461410847847091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109575494758974273898564727 164363242138461410847847091)
    ·
      refine ⟨246544863207692116271770637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164363242138461410847847091 246544863207692116271770637)
      ·
        refine ⟨92454323702884543601913989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246544863207692116271770637 92454323702884543601913989)
        ·
          refine ⟨17335185694290851925358873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92454323702884543601913989 17335185694290851925358873)
          ·
            refine ⟨13001389270718138944019155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17335185694290851925358873 13001389270718138944019155)
            ·
              refine ⟨19502083906077208416028733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13001389270718138944019155 19502083906077208416028733)
              ·
                refine ⟨7313281464778953156010775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19502083906077208416028733 7313281464778953156010775)
                ·
                  refine ⟨10969922197168429734016163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7313281464778953156010775 10969922197168429734016163)
                  ·
                    refine ⟨16454883295752644601024245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10969922197168429734016163 16454883295752644601024245)
                    ·
                      refine ⟨1542645308976810431346023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16454883295752644601024245 1542645308976810431346023)
                      ·
                        rfl

theorem cell23_3004291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 5].length) (baseStart_3004291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004291 prefixEnd_3004291 := by exact prefixLift 3004291
  have htrace : WordTrace (prefixWord ++ tailWord_3004291) baseStart_3004291 baseEnd_3004291 := by
    simpa [prefixWord, tailWord_3004291, baseEnd_3004291] using wordTrace_append hprefix tailTrace_3004291
  have hstable : (prefixWord ++ tailWord_3004291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004291).length < 2 ^ (prefixWord ++ tailWord_3004291).sum := by decide
  have hdescent : baseEnd_3004291 < baseStart_3004291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004304 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 7]
def baseStart_3004304 : Nat := 118140960795 + 3004304 * 2 ^ 59
def prefixEnd_3004304 : Nat := 4983230072969 + 3 ^ 40 * 3004304 * 2
def baseEnd_3004304 : Nat := 1542651984225318880483463

theorem tailTrace_3004304 : CollatzResearch.WordTrace tailWord_3004304 prefixEnd_3004304 1542651984225318880483463 := by
  unfold tailWord_3004304
  simp only [CollatzResearch.WordTrace]
  refine ⟨54787984453963588559393983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73050645938618118079191977 54787984453963588559393983)
  ·
    refine ⟨82181976680945382839090975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54787984453963588559393983 82181976680945382839090975)
    ·
      refine ⟨123272965021418074258636463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82181976680945382839090975 123272965021418074258636463)
      ·
        refine ⟨184909447532127111387954695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123272965021418074258636463 184909447532127111387954695)
        ·
          refine ⟨277364171298190667081932043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184909447532127111387954695 277364171298190667081932043)
          ·
            refine ⟨416046256947286000622898065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277364171298190667081932043 416046256947286000622898065)
            ·
              refine ⟨312034692710464500467173549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 416046256947286000622898065 312034692710464500467173549)
              ·
                refine ⟨117013009766424187675190081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 312034692710464500467173549 117013009766424187675190081)
                ·
                  refine ⟨87759757324818140756392561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117013009766424187675190081 87759757324818140756392561)
                  ·
                    refine ⟨65819817993613605567294421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87759757324818140756392561 65819817993613605567294421)
                    ·
                      refine ⟨1542651984225318880483463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 65819817993613605567294421 1542651984225318880483463)
                      ·
                        rfl

theorem cell23_3004304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 7].length) (baseStart_3004304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004304 prefixEnd_3004304 := by exact prefixLift 3004304
  have htrace : WordTrace (prefixWord ++ tailWord_3004304) baseStart_3004304 baseEnd_3004304 := by
    simpa [prefixWord, tailWord_3004304, baseEnd_3004304] using wordTrace_append hprefix tailTrace_3004304
  have hstable : (prefixWord ++ tailWord_3004304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004304).length < 2 ^ (prefixWord ++ tailWord_3004304).sum := by decide
  have hdescent : baseEnd_3004304 < baseStart_3004304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004305 : List Nat := [1, 2, 2, 1, 1, 1, 7, 1, 3, 2, 2]
def baseStart_3004305 : Nat := 118140960795 + 3004305 * 2 ^ 59
def prefixEnd_3004305 : Nat := 4983230072969 + 3 ^ 40 * 3004305 * 2
def baseEnd_3004305 : Nat := 1542652497705973376570959

theorem tailTrace_3004305 : CollatzResearch.WordTrace tailWord_3004305 prefixEnd_3004305 1542652497705973376570959 := by
  unfold tailWord_3004305
  simp only [CollatzResearch.WordTrace]
  refine ⟨109576005380923554289574369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73050670253949036193049579 109576005380923554289574369)
  ·
    refine ⟨82182004035692665717180777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109576005380923554289574369 82182004035692665717180777)
    ·
      refine ⟨61636503026769499287885583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82182004035692665717180777 61636503026769499287885583)
      ·
        refine ⟨92454754540154248931828375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61636503026769499287885583 92454754540154248931828375)
        ·
          refine ⟨138682131810231373397742563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92454754540154248931828375 138682131810231373397742563)
          ·
            refine ⟨208023197715347060096613845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138682131810231373397742563 208023197715347060096613845)
            ·
              refine ⟨4875543696453446721014387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 208023197715347060096613845 4875543696453446721014387)
              ·
                refine ⟨7313315544680170081521581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4875543696453446721014387 7313315544680170081521581)
                ·
                  refine ⟨2742493329255063780570593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7313315544680170081521581 2742493329255063780570593)
                  ·
                    refine ⟨2056869996941297835427945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2742493329255063780570593 2056869996941297835427945)
                    ·
                      refine ⟨1542652497705973376570959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2056869996941297835427945 1542652497705973376570959)
                      ·
                        rfl

theorem cell23_3004305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 3, 2, 2].length) (baseStart_3004305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004305 prefixEnd_3004305 := by exact prefixLift 3004305
  have htrace : WordTrace (prefixWord ++ tailWord_3004305) baseStart_3004305 baseEnd_3004305 := by
    simpa [prefixWord, tailWord_3004305, baseEnd_3004305] using wordTrace_append hprefix tailTrace_3004305
  have hstable : (prefixWord ++ tailWord_3004305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004305).length < 2 ^ (prefixWord ++ tailWord_3004305).sum := by decide
  have hdescent : baseEnd_3004305 < baseStart_3004305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004308 : List Nat := [2, 4, 2, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_3004308 : Nat := 118140960795 + 3004308 * 2 ^ 59
def prefixEnd_3004308 : Nat := 4983230072969 + 3 ^ 40 * 3004308 * 2
def baseEnd_3004308 : Nat := 1542654038147936864833445

theorem tailTrace_3004308 : CollatzResearch.WordTrace tailWord_3004308 prefixEnd_3004308 1542654038147936864833445 := by
  unfold tailWord_3004308
  simp only [CollatzResearch.WordTrace]
  refine ⟨54788057399956342900966789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73050743199941790534622385 54788057399956342900966789)
  ·
    refine ⟨10272760762491814293931273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54788057399956342900966789 10272760762491814293931273)
    ·
      refine ⟨7704570571868860720448455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10272760762491814293931273 7704570571868860720448455)
      ·
        refine ⟨11556855857803291080672683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7704570571868860720448455 11556855857803291080672683)
        ·
          refine ⟨17335283786704936621009025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11556855857803291080672683 17335283786704936621009025)
          ·
            refine ⟨13001462840028702465756769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17335283786704936621009025 13001462840028702465756769)
            ·
              refine ⟨9751097130021526849317577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13001462840028702465756769 9751097130021526849317577)
              ·
                refine ⟨7313322847516145136988183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9751097130021526849317577 7313322847516145136988183)
                ·
                  refine ⟨10969984271274217705482275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7313322847516145136988183 10969984271274217705482275)
                  ·
                    refine ⟨16454976406911326558223413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10969984271274217705482275 16454976406911326558223413)
                    ·
                      refine ⟨1542654038147936864833445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16454976406911326558223413 1542654038147936864833445)
                      ·
                        rfl

theorem cell23_3004308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_3004308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004308 prefixEnd_3004308 := by exact prefixLift 3004308
  have htrace : WordTrace (prefixWord ++ tailWord_3004308) baseStart_3004308 baseEnd_3004308 := by
    simpa [prefixWord, tailWord_3004308, baseEnd_3004308] using wordTrace_append hprefix tailTrace_3004308
  have hstable : (prefixWord ++ tailWord_3004308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004308).length < 2 ^ (prefixWord ++ tailWord_3004308).sum := by decide
  have hdescent : baseEnd_3004308 < baseStart_3004308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004311 : List Nat := [1, 1, 3, 3, 1, 4, 2, 8]
def baseStart_3004311 : Nat := 118140960795 + 3004311 * 2 ^ 59
def prefixEnd_3004311 : Nat := 4983230072969 + 3 ^ 40 * 3004311 * 2
def baseEnd_3004311 : Nat := 57135391799625939003553

theorem tailTrace_3004311 : CollatzResearch.WordTrace tailWord_3004311 prefixEnd_3004311 57135391799625939003553 := by
  unfold tailWord_3004311
  simp only [CollatzResearch.WordTrace]
  refine ⟨109576224218901817314292787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73050816145934544876195191 109576224218901817314292787)
  ·
    refine ⟨164364336328352725971439181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109576224218901817314292787 164364336328352725971439181)
    ·
      refine ⟨61636626123132272239289693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164364336328352725971439181 61636626123132272239289693)
      ·
        refine ⟨23113734796174602089733635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61636626123132272239289693 23113734796174602089733635)
        ·
          refine ⟨34670602194261903134600453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23113734796174602089733635 34670602194261903134600453)
          ·
            refine ⟨6500737911424106837737585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34670602194261903134600453 6500737911424106837737585)
            ·
              refine ⟨4875553433568080128303189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6500737911424106837737585 4875553433568080128303189)
              ·
                refine ⟨57135391799625939003553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4875553433568080128303189 57135391799625939003553)
                ·
                  rfl

theorem cell23_3004311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 8].length) (baseStart_3004311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004311 prefixEnd_3004311 := by exact prefixLift 3004311
  have htrace : WordTrace (prefixWord ++ tailWord_3004311) baseStart_3004311 baseEnd_3004311 := by
    simpa [prefixWord, tailWord_3004311, baseEnd_3004311] using wordTrace_append hprefix tailTrace_3004311
  have hstable : (prefixWord ++ tailWord_3004311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004311).length < 2 ^ (prefixWord ++ tailWord_3004311).sum := by decide
  have hdescent : baseEnd_3004311 < baseStart_3004311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004322 : List Nat := [3, 3, 1, 2, 3, 2, 1, 2, 1, 1, 4]
def baseStart_3004322 : Nat := 118140960795 + 3004322 * 2 ^ 59
def prefixEnd_3004322 : Nat := 4983230072969 + 3 ^ 40 * 3004322 * 2
def baseEnd_3004322 : Nat := 1542661226877099810058381

theorem tailTrace_3004322 : CollatzResearch.WordTrace tailWord_3004322 prefixEnd_3004322 1542661226877099810058381 := by
  unfold tailWord_3004322
  simp only [CollatzResearch.WordTrace]
  refine ⟨27394156355465491548235805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73051083614574644128628813 27394156355465491548235805)
  ·
    refine ⟨10272808633299559330588427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27394156355465491548235805 10272808633299559330588427)
    ·
      refine ⟨15409212949949338995882641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10272808633299559330588427 15409212949949338995882641)
      ·
        refine ⟨11556909712462004246911981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15409212949949338995882641 11556909712462004246911981)
        ·
          refine ⟨4333841142173251592591993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11556909712462004246911981 4333841142173251592591993)
          ·
            refine ⟨3250380856629938694443995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4333841142173251592591993 3250380856629938694443995)
            ·
              refine ⟨4875571284944908041665993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3250380856629938694443995 4875571284944908041665993)
              ·
                refine ⟨3656678463708681031249495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4875571284944908041665993 3656678463708681031249495)
                ·
                  refine ⟨5485017695563021546874243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3656678463708681031249495 5485017695563021546874243)
                  ·
                    refine ⟨8227526543344532320311365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5485017695563021546874243 8227526543344532320311365)
                    ·
                      refine ⟨1542661226877099810058381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8227526543344532320311365 1542661226877099810058381)
                      ·
                        rfl

theorem cell23_3004322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_3004322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004322 prefixEnd_3004322 := by exact prefixLift 3004322
  have htrace : WordTrace (prefixWord ++ tailWord_3004322) baseStart_3004322 baseEnd_3004322 := by
    simpa [prefixWord, tailWord_3004322, baseEnd_3004322] using wordTrace_append hprefix tailTrace_3004322
  have hstable : (prefixWord ++ tailWord_3004322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004322).length < 2 ^ (prefixWord ++ tailWord_3004322).sum := by decide
  have hdescent : baseEnd_3004322 < baseStart_3004322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004338 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3]
def baseStart_3004338 : Nat := 118140960795 + 3004338 * 2 ^ 59
def prefixEnd_3004338 : Nat := 4983230072969 + 3 ^ 40 * 3004338 * 2
def baseEnd_3004338 : Nat := 1542669442567571747458307

theorem tailTrace_3004338 : CollatzResearch.WordTrace tailWord_3004338 prefixEnd_3004338 1542669442567571747458307 := by
  unfold tailWord_3004338
  simp only [CollatzResearch.WordTrace]
  refine ⟨27394302247451000231381417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73051472659869333950350445 27394302247451000231381417)
  ·
    refine ⟨20545726685588250173536063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27394302247451000231381417 20545726685588250173536063)
    ·
      refine ⟨30818590028382375260304095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20545726685588250173536063 30818590028382375260304095)
      ·
        refine ⟨46227885042573562890456143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30818590028382375260304095 46227885042573562890456143)
        ·
          refine ⟨69341827563860344335684215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46227885042573562890456143 69341827563860344335684215)
          ·
            refine ⟨104012741345790516503526323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69341827563860344335684215 104012741345790516503526323)
            ·
              refine ⟨156019112018685774755289485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104012741345790516503526323 156019112018685774755289485)
              ·
                refine ⟨58507167007007165533233557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156019112018685774755289485 58507167007007165533233557)
                ·
                  refine ⟨2742523453453460884370323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58507167007007165533233557 2742523453453460884370323)
                  ·
                    refine ⟨4113785180180191326555485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2742523453453460884370323 4113785180180191326555485)
                    ·
                      refine ⟨1542669442567571747458307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4113785180180191326555485 1542669442567571747458307)
                      ·
                        rfl

theorem cell23_3004338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3].length) (baseStart_3004338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004338 prefixEnd_3004338 := by exact prefixLift 3004338
  have htrace : WordTrace (prefixWord ++ tailWord_3004338) baseStart_3004338 baseEnd_3004338 := by
    simpa [prefixWord, tailWord_3004338, baseEnd_3004338] using wordTrace_append hprefix tailTrace_3004338
  have hstable : (prefixWord ++ tailWord_3004338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004338).length < 2 ^ (prefixWord ++ tailWord_3004338).sum := by decide
  have hdescent : baseEnd_3004338 < baseStart_3004338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004406 : List Nat := [5, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3]
def baseStart_3004406 : Nat := 118140960795 + 3004406 * 2 ^ 59
def prefixEnd_3004406 : Nat := 4983230072969 + 3 ^ 40 * 3004406 * 2
def baseEnd_3004406 : Nat := 1542704359252077481407995

theorem tailTrace_3004406 : CollatzResearch.WordTrace tailWord_3004406 prefixEnd_3004406 1542704359252077481407995 := by
  unfold tailWord_3004406
  simp only [CollatzResearch.WordTrace]
  refine ⟨6848730572097353033687567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73053126102371765692667381 6848730572097353033687567)
  ·
    refine ⟨10273095858146029550531351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6848730572097353033687567 10273095858146029550531351)
    ·
      refine ⟨15409643787219044325797027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10273095858146029550531351 15409643787219044325797027)
      ·
        refine ⟨23114465680828566488695541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15409643787219044325797027 23114465680828566488695541)
        ·
          refine ⟨2166981157577678108315207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23114465680828566488695541 2166981157577678108315207)
          ·
            refine ⟨3250471736366517162472811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2166981157577678108315207 3250471736366517162472811)
            ·
              refine ⟨4875707604549775743709217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3250471736366517162472811 4875707604549775743709217)
              ·
                refine ⟨3656780703412331807781913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4875707604549775743709217 3656780703412331807781913)
                ·
                  refine ⟨2742585527559248855836435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3656780703412331807781913 2742585527559248855836435)
                  ·
                    refine ⟨4113878291338873283754653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2742585527559248855836435 4113878291338873283754653)
                    ·
                      refine ⟨1542704359252077481407995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4113878291338873283754653 1542704359252077481407995)
                      ·
                        rfl

theorem cell23_3004406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_3004406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004406 prefixEnd_3004406 := by exact prefixLift 3004406
  have htrace : WordTrace (prefixWord ++ tailWord_3004406) baseStart_3004406 baseEnd_3004406 := by
    simpa [prefixWord, tailWord_3004406, baseEnd_3004406] using wordTrace_append hprefix tailTrace_3004406
  have hstable : (prefixWord ++ tailWord_3004406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004406).length < 2 ^ (prefixWord ++ tailWord_3004406).sum := by decide
  have hdescent : baseEnd_3004406 < baseStart_3004406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004428 : List Nat := [2, 2, 1, 2, 3, 1, 1, 3, 2, 3, 3]
def baseStart_3004428 : Nat := 118140960795 + 3004428 * 2 ^ 59
def prefixEnd_3004428 : Nat := 4983230072969 + 3 ^ 40 * 3004428 * 2
def baseEnd_3004428 : Nat := 1542715655826476395332893

theorem tailTrace_3004428 : CollatzResearch.WordTrace tailWord_3004428 prefixEnd_3004428 1542715655826476395332893 := by
  unfold tailWord_3004428
  simp only [CollatzResearch.WordTrace]
  refine ⟨54790245779738973148150969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73053661039651964197534625 54790245779738973148150969)
  ·
    refine ⟨41092684334804229861113227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54790245779738973148150969 41092684334804229861113227)
    ·
      refine ⟨61639026502206344791669841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41092684334804229861113227 61639026502206344791669841)
      ·
        refine ⟨46229269876654758593752381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61639026502206344791669841 46229269876654758593752381)
        ·
          refine ⟨17335976203745534472657143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46229269876654758593752381 17335976203745534472657143)
          ·
            refine ⟨26003964305618301708985715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17335976203745534472657143 26003964305618301708985715)
            ·
              refine ⟨39005946458427452563478573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26003964305618301708985715 39005946458427452563478573)
              ·
                refine ⟨14627229921910294711304465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39005946458427452563478573 14627229921910294711304465)
                ·
                  refine ⟨10970422441432721033478349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14627229921910294711304465 10970422441432721033478349)
                  ·
                    refine ⟨4113908415537270387554381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10970422441432721033478349 4113908415537270387554381)
                    ·
                      refine ⟨1542715655826476395332893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4113908415537270387554381 1542715655826476395332893)
                      ·
                        rfl

theorem cell23_3004428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_3004428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004428 prefixEnd_3004428 := by exact prefixLift 3004428
  have htrace : WordTrace (prefixWord ++ tailWord_3004428) baseStart_3004428 baseEnd_3004428 := by
    simpa [prefixWord, tailWord_3004428, baseEnd_3004428] using wordTrace_append hprefix tailTrace_3004428
  have hstable : (prefixWord ++ tailWord_3004428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004428).length < 2 ^ (prefixWord ++ tailWord_3004428).sum := by decide
  have hdescent : baseEnd_3004428 < baseStart_3004428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004441 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 3, 2, 5]
def baseStart_3004441 : Nat := 118140960795 + 3004441 * 2 ^ 59
def prefixEnd_3004441 : Nat := 4983230072969 + 3 ^ 40 * 3004441 * 2
def baseEnd_3004441 : Nat := 1542722331074984844470333

theorem tailTrace_3004441 : CollatzResearch.WordTrace tailWord_3004441 prefixEnd_3004441 1542722331074984844470333 := by
  unfold tailWord_3004441
  simp only [CollatzResearch.WordTrace]
  refine ⟨109580965708430849516525177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73053977138953899677683451 109580965708430849516525177)
  ·
    refine ⟨82185724281323137137393883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109580965708430849516525177 82185724281323137137393883)
    ·
      refine ⟨123278586421984705706090825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82185724281323137137393883 123278586421984705706090825)
      ·
        refine ⟨92458939816488529279568119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123278586421984705706090825 92458939816488529279568119)
        ·
          refine ⟨138688409724732793919352179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92458939816488529279568119 138688409724732793919352179)
          ·
            refine ⟨208032614587099190879028269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138688409724732793919352179 208032614587099190879028269)
            ·
              refine ⟨78012230470162196579635601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 208032614587099190879028269 78012230470162196579635601)
              ·
                refine ⟨58509172852621647434726701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78012230470162196579635601 58509172852621647434726701)
                ·
                  refine ⟨21940939819733117788022513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58509172852621647434726701 21940939819733117788022513)
                  ·
                    refine ⟨16455704864799838341016885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21940939819733117788022513 16455704864799838341016885)
                    ·
                      refine ⟨1542722331074984844470333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16455704864799838341016885 1542722331074984844470333)
                      ·
                        rfl

theorem cell23_3004441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_3004441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004441 prefixEnd_3004441 := by exact prefixLift 3004441
  have htrace : WordTrace (prefixWord ++ tailWord_3004441) baseStart_3004441 baseEnd_3004441 := by
    simpa [prefixWord, tailWord_3004441, baseEnd_3004441] using wordTrace_append hprefix tailTrace_3004441
  have hstable : (prefixWord ++ tailWord_3004441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004441).length < 2 ^ (prefixWord ++ tailWord_3004441).sum := by decide
  have hdescent : baseEnd_3004441 < baseStart_3004441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004488 : List Nat := [2, 1, 3, 1, 1, 1, 2, 4, 1, 4, 3]
def baseStart_3004488 : Nat := 118140960795 + 3004488 * 2 ^ 59
def prefixEnd_3004488 : Nat := 4983230072969 + 3 ^ 40 * 3004488 * 2
def baseEnd_3004488 : Nat := 1542746464665746160582617

theorem tailTrace_3004488 : CollatzResearch.WordTrace tailWord_3004488 prefixEnd_3004488 1542746464665746160582617 := by
  unfold tailWord_3004488
  simp only [CollatzResearch.WordTrace]
  refine ⟨54791339969630288271743059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73055119959507051028990745 54791339969630288271743059)
  ·
    refine ⟨82187009954445432407614589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54791339969630288271743059 82187009954445432407614589)
    ·
      refine ⟨30820128732917037152855471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82187009954445432407614589 30820128732917037152855471)
      ·
        refine ⟨46230193099375555729283207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30820128732917037152855471 46230193099375555729283207)
        ·
          refine ⟨69345289649063333593924811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46230193099375555729283207 69345289649063333593924811)
          ·
            refine ⟨104017934473595000390887217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69345289649063333593924811 104017934473595000390887217)
            ·
              refine ⟨78013450855196250293165413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104017934473595000390887217 78013450855196250293165413)
              ·
                refine ⟨14627522035349296929968515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78013450855196250293165413 14627522035349296929968515)
                ·
                  refine ⟨21941283053023945394952773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14627522035349296929968515 21941283053023945394952773)
                  ·
                    refine ⟨4113990572441989761553645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21941283053023945394952773 4113990572441989761553645)
                    ·
                      refine ⟨1542746464665746160582617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4113990572441989761553645 1542746464665746160582617)
                      ·
                        rfl

theorem cell23_3004488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_3004488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004488 prefixEnd_3004488 := by exact prefixLift 3004488
  have htrace : WordTrace (prefixWord ++ tailWord_3004488) baseStart_3004488 baseEnd_3004488 := by
    simpa [prefixWord, tailWord_3004488, baseEnd_3004488] using wordTrace_append hprefix tailTrace_3004488
  have hstable : (prefixWord ++ tailWord_3004488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004488).length < 2 ^ (prefixWord ++ tailWord_3004488).sum := by decide
  have hdescent : baseEnd_3004488 < baseStart_3004488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004505 : List Nat := [1, 2, 1, 2, 2, 1, 6, 1, 2, 2, 3]
def baseStart_3004505 : Nat := 118140960795 + 3004505 * 2 ^ 59
def prefixEnd_3004505 : Nat := 4983230072969 + 3 ^ 40 * 3004505 * 2
def baseEnd_3004505 : Nat := 1542755193836872594070039

theorem tailTrace_3004505 : CollatzResearch.WordTrace tailWord_3004505 prefixEnd_3004505 1542755193836872594070039 := by
  unfold tailWord_3004505
  simp only [CollatzResearch.WordTrace]
  refine ⟨109583299980198988446854969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73055533320132658964569979 109583299980198988446854969)
  ·
    refine ⟨82187474985149241335141227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109583299980198988446854969 82187474985149241335141227)
    ·
      refine ⟨123281212477723862002711841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82187474985149241335141227 123281212477723862002711841)
      ·
        refine ⟨92460909358292896502033881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123281212477723862002711841 92460909358292896502033881)
        ·
          refine ⟨69345682018719672376525411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92460909358292896502033881 69345682018719672376525411)
          ·
            refine ⟨104018523028079508564788117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69345682018719672376525411 104018523028079508564788117)
            ·
              refine ⟨4875868266941226963974443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 104018523028079508564788117 4875868266941226963974443)
              ·
                refine ⟨7313802400411840445961665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4875868266941226963974443 7313802400411840445961665)
                ·
                  refine ⟨5485351800308880334471249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7313802400411840445961665 5485351800308880334471249)
                  ·
                    refine ⟨4114013850231660250853437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5485351800308880334471249 4114013850231660250853437)
                    ·
                      refine ⟨1542755193836872594070039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4114013850231660250853437 1542755193836872594070039)
                      ·
                        rfl

theorem cell23_3004505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 2, 3].length) (baseStart_3004505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004505 prefixEnd_3004505 := by exact prefixLift 3004505
  have htrace : WordTrace (prefixWord ++ tailWord_3004505) baseStart_3004505 baseEnd_3004505 := by
    simpa [prefixWord, tailWord_3004505, baseEnd_3004505] using wordTrace_append hprefix tailTrace_3004505
  have hstable : (prefixWord ++ tailWord_3004505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004505).length < 2 ^ (prefixWord ++ tailWord_3004505).sum := by decide
  have hdescent : baseEnd_3004505 < baseStart_3004505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004525 : List Nat := [1, 5, 1, 1, 2, 1, 4, 2, 6]
def baseStart_3004525 : Nat := 118140960795 + 3004525 * 2 ^ 59
def prefixEnd_3004525 : Nat := 4983230072969 + 3 ^ 40 * 3004525 * 2
def baseEnd_3004525 : Nat := 171418384827773612868883

theorem tailTrace_3004525 : CollatzResearch.WordTrace tailWord_3004525 prefixEnd_3004525 171418384827773612868883 := by
  unfold tailWord_3004525
  simp only [CollatzResearch.WordTrace]
  refine ⟨109584029440126531862583029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73056019626751021241722019 109584029440126531862583029)
  ·
    refine ⟨10273502760011862362117159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109584029440126531862583029 10273502760011862362117159)
    ·
      refine ⟨15410254140017793543175739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10273502760011862362117159 15410254140017793543175739)
      ·
        refine ⟨23115381210026690314763609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15410254140017793543175739 23115381210026690314763609)
        ·
          refine ⟨17336535907520017736072707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23115381210026690314763609 17336535907520017736072707)
          ·
            refine ⟨26004803861280026604109061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17336535907520017736072707 26004803861280026604109061)
            ·
              refine ⟨4875900723990004988270449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26004803861280026604109061 4875900723990004988270449)
              ·
                refine ⟨3656925542992503741202837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4875900723990004988270449 3656925542992503741202837)
                ·
                  refine ⟨171418384827773612868883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3656925542992503741202837 171418384827773612868883)
                  ·
                    rfl

theorem cell23_3004525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_3004525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004525 prefixEnd_3004525 := by exact prefixLift 3004525
  have htrace : WordTrace (prefixWord ++ tailWord_3004525) baseStart_3004525 baseEnd_3004525 := by
    simpa [prefixWord, tailWord_3004525, baseEnd_3004525] using wordTrace_append hprefix tailTrace_3004525
  have hstable : (prefixWord ++ tailWord_3004525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004525).length < 2 ^ (prefixWord ++ tailWord_3004525).sum := by decide
  have hdescent : baseEnd_3004525 < baseStart_3004525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004548 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 2, 1, 7]
def baseStart_3004548 : Nat := 118140960795 + 3004548 * 2 ^ 59
def prefixEnd_3004548 : Nat := 4983230072969 + 3 ^ 40 * 3004548 * 2
def baseEnd_3004548 : Nat := 1542777273505015925832341

theorem tailTrace_3004548 : CollatzResearch.WordTrace tailWord_3004548 prefixEnd_3004548 1542777273505015925832341 := by
  unfold tailWord_3004548
  simp only [CollatzResearch.WordTrace]
  refine ⟨54792434159521603395335149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73056578879362137860446865 54792434159521603395335149)
  ·
    refine ⟨20547162809820601273250681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54792434159521603395335149 20547162809820601273250681)
    ·
      refine ⟨15410372107365450954938011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20547162809820601273250681 15410372107365450954938011)
      ·
        refine ⟨23115558161048176432407017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15410372107365450954938011 23115558161048176432407017)
        ·
          refine ⟨17336668620786132324305263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23115558161048176432407017 17336668620786132324305263)
          ·
            refine ⟨26005002931179198486457895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17336668620786132324305263 26005002931179198486457895)
            ·
              refine ⟨39007504396768797729686843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26005002931179198486457895 39007504396768797729686843)
              ·
                refine ⟨58511256595153196594530265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39007504396768797729686843 58511256595153196594530265)
                ·
                  refine ⟨43883442446364897445897699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58511256595153196594530265 43883442446364897445897699)
                  ·
                    refine ⟨65825163669547346168846549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43883442446364897445897699 65825163669547346168846549)
                    ·
                      refine ⟨1542777273505015925832341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 65825163669547346168846549 1542777273505015925832341)
                      ·
                        rfl

theorem cell23_3004548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_3004548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004548 prefixEnd_3004548 := by exact prefixLift 3004548
  have htrace : WordTrace (prefixWord ++ tailWord_3004548) baseStart_3004548 baseEnd_3004548 := by
    simpa [prefixWord, tailWord_3004548, baseEnd_3004548] using wordTrace_append hprefix tailTrace_3004548
  have hstable : (prefixWord ++ tailWord_3004548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004548).length < 2 ^ (prefixWord ++ tailWord_3004548).sum := by decide
  have hdescent : baseEnd_3004548 < baseStart_3004548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004552 : List Nat := [2, 1, 3, 4, 1, 1, 1, 1, 5, 1, 3]
def baseStart_3004552 : Nat := 118140960795 + 3004552 * 2 ^ 59
def prefixEnd_3004552 : Nat := 4983230072969 + 3 ^ 40 * 3004552 * 2
def baseEnd_3004552 : Nat := 1542779327427633910182323

theorem tailTrace_3004552 : CollatzResearch.WordTrace tailWord_3004552 prefixEnd_3004552 1542779327427633910182323 := by
  unfold tailWord_3004552
  simp only [CollatzResearch.WordTrace]
  refine ⟨54792507105514357736907955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73056676140685810315877273 54792507105514357736907955)
  ·
    refine ⟨82188760658271536605361933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54792507105514357736907955 82188760658271536605361933)
    ·
      refine ⟨30820785246851826227010725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82188760658271536605361933 30820785246851826227010725)
      ·
        refine ⟨5778897233784717417564511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30820785246851826227010725 5778897233784717417564511)
        ·
          refine ⟨8668345850677076126346767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5778897233784717417564511 8668345850677076126346767)
          ·
            refine ⟨13002518776015614189520151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8668345850677076126346767 13002518776015614189520151)
            ·
              refine ⟨19503778164023421284280227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13002518776015614189520151 19503778164023421284280227)
              ·
                refine ⟨29255667246035131926420341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19503778164023421284280227 29255667246035131926420341)
                ·
                  refine ⟨2742718804315793618101907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29255667246035131926420341 2742718804315793618101907)
                  ·
                    refine ⟨4114078206473690427152861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2742718804315793618101907 4114078206473690427152861)
                    ·
                      refine ⟨1542779327427633910182323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4114078206473690427152861 1542779327427633910182323)
                      ·
                        rfl

theorem cell23_3004552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_3004552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004552 prefixEnd_3004552 := by exact prefixLift 3004552
  have htrace : WordTrace (prefixWord ++ tailWord_3004552) baseStart_3004552 baseEnd_3004552 := by
    simpa [prefixWord, tailWord_3004552, baseEnd_3004552] using wordTrace_append hprefix tailTrace_3004552
  have hstable : (prefixWord ++ tailWord_3004552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004552).length < 2 ^ (prefixWord ++ tailWord_3004552).sum := by decide
  have hdescent : baseEnd_3004552 < baseStart_3004552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004562 : List Nat := [3, 2, 3, 1, 1, 1, 3, 1, 1, 5, 2]
def baseStart_3004562 : Nat := 118140960795 + 3004562 * 2 ^ 59
def prefixEnd_3004562 : Nat := 4983230072969 + 3 ^ 40 * 3004562 * 2
def baseEnd_3004562 : Nat := 1542784462234178871057277

theorem tailTrace_3004562 : CollatzResearch.WordTrace tailWord_3004562 prefixEnd_3004562 1542784462234178871057277 := by
  unfold tailWord_3004562
  simp only [CollatzResearch.WordTrace]
  refine ⟨27396344735248121795419985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73056919293994991454453293 27396344735248121795419985)
  ·
    refine ⟨20547258551436091346564989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27396344735248121795419985 20547258551436091346564989)
    ·
      refine ⟨7705221956788534254961871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20547258551436091346564989 7705221956788534254961871)
      ·
        refine ⟨11557832935182801382442807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7705221956788534254961871 11557832935182801382442807)
        ·
          refine ⟨17336749402774202073664211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11557832935182801382442807 17336749402774202073664211)
          ·
            refine ⟨26005124104161303110496317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17336749402774202073664211 26005124104161303110496317)
            ·
              refine ⟨9751921539060488666436119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26005124104161303110496317 9751921539060488666436119)
              ·
                refine ⟨14627882308590732999654179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9751921539060488666436119 14627882308590732999654179)
                ·
                  refine ⟨21941823462886099499481269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14627882308590732999654179 21941823462886099499481269)
                  ·
                    refine ⟨2057045949645571828076369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21941823462886099499481269 2057045949645571828076369)
                    ·
                      refine ⟨1542784462234178871057277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2057045949645571828076369 1542784462234178871057277)
                      ·
                        rfl

theorem cell23_3004562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_3004562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004562 prefixEnd_3004562 := by exact prefixLift 3004562
  have htrace : WordTrace (prefixWord ++ tailWord_3004562) baseStart_3004562 baseEnd_3004562 := by
    simpa [prefixWord, tailWord_3004562, baseEnd_3004562] using wordTrace_append hprefix tailTrace_3004562
  have hstable : (prefixWord ++ tailWord_3004562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004562).length < 2 ^ (prefixWord ++ tailWord_3004562).sum := by decide
  have hdescent : baseEnd_3004562 < baseStart_3004562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004586 : List Nat := [3, 1, 5, 1, 2, 1, 2, 1, 3, 1, 3]
def baseStart_3004586 : Nat := 118140960795 + 3004586 * 2 ^ 59
def prefixEnd_3004586 : Nat := 4983230072969 + 3 ^ 40 * 3004586 * 2
def baseEnd_3004586 : Nat := 1542796785769886777157167

theorem tailTrace_3004586 : CollatzResearch.WordTrace tailWord_3004586 prefixEnd_3004586 1542796785769886777157167 := by
  unfold tailWord_3004586
  simp only [CollatzResearch.WordTrace]
  refine ⟨27396563573226384820138403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73057502861937026187035741 27396563573226384820138403)
  ·
    refine ⟨41094845359839577230207605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27396563573226384820138403 41094845359839577230207605)
    ·
      refine ⟨3852641752484960365331963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41094845359839577230207605 3852641752484960365331963)
      ·
        refine ⟨5778962628727440547997945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3852641752484960365331963 5778962628727440547997945)
        ·
          refine ⟨4334221971545580410998459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5778962628727440547997945 4334221971545580410998459)
          ·
            refine ⟨6501332957318370616497689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4334221971545580410998459 6501332957318370616497689)
            ·
              refine ⟨4875999717988777962373267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6501332957318370616497689 4875999717988777962373267)
              ·
                refine ⟨7313999576983166943559901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4875999717988777962373267 7313999576983166943559901)
                ·
                  refine ⟨2742749841368687603834963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7313999576983166943559901 2742749841368687603834963)
                  ·
                    refine ⟨4114124762053031405752445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2742749841368687603834963 4114124762053031405752445)
                    ·
                      refine ⟨1542796785769886777157167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4114124762053031405752445 1542796785769886777157167)
                      ·
                        rfl

theorem cell23_3004586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_3004586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004586 prefixEnd_3004586 := by exact prefixLift 3004586
  have htrace : WordTrace (prefixWord ++ tailWord_3004586) baseStart_3004586 baseEnd_3004586 := by
    simpa [prefixWord, tailWord_3004586, baseEnd_3004586] using wordTrace_append hprefix tailTrace_3004586
  have hstable : (prefixWord ++ tailWord_3004586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004586).length < 2 ^ (prefixWord ++ tailWord_3004586).sum := by decide
  have hdescent : baseEnd_3004586 < baseStart_3004586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004620 : List Nat := [2, 2, 1, 6, 2, 1, 1, 3, 1, 1, 3]
def baseStart_3004620 : Nat := 118140960795 + 3004620 * 2 ^ 59
def prefixEnd_3004620 : Nat := 4983230072969 + 3 ^ 40 * 3004620 * 2
def baseEnd_3004620 : Nat := 1542814244112139644132011

theorem tailTrace_3004620 : CollatzResearch.WordTrace tailWord_3004620 prefixEnd_3004620 1542814244112139644132011 := by
  unfold tailWord_3004620
  simp only [CollatzResearch.WordTrace]
  refine ⟨54793747187391181543645657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73058329583188242058194209 54793747187391181543645657)
  ·
    refine ⟨41095310390543386157734243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54793747187391181543645657 41095310390543386157734243)
    ·
      refine ⟨61642965585815079236601365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41095310390543386157734243 61642965585815079236601365)
      ·
        refine ⟨2889514011835081839215689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 61642965585815079236601365 2889514011835081839215689)
        ·
          refine ⟨2167135508876311379411767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2889514011835081839215689 2167135508876311379411767)
          ·
            refine ⟨3250703263314467069117651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2167135508876311379411767 3250703263314467069117651)
            ·
              refine ⟨4876054894971700603676477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3250703263314467069117651 4876054894971700603676477)
              ·
                refine ⟨1828520585614387726378679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4876054894971700603676477 1828520585614387726378679)
                ·
                  refine ⟨2742780878421581589568019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1828520585614387726378679 2742780878421581589568019)
                  ·
                    refine ⟨4114171317632372384352029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2742780878421581589568019 4114171317632372384352029)
                    ·
                      refine ⟨1542814244112139644132011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4114171317632372384352029 1542814244112139644132011)
                      ·
                        rfl

theorem cell23_3004620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_3004620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004620 prefixEnd_3004620 := by exact prefixLift 3004620
  have htrace : WordTrace (prefixWord ++ tailWord_3004620) baseStart_3004620 baseEnd_3004620 := by
    simpa [prefixWord, tailWord_3004620, baseEnd_3004620] using wordTrace_append hprefix tailTrace_3004620
  have hstable : (prefixWord ++ tailWord_3004620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004620).length < 2 ^ (prefixWord ++ tailWord_3004620).sum := by decide
  have hdescent : baseEnd_3004620 < baseStart_3004620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004625 : List Nat := [1, 2, 2, 1, 2, 2, 2, 4, 1, 3, 3]
def baseStart_3004625 : Nat := 118140960795 + 3004625 * 2 ^ 59
def prefixEnd_3004625 : Nat := 4983230072969 + 3 ^ 40 * 3004625 * 2
def baseEnd_3004625 : Nat := 1542816811515412124569487

theorem tailTrace_3004625 : CollatzResearch.WordTrace tailWord_3004625 prefixEnd_3004625 1542816811515412124569487 := by
  unfold tailWord_3004625
  simp only [CollatzResearch.WordTrace]
  refine ⟨109587676739764248941223329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73058451159842832627482219 109587676739764248941223329)
  ·
    refine ⟨82190757554823186705917497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109587676739764248941223329 82190757554823186705917497)
    ·
      refine ⟨61643068166117390029438123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82190757554823186705917497 61643068166117390029438123)
      ·
        refine ⟨92464602249176085044157185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61643068166117390029438123 92464602249176085044157185)
        ·
          refine ⟨69348451686882063783117889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92464602249176085044157185 69348451686882063783117889)
          ·
            refine ⟨52011338765161547837338417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69348451686882063783117889 52011338765161547837338417)
            ·
              refine ⟨39008504073871160878003813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52011338765161547837338417 39008504073871160878003813)
              ·
                refine ⟨7314094513850842664625715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39008504073871160878003813 7314094513850842664625715)
                ·
                  refine ⟨10971141770776263996938573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7314094513850842664625715 10971141770776263996938573)
                  ·
                    refine ⟨4114178164041098998851965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10971141770776263996938573 4114178164041098998851965)
                    ·
                      refine ⟨1542816811515412124569487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4114178164041098998851965 1542816811515412124569487)
                      ·
                        rfl

theorem cell23_3004625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 3, 3].length) (baseStart_3004625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004625 prefixEnd_3004625 := by exact prefixLift 3004625
  have htrace : WordTrace (prefixWord ++ tailWord_3004625) baseStart_3004625 baseEnd_3004625 := by
    simpa [prefixWord, tailWord_3004625, baseEnd_3004625] using wordTrace_append hprefix tailTrace_3004625
  have hstable : (prefixWord ++ tailWord_3004625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004625).length < 2 ^ (prefixWord ++ tailWord_3004625).sum := by decide
  have hdescent : baseEnd_3004625 < baseStart_3004625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004643 : List Nat := [1, 1, 1, 8, 1, 2, 1, 1, 3, 2, 2]
def baseStart_3004643 : Nat := 118140960795 + 3004643 * 2 ^ 59
def prefixEnd_3004643 : Nat := 4983230072969 + 3 ^ 40 * 3004643 * 2
def baseEnd_3004643 : Nat := 1542826054167193054144405

theorem tailTrace_3004643 : CollatzResearch.WordTrace tailWord_3004643 prefixEnd_3004643 1542826054167193054144405 := by
  unfold tailWord_3004643
  simp only [CollatzResearch.WordTrace]
  refine ⟨109588333253699038015378583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73058888835799358676919055 109588333253699038015378583)
  ·
    refine ⟨164382499880548557023067875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109588333253699038015378583 164382499880548557023067875)
    ·
      refine ⟨246573749820822835534601813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164382499880548557023067875 246573749820822835534601813)
      ·
        refine ⟨2889536130712767603921115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 246573749820822835534601813 2889536130712767603921115)
        ·
          refine ⟨4334304196069151405881673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2889536130712767603921115 4334304196069151405881673)
          ·
            refine ⟨3250728147051863554411255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4334304196069151405881673 3250728147051863554411255)
            ·
              refine ⟨4876092220577795331616883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3250728147051863554411255 4876092220577795331616883)
              ·
                refine ⟨7314138330866692997425325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4876092220577795331616883 7314138330866692997425325)
                ·
                  refine ⟨2742801874075009874034497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7314138330866692997425325 2742801874075009874034497)
                  ·
                    refine ⟨2057101405556257405525873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2742801874075009874034497 2057101405556257405525873)
                    ·
                      refine ⟨1542826054167193054144405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2057101405556257405525873 1542826054167193054144405)
                      ·
                        rfl

theorem cell23_3004643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_3004643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004643 prefixEnd_3004643 := by exact prefixLift 3004643
  have htrace : WordTrace (prefixWord ++ tailWord_3004643) baseStart_3004643 baseEnd_3004643 := by
    simpa [prefixWord, tailWord_3004643, baseEnd_3004643] using wordTrace_append hprefix tailTrace_3004643
  have hstable : (prefixWord ++ tailWord_3004643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004643).length < 2 ^ (prefixWord ++ tailWord_3004643).sum := by decide
  have hdescent : baseEnd_3004643 < baseStart_3004643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004652 : List Nat := [2, 2, 1, 1, 2, 3, 2, 2, 3, 3, 2]
def baseStart_3004652 : Nat := 118140960795 + 3004652 * 2 ^ 59
def prefixEnd_3004652 : Nat := 4983230072969 + 3 ^ 40 * 3004652 * 2
def baseEnd_3004652 : Nat := 1542830675493083518931863

theorem tailTrace_3004652 : CollatzResearch.WordTrace tailWord_3004652 prefixEnd_3004652 1542830675493083518931863 := by
  unfold tailWord_3004652
  simp only [CollatzResearch.WordTrace]
  refine ⟨54794330755333216276228105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73059107673777621701637473 54794330755333216276228105)
  ·
    refine ⟨41095748066499912207171079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54794330755333216276228105 41095748066499912207171079)
    ·
      refine ⟨61643622099749868310756619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41095748066499912207171079 61643622099749868310756619)
      ·
        refine ⟨92465433149624802466134929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61643622099749868310756619 92465433149624802466134929)
        ·
          refine ⟨69349074862218601849601197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92465433149624802466134929 69349074862218601849601197)
          ·
            refine ⟨26005903073331975693600449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69349074862218601849601197 26005903073331975693600449)
            ·
              refine ⟨19504427304998981770200337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26005903073331975693600449 19504427304998981770200337)
              ·
                refine ⟨14628320478749236327650253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19504427304998981770200337 14628320478749236327650253)
                ·
                  refine ⟨5485620179530963622868845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14628320478749236327650253 5485620179530963622868845)
                  ·
                    refine ⟨2057107567324111358575817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5485620179530963622868845 2057107567324111358575817)
                    ·
                      refine ⟨1542830675493083518931863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2057107567324111358575817 1542830675493083518931863)
                      ·
                        rfl

theorem cell23_3004652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 3, 2].length) (baseStart_3004652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004652 prefixEnd_3004652 := by exact prefixLift 3004652
  have htrace : WordTrace (prefixWord ++ tailWord_3004652) baseStart_3004652 baseEnd_3004652 := by
    simpa [prefixWord, tailWord_3004652, baseEnd_3004652] using wordTrace_append hprefix tailTrace_3004652
  have hstable : (prefixWord ++ tailWord_3004652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004652).length < 2 ^ (prefixWord ++ tailWord_3004652).sum := by decide
  have hdescent : baseEnd_3004652 < baseStart_3004652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004653 : List Nat := [1, 5, 1, 2, 4, 1, 2, 1, 2, 4]
def baseStart_3004653 : Nat := 118140960795 + 3004653 * 2 ^ 59
def prefixEnd_3004653 : Nat := 4983230072969 + 3 ^ 40 * 3004653 * 2
def baseEnd_3004653 : Nat := 514277062991246005006453

theorem tailTrace_3004653 : CollatzResearch.WordTrace tailWord_3004653 prefixEnd_3004653 514277062991246005006453 := by
  unfold tailWord_3004653
  simp only [CollatzResearch.WordTrace]
  refine ⟨109588697983662809723242613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73059131989108539815495075 109588697983662809723242613)
  ·
    refine ⟨10273940435968388411553995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109588697983662809723242613 10273940435968388411553995)
    ·
      refine ⟨15410910653952582617330993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10273940435968388411553995 15410910653952582617330993)
      ·
        refine ⟨11558182990464436962998245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15410910653952582617330993 11558182990464436962998245)
        ·
          refine ⟨2167159310712081930562171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11558182990464436962998245 2167159310712081930562171)
          ·
            refine ⟨3250738966068122895843257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2167159310712081930562171 3250738966068122895843257)
            ·
              refine ⟨2438054224551092171882443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3250738966068122895843257 2438054224551092171882443)
              ·
                refine ⟨3657081336826638257823665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2438054224551092171882443 3657081336826638257823665)
                ·
                  refine ⟨2742811002619978693367749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3657081336826638257823665 2742811002619978693367749)
                  ·
                    refine ⟨514277062991246005006453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2742811002619978693367749 514277062991246005006453)
                    ·
                      rfl

theorem cell23_3004653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_3004653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004653 prefixEnd_3004653 := by exact prefixLift 3004653
  have htrace : WordTrace (prefixWord ++ tailWord_3004653) baseStart_3004653 baseEnd_3004653 := by
    simpa [prefixWord, tailWord_3004653, baseEnd_3004653] using wordTrace_append hprefix tailTrace_3004653
  have hstable : (prefixWord ++ tailWord_3004653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004653).length < 2 ^ (prefixWord ++ tailWord_3004653).sum := by decide
  have hdescent : baseEnd_3004653 < baseStart_3004653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004682 : List Nat := [3, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2]
def baseStart_3004682 : Nat := 118140960795 + 3004682 * 2 ^ 59
def prefixEnd_3004682 : Nat := 4983230072969 + 3 ^ 40 * 3004682 * 2
def baseEnd_3004682 : Nat := 1542846079912718401556725

theorem tailTrace_3004682 : CollatzResearch.WordTrace tailWord_3004682 prefixEnd_3004682 1542846079912718401556725 := by
  unfold tailWord_3004682
  simp only [CollatzResearch.WordTrace]
  refine ⟨27397438925139436919012075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73059837133705165117365533 27397438925139436919012075)
  ·
    refine ⟨41096158387709155378518113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27397438925139436919012075 41096158387709155378518113)
    ·
      refine ⟨30822118790781866533888585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41096158387709155378518113 30822118790781866533888585)
      ·
        refine ⟨23116589093086399900416439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30822118790781866533888585 23116589093086399900416439)
        ·
          refine ⟨34674883639629599850624659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23116589093086399900416439 34674883639629599850624659)
          ·
            refine ⟨52012325459444399775936989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34674883639629599850624659 52012325459444399775936989)
            ·
              refine ⟨19504622047291649915976371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52012325459444399775936989 19504622047291649915976371)
              ·
                refine ⟨29256933070937474873964557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19504622047291649915976371 29256933070937474873964557)
                ·
                  refine ⟨10971349901601553077736709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29256933070937474873964557 10971349901601553077736709)
                  ·
                    refine ⟨2057128106550291202075633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10971349901601553077736709 2057128106550291202075633)
                    ·
                      refine ⟨1542846079912718401556725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2057128106550291202075633 1542846079912718401556725)
                      ·
                        rfl

theorem cell23_3004682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_3004682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004682 prefixEnd_3004682 := by exact prefixLift 3004682
  have htrace : WordTrace (prefixWord ++ tailWord_3004682) baseStart_3004682 baseEnd_3004682 := by
    simpa [prefixWord, tailWord_3004682, baseEnd_3004682] using wordTrace_append hprefix tailTrace_3004682
  have hstable : (prefixWord ++ tailWord_3004682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004682).length < 2 ^ (prefixWord ++ tailWord_3004682).sum := by decide
  have hdescent : baseEnd_3004682 < baseStart_3004682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004686 : List Nat := [4, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2]
def baseStart_3004686 : Nat := 118140960795 + 3004686 * 2 ^ 59
def prefixEnd_3004686 : Nat := 4983230072969 + 3 ^ 40 * 3004686 * 2
def baseEnd_3004686 : Nat := 1542848133835336385906707

theorem tailTrace_3004686 : CollatzResearch.WordTrace tailWord_3004686 prefixEnd_3004686 1542848133835336385906707 := by
  unfold tailWord_3004686
  simp only [CollatzResearch.WordTrace]
  refine ⟨13698737699067907044899239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73059934395028837572795941 13698737699067907044899239)
  ·
    refine ⟨20548106548601860567348859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13698737699067907044899239 20548106548601860567348859)
    ·
      refine ⟨30822159822902790851023289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20548106548601860567348859 30822159822902790851023289)
      ·
        refine ⟨23116619867177093138267467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30822159822902790851023289 23116619867177093138267467)
        ·
          refine ⟨34674929800765639707401201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23116619867177093138267467 34674929800765639707401201)
          ·
            refine ⟨26006197350574229780550901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34674929800765639707401201 26006197350574229780550901)
            ·
              refine ⟨2438081001616334041926647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26006197350574229780550901 2438081001616334041926647)
              ·
                refine ⟨3657121502424501062889971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2438081001616334041926647 3657121502424501062889971)
                ·
                  refine ⟨5485682253636751594334957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3657121502424501062889971 5485682253636751594334957)
                  ·
                    refine ⟨2057130845113781847875609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5485682253636751594334957 2057130845113781847875609)
                    ·
                      refine ⟨1542848133835336385906707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2057130845113781847875609 1542848133835336385906707)
                      ·
                        rfl

theorem cell23_3004686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_3004686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004686 prefixEnd_3004686 := by exact prefixLift 3004686
  have htrace : WordTrace (prefixWord ++ tailWord_3004686) baseStart_3004686 baseEnd_3004686 := by
    simpa [prefixWord, tailWord_3004686, baseEnd_3004686] using wordTrace_append hprefix tailTrace_3004686
  have hstable : (prefixWord ++ tailWord_3004686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004686).length < 2 ^ (prefixWord ++ tailWord_3004686).sum := by decide
  have hdescent : baseEnd_3004686 < baseStart_3004686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004699 : List Nat := [1, 1, 1, 1, 1, 1, 7, 4, 2, 2, 2]
def baseStart_3004699 : Nat := 118140960795 + 3004699 * 2 ^ 59
def prefixEnd_3004699 : Nat := 4983230072969 + 3 ^ 40 * 3004699 * 2
def baseEnd_3004699 : Nat := 1542854809083844835044147

theorem tailTrace_3004699 : CollatzResearch.WordTrace tailWord_3004699 prefixEnd_3004699 1542854809083844835044147 := by
  unfold tailWord_3004699
  simp only [CollatzResearch.WordTrace]
  refine ⟨109590375741496159579417151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73060250494330773052944767 109590375741496159579417151)
  ·
    refine ⟨164385563612244239369125727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109590375741496159579417151 164385563612244239369125727)
    ·
      refine ⟨246578345418366359053688591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164385563612244239369125727 246578345418366359053688591)
      ·
        refine ⟨369867518127549538580532887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246578345418366359053688591 369867518127549538580532887)
        ·
          refine ⟨554801277191324307870799331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369867518127549538580532887 554801277191324307870799331)
          ·
            refine ⟨832201915786986461806198997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554801277191324307870799331 832201915786986461806198997)
            ·
              refine ⟨19504732401257495198582789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 832201915786986461806198997 19504732401257495198582789)
              ·
                refine ⟨3657137325235780349734273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19504732401257495198582789 3657137325235780349734273)
                ·
                  refine ⟨2742852993926835262300705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3657137325235780349734273 2742852993926835262300705)
                  ·
                    refine ⟨2057139745445126446725529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2742852993926835262300705 2057139745445126446725529)
                    ·
                      refine ⟨1542854809083844835044147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2057139745445126446725529 1542854809083844835044147)
                      ·
                        rfl

theorem cell23_3004699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 2, 2, 2].length) (baseStart_3004699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004699 prefixEnd_3004699 := by exact prefixLift 3004699
  have htrace : WordTrace (prefixWord ++ tailWord_3004699) baseStart_3004699 baseEnd_3004699 := by
    simpa [prefixWord, tailWord_3004699, baseEnd_3004699] using wordTrace_append hprefix tailTrace_3004699
  have hstable : (prefixWord ++ tailWord_3004699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004699).length < 2 ^ (prefixWord ++ tailWord_3004699).sum := by decide
  have hdescent : baseEnd_3004699 < baseStart_3004699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004722 : List Nat := [3, 2, 1, 1, 5, 1, 1, 2, 7]
def baseStart_3004722 : Nat := 118140960795 + 3004722 * 2 ^ 59
def prefixEnd_3004722 : Nat := 4983230072969 + 3 ^ 40 * 3004722 * 2
def baseEnd_3004722 : Nat := 171429624348766471672949

theorem tailTrace_3004722 : CollatzResearch.WordTrace tailWord_3004722 prefixEnd_3004722 171429624348766471672949 := by
  unfold tailWord_3004722
  simp only [CollatzResearch.WordTrace]
  refine ⟨27397803655103208626876105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73060809746941889671669613 27397803655103208626876105)
  ·
    refine ⟨20548352741327406470157079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27397803655103208626876105 20548352741327406470157079)
    ·
      refine ⟨30822529111991109705235619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20548352741327406470157079 30822529111991109705235619)
      ·
        refine ⟨46233793667986664557853429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30822529111991109705235619 46233793667986664557853429)
        ·
          refine ⟨4334418156373749802298759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46233793667986664557853429 4334418156373749802298759)
          ·
            refine ⟨6501627234560624703448139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4334418156373749802298759 6501627234560624703448139)
            ·
              refine ⟨9752440851840937055172209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6501627234560624703448139 9752440851840937055172209)
              ·
                refine ⟨7314330638880702791379157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9752440851840937055172209 7314330638880702791379157)
                ·
                  refine ⟨171429624348766471672949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7314330638880702791379157 171429624348766471672949)
                  ·
                    rfl

theorem cell23_3004722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 7].length) (baseStart_3004722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004722 prefixEnd_3004722 := by exact prefixLift 3004722
  have htrace : WordTrace (prefixWord ++ tailWord_3004722) baseStart_3004722 baseEnd_3004722 := by
    simpa [prefixWord, tailWord_3004722, baseEnd_3004722] using wordTrace_append hprefix tailTrace_3004722
  have hstable : (prefixWord ++ tailWord_3004722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004722).length < 2 ^ (prefixWord ++ tailWord_3004722).sum := by decide
  have hdescent : baseEnd_3004722 < baseStart_3004722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004735 : List Nat := [1, 1, 2, 2, 4, 1, 3, 1, 1, 7]
def baseStart_3004735 : Nat := 118140960795 + 3004735 * 2 ^ 59
def prefixEnd_3004735 : Nat := 4983230072969 + 3 ^ 40 * 3004735 * 2
def baseEnd_3004735 : Nat := 514291098129135564731327

theorem tailTrace_3004735 : CollatzResearch.WordTrace tailWord_3004735 prefixEnd_3004735 514291098129135564731327 := by
  unfold tailWord_3004735
  simp only [CollatzResearch.WordTrace]
  refine ⟨109591688769365737727727659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73061125846243825151818439 109591688769365737727727659)
  ·
    refine ⟨164387533154048606591591489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109591688769365737727727659 164387533154048606591591489)
    ·
      refine ⟨123290649865536454943693617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164387533154048606591591489 123290649865536454943693617)
      ·
        refine ⟨92467987399152341207770213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123290649865536454943693617 92467987399152341207770213)
        ·
          refine ⟨17337747637341063976456915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92467987399152341207770213 17337747637341063976456915)
          ·
            refine ⟨26006621456011595964685373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17337747637341063976456915 26006621456011595964685373)
            ·
              refine ⟨9752483046004348486757015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26006621456011595964685373 9752483046004348486757015)
              ·
                refine ⟨14628724569006522730135523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9752483046004348486757015 14628724569006522730135523)
                ·
                  refine ⟨21943086853509784095203285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14628724569006522730135523 21943086853509784095203285)
                  ·
                    refine ⟨514291098129135564731327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21943086853509784095203285 514291098129135564731327)
                    ·
                      rfl

theorem cell23_3004735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 7].length) (baseStart_3004735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004735 prefixEnd_3004735 := by exact prefixLift 3004735
  have htrace : WordTrace (prefixWord ++ tailWord_3004735) baseStart_3004735 baseEnd_3004735 := by
    simpa [prefixWord, tailWord_3004735, baseEnd_3004735] using wordTrace_append hprefix tailTrace_3004735
  have hstable : (prefixWord ++ tailWord_3004735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004735).length < 2 ^ (prefixWord ++ tailWord_3004735).sum := by decide
  have hdescent : baseEnd_3004735 < baseStart_3004735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004785 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 1, 6, 4]
def baseStart_3004785 : Nat := 118140960795 + 3004785 * 2 ^ 59
def prefixEnd_3004785 : Nat := 4983230072969 + 3 ^ 40 * 3004785 * 2
def baseEnd_3004785 : Nat := 1542898968420131498568751

theorem tailTrace_3004785 : CollatzResearch.WordTrace tailWord_3004785 prefixEnd_3004785 1542898968420131498568751 := by
  unfold tailWord_3004785
  simp only [CollatzResearch.WordTrace]
  refine ⟨109593512419184596267047809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73062341612789730844698539 109593512419184596267047809)
  ·
    refine ⟨82195134314388447200285857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109593512419184596267047809 82195134314388447200285857)
    ·
      refine ⟨61646350735791335400214393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82195134314388447200285857 61646350735791335400214393)
      ·
        refine ⟨46234763051843501550160795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61646350735791335400214393 46234763051843501550160795)
        ·
          refine ⟨69352144577765252325241193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46234763051843501550160795 69352144577765252325241193)
          ·
            refine ⟨52014108433323939243930895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69352144577765252325241193 52014108433323939243930895)
            ·
              refine ⟨78021162649985908865896343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52014108433323939243930895 78021162649985908865896343)
              ·
                refine ⟨117031743974978863298844515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78021162649985908865896343 117031743974978863298844515)
                ·
                  refine ⟨175547615962468294948266773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117031743974978863298844515 175547615962468294948266773)
                  ·
                    refine ⟨8228794498240701325700005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 175547615962468294948266773 8228794498240701325700005)
                    ·
                      refine ⟨1542898968420131498568751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8228794498240701325700005 1542898968420131498568751)
                      ·
                        rfl

theorem cell23_3004785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_3004785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004785 prefixEnd_3004785 := by exact prefixLift 3004785
  have htrace : WordTrace (prefixWord ++ tailWord_3004785) baseStart_3004785 baseEnd_3004785 := by
    simpa [prefixWord, tailWord_3004785, baseEnd_3004785] using wordTrace_append hprefix tailTrace_3004785
  have hstable : (prefixWord ++ tailWord_3004785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004785).length < 2 ^ (prefixWord ++ tailWord_3004785).sum := by decide
  have hdescent : baseEnd_3004785 < baseStart_3004785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004790 : List Nat := [5, 1, 1, 4, 2, 1, 1, 3, 5]
def baseStart_3004790 : Nat := 118140960795 + 3004790 * 2 ^ 59
def prefixEnd_3004790 : Nat := 4983230072969 + 3 ^ 40 * 3004790 * 2
def baseEnd_3004790 : Nat := 171433503980378219889581

theorem tailTrace_3004790 : CollatzResearch.WordTrace tailWord_3004790 prefixEnd_3004790 171433503980378219889581 := by
  unfold tailWord_3004790
  simp only [CollatzResearch.WordTrace]
  refine ⟨6849605924010405132561239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73062463189444321413986549 6849605924010405132561239)
  ·
    refine ⟨10274408886015607698841859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6849605924010405132561239 10274408886015607698841859)
    ·
      refine ⟨15411613329023411548262789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10274408886015607698841859 15411613329023411548262789)
      ·
        refine ⟨2889677499191889665299273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15411613329023411548262789 2889677499191889665299273)
        ·
          refine ⟨2167258124393917248974455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2889677499191889665299273 2167258124393917248974455)
          ·
            refine ⟨3250887186590875873461683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2167258124393917248974455 3250887186590875873461683)
            ·
              refine ⟨4876330779886313810192525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3250887186590875873461683 4876330779886313810192525)
              ·
                refine ⟨1828624042457367678822197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4876330779886313810192525 1828624042457367678822197)
                ·
                  refine ⟨171433503980378219889581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1828624042457367678822197 171433503980378219889581)
                  ·
                    rfl

theorem cell23_3004790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_3004790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004790 prefixEnd_3004790 := by exact prefixLift 3004790
  have htrace : WordTrace (prefixWord ++ tailWord_3004790) baseStart_3004790 baseEnd_3004790 := by
    simpa [prefixWord, tailWord_3004790, baseEnd_3004790] using wordTrace_append hprefix tailTrace_3004790
  have hstable : (prefixWord ++ tailWord_3004790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004790).length < 2 ^ (prefixWord ++ tailWord_3004790).sum := by decide
  have hdescent : baseEnd_3004790 < baseStart_3004790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004795 : List Nat := [1, 1, 1, 1, 1, 7, 1, 2, 8]
def baseStart_3004795 : Nat := 118140960795 + 3004795 * 2 ^ 59
def prefixEnd_3004795 : Nat := 4983230072969 + 3 ^ 40 * 3004795 * 2
def baseEnd_3004795 : Nat := 171433789247408495493745

theorem tailTrace_3004795 : CollatzResearch.WordTrace tailWord_3004795 prefixEnd_3004795 171433789247408495493745 := by
  unfold tailWord_3004795
  simp only [CollatzResearch.WordTrace]
  refine ⟨109593877149148367974911839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73062584766098911983274559 109593877149148367974911839)
  ·
    refine ⟨164390815723722551962367759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109593877149148367974911839 164390815723722551962367759)
    ·
      refine ⟨246586223585583827943551639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164390815723722551962367759 246586223585583827943551639)
      ·
        refine ⟨369879335378375741915327459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246586223585583827943551639 369879335378375741915327459)
        ·
          refine ⟨554819003067563612872991189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369879335378375741915327459 554819003067563612872991189)
          ·
            refine ⟨13003570384396022176710731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 554819003067563612872991189 13003570384396022176710731)
            ·
              refine ⟨19505355576594033265066097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13003570384396022176710731 19505355576594033265066097)
              ·
                refine ⟨14629016682445524948799573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19505355576594033265066097 14629016682445524948799573)
                ·
                  refine ⟨171433789247408495493745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14629016682445524948799573 171433789247408495493745)
                  ·
                    rfl

theorem cell23_3004795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 8].length) (baseStart_3004795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004795 prefixEnd_3004795 := by exact prefixLift 3004795
  have htrace : WordTrace (prefixWord ++ tailWord_3004795) baseStart_3004795 baseEnd_3004795 := by
    simpa [prefixWord, tailWord_3004795, baseEnd_3004795] using wordTrace_append hprefix tailTrace_3004795
  have hstable : (prefixWord ++ tailWord_3004795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004795).length < 2 ^ (prefixWord ++ tailWord_3004795).sum := by decide
  have hdescent : baseEnd_3004795 < baseStart_3004795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004809 : List Nat := [1, 2, 1, 1, 6, 2, 1, 2, 2, 2, 3]
def baseStart_3004809 : Nat := 118140960795 + 3004809 * 2 ^ 59
def prefixEnd_3004809 : Nat := 4983230072969 + 3 ^ 40 * 3004809 * 2
def baseEnd_3004809 : Nat := 1542911291955839404668641

theorem tailTrace_3004809 : CollatzResearch.WordTrace tailWord_3004809 prefixEnd_3004809 1542911291955839404668641 := by
  unfold tailWord_3004809
  simp only [CollatzResearch.WordTrace]
  refine ⟨109594387771097648365921481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73062925180731765577280987 109594387771097648365921481)
  ·
    refine ⟨82195790828323236274441111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109594387771097648365921481 82195790828323236274441111)
    ·
      refine ⟨123293686242484854411661667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82195790828323236274441111 123293686242484854411661667)
      ·
        refine ⟨184940529363727281617492501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123293686242484854411661667 184940529363727281617492501)
        ·
          refine ⟨8669087313924716325819961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 184940529363727281617492501 8669087313924716325819961)
          ·
            refine ⟨6501815485443537244364971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8669087313924716325819961 6501815485443537244364971)
            ·
              refine ⟨9752723228165305866547457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6501815485443537244364971 9752723228165305866547457)
              ·
                refine ⟨7314542421123979399910593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9752723228165305866547457 7314542421123979399910593)
                ·
                  refine ⟨5485906815842984549932945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7314542421123979399910593 5485906815842984549932945)
                  ·
                    refine ⟨4114430111882238412449709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5485906815842984549932945 4114430111882238412449709)
                    ·
                      refine ⟨1542911291955839404668641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4114430111882238412449709 1542911291955839404668641)
                      ·
                        rfl

theorem cell23_3004809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 2, 3].length) (baseStart_3004809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004809 prefixEnd_3004809 := by exact prefixLift 3004809
  have htrace : WordTrace (prefixWord ++ tailWord_3004809) baseStart_3004809 baseEnd_3004809 := by
    simpa [prefixWord, tailWord_3004809, baseEnd_3004809] using wordTrace_append hprefix tailTrace_3004809
  have hstable : (prefixWord ++ tailWord_3004809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004809).length < 2 ^ (prefixWord ++ tailWord_3004809).sum := by decide
  have hdescent : baseEnd_3004809 < baseStart_3004809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004829 : List Nat := [1, 4, 2, 1, 4, 1, 1, 3, 6]
def baseStart_3004829 : Nat := 118140960795 + 3004829 * 2 ^ 59
def prefixEnd_3004829 : Nat := 4983230072969 + 3 ^ 40 * 3004829 * 2
def baseEnd_3004829 : Nat := 171435729063214369602061

theorem tailTrace_3004829 : CollatzResearch.WordTrace tailWord_3004829 prefixEnd_3004829 171435729063214369602061 := by
  unfold tailWord_3004829
  simp only [CollatzResearch.WordTrace]
  refine ⟨109595117231025191781649541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73063411487350127854433027 109595117231025191781649541)
  ·
    refine ⟨20549084480817223459059289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109595117231025191781649541 20549084480817223459059289)
    ·
      refine ⟨15411813360612917594294467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20549084480817223459059289 15411813360612917594294467)
      ·
        refine ⟨23117720040919376391441701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15411813360612917594294467 23117720040919376391441701)
        ·
          refine ⟨4334572507672383073395319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23117720040919376391441701 4334572507672383073395319)
          ·
            refine ⟨6501858761508574610092979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4334572507672383073395319 6501858761508574610092979)
            ·
              refine ⟨9752788142262861915139469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6501858761508574610092979 9752788142262861915139469)
              ·
                refine ⟨3657295553348573218177301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9752788142262861915139469 3657295553348573218177301)
                ·
                  refine ⟨171435729063214369602061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3657295553348573218177301 171435729063214369602061)
                  ·
                    rfl

theorem cell23_3004829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 6].length) (baseStart_3004829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004829 prefixEnd_3004829 := by exact prefixLift 3004829
  have htrace : WordTrace (prefixWord ++ tailWord_3004829) baseStart_3004829 baseEnd_3004829 := by
    simpa [prefixWord, tailWord_3004829, baseEnd_3004829] using wordTrace_append hprefix tailTrace_3004829
  have hstable : (prefixWord ++ tailWord_3004829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004829).length < 2 ^ (prefixWord ++ tailWord_3004829).sum := by decide
  have hdescent : baseEnd_3004829 < baseStart_3004829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004856 : List Nat := [2, 1, 2, 1, 2, 2, 1, 7, 1, 1, 3]
def baseStart_3004856 : Nat := 118140960795 + 3004856 * 2 ^ 59
def prefixEnd_3004856 : Nat := 4983230072969 + 3 ^ 40 * 3004856 * 2
def baseEnd_3004856 : Nat := 1542935425546600720780925

theorem tailTrace_3004856 : CollatzResearch.WordTrace tailWord_3004856 prefixEnd_3004856 1542935425546600720780925 := by
  unfold tailWord_3004856
  simp only [CollatzResearch.WordTrace]
  refine ⟨54798051000963687696441211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73064068001284916928588281 54798051000963687696441211)
  ·
    refine ⟨82197076501445531544661817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54798051000963687696441211 82197076501445531544661817)
    ·
      refine ⟨61647807376084148658496363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82197076501445531544661817 61647807376084148658496363)
      ·
        refine ⟨92471711064126222987744545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61647807376084148658496363 92471711064126222987744545)
        ·
          refine ⟨69353783298094667240808409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92471711064126222987744545 69353783298094667240808409)
          ·
            refine ⟨52015337473571000430606307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69353783298094667240808409 52015337473571000430606307)
            ·
              refine ⟨78023006210356500645909461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52015337473571000430606307 78023006210356500645909461)
              ·
                refine ⟨1828664208055230483888503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 78023006210356500645909461 1828664208055230483888503)
                ·
                  refine ⟨2742996312082845725832755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1828664208055230483888503 2742996312082845725832755)
                  ·
                    refine ⟨4114494468124268588749133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2742996312082845725832755 4114494468124268588749133)
                    ·
                      refine ⟨1542935425546600720780925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4114494468124268588749133 1542935425546600720780925)
                      ·
                        rfl

theorem cell23_3004856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 7, 1, 1, 3].length) (baseStart_3004856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004856 prefixEnd_3004856 := by exact prefixLift 3004856
  have htrace : WordTrace (prefixWord ++ tailWord_3004856) baseStart_3004856 baseEnd_3004856 := by
    simpa [prefixWord, tailWord_3004856, baseEnd_3004856] using wordTrace_append hprefix tailTrace_3004856
  have hstable : (prefixWord ++ tailWord_3004856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004856).length < 2 ^ (prefixWord ++ tailWord_3004856).sum := by decide
  have hdescent : baseEnd_3004856 < baseStart_3004856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004873 : List Nat := [1, 2, 1, 1, 2, 1, 8, 2, 1, 1, 3]
def baseStart_3004873 : Nat := 118140960795 + 3004873 * 2 ^ 59
def prefixEnd_3004873 : Nat := 4983230072969 + 3 ^ 40 * 3004873 * 2
def baseEnd_3004873 : Nat := 1542944154717727154268347

theorem tailTrace_3004873 : CollatzResearch.WordTrace tailWord_3004873 prefixEnd_3004873 1542944154717727154268347 := by
  unfold tailWord_3004873
  simp only [CollatzResearch.WordTrace]
  refine ⟨109596722042865787296251273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73064481361910524864167515 109596722042865787296251273)
  ·
    refine ⟨82197541532149340472188455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109596722042865787296251273 82197541532149340472188455)
    ·
      refine ⟨123296312298224010708282683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82197541532149340472188455 123296312298224010708282683)
      ·
        refine ⟨184944468447336016062424025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123296312298224010708282683 184944468447336016062424025)
        ·
          refine ⟨138708351335502012046818019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184944468447336016062424025 138708351335502012046818019)
          ·
            refine ⟨208062527003253018070227029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138708351335502012046818019 208062527003253018070227029)
            ·
              refine ⟨2438232738319371305510473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 208062527003253018070227029 2438232738319371305510473)
              ·
                refine ⟨1828674553739528479132855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2438232738319371305510473 1828674553739528479132855)
                ·
                  refine ⟨2743011830609292718699283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1828674553739528479132855 2743011830609292718699283)
                  ·
                    refine ⟨4114517745913939078048925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2743011830609292718699283 4114517745913939078048925)
                    ·
                      refine ⟨1542944154717727154268347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4114517745913939078048925 1542944154717727154268347)
                      ·
                        rfl

theorem cell23_3004873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 2, 1, 1, 3].length) (baseStart_3004873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3004873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3004873 prefixEnd_3004873 := by exact prefixLift 3004873
  have htrace : WordTrace (prefixWord ++ tailWord_3004873) baseStart_3004873 baseEnd_3004873 := by
    simpa [prefixWord, tailWord_3004873, baseEnd_3004873] using wordTrace_append hprefix tailTrace_3004873
  have hstable : (prefixWord ++ tailWord_3004873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004873).length < 2 ^ (prefixWord ++ tailWord_3004873).sum := by decide
  have hdescent : baseEnd_3004873 < baseStart_3004873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
