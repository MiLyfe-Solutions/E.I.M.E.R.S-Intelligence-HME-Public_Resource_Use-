import V185TrunkScan22Chunk108

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_977189 : List Nat := [1, 3, 1, 2, 5, 1, 1, 1, 1, 6]
def baseStart_977189 : Nat := 118140960795 + 977189 * 2 ^ 59
def prefixEnd_977189 : Nat := 4983230072969 + 3 ^ 40 * 977189 * 2
def baseEnd_977189 : Nat := 334511764857654984828997

theorem tailTrace_977189 : CollatzResearch.WordTrace tailWord_977189 prefixEnd_977189 334511764857654984828997 := by
  unfold tailWord_977189
  simp only [CollatzResearch.WordTrace]
  refine ⟨35641010856818618439470621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23760673904545745626313747 35641010856818618439470621)
  ·
    refine ⟨13365379071306981914801483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35641010856818618439470621 13365379071306981914801483)
    ·
      refine ⟨20048068606960472872202225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13365379071306981914801483 20048068606960472872202225)
      ·
        refine ⟨15036051455220354654151669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20048068606960472872202225 15036051455220354654151669)
        ·
          refine ⟨1409629823926908248826719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15036051455220354654151669 1409629823926908248826719)
          ·
            refine ⟨2114444735890362373240079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1409629823926908248826719 2114444735890362373240079)
            ·
              refine ⟨3171667103835543559860119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2114444735890362373240079 3171667103835543559860119)
              ·
                refine ⟨4757500655753315339790179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3171667103835543559860119 4757500655753315339790179)
                ·
                  refine ⟨7136250983629973009685269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4757500655753315339790179 7136250983629973009685269)
                  ·
                    refine ⟨334511764857654984828997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7136250983629973009685269 334511764857654984828997)
                    ·
                      rfl

theorem cell22_977189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 6].length) (baseStart_977189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_977189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_977189 prefixEnd_977189 := by exact prefixLift 977189
  have htrace : WordTrace (prefixWord ++ tailWord_977189) baseStart_977189 baseEnd_977189 := by
    simpa [prefixWord, tailWord_977189, baseEnd_977189] using wordTrace_append hprefix tailTrace_977189
  have hstable : (prefixWord ++ tailWord_977189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977189).length < 2 ^ (prefixWord ++ tailWord_977189).sum := by decide
  have hdescent : baseEnd_977189 < baseStart_977189 := by decide
  rcases family_descends (prefixWord ++ tailWord_977189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977204 : List Nat := [2, 5, 1, 1, 1, 3, 9]
def baseStart_977204 : Nat := 118140960795 + 977204 * 2 ^ 59
def prefixEnd_977204 : Nat := 4983230072969 + 3 ^ 40 * 977204 * 2
def baseEnd_977204 : Nat := 12389514802377775766813

theorem tailTrace_977204 : CollatzResearch.WordTrace tailWord_977204 prefixEnd_977204 12389514802377775766813 := by
  unfold tailWord_977204
  simp only [CollatzResearch.WordTrace]
  refine ⟨17820778975882138000633333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23761038634509517334177777 17820778975882138000633333)
  ·
    refine ⟨1670698028988950437559375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17820778975882138000633333 1670698028988950437559375)
    ·
      refine ⟨2506047043483425656339063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1670698028988950437559375 2506047043483425656339063)
      ·
        refine ⟨3759070565225138484508595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2506047043483425656339063 3759070565225138484508595)
        ·
          refine ⟨5638605847837707726762893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3759070565225138484508595 5638605847837707726762893)
          ·
            refine ⟨2114477192939140397536085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5638605847837707726762893 2114477192939140397536085)
            ·
              refine ⟨12389514802377775766813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2114477192939140397536085 12389514802377775766813)
              ·
                rfl

theorem cell22_977204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 9].length) (baseStart_977204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_977204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_977204 prefixEnd_977204 := by exact prefixLift 977204
  have htrace : WordTrace (prefixWord ++ tailWord_977204) baseStart_977204 baseEnd_977204 := by
    simpa [prefixWord, tailWord_977204, baseEnd_977204] using wordTrace_append hprefix tailTrace_977204
  have hstable : (prefixWord ++ tailWord_977204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977204).length < 2 ^ (prefixWord ++ tailWord_977204).sum := by decide
  have hdescent : baseEnd_977204 < baseStart_977204 := by decide
  rcases family_descends (prefixWord ++ tailWord_977204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977219 : List Nat := [1, 1, 1, 3, 1, 3, 3, 3, 3, 3]
def baseStart_977219 : Nat := 118140960795 + 977219 * 2 ^ 59
def prefixEnd_977219 : Nat := 4983230072969 + 3 ^ 40 * 977219 * 2
def baseEnd_977219 : Nat := 334522034470744906578905

theorem tailTrace_977219 : CollatzResearch.WordTrace tailWord_977219 prefixEnd_977219 334522034470744906578905 := by
  unfold tailWord_977219
  simp only [CollatzResearch.WordTrace]
  refine ⟨35642105046709933563062711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23761403364473289042041807 35642105046709933563062711)
  ·
    refine ⟨53463157570064900344594067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35642105046709933563062711 53463157570064900344594067)
    ·
      refine ⟨80194736355097350516891101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53463157570064900344594067 80194736355097350516891101)
      ·
        refine ⟨30073026133161506443834163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80194736355097350516891101 30073026133161506443834163)
        ·
          refine ⟨45109539199742259665751245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30073026133161506443834163 45109539199742259665751245)
          ·
            refine ⟨16916077199903347374656717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45109539199742259665751245 16916077199903347374656717)
            ·
              refine ⟨6343528949963755265496269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16916077199903347374656717 6343528949963755265496269)
              ·
                refine ⟨2378823356236408224561101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6343528949963755265496269 2378823356236408224561101)
                ·
                  refine ⟨892058758588653084210413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2378823356236408224561101 892058758588653084210413)
                  ·
                    refine ⟨334522034470744906578905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 892058758588653084210413 334522034470744906578905)
                    ·
                      rfl

theorem cell22_977219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 3, 3].length) (baseStart_977219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_977219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_977219 prefixEnd_977219 := by exact prefixLift 977219
  have htrace : WordTrace (prefixWord ++ tailWord_977219) baseStart_977219 baseEnd_977219 := by
    simpa [prefixWord, tailWord_977219, baseEnd_977219] using wordTrace_append hprefix tailTrace_977219
  have hstable : (prefixWord ++ tailWord_977219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977219).length < 2 ^ (prefixWord ++ tailWord_977219).sum := by decide
  have hdescent : baseEnd_977219 < baseStart_977219 := by decide
  rcases family_descends (prefixWord ++ tailWord_977219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977236 : List Nat := [2, 4, 1, 1, 2, 2, 2, 2, 3, 3]
def baseStart_977236 : Nat := 118140960795 + 977236 * 2 ^ 59
def prefixEnd_977236 : Nat := 4983230072969 + 3 ^ 40 * 977236 * 2
def baseEnd_977236 : Nat := 334527853918162528903853

theorem tailTrace_977236 : CollatzResearch.WordTrace tailWord_977236 prefixEnd_977236 334527853918162528903853 := by
  unfold tailWord_977236
  simp only [CollatzResearch.WordTrace]
  refine ⟨17821362543824172733215781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23761816725098896977621041 17821362543824172733215781)
  ·
    refine ⟨3341505476967032387477959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17821362543824172733215781 3341505476967032387477959)
    ·
      refine ⟨5012258215450548581216939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3341505476967032387477959 5012258215450548581216939)
      ·
        refine ⟨7518387323175822871825409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5012258215450548581216939 7518387323175822871825409)
        ·
          refine ⟨5638790492381867153869057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7518387323175822871825409 5638790492381867153869057)
          ·
            refine ⟨4229092869286400365401793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5638790492381867153869057 4229092869286400365401793)
            ·
              refine ⟨3171819651964800274051345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4229092869286400365401793 3171819651964800274051345)
              ·
                refine ⟨2378864738973600205538509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3171819651964800274051345 2378864738973600205538509)
                ·
                  refine ⟨892074277115100077076941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2378864738973600205538509 892074277115100077076941)
                  ·
                    refine ⟨334527853918162528903853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 892074277115100077076941 334527853918162528903853)
                    ·
                      rfl

theorem cell22_977236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_977236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_977236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_977236 prefixEnd_977236 := by exact prefixLift 977236
  have htrace : WordTrace (prefixWord ++ tailWord_977236) baseStart_977236 baseEnd_977236 := by
    simpa [prefixWord, tailWord_977236, baseEnd_977236] using wordTrace_append hprefix tailTrace_977236
  have hstable : (prefixWord ++ tailWord_977236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977236).length < 2 ^ (prefixWord ++ tailWord_977236).sum := by decide
  have hdescent : baseEnd_977236 < baseStart_977236 := by decide
  rcases family_descends (prefixWord ++ tailWord_977236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977247 : List Nat := [1, 1, 2, 3, 1, 2, 2, 2, 1, 7]
def baseStart_977247 : Nat := 118140960795 + 977247 * 2 ^ 59
def prefixEnd_977247 : Nat := 4983230072969 + 3 ^ 40 * 977247 * 2
def baseEnd_977247 : Nat := 334531619442962166878819

theorem tailTrace_977247 : CollatzResearch.WordTrace tailWord_977247 prefixEnd_977247 334531619442962166878819 := by
  unfold tailWord_977247
  simp only [CollatzResearch.WordTrace]
  refine ⟨35643126290608494345081995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23762084193738996230054663 35643126290608494345081995)
  ·
    refine ⟨53464689435912741517622993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35643126290608494345081995 53464689435912741517622993)
    ·
      refine ⟨40098517076934556138217245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53464689435912741517622993 40098517076934556138217245)
      ·
        refine ⟨15036943903850458551831467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40098517076934556138217245 15036943903850458551831467)
        ·
          refine ⟨22555415855775687827747201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15036943903850458551831467 22555415855775687827747201)
          ·
            refine ⟨16916561891831765870810401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22555415855775687827747201 16916561891831765870810401)
            ·
              refine ⟨12687421418873824403107801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16916561891831765870810401 12687421418873824403107801)
              ·
                refine ⟨9515566064155368302330851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12687421418873824403107801 9515566064155368302330851)
                ·
                  refine ⟨14273349096233052453496277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9515566064155368302330851 14273349096233052453496277)
                  ·
                    refine ⟨334531619442962166878819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14273349096233052453496277 334531619442962166878819)
                    ·
                      rfl

theorem cell22_977247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 7].length) (baseStart_977247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_977247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_977247 prefixEnd_977247 := by exact prefixLift 977247
  have htrace : WordTrace (prefixWord ++ tailWord_977247) baseStart_977247 baseEnd_977247 := by
    simpa [prefixWord, tailWord_977247, baseEnd_977247] using wordTrace_append hprefix tailTrace_977247
  have hstable : (prefixWord ++ tailWord_977247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977247).length < 2 ^ (prefixWord ++ tailWord_977247).sum := by decide
  have hdescent : baseEnd_977247 < baseStart_977247 := by decide
  rcases family_descends (prefixWord ++ tailWord_977247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977253 : List Nat := [1, 3, 1, 3, 1, 3, 3, 3, 1, 3]
def baseStart_977253 : Nat := 118140960795 + 977253 * 2 ^ 59
def prefixEnd_977253 : Nat := 4983230072969 + 3 ^ 40 * 977253 * 2
def baseEnd_977253 : Nat := 334533673365580151228801

theorem tailTrace_977253 : CollatzResearch.WordTrace tailWord_977253 prefixEnd_977253 334533673365580151228801 := by
  unfold tailWord_977253
  simp only [CollatzResearch.WordTrace]
  refine ⟨35643345128586757369800413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23762230085724504913200275 35643345128586757369800413)
  ·
    refine ⟨13366254423220034013675155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35643345128586757369800413 13366254423220034013675155)
    ·
      refine ⟨20049381634830051020512733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13366254423220034013675155 20049381634830051020512733)
      ·
        refine ⟨7518518113061269132692275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20049381634830051020512733 7518518113061269132692275)
        ·
          refine ⟨11277777169591903699038413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7518518113061269132692275 11277777169591903699038413)
          ·
            refine ⟨4229166438596963887139405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11277777169591903699038413 4229166438596963887139405)
            ·
              refine ⟨1585937414473861457677277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4229166438596963887139405 1585937414473861457677277)
              ·
                refine ⟨594726530427698046628979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1585937414473861457677277 594726530427698046628979)
                ·
                  refine ⟨892089795641547069943469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 594726530427698046628979 892089795641547069943469)
                  ·
                    refine ⟨334533673365580151228801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 892089795641547069943469 334533673365580151228801)
                    ·
                      rfl

theorem cell22_977253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 3, 1, 3].length) (baseStart_977253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_977253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_977253 prefixEnd_977253 := by exact prefixLift 977253
  have htrace : WordTrace (prefixWord ++ tailWord_977253) baseStart_977253 baseEnd_977253 := by
    simpa [prefixWord, tailWord_977253, baseEnd_977253] using wordTrace_append hprefix tailTrace_977253
  have hstable : (prefixWord ++ tailWord_977253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977253).length < 2 ^ (prefixWord ++ tailWord_977253).sum := by decide
  have hdescent : baseEnd_977253 < baseStart_977253 := by decide
  rcases family_descends (prefixWord ++ tailWord_977253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977283 : List Nat := [1, 1, 1, 3, 6, 2, 2, 1, 5]
def baseStart_977283 : Nat := 118140960795 + 977283 * 2 ^ 59
def prefixEnd_977283 : Nat := 4983230072969 + 3 ^ 40 * 977283 * 2
def baseEnd_977283 : Nat := 111514647659556690992903

theorem tailTrace_977283 : CollatzResearch.WordTrace tailWord_977283 prefixEnd_977283 111514647659556690992903 := by
  unfold tailWord_977283
  simp only [CollatzResearch.WordTrace]
  refine ⟨35644439318478072493392503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23762959545652048328928335 35644439318478072493392503)
  ·
    refine ⟨53466658977717108740088755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35644439318478072493392503 53466658977717108740088755)
    ·
      refine ⟨80199988466575663110133133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53466658977717108740088755 80199988466575663110133133)
      ·
        refine ⟨30074995674965873666299925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80199988466575663110133133 30074995674965873666299925)
        ·
          refine ⟨1409765422264025328107809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30074995674965873666299925 1409765422264025328107809)
          ·
            refine ⟨1057324066698018996080857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1409765422264025328107809 1057324066698018996080857)
            ·
              refine ⟨792993050023514247060643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1057324066698018996080857 792993050023514247060643)
              ·
                refine ⟨1189489575035271370590965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 792993050023514247060643 1189489575035271370590965)
                ·
                  refine ⟨111514647659556690992903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1189489575035271370590965 111514647659556690992903)
                  ·
                    rfl

theorem cell22_977283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 5].length) (baseStart_977283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_977283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_977283 prefixEnd_977283 := by exact prefixLift 977283
  have htrace : WordTrace (prefixWord ++ tailWord_977283) baseStart_977283 baseEnd_977283 := by
    simpa [prefixWord, tailWord_977283, baseEnd_977283] using wordTrace_append hprefix tailTrace_977283
  have hstable : (prefixWord ++ tailWord_977283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977283).length < 2 ^ (prefixWord ++ tailWord_977283).sum := by decide
  have hdescent : baseEnd_977283 < baseStart_977283 := by decide
  rcases family_descends (prefixWord ++ tailWord_977283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977311 : List Nat := [1, 1, 2, 5, 1, 1, 2, 5, 4]
def baseStart_977311 : Nat := 118140960795 + 977311 * 2 ^ 59
def prefixEnd_977311 : Nat := 4983230072969 + 3 ^ 40 * 977311 * 2
def baseEnd_977311 : Nat := 111517842650295777759541

theorem tailTrace_977311 : CollatzResearch.WordTrace tailWord_977311 prefixEnd_977311 111517842650295777759541 := by
  unfold tailWord_977311
  simp only [CollatzResearch.WordTrace]
  refine ⟨35645460562376633275411787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23763640374917755516941191 35645460562376633275411787)
  ·
    refine ⟨53468190843564949913117681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35645460562376633275411787 53468190843564949913117681)
    ·
      refine ⟨40101143132673712434838261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53468190843564949913117681 40101143132673712434838261)
      ·
        refine ⟨3759482168688160540766087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40101143132673712434838261 3759482168688160540766087)
        ·
          refine ⟨5639223253032240811149131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3759482168688160540766087 5639223253032240811149131)
          ·
            refine ⟨8458834879548361216723697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5639223253032240811149131 8458834879548361216723697)
            ·
              refine ⟨6344126159661270912542773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8458834879548361216723697 6344126159661270912542773)
              ·
                refine ⟨594761827468244148050885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6344126159661270912542773 594761827468244148050885)
                ·
                  refine ⟨111517842650295777759541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 594761827468244148050885 111517842650295777759541)
                  ·
                    rfl

theorem cell22_977311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 5, 4].length) (baseStart_977311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_977311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_977311 prefixEnd_977311 := by exact prefixLift 977311
  have htrace : WordTrace (prefixWord ++ tailWord_977311) baseStart_977311 baseEnd_977311 := by
    simpa [prefixWord, tailWord_977311, baseEnd_977311] using wordTrace_append hprefix tailTrace_977311
  have hstable : (prefixWord ++ tailWord_977311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977311).length < 2 ^ (prefixWord ++ tailWord_977311).sum := by decide
  have hdescent : baseEnd_977311 < baseStart_977311 := by decide
  rcases family_descends (prefixWord ++ tailWord_977311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977345 : List Nat := [1, 2, 7, 1, 1, 1, 1, 2, 6]
def baseStart_977345 : Nat := 118140960795 + 977345 * 2 ^ 59
def prefixEnd_977345 : Nat := 4983230072969 + 3 ^ 40 * 977345 * 2
def baseEnd_977345 : Nat := 111521722281907525976173

theorem tailTrace_977345 : CollatzResearch.WordTrace tailWord_977345 prefixEnd_977345 111521722281907525976173 := by
  unfold tailWord_977345
  simp only [CollatzResearch.WordTrace]
  refine ⟨35646700644253457082149489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23764467096168971388099659 35646700644253457082149489)
  ·
    refine ⟨26735025483190092811612117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35646700644253457082149489 26735025483190092811612117)
    ·
      refine ⟨626602159762267800272159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 26735025483190092811612117 626602159762267800272159)
      ·
        refine ⟨939903239643401700408239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626602159762267800272159 939903239643401700408239)
        ·
          refine ⟨1409854859465102550612359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 939903239643401700408239 1409854859465102550612359)
          ·
            refine ⟨2114782289197653825918539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1409854859465102550612359 2114782289197653825918539)
            ·
              refine ⟨3172173433796480738877809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2114782289197653825918539 3172173433796480738877809)
              ·
                refine ⟨2379130075347360554158357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3172173433796480738877809 2379130075347360554158357)
                ·
                  refine ⟨111521722281907525976173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2379130075347360554158357 111521722281907525976173)
                  ·
                    rfl

theorem cell22_977345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 6].length) (baseStart_977345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_977345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_977345 prefixEnd_977345 := by exact prefixLift 977345
  have htrace : WordTrace (prefixWord ++ tailWord_977345) baseStart_977345 baseEnd_977345 := by
    simpa [prefixWord, tailWord_977345, baseEnd_977345] using wordTrace_append hprefix tailTrace_977345
  have hstable : (prefixWord ++ tailWord_977345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977345).length < 2 ^ (prefixWord ++ tailWord_977345).sum := by decide
  have hdescent : baseEnd_977345 < baseStart_977345 := by decide
  rcases family_descends (prefixWord ++ tailWord_977345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977388 : List Nat := [2, 2, 1, 1, 2, 1, 3, 6, 1, 3]
def baseStart_977388 : Nat := 118140960795 + 977388 * 2 ^ 59
def prefixEnd_977388 : Nat := 4983230072969 + 3 ^ 40 * 977388 * 2
def baseEnd_977388 : Nat := 334579886624484799103387

theorem tailTrace_977388 : CollatzResearch.WordTrace tailWord_977388 prefixEnd_977388 334579886624484799103387 := by
  unfold tailWord_977388
  simp only [CollatzResearch.WordTrace]
  refine ⟨17824134491548837712982409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23765512655398450283976545 17824134491548837712982409)
  ·
    refine ⟨13368100868661628284736807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17824134491548837712982409 13368100868661628284736807)
    ·
      refine ⟨20052151302992442427105211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13368100868661628284736807 20052151302992442427105211)
      ·
        refine ⟨30078226954488663640657817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20052151302992442427105211 30078226954488663640657817)
        ·
          refine ⟨22558670215866497730493363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30078226954488663640657817 22558670215866497730493363)
          ·
            refine ⟨33838005323799746595740045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22558670215866497730493363 33838005323799746595740045)
            ·
              refine ⟨12689251996424904973402517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33838005323799746595740045 12689251996424904973402517)
              ·
                refine ⟨594808687332417420628243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12689251996424904973402517 594808687332417420628243)
                ·
                  refine ⟨892213030998626130942365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 594808687332417420628243 892213030998626130942365)
                  ·
                    refine ⟨334579886624484799103387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 892213030998626130942365 334579886624484799103387)
                    ·
                      rfl

theorem cell22_977388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 6, 1, 3].length) (baseStart_977388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_977388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_977388 prefixEnd_977388 := by exact prefixLift 977388
  have htrace : WordTrace (prefixWord ++ tailWord_977388) baseStart_977388 baseEnd_977388 := by
    simpa [prefixWord, tailWord_977388, baseEnd_977388] using wordTrace_append hprefix tailTrace_977388
  have hstable : (prefixWord ++ tailWord_977388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977388).length < 2 ^ (prefixWord ++ tailWord_977388).sum := by decide
  have hdescent : baseEnd_977388 < baseStart_977388 := by decide
  rcases family_descends (prefixWord ++ tailWord_977388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977422 : List Nat := [4, 1, 1, 2, 3, 3, 1, 3, 1, 3]
def baseStart_977422 : Nat := 118140960795 + 977422 * 2 ^ 59
def prefixEnd_977422 : Nat := 4983230072969 + 3 ^ 40 * 977422 * 2
def baseEnd_977422 : Nat := 334591525519320043753283

theorem tailTrace_977422 : CollatzResearch.WordTrace tailWord_977422 prefixEnd_977422 334591525519320043753283 := by
  unfold tailWord_977422
  simp only [CollatzResearch.WordTrace]
  refine ⟨4456188633121812404087815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23766339376649666155135013 4456188633121812404087815)
  ·
    refine ⟨6684282949682718606131723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4456188633121812404087815 6684282949682718606131723)
    ·
      refine ⟨10026424424524077909197585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6684282949682718606131723 10026424424524077909197585)
      ·
        refine ⟨7519818318393058431898189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10026424424524077909197585 7519818318393058431898189)
        ·
          refine ⟨2819931869397396911961821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7519818318393058431898189 2819931869397396911961821)
          ·
            refine ⟨1057474451024023841985683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2819931869397396911961821 1057474451024023841985683)
            ·
              refine ⟨1586211676536035762978525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1057474451024023841985683 1586211676536035762978525)
              ·
                refine ⟨594829378701013411116947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1586211676536035762978525 594829378701013411116947)
                ·
                  refine ⟨892244068051520116675421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 594829378701013411116947 892244068051520116675421)
                  ·
                    refine ⟨334591525519320043753283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 892244068051520116675421 334591525519320043753283)
                    ·
                      rfl

theorem cell22_977422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 3, 1, 3].length) (baseStart_977422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_977422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_977422 prefixEnd_977422 := by exact prefixLift 977422
  have htrace : WordTrace (prefixWord ++ tailWord_977422) baseStart_977422 baseEnd_977422 := by
    simpa [prefixWord, tailWord_977422, baseEnd_977422] using wordTrace_append hprefix tailTrace_977422
  have hstable : (prefixWord ++ tailWord_977422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977422).length < 2 ^ (prefixWord ++ tailWord_977422).sum := by decide
  have hdescent : baseEnd_977422 < baseStart_977422 := by decide
  rcases family_descends (prefixWord ++ tailWord_977422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977461 : List Nat := [1, 3, 3, 1, 1, 2, 2, 3, 1, 5]
def baseStart_977461 : Nat := 118140960795 + 977461 * 2 ^ 59
def prefixEnd_977461 : Nat := 4983230072969 + 3 ^ 40 * 977461 * 2
def baseEnd_977461 : Nat := 334604876016336942028163

theorem tailTrace_977461 : CollatzResearch.WordTrace tailWord_977461 prefixEnd_977461 334604876016336942028163 := by
  unfold tailWord_977461
  simp only [CollatzResearch.WordTrace]
  refine ⟨35650931511833208893372237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23767287674555472595581491 35650931511833208893372237)
  ·
    refine ⟨13369099316937453335014589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35650931511833208893372237 13369099316937453335014589)
    ·
      refine ⟨5013412243851545000630471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13369099316937453335014589 5013412243851545000630471)
      ·
        refine ⟨7520118365777317500945707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5013412243851545000630471 7520118365777317500945707)
        ·
          refine ⟨11280177548665976251418561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7520118365777317500945707 11280177548665976251418561)
          ·
            refine ⟨8460133161499482188563921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11280177548665976251418561 8460133161499482188563921)
            ·
              refine ⟨6345099871124611641422941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8460133161499482188563921 6345099871124611641422941)
              ·
                refine ⟨2379412451671729365533603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6345099871124611641422941 2379412451671729365533603)
                ·
                  refine ⟨3569118677507594048300405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2379412451671729365533603 3569118677507594048300405)
                  ·
                    refine ⟨334604876016336942028163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3569118677507594048300405 334604876016336942028163)
                    ·
                      rfl

theorem cell22_977461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_977461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_977461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_977461 prefixEnd_977461 := by exact prefixLift 977461
  have htrace : WordTrace (prefixWord ++ tailWord_977461) baseStart_977461 baseEnd_977461 := by
    simpa [prefixWord, tailWord_977461, baseEnd_977461] using wordTrace_append hprefix tailTrace_977461
  have hstable : (prefixWord ++ tailWord_977461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977461).length < 2 ^ (prefixWord ++ tailWord_977461).sum := by decide
  have hdescent : baseEnd_977461 < baseStart_977461 := by decide
  rcases family_descends (prefixWord ++ tailWord_977461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977525 : List Nat := [1, 3, 4, 2, 2, 1, 3, 6]
def baseStart_977525 : Nat := 118140960795 + 977525 * 2 ^ 59
def prefixEnd_977525 : Nat := 4983230072969 + 3 ^ 40 * 977525 * 2
def baseEnd_977525 : Nat := 37180753836029123158663

theorem tailTrace_977525 : CollatzResearch.WordTrace tailWord_977525 prefixEnd_977525 37180753836029123158663 := by
  unfold tailWord_977525
  simp only [CollatzResearch.WordTrace]
  refine ⟨35653265783601347823702029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23768843855734231882468019 35653265783601347823702029)
  ·
    refine ⟨13369974668850505433888261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35653265783601347823702029 13369974668850505433888261)
    ·
      refine ⟨2506870250409469768854049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13369974668850505433888261 2506870250409469768854049)
      ·
        refine ⟨1880152687807102326640537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2506870250409469768854049 1880152687807102326640537)
        ·
          refine ⟨1410114515855326744980403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1880152687807102326640537 1410114515855326744980403)
          ·
            refine ⟨2115171773782990117470605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1410114515855326744980403 2115171773782990117470605)
            ·
              refine ⟨793189415168621294051477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2115171773782990117470605 793189415168621294051477)
              ·
                refine ⟨37180753836029123158663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 793189415168621294051477 37180753836029123158663)
                ·
                  rfl

theorem cell22_977525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 6].length) (baseStart_977525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_977525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_977525 prefixEnd_977525 := by exact prefixLift 977525
  have htrace : WordTrace (prefixWord ++ tailWord_977525) baseStart_977525 baseEnd_977525 := by
    simpa [prefixWord, tailWord_977525, baseEnd_977525] using wordTrace_append hprefix tailTrace_977525
  have hstable : (prefixWord ++ tailWord_977525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977525).length < 2 ^ (prefixWord ++ tailWord_977525).sum := by decide
  have hdescent : baseEnd_977525 < baseStart_977525 := by decide
  rcases family_descends (prefixWord ++ tailWord_977525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977583 : List Nat := [1, 1, 2, 1, 2, 5, 1, 4, 1, 4]
def baseStart_977583 : Nat := 118140960795 + 977583 * 2 ^ 59
def prefixEnd_977583 : Nat := 4983230072969 + 3 ^ 40 * 977583 * 2
def baseEnd_977583 : Nat := 334646639109569290477789

theorem tailTrace_977583 : CollatzResearch.WordTrace tailWord_977583 prefixEnd_977583 334646639109569290477789 := by
  unfold tailWord_977583
  simp only [CollatzResearch.WordTrace]
  refine ⟨35655381217391223729313403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23770254144927482486208935 35655381217391223729313403)
  ·
    refine ⟨53483071826086835593970105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35655381217391223729313403 53483071826086835593970105)
    ·
      refine ⟨40112303869565126695477579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53483071826086835593970105 40112303869565126695477579)
      ·
        refine ⟨60168455804347690043216369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40112303869565126695477579 60168455804347690043216369)
        ·
          refine ⟨45126341853260767532412277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60168455804347690043216369 45126341853260767532412277)
          ·
            refine ⟨4230594548743196956163651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45126341853260767532412277 4230594548743196956163651)
            ·
              refine ⟨6345891823114795434245477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4230594548743196956163651 6345891823114795434245477)
              ·
                refine ⟨1189854716834024143921027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6345891823114795434245477 1189854716834024143921027)
                ·
                  refine ⟨1784782075251036215881541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1189854716834024143921027 1784782075251036215881541)
                  ·
                    refine ⟨334646639109569290477789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1784782075251036215881541 334646639109569290477789)
                    ·
                      rfl

theorem cell22_977583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 4].length) (baseStart_977583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_977583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_977583 prefixEnd_977583 := by exact prefixLift 977583
  have htrace : WordTrace (prefixWord ++ tailWord_977583) baseStart_977583 baseEnd_977583 := by
    simpa [prefixWord, tailWord_977583, baseEnd_977583] using wordTrace_append hprefix tailTrace_977583
  have hstable : (prefixWord ++ tailWord_977583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977583).length < 2 ^ (prefixWord ++ tailWord_977583).sum := by decide
  have hdescent : baseEnd_977583 < baseStart_977583 := by decide
  rcases family_descends (prefixWord ++ tailWord_977583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977641 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 2, 7]
def baseStart_977641 : Nat := 118140960795 + 977641 * 2 ^ 59
def prefixEnd_977641 : Nat := 4983230072969 + 3 ^ 40 * 977641 * 2
def baseEnd_977641 : Nat := 334666493694876472527611

theorem tailTrace_977641 : CollatzResearch.WordTrace tailWord_977641 prefixEnd_977641 334666493694876472527611 := by
  unfold tailWord_977641
  simp only [CollatzResearch.WordTrace]
  refine ⟨35657496651181099634924777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23771664434120733089949851 35657496651181099634924777)
  ·
    refine ⟨26743122488385824726193583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35657496651181099634924777 26743122488385824726193583)
    ·
      refine ⟨40114683732578737089290375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26743122488385824726193583 40114683732578737089290375)
      ·
        refine ⟨60172025598868105633935563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40114683732578737089290375 60172025598868105633935563)
        ·
          refine ⟨90258038398302158450903345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60172025598868105633935563 90258038398302158450903345)
          ·
            refine ⟨67693528798726618838177509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90258038398302158450903345 67693528798726618838177509)
            ·
              refine ⟨12692536649761241032158283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67693528798726618838177509 12692536649761241032158283)
              ·
                refine ⟨19038804974641861548237425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12692536649761241032158283 19038804974641861548237425)
                ·
                  refine ⟨14279103730981396161178069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19038804974641861548237425 14279103730981396161178069)
                  ·
                    refine ⟨334666493694876472527611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14279103730981396161178069 334666493694876472527611)
                    ·
                      rfl

theorem cell22_977641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 7].length) (baseStart_977641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_977641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_977641 prefixEnd_977641 := by exact prefixLift 977641
  have htrace : WordTrace (prefixWord ++ tailWord_977641) baseStart_977641 baseEnd_977641 := by
    simpa [prefixWord, tailWord_977641, baseEnd_977641] using wordTrace_append hprefix tailTrace_977641
  have hstable : (prefixWord ++ tailWord_977641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977641).length < 2 ^ (prefixWord ++ tailWord_977641).sum := by decide
  have hdescent : baseEnd_977641 < baseStart_977641 := by decide
  rcases family_descends (prefixWord ++ tailWord_977641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977645 : List Nat := [1, 5, 1, 2, 1, 1, 4, 1, 2, 4]
def baseStart_977645 : Nat := 118140960795 + 977645 * 2 ^ 59
def prefixEnd_977645 : Nat := 4983230072969 + 3 ^ 40 * 977645 * 2
def baseEnd_977645 : Nat := 334667862976621795427599

theorem tailTrace_977645 : CollatzResearch.WordTrace tailWord_977645 prefixEnd_977645 334667862976621795427599 := by
  unfold tailWord_977645
  simp only [CollatzResearch.WordTrace]
  refine ⟨35657642543166608318070389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23771761695444405545380259 35657642543166608318070389)
  ·
    refine ⟨3342903988421869529819099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35657642543166608318070389 3342903988421869529819099)
    ·
      refine ⟨5014355982632804294728649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3342903988421869529819099 5014355982632804294728649)
      ·
        refine ⟨3760766986974603221046487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5014355982632804294728649 3760766986974603221046487)
        ·
          refine ⟨5641150480461904831569731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3760766986974603221046487 5641150480461904831569731)
          ·
            refine ⟨8461725720692857247354597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5641150480461904831569731 8461725720692857247354597)
            ·
              refine ⟨1586573572629910733878987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8461725720692857247354597 1586573572629910733878987)
              ·
                refine ⟨2379860358944866100818481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1586573572629910733878987 2379860358944866100818481)
                ·
                  refine ⟨1784895269208649575613861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2379860358944866100818481 1784895269208649575613861)
                  ·
                    refine ⟨334667862976621795427599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1784895269208649575613861 334667862976621795427599)
                    ·
                      rfl

theorem cell22_977645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_977645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_977645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_977645 prefixEnd_977645 := by exact prefixLift 977645
  have htrace : WordTrace (prefixWord ++ tailWord_977645) baseStart_977645 baseEnd_977645 := by
    simpa [prefixWord, tailWord_977645, baseEnd_977645] using wordTrace_append hprefix tailTrace_977645
  have hstable : (prefixWord ++ tailWord_977645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977645).length < 2 ^ (prefixWord ++ tailWord_977645).sum := by decide
  have hdescent : baseEnd_977645 < baseStart_977645 := by decide
  rcases family_descends (prefixWord ++ tailWord_977645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977722 : List Nat := [3, 1, 1, 1, 6, 2, 1, 2, 5]
def baseStart_977722 : Nat := 118140960795 + 977722 * 2 ^ 59
def prefixEnd_977722 : Nat := 4983230072969 + 3 ^ 40 * 977722 * 2
def baseEnd_977722 : Nat := 111564740550073087084121

theorem tailTrace_977722 : CollatzResearch.WordTrace tailWord_977722 prefixEnd_977722 111564740550073087084121 := by
  unfold tailWord_977722
  simp only [CollatzResearch.WordTrace]
  refine ⟨8915112740971912617155855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23773633975925100312415613 8915112740971912617155855)
  ·
    refine ⟨13372669111457868925733783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8915112740971912617155855 13372669111457868925733783)
    ·
      refine ⟨20059003667186803388600675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13372669111457868925733783 20059003667186803388600675)
      ·
        refine ⟨30088505500780205082901013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20059003667186803388600675 30088505500780205082901013)
        ·
          refine ⟨1410398695349072113260985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30088505500780205082901013 1410398695349072113260985)
          ·
            refine ⟨1057799021511804084945739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1410398695349072113260985 1057799021511804084945739)
            ·
              refine ⟨1586698532267706127418609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1057799021511804084945739 1586698532267706127418609)
              ·
                refine ⟨1190023899200779595563957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1586698532267706127418609 1190023899200779595563957)
                ·
                  refine ⟨111564740550073087084121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1190023899200779595563957 111564740550073087084121)
                  ·
                    rfl

theorem cell22_977722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 5].length) (baseStart_977722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_977722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_977722 prefixEnd_977722 := by exact prefixLift 977722
  have htrace : WordTrace (prefixWord ++ tailWord_977722) baseStart_977722 baseEnd_977722 := by
    simpa [prefixWord, tailWord_977722, baseEnd_977722] using wordTrace_append hprefix tailTrace_977722
  have hstable : (prefixWord ++ tailWord_977722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977722).length < 2 ^ (prefixWord ++ tailWord_977722).sum := by decide
  have hdescent : baseEnd_977722 < baseStart_977722 := by decide
  rcases family_descends (prefixWord ++ tailWord_977722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977765 : List Nat := [1, 3, 1, 3, 1, 1, 3, 2, 4, 3]
def baseStart_977765 : Nat := 118140960795 + 977765 * 2 ^ 59
def prefixEnd_977765 : Nat := 4983230072969 + 3 ^ 40 * 977765 * 2
def baseEnd_977765 : Nat := 334708941428981482427231

theorem tailTrace_977765 : CollatzResearch.WordTrace tailWord_977765 prefixEnd_977765 334708941428981482427231 := by
  unfold tailWord_977765
  simp only [CollatzResearch.WordTrace]
  refine ⟨35662019302731868812438749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23774679535154579208292499 35662019302731868812438749)
  ·
    refine ⟨13373257238524450804664531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35662019302731868812438749 13373257238524450804664531)
    ·
      refine ⟨20059885857786676206996797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13373257238524450804664531 20059885857786676206996797)
      ·
        refine ⟨7522457196670003577623799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20059885857786676206996797 7522457196670003577623799)
        ·
          refine ⟨11283685795005005366435699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7522457196670003577623799 11283685795005005366435699)
          ·
            refine ⟨16925528692507508049653549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11283685795005005366435699 16925528692507508049653549)
            ·
              refine ⟨6347073259690315518620081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16925528692507508049653549 6347073259690315518620081)
              ·
                refine ⟨4760304944767736638965061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6347073259690315518620081 4760304944767736638965061)
                ·
                  refine ⟨892557177143950619805949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4760304944767736638965061 892557177143950619805949)
                  ·
                    refine ⟨334708941428981482427231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 892557177143950619805949 334708941428981482427231)
                    ·
                      rfl

theorem cell22_977765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 4, 3].length) (baseStart_977765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_977765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_977765 prefixEnd_977765 := by exact prefixLift 977765
  have htrace : WordTrace (prefixWord ++ tailWord_977765) baseStart_977765 baseEnd_977765 := by
    simpa [prefixWord, tailWord_977765, baseEnd_977765] using wordTrace_append hprefix tailTrace_977765
  have hstable : (prefixWord ++ tailWord_977765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977765).length < 2 ^ (prefixWord ++ tailWord_977765).sum := by decide
  have hdescent : baseEnd_977765 < baseStart_977765 := by decide
  rcases family_descends (prefixWord ++ tailWord_977765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977767 : List Nat := [1, 1, 5, 1, 2, 2, 3, 3, 4]
def baseStart_977767 : Nat := 118140960795 + 977767 * 2 ^ 59
def prefixEnd_977767 : Nat := 4983230072969 + 3 ^ 40 * 977767 * 2
def baseEnd_977767 : Nat := 111569875356618047959075

theorem tailTrace_977767 : CollatzResearch.WordTrace tailWord_977767 prefixEnd_977767 111569875356618047959075 := by
  unfold tailWord_977767
  simp only [CollatzResearch.WordTrace]
  refine ⟨35662092248724623154011555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23774728165816415436007703 35662092248724623154011555)
  ·
    refine ⟨53493138373086934731017333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35662092248724623154011555 53493138373086934731017333)
    ·
      refine ⟨5014981722476900131032875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53493138373086934731017333 5014981722476900131032875)
      ·
        refine ⟨7522472583715350196549313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5014981722476900131032875 7522472583715350196549313)
        ·
          refine ⟨5641854437786512647411985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7522472583715350196549313 5641854437786512647411985)
          ·
            refine ⟨4231390828339884485558989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5641854437786512647411985 4231390828339884485558989)
            ·
              refine ⟨1586771560627456682084621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4231390828339884485558989 1586771560627456682084621)
              ·
                refine ⟨595039335235296255781733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1586771560627456682084621 595039335235296255781733)
                ·
                  refine ⟨111569875356618047959075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 595039335235296255781733 111569875356618047959075)
                  ·
                    rfl

theorem cell22_977767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 3, 4].length) (baseStart_977767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_977767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_977767 prefixEnd_977767 := by exact prefixLift 977767
  have htrace : WordTrace (prefixWord ++ tailWord_977767) baseStart_977767 baseEnd_977767 := by
    simpa [prefixWord, tailWord_977767, baseEnd_977767] using wordTrace_append hprefix tailTrace_977767
  have hstable : (prefixWord ++ tailWord_977767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977767).length < 2 ^ (prefixWord ++ tailWord_977767).sum := by decide
  have hdescent : baseEnd_977767 < baseStart_977767 := by decide
  rcases family_descends (prefixWord ++ tailWord_977767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977778 : List Nat := [3, 2, 1, 2, 1, 1, 12]
def baseStart_977778 : Nat := 118140960795 + 977778 * 2 ^ 59
def prefixEnd_977778 : Nat := 4983230072969 + 3 ^ 40 * 977778 * 2
def baseEnd_977778 : Nat := 12396792281283473401933

theorem tailTrace_977778 : CollatzResearch.WordTrace tailWord_977778 prefixEnd_977778 12396792281283473401933 := by
  unfold tailWord_977778
  simp only [CollatzResearch.WordTrace]
  refine ⟨8915623362921193008165497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23774995634456514688441325 8915623362921193008165497)
  ·
    refine ⟨6686717522190894756124123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8915623362921193008165497 6686717522190894756124123)
    ·
      refine ⟨10030076283286342134186185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6686717522190894756124123 10030076283286342134186185)
      ·
        refine ⟨7522557212464756600639639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10030076283286342134186185 7522557212464756600639639)
        ·
          refine ⟨11283835818697134900959459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7522557212464756600639639 11283835818697134900959459)
          ·
            refine ⟨16925753728045702351439189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11283835818697134900959459 16925753728045702351439189)
            ·
              refine ⟨12396792281283473401933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 16925753728045702351439189 12396792281283473401933)
              ·
                rfl

theorem cell22_977778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 12].length) (baseStart_977778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_977778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_977778 prefixEnd_977778 := by exact prefixLift 977778
  have htrace : WordTrace (prefixWord ++ tailWord_977778) baseStart_977778 baseEnd_977778 := by
    simpa [prefixWord, tailWord_977778, baseEnd_977778] using wordTrace_append hprefix tailTrace_977778
  have hstable : (prefixWord ++ tailWord_977778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977778).length < 2 ^ (prefixWord ++ tailWord_977778).sum := by decide
  have hdescent : baseEnd_977778 < baseStart_977778 := by decide
  rcases family_descends (prefixWord ++ tailWord_977778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977799 : List Nat := [1, 1, 4, 2, 3, 1, 4, 1, 2, 3]
def baseStart_977799 : Nat := 118140960795 + 977799 * 2 ^ 59
def prefixEnd_977799 : Nat := 4983230072969 + 3 ^ 40 * 977799 * 2
def baseEnd_977799 : Nat := 334720580323816727077127

theorem tailTrace_977799 : CollatzResearch.WordTrace tailWord_977799 prefixEnd_977799 334720580323816727077127 := by
  unfold tailWord_977799
  simp only [CollatzResearch.WordTrace]
  refine ⟨35663259384608692619176451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23775506256405795079450967 35663259384608692619176451)
  ·
    refine ⟨53494889076913038928764677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35663259384608692619176451 53494889076913038928764677)
    ·
      refine ⟨10030291701921194799143377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53494889076913038928764677 10030291701921194799143377)
      ·
        refine ⟨7522718776440896099357533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10030291701921194799143377 7522718776440896099357533)
        ·
          refine ⟨2821019541165336037259075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7522718776440896099357533 2821019541165336037259075)
          ·
            refine ⟨4231529311748004055888613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2821019541165336037259075 4231529311748004055888613)
            ·
              refine ⟨793411745952750760479115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4231529311748004055888613 793411745952750760479115)
              ·
                refine ⟨1190117618929126140718673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 793411745952750760479115 1190117618929126140718673)
                ·
                  refine ⟨892588214196844605539005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1190117618929126140718673 892588214196844605539005)
                  ·
                    refine ⟨334720580323816727077127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 892588214196844605539005 334720580323816727077127)
                    ·
                      rfl

theorem cell22_977799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 2, 3].length) (baseStart_977799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_977799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_977799 prefixEnd_977799 := by exact prefixLift 977799
  have htrace : WordTrace (prefixWord ++ tailWord_977799) baseStart_977799 baseEnd_977799 := by
    simpa [prefixWord, tailWord_977799, baseEnd_977799] using wordTrace_append hprefix tailTrace_977799
  have hstable : (prefixWord ++ tailWord_977799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977799).length < 2 ^ (prefixWord ++ tailWord_977799).sum := by decide
  have hdescent : baseEnd_977799 < baseStart_977799 := by decide
  rcases family_descends (prefixWord ++ tailWord_977799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977878 : List Nat := [5, 2, 1, 1, 2, 2, 2, 3, 1, 3]
def baseStart_977878 : Nat := 118140960795 + 977878 * 2 ^ 59
def prefixEnd_977878 : Nat := 4983230072969 + 3 ^ 40 * 977878 * 2
def baseEnd_977878 : Nat := 334747623638286854351885

theorem tailTrace_977878 : CollatzResearch.WordTrace tailWord_977878 prefixEnd_977878 334747623638286854351885 := by
  unfold tailWord_977878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2229133796957655569456393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23777427167548326074201525 2229133796957655569456393)
  ·
    refine ⟨1671850347718241677092295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2229133796957655569456393 1671850347718241677092295)
    ·
      refine ⟨2507775521577362515638443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1671850347718241677092295 2507775521577362515638443)
      ·
        refine ⟨3761663282366043773457665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2507775521577362515638443 3761663282366043773457665)
        ·
          refine ⟨2821247461774532830093249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3761663282366043773457665 2821247461774532830093249)
          ·
            refine ⟨2115935596330899622569937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2821247461774532830093249 2115935596330899622569937)
            ·
              refine ⟨1586951697248174716927453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2115935596330899622569937 1586951697248174716927453)
              ·
                refine ⟨595106886468065518847795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1586951697248174716927453 595106886468065518847795)
                ·
                  refine ⟨892660329702098278271693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 595106886468065518847795 892660329702098278271693)
                  ·
                    refine ⟨334747623638286854351885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 892660329702098278271693 334747623638286854351885)
                    ·
                      rfl

theorem cell22_977878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_977878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_977878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_977878 prefixEnd_977878 := by exact prefixLift 977878
  have htrace : WordTrace (prefixWord ++ tailWord_977878) baseStart_977878 baseEnd_977878 := by
    simpa [prefixWord, tailWord_977878, baseEnd_977878] using wordTrace_append hprefix tailTrace_977878
  have hstable : (prefixWord ++ tailWord_977878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977878).length < 2 ^ (prefixWord ++ tailWord_977878).sum := by decide
  have hdescent : baseEnd_977878 < baseStart_977878 := by decide
  rcases family_descends (prefixWord ++ tailWord_977878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_977949 : List Nat := [1, 4, 2, 2, 3, 1, 1, 2, 2, 4]
def baseStart_977949 : Nat := 118140960795 + 977949 * 2 ^ 59
def prefixEnd_977949 : Nat := 4983230072969 + 3 ^ 40 * 977949 * 2
def baseEnd_977949 : Nat := 334771928389266335826667

theorem tailTrace_977949 : CollatzResearch.WordTrace tailWord_977949 prefixEnd_977949 334771928389266335826667 := by
  unfold tailWord_977949
  simp only [CollatzResearch.WordTrace]
  refine ⟨35668730334065268237136901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23779153556043512158091267 35668730334065268237136901)
  ·
    refine ⟨6687886937637237794463169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35668730334065268237136901 6687886937637237794463169)
    ·
      refine ⟨5015915203227928345847377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6687886937637237794463169 5015915203227928345847377)
      ·
        refine ⟨3761936402420946259385533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5015915203227928345847377 3761936402420946259385533)
        ·
          refine ⟨1410726150907854847269575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3761936402420946259385533 1410726150907854847269575)
          ·
            refine ⟨2116089226361782270904363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1410726150907854847269575 2116089226361782270904363)
            ·
              refine ⟨3174133839542673406356545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2116089226361782270904363 3174133839542673406356545)
              ·
                refine ⟨2380600379657005054767409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3174133839542673406356545 2380600379657005054767409)
                ·
                  refine ⟨1785450284742753791075557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2380600379657005054767409 1785450284742753791075557)
                  ·
                    refine ⟨334771928389266335826667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1785450284742753791075557 334771928389266335826667)
                    ·
                      rfl

theorem cell22_977949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_977949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_977949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_977949 prefixEnd_977949 := by exact prefixLift 977949
  have htrace : WordTrace (prefixWord ++ tailWord_977949) baseStart_977949 baseEnd_977949 := by
    simpa [prefixWord, tailWord_977949, baseEnd_977949] using wordTrace_append hprefix tailTrace_977949
  have hstable : (prefixWord ++ tailWord_977949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_977949).length < 2 ^ (prefixWord ++ tailWord_977949).sum := by decide
  have hdescent : baseEnd_977949 < baseStart_977949 := by decide
  rcases family_descends (prefixWord ++ tailWord_977949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978056 : List Nat := [2, 1, 3, 4, 2, 1, 1, 3, 1, 4]
def baseStart_978056 : Nat := 118140960795 + 978056 * 2 ^ 59
def prefixEnd_978056 : Nat := 4983230072969 + 3 ^ 40 * 978056 * 2
def baseEnd_978056 : Nat := 334808556675953723401339

theorem tailTrace_978056 : CollatzResearch.WordTrace tailWord_978056 prefixEnd_978056 334808556675953723401339 := by
  unfold tailWord_978056
  simp only [CollatzResearch.WordTrace]
  refine ⟨17836316472338812755641011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23781755296451750340854681 17836316472338812755641011)
  ·
    refine ⟨26754474708508219133461517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17836316472338812755641011 26754474708508219133461517)
    ·
      refine ⟨10032928015690582175048069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26754474708508219133461517 10032928015690582175048069)
      ·
        refine ⟨1881174002941984157821513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10032928015690582175048069 1881174002941984157821513)
        ·
          refine ⟨1410880502206488118366135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1881174002941984157821513 1410880502206488118366135)
          ·
            refine ⟨2116320753309732177549203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1410880502206488118366135 2116320753309732177549203)
            ·
              refine ⟨3174481129964598266323805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2116320753309732177549203 3174481129964598266323805)
              ·
                refine ⟨1190430423736724349871427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3174481129964598266323805 1190430423736724349871427)
                ·
                  refine ⟨1785645635605086524807141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1190430423736724349871427 1785645635605086524807141)
                  ·
                    refine ⟨334808556675953723401339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1785645635605086524807141 334808556675953723401339)
                    ·
                      rfl

theorem cell22_978056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_978056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_978056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_978056 prefixEnd_978056 := by exact prefixLift 978056
  have htrace : WordTrace (prefixWord ++ tailWord_978056) baseStart_978056 baseEnd_978056 := by
    simpa [prefixWord, tailWord_978056, baseEnd_978056] using wordTrace_append hprefix tailTrace_978056
  have hstable : (prefixWord ++ tailWord_978056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978056).length < 2 ^ (prefixWord ++ tailWord_978056).sum := by decide
  have hdescent : baseEnd_978056 < baseStart_978056 := by decide
  rcases family_descends (prefixWord ++ tailWord_978056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978067 : List Nat := [1, 1, 1, 2, 1, 2, 4, 4, 2, 4]
def baseStart_978067 : Nat := 118140960795 + 978067 * 2 ^ 59
def prefixEnd_978067 : Nat := 4983230072969 + 3 ^ 40 * 978067 * 2
def baseEnd_978067 : Nat := 334812322200753361376305

theorem tailTrace_978067 : CollatzResearch.WordTrace tailWord_978067 prefixEnd_978067 334812322200753361376305 := by
  unfold tailWord_978067
  simp only [CollatzResearch.WordTrace]
  refine ⟨35673034147637774389932455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23782022765091849593288303 35673034147637774389932455)
  ·
    refine ⟨53509551221456661584898683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35673034147637774389932455 53509551221456661584898683)
    ·
      refine ⟨80264326832184992377348025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53509551221456661584898683 80264326832184992377348025)
      ·
        refine ⟨60198245124138744283011019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80264326832184992377348025 60198245124138744283011019)
        ·
          refine ⟨90297367686208116424516529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60198245124138744283011019 90297367686208116424516529)
          ·
            refine ⟨67723025764656087318387397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90297367686208116424516529 67723025764656087318387397)
            ·
              refine ⟨12698067330873016372197637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67723025764656087318387397 12698067330873016372197637)
              ·
                refine ⟨2380887624538690569787057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12698067330873016372197637 2380887624538690569787057)
                ·
                  refine ⟨1785665718404017927340293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2380887624538690569787057 1785665718404017927340293)
                  ·
                    refine ⟨334812322200753361376305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1785665718404017927340293 334812322200753361376305)
                    ·
                      rfl

theorem cell22_978067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 4].length) (baseStart_978067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_978067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_978067 prefixEnd_978067 := by exact prefixLift 978067
  have htrace : WordTrace (prefixWord ++ tailWord_978067) baseStart_978067 baseEnd_978067 := by
    simpa [prefixWord, tailWord_978067, baseEnd_978067] using wordTrace_append hprefix tailTrace_978067
  have hstable : (prefixWord ++ tailWord_978067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978067).length < 2 ^ (prefixWord ++ tailWord_978067).sum := by decide
  have hdescent : baseEnd_978067 < baseStart_978067 := by decide
  rcases family_descends (prefixWord ++ tailWord_978067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978069 : List Nat := [1, 3, 2, 1, 1, 1, 2, 6, 2, 3]
def baseStart_978069 : Nat := 118140960795 + 978069 * 2 ^ 59
def prefixEnd_978069 : Nat := 4983230072969 + 3 ^ 40 * 978069 * 2
def baseEnd_978069 : Nat := 334813006841626022826299

theorem tailTrace_978069 : CollatzResearch.WordTrace tailWord_978069 prefixEnd_978069 334813006841626022826299 := by
  unfold tailWord_978069
  simp only [CollatzResearch.WordTrace]
  refine ⟨35673107093630528731505261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23782071395753685821003507 35673107093630528731505261)
  ·
    refine ⟨13377415160111448274314473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35673107093630528731505261 13377415160111448274314473)
    ·
      refine ⟨10033061370083586205735855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13377415160111448274314473 10033061370083586205735855)
      ·
        refine ⟨15049592055125379308603783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10033061370083586205735855 15049592055125379308603783)
        ·
          refine ⟨22574388082688068962905675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15049592055125379308603783 22574388082688068962905675)
          ·
            refine ⟨33861582124032103444358513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22574388082688068962905675 33861582124032103444358513)
            ·
              refine ⟨25396186593024077583268885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33861582124032103444358513 25396186593024077583268885)
              ·
                refine ⟨1190446246548003636715729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25396186593024077583268885 1190446246548003636715729)
                ·
                  refine ⟨892834684911002727536797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1190446246548003636715729 892834684911002727536797)
                  ·
                    refine ⟨334813006841626022826299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 892834684911002727536797 334813006841626022826299)
                    ·
                      rfl

theorem cell22_978069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_978069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_978069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_978069 prefixEnd_978069 := by exact prefixLift 978069
  have htrace : WordTrace (prefixWord ++ tailWord_978069) baseStart_978069 baseEnd_978069 := by
    simpa [prefixWord, tailWord_978069, baseEnd_978069] using wordTrace_append hprefix tailTrace_978069
  have hstable : (prefixWord ++ tailWord_978069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978069).length < 2 ^ (prefixWord ++ tailWord_978069).sum := by decide
  have hdescent : baseEnd_978069 < baseStart_978069 := by decide
  rcases family_descends (prefixWord ++ tailWord_978069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978116 : List Nat := [2, 3, 3, 1, 4, 1, 8]
def baseStart_978116 : Nat := 118140960795 + 978116 * 2 ^ 59
def prefixEnd_978116 : Nat := 4983230072969 + 3 ^ 40 * 978116 * 2
def baseEnd_978116 : Nat := 12401077626004946922265

theorem tailTrace_978116 : CollatzResearch.WordTrace tailWord_978116 prefixEnd_978116 12401077626004946922265 := by
  unfold tailWord_978116
  simp only [CollatzResearch.WordTrace]
  refine ⟨17837410662230127879233101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23783214216306837172310801 17837410662230127879233101)
  ·
    refine ⟨6689028998336297954712413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17837410662230127879233101 6689028998336297954712413)
    ·
      refine ⟨2508385874376111733017155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6689028998336297954712413 2508385874376111733017155)
      ·
        refine ⟨3762578811564167599525733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2508385874376111733017155 3762578811564167599525733)
        ·
          refine ⟨705483527168281424911075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3762578811564167599525733 705483527168281424911075)
          ·
            refine ⟨1058225290752422137366613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705483527168281424911075 1058225290752422137366613)
            ·
              refine ⟨12401077626004946922265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1058225290752422137366613 12401077626004946922265)
              ·
                rfl

theorem cell22_978116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 8].length) (baseStart_978116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_978116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_978116 prefixEnd_978116 := by exact prefixLift 978116
  have htrace : WordTrace (prefixWord ++ tailWord_978116) baseStart_978116 baseEnd_978116 := by
    simpa [prefixWord, tailWord_978116, baseEnd_978116] using wordTrace_append hprefix tailTrace_978116
  have hstable : (prefixWord ++ tailWord_978116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978116).length < 2 ^ (prefixWord ++ tailWord_978116).sum := by decide
  have hdescent : baseEnd_978116 < baseStart_978116 := by decide
  rcases family_descends (prefixWord ++ tailWord_978116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978144 : List Nat := [2, 1, 1, 3, 1, 5, 1, 3, 5]
def baseStart_978144 : Nat := 118140960795 + 978144 * 2 ^ 59
def prefixEnd_978144 : Nat := 4983230072969 + 3 ^ 40 * 978144 * 2
def baseEnd_978144 : Nat := 111612893624783609067023

theorem tailTrace_978144 : CollatzResearch.WordTrace tailWord_978144 prefixEnd_978144 111612893624783609067023 := by
  unfold tailWord_978144
  simp only [CollatzResearch.WordTrace]
  refine ⟨17837921284179408270242743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23783895045572544360323657 17837921284179408270242743)
  ·
    refine ⟨26756881926269112405364115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17837921284179408270242743 26756881926269112405364115)
    ·
      refine ⟨40135322889403668608046173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26756881926269112405364115 40135322889403668608046173)
      ·
        refine ⟨15050746083526375728017315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40135322889403668608046173 15050746083526375728017315)
        ·
          refine ⟨22576119125289563592025973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15050746083526375728017315 22576119125289563592025973)
          ·
            refine ⟨2116511167995896586752435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22576119125289563592025973 2116511167995896586752435)
            ·
              refine ⟨3174766751993844880128653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2116511167995896586752435 3174766751993844880128653)
              ·
                refine ⟨1190537531997691830048245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3174766751993844880128653 1190537531997691830048245)
                ·
                  refine ⟨111612893624783609067023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1190537531997691830048245 111612893624783609067023)
                  ·
                    rfl

theorem cell22_978144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 5].length) (baseStart_978144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_978144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_978144 prefixEnd_978144 := by exact prefixLift 978144
  have htrace : WordTrace (prefixWord ++ tailWord_978144) baseStart_978144 baseEnd_978144 := by
    simpa [prefixWord, tailWord_978144, baseEnd_978144] using wordTrace_append hprefix tailTrace_978144
  have hstable : (prefixWord ++ tailWord_978144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978144).length < 2 ^ (prefixWord ++ tailWord_978144).sum := by decide
  have hdescent : baseEnd_978144 < baseStart_978144 := by decide
  rcases family_descends (prefixWord ++ tailWord_978144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978178 : List Nat := [3, 4, 1, 1, 3, 1, 2, 2, 5]
def baseStart_978178 : Nat := 118140960795 + 978178 * 2 ^ 59
def prefixEnd_978178 : Nat := 4983230072969 + 3 ^ 40 * 978178 * 2
def baseEnd_978178 : Nat := 111616773256395357283655

theorem tailTrace_978178 : CollatzResearch.WordTrace tailWord_978178 prefixEnd_978178 111616773256395357283655 := by
  unfold tailWord_978178
  simp only [CollatzResearch.WordTrace]
  refine ⟨8919270662558910086805797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23784721766823760231482125 8919270662558910086805797)
  ·
    refine ⟨1672363249229795641276087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8919270662558910086805797 1672363249229795641276087)
    ·
      refine ⟨2508544873844693461914131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1672363249229795641276087 2508544873844693461914131)
      ·
        refine ⟨3762817310767040192871197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2508544873844693461914131 3762817310767040192871197)
        ·
          refine ⟨1411056491537640072326699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3762817310767040192871197 1411056491537640072326699)
          ·
            refine ⟨2116584737306460108490049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1411056491537640072326699 2116584737306460108490049)
            ·
              refine ⟨1587438552979845081367537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2116584737306460108490049 1587438552979845081367537)
              ·
                refine ⟨1190578914734883811025653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1587438552979845081367537 1190578914734883811025653)
                ·
                  refine ⟨111616773256395357283655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1190578914734883811025653 111616773256395357283655)
                  ·
                    rfl

theorem cell22_978178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_978178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_978178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_978178 prefixEnd_978178 := by exact prefixLift 978178
  have htrace : WordTrace (prefixWord ++ tailWord_978178) baseStart_978178 baseEnd_978178 := by
    simpa [prefixWord, tailWord_978178, baseEnd_978178] using wordTrace_append hprefix tailTrace_978178
  have hstable : (prefixWord ++ tailWord_978178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978178).length < 2 ^ (prefixWord ++ tailWord_978178).sum := by decide
  have hdescent : baseEnd_978178 < baseStart_978178 := by decide
  rcases family_descends (prefixWord ++ tailWord_978178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978204 : List Nat := [2, 2, 3, 1, 1, 1, 3, 3, 1, 5]
def baseStart_978204 : Nat := 118140960795 + 978204 * 2 ^ 59
def prefixEnd_978204 : Nat := 4983230072969 + 3 ^ 40 * 978204 * 2
def baseEnd_978204 : Nat := 334859220100530670700885

theorem tailTrace_978204 : CollatzResearch.WordTrace tailWord_978204 prefixEnd_978204 334859220100530670700885 := by
  unfold tailWord_978204
  simp only [CollatzResearch.WordTrace]
  refine ⟨17839015474070723393834833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23785353965427631191779777 17839015474070723393834833)
  ·
    refine ⟨13379261605553042545376125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17839015474070723393834833 13379261605553042545376125)
    ·
      refine ⟨5017223102082390954516047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13379261605553042545376125 5017223102082390954516047)
      ·
        refine ⟨7525834653123586431774071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5017223102082390954516047 7525834653123586431774071)
        ·
          refine ⟨11288751979685379647661107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7525834653123586431774071 11288751979685379647661107)
          ·
            refine ⟨16933127969528069471491661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11288751979685379647661107 16933127969528069471491661)
            ·
              refine ⟨6349922988573026051809373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16933127969528069471491661 6349922988573026051809373)
              ·
                refine ⟨2381221120714884769428515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6349922988573026051809373 2381221120714884769428515)
                ·
                  refine ⟨3571831681072327154142773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2381221120714884769428515 3571831681072327154142773)
                  ·
                    refine ⟨334859220100530670700885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3571831681072327154142773 334859220100530670700885)
                    ·
                      rfl

theorem cell22_978204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_978204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_978204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_978204 prefixEnd_978204 := by exact prefixLift 978204
  have htrace : WordTrace (prefixWord ++ tailWord_978204) baseStart_978204 baseEnd_978204 := by
    simpa [prefixWord, tailWord_978204, baseEnd_978204] using wordTrace_append hprefix tailTrace_978204
  have hstable : (prefixWord ++ tailWord_978204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978204).length < 2 ^ (prefixWord ++ tailWord_978204).sum := by decide
  have hdescent : baseEnd_978204 < baseStart_978204 := by decide
  rcases family_descends (prefixWord ++ tailWord_978204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978266 : List Nat := [3, 1, 1, 2, 1, 2, 4, 2, 3, 3]
def baseStart_978266 : Nat := 118140960795 + 978266 * 2 ^ 59
def prefixEnd_978266 : Nat := 4983230072969 + 3 ^ 40 * 978266 * 2
def baseEnd_978266 : Nat := 334880443967583175650695

theorem tailTrace_978266 : CollatzResearch.WordTrace tailWord_978266 prefixEnd_978266 334880443967583175650695 := by
  unfold tailWord_978266
  simp only [CollatzResearch.WordTrace]
  refine ⟨8920073068479207844106663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23786861515944554250951101 8920073068479207844106663)
  ·
    refine ⟨13380109602718811766159995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8920073068479207844106663 13380109602718811766159995)
    ·
      refine ⟨20070164404078217649239993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13380109602718811766159995 20070164404078217649239993)
      ·
        refine ⟨15052623303058663236929995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20070164404078217649239993 15052623303058663236929995)
        ·
          refine ⟨22578934954587994855394993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15052623303058663236929995 22578934954587994855394993)
          ·
            refine ⟨16934201215940996141546245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22578934954587994855394993 16934201215940996141546245)
            ·
              refine ⟨3175162727988936776539921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16934201215940996141546245 3175162727988936776539921)
              ·
                refine ⟨2381372045991702582404941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3175162727988936776539921 2381372045991702582404941)
                ·
                  refine ⟨893014517246888468401853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2381372045991702582404941 893014517246888468401853)
                  ·
                    refine ⟨334880443967583175650695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 893014517246888468401853 334880443967583175650695)
                    ·
                      rfl

theorem cell22_978266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 3, 3].length) (baseStart_978266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_978266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_978266 prefixEnd_978266 := by exact prefixLift 978266
  have htrace : WordTrace (prefixWord ++ tailWord_978266) baseStart_978266 baseEnd_978266 := by
    simpa [prefixWord, tailWord_978266, baseEnd_978266] using wordTrace_append hprefix tailTrace_978266
  have hstable : (prefixWord ++ tailWord_978266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978266).length < 2 ^ (prefixWord ++ tailWord_978266).sum := by decide
  have hdescent : baseEnd_978266 < baseStart_978266 := by decide
  rcases family_descends (prefixWord ++ tailWord_978266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978300 : List Nat := [2, 2, 2, 1, 1, 1, 7, 2, 1, 3]
def baseStart_978300 : Nat := 118140960795 + 978300 * 2 ^ 59
def prefixEnd_978300 : Nat := 4983230072969 + 3 ^ 40 * 978300 * 2
def baseEnd_978300 : Nat := 334892082862418420300591

theorem tailTrace_978300 : CollatzResearch.WordTrace tailWord_978300 prefixEnd_978300 334892082862418420300591 := by
  unfold tailWord_978300
  simp only [CollatzResearch.WordTrace]
  refine ⟨17840766177896827591582177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23787688237195770122109569 17840766177896827591582177)
  ·
    refine ⟨13380574633422620693686633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17840766177896827591582177 13380574633422620693686633)
    ·
      refine ⟨10035430975066965520264975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13380574633422620693686633 10035430975066965520264975)
      ·
        refine ⟨15053146462600448280397463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10035430975066965520264975 15053146462600448280397463)
        ·
          refine ⟨22579719693900672420596195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15053146462600448280397463 22579719693900672420596195)
          ·
            refine ⟨33869579540851008630894293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22579719693900672420596195 33869579540851008630894293)
            ·
              refine ⟨793818270488695514786585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 33869579540851008630894293 793818270488695514786585)
              ·
                refine ⟨595363702866521636089939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 793818270488695514786585 595363702866521636089939)
                ·
                  refine ⟨893045554299782454134909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 595363702866521636089939 893045554299782454134909)
                  ·
                    refine ⟨334892082862418420300591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 893045554299782454134909 334892082862418420300591)
                    ·
                      rfl

theorem cell22_978300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 2, 1, 3].length) (baseStart_978300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_978300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_978300 prefixEnd_978300 := by exact prefixLift 978300
  have htrace : WordTrace (prefixWord ++ tailWord_978300) baseStart_978300 baseEnd_978300 := by
    simpa [prefixWord, tailWord_978300, baseEnd_978300] using wordTrace_append hprefix tailTrace_978300
  have hstable : (prefixWord ++ tailWord_978300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978300).length < 2 ^ (prefixWord ++ tailWord_978300).sum := by decide
  have hdescent : baseEnd_978300 < baseStart_978300 := by decide
  rcases family_descends (prefixWord ++ tailWord_978300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978384 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 2, 7]
def baseStart_978384 : Nat := 118140960795 + 978384 * 2 ^ 59
def prefixEnd_978384 : Nat := 4983230072969 + 3 ^ 40 * 978384 * 2
def baseEnd_978384 : Nat := 334920837779070201200333

theorem tailTrace_978384 : CollatzResearch.WordTrace tailWord_978384 prefixEnd_978384 334920837779070201200333 := by
  unfold tailWord_978384
  simp only [CollatzResearch.WordTrace]
  refine ⟨17842298043744668764611103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23789730724992891686148137 17842298043744668764611103)
  ·
    refine ⟨26763447065617003146916655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17842298043744668764611103 26763447065617003146916655)
    ·
      refine ⟨40145170598425504720374983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26763447065617003146916655 40145170598425504720374983)
      ·
        refine ⟨60217755897638257080562475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40145170598425504720374983 60217755897638257080562475)
        ·
          refine ⟨90326633846457385620843713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60217755897638257080562475 90326633846457385620843713)
          ·
            refine ⟨67744975384843039215632785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90326633846457385620843713 67744975384843039215632785)
            ·
              refine ⟨50808731538632279411724589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67744975384843039215632785 50808731538632279411724589)
              ·
                refine ⟨19053274326987104779396721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50808731538632279411724589 19053274326987104779396721)
                ·
                  refine ⟨14289955745240328584547541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19053274326987104779396721 14289955745240328584547541)
                  ·
                    refine ⟨334920837779070201200333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14289955745240328584547541 334920837779070201200333)
                    ·
                      rfl

theorem cell22_978384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 2, 7].length) (baseStart_978384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_978384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_978384 prefixEnd_978384 := by exact prefixLift 978384
  have htrace : WordTrace (prefixWord ++ tailWord_978384) baseStart_978384 baseEnd_978384 := by
    simpa [prefixWord, tailWord_978384, baseEnd_978384] using wordTrace_append hprefix tailTrace_978384
  have hstable : (prefixWord ++ tailWord_978384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978384).length < 2 ^ (prefixWord ++ tailWord_978384).sum := by decide
  have hdescent : baseEnd_978384 < baseStart_978384 := by decide
  rcases family_descends (prefixWord ++ tailWord_978384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978388 : List Nat := [2, 4, 1, 2, 3, 1, 1, 1, 1, 6]
def baseStart_978388 : Nat := 118140960795 + 978388 * 2 ^ 59
def prefixEnd_978388 : Nat := 4983230072969 + 3 ^ 40 * 978388 * 2
def baseEnd_978388 : Nat := 334922207060815524100321

theorem tailTrace_978388 : CollatzResearch.WordTrace tailWord_978388 prefixEnd_978388 334922207060815524100321 := by
  unfold tailWord_978388
  simp only [CollatzResearch.WordTrace]
  refine ⟨17842370989737423106183909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23789827986316564141578545 17842370989737423106183909)
  ·
    refine ⟨3345444560575766832409483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17842370989737423106183909 3345444560575766832409483)
    ·
      refine ⟨5018166840863650248614225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3345444560575766832409483 5018166840863650248614225)
      ·
        refine ⟨3763625130647737686460669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5018166840863650248614225 3763625130647737686460669)
        ·
          refine ⟨1411359423992901632422751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3763625130647737686460669 1411359423992901632422751)
          ·
            refine ⟨2117039135989352448634127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1411359423992901632422751 2117039135989352448634127)
            ·
              refine ⟨3175558703984028672951191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2117039135989352448634127 3175558703984028672951191)
              ·
                refine ⟨4763338055976043009426787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3175558703984028672951191 4763338055976043009426787)
                ·
                  refine ⟨7145007083964064514140181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4763338055976043009426787 7145007083964064514140181)
                  ·
                    refine ⟨334922207060815524100321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7145007083964064514140181 334922207060815524100321)
                    ·
                      rfl

theorem cell22_978388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_978388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_978388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_978388 prefixEnd_978388 := by exact prefixLift 978388
  have htrace : WordTrace (prefixWord ++ tailWord_978388) baseStart_978388 baseEnd_978388 := by
    simpa [prefixWord, tailWord_978388, baseEnd_978388] using wordTrace_append hprefix tailTrace_978388
  have hstable : (prefixWord ++ tailWord_978388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978388).length < 2 ^ (prefixWord ++ tailWord_978388).sum := by decide
  have hdescent : baseEnd_978388 < baseStart_978388 := by decide
  rcases family_descends (prefixWord ++ tailWord_978388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978495 : List Nat := [1, 1, 2, 2, 3, 5, 1, 2, 1, 4]
def baseStart_978495 : Nat := 118140960795 + 978495 * 2 ^ 59
def prefixEnd_978495 : Nat := 4983230072969 + 3 ^ 40 * 978495 * 2
def baseEnd_978495 : Nat := 334958835347502911674993

theorem tailTrace_978495 : CollatzResearch.WordTrace tailWord_978495 prefixEnd_978495 334958835347502911674993 := by
  unfold tailWord_978495
  simp only [CollatzResearch.WordTrace]
  refine ⟨35688644590087203486512939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23792429726724802324341959 35688644590087203486512939)
  ·
    refine ⟨53532966885130805229769409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35688644590087203486512939 53532966885130805229769409)
    ·
      refine ⟨40149725163848103922327057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53532966885130805229769409 40149725163848103922327057)
      ·
        refine ⟨30112293872886077941745293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40149725163848103922327057 30112293872886077941745293)
        ·
          refine ⟨11292110202332279228154485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30112293872886077941745293 11292110202332279228154485)
          ·
            refine ⟨1058635331468651177639483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11292110202332279228154485 1058635331468651177639483)
            ·
              refine ⟨1587952997202976766459225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1058635331468651177639483 1587952997202976766459225)
              ·
                refine ⟨1190964747902232574844419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1587952997202976766459225 1190964747902232574844419)
                ·
                  refine ⟨1786447121853348862266629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1190964747902232574844419 1786447121853348862266629)
                  ·
                    refine ⟨334958835347502911674993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1786447121853348862266629 334958835347502911674993)
                    ·
                      rfl

theorem cell22_978495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 4].length) (baseStart_978495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_978495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_978495 prefixEnd_978495 := by exact prefixLift 978495
  have htrace : WordTrace (prefixWord ++ tailWord_978495) baseStart_978495 baseEnd_978495 := by
    simpa [prefixWord, tailWord_978495, baseEnd_978495] using wordTrace_append hprefix tailTrace_978495
  have hstable : (prefixWord ++ tailWord_978495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978495).length < 2 ^ (prefixWord ++ tailWord_978495).sum := by decide
  have hdescent : baseEnd_978495 < baseStart_978495 := by decide
  rcases family_descends (prefixWord ++ tailWord_978495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978508 : List Nat := [2, 2, 1, 3, 1, 4, 1, 2, 1, 5]
def baseStart_978508 : Nat := 118140960795 + 978508 * 2 ^ 59
def prefixEnd_978508 : Nat := 4983230072969 + 3 ^ 40 * 978508 * 2
def baseEnd_978508 : Nat := 334963285513175211099953

theorem tailTrace_978508 : CollatzResearch.WordTrace tailWord_978508 prefixEnd_978508 334963285513175211099953 := by
  unfold tailWord_978508
  simp only [CollatzResearch.WordTrace]
  refine ⟨17844559369520053353368089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23792745826026737804490785 17844559369520053353368089)
  ·
    refine ⟨13383419527140040015026067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17844559369520053353368089 13383419527140040015026067)
    ·
      refine ⟨20075129290710060022539101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13383419527140040015026067 20075129290710060022539101)
      ·
        refine ⟨7528173484016272508452163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20075129290710060022539101 7528173484016272508452163)
        ·
          refine ⟨11292260226024408762678245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7528173484016272508452163 11292260226024408762678245)
          ·
            refine ⟨2117298792379576643002171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11292260226024408762678245 2117298792379576643002171)
            ·
              refine ⟨3175948188569364964503257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2117298792379576643002171 3175948188569364964503257)
              ·
                refine ⟨2381961141427023723377443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3175948188569364964503257 2381961141427023723377443)
                ·
                  refine ⟨3572941712140535585066165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2381961141427023723377443 3572941712140535585066165)
                  ·
                    refine ⟨334963285513175211099953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3572941712140535585066165 334963285513175211099953)
                    ·
                      rfl

theorem cell22_978508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_978508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_978508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_978508 prefixEnd_978508 := by exact prefixLift 978508
  have htrace : WordTrace (prefixWord ++ tailWord_978508) baseStart_978508 baseEnd_978508 := by
    simpa [prefixWord, tailWord_978508, baseEnd_978508] using wordTrace_append hprefix tailTrace_978508
  have hstable : (prefixWord ++ tailWord_978508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978508).length < 2 ^ (prefixWord ++ tailWord_978508).sum := by decide
  have hdescent : baseEnd_978508 < baseStart_978508 := by decide
  rcases family_descends (prefixWord ++ tailWord_978508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978538 : List Nat := [3, 1, 3, 2, 1, 2, 3, 7]
def baseStart_978538 : Nat := 118140960795 + 978538 * 2 ^ 59
def prefixEnd_978538 : Nat := 4983230072969 + 3 ^ 40 * 978538 * 2
def baseEnd_978538 : Nat := 37219283902918348094429

theorem tailTrace_978538 : CollatzResearch.WordTrace tailWord_978538 prefixEnd_978538 37219283902918348094429 := by
  unfold tailWord_978538
  simp only [CollatzResearch.WordTrace]
  refine ⟨8922553232232855457582067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23793475285954281220218845 8922553232232855457582067)
  ·
    refine ⟨13383829848349283186373101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8922553232232855457582067 13383829848349283186373101)
    ·
      refine ⟨5018936193130981194889913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13383829848349283186373101 5018936193130981194889913)
      ·
        refine ⟨3764202144848235896167435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5018936193130981194889913 3764202144848235896167435)
        ·
          refine ⟨5646303217272353844251153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3764202144848235896167435 5646303217272353844251153)
          ·
            refine ⟨4234727412954265383188365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5646303217272353844251153 4234727412954265383188365)
            ·
              refine ⟨1588022779857849518695637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4234727412954265383188365 1588022779857849518695637)
              ·
                refine ⟨37219283902918348094429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1588022779857849518695637 37219283902918348094429)
                ·
                  rfl

theorem cell22_978538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 7].length) (baseStart_978538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_978538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_978538 prefixEnd_978538 := by exact prefixLift 978538
  have htrace : WordTrace (prefixWord ++ tailWord_978538) baseStart_978538 baseEnd_978538 := by
    simpa [prefixWord, tailWord_978538, baseEnd_978538] using wordTrace_append hprefix tailTrace_978538
  have hstable : (prefixWord ++ tailWord_978538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978538).length < 2 ^ (prefixWord ++ tailWord_978538).sum := by decide
  have hdescent : baseEnd_978538 < baseStart_978538 := by decide
  rcases family_descends (prefixWord ++ tailWord_978538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978551 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 4, 6]
def baseStart_978551 : Nat := 118140960795 + 978551 * 2 ^ 59
def prefixEnd_978551 : Nat := 4983230072969 + 3 ^ 40 * 978551 * 2
def baseEnd_978551 : Nat := 334978005291937432274821

theorem tailTrace_978551 : CollatzResearch.WordTrace tailWord_978551 prefixEnd_978551 334978005291937432274821 := by
  unfold tailWord_978551
  simp only [CollatzResearch.WordTrace]
  refine ⟨35690687077884325050551507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23793791385256216700367671 35690687077884325050551507)
  ·
    refine ⟨53536030616826487575827261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35690687077884325050551507 53536030616826487575827261)
    ·
      refine ⟨20076011481309932840935223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53536030616826487575827261 20076011481309932840935223)
      ·
        refine ⟨30114017221964899261402835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20076011481309932840935223 30114017221964899261402835)
        ·
          refine ⟨45171025832947348892104253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30114017221964899261402835 45171025832947348892104253)
          ·
            refine ⟨16939134687355255834539095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45171025832947348892104253 16939134687355255834539095)
            ·
              refine ⟨25408702031032883751808643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16939134687355255834539095 25408702031032883751808643)
              ·
                refine ⟨38113053046549325627712965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25408702031032883751808643 38113053046549325627712965)
                ·
                  refine ⟨7146197446227998555196181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38113053046549325627712965 7146197446227998555196181)
                  ·
                    refine ⟨334978005291937432274821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7146197446227998555196181 334978005291937432274821)
                    ·
                      rfl

theorem cell22_978551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_978551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_978551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_978551 prefixEnd_978551 := by exact prefixLift 978551
  have htrace : WordTrace (prefixWord ++ tailWord_978551) baseStart_978551 baseEnd_978551 := by
    simpa [prefixWord, tailWord_978551, baseEnd_978551] using wordTrace_append hprefix tailTrace_978551
  have hstable : (prefixWord ++ tailWord_978551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978551).length < 2 ^ (prefixWord ++ tailWord_978551).sum := by decide
  have hdescent : baseEnd_978551 < baseStart_978551 := by decide
  rcases family_descends (prefixWord ++ tailWord_978551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978583 : List Nat := [1, 1, 3, 3, 2, 3, 1, 1, 7]
def baseStart_978583 : Nat := 118140960795 + 978583 * 2 ^ 59
def prefixEnd_978583 : Nat := 4983230072969 + 3 ^ 40 * 978583 * 2
def baseEnd_978583 : Nat := 111662986515300005158241

theorem tailTrace_978583 : CollatzResearch.WordTrace tailWord_978583 prefixEnd_978583 111662986515300005158241 := by
  unfold tailWord_978583
  simp only [CollatzResearch.WordTrace]
  refine ⟨35691854213768394515716403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23794569475845596343810935 35691854213768394515716403)
  ·
    refine ⟨53537781320652591773574605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35691854213768394515716403 53537781320652591773574605)
    ·
      refine ⟨20076667995244721915090477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53537781320652591773574605 20076667995244721915090477)
      ·
        refine ⟨7528750498216770718158929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20076667995244721915090477 7528750498216770718158929)
        ·
          refine ⟨5646562873662578038619197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7528750498216770718158929 5646562873662578038619197)
          ·
            refine ⟨2117461077623466764482199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5646562873662578038619197 2117461077623466764482199)
            ·
              refine ⟨3176191616435200146723299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2117461077623466764482199 3176191616435200146723299)
              ·
                refine ⟨4764287424652800220084949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3176191616435200146723299 4764287424652800220084949)
                ·
                  refine ⟨111662986515300005158241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4764287424652800220084949 111662986515300005158241)
                  ·
                    rfl

theorem cell22_978583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 7].length) (baseStart_978583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_978583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_978583 prefixEnd_978583 := by exact prefixLift 978583
  have htrace : WordTrace (prefixWord ++ tailWord_978583) baseStart_978583 baseEnd_978583 := by
    simpa [prefixWord, tailWord_978583, baseEnd_978583] using wordTrace_append hprefix tailTrace_978583
  have hstable : (prefixWord ++ tailWord_978583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978583).length < 2 ^ (prefixWord ++ tailWord_978583).sum := by decide
  have hdescent : baseEnd_978583 < baseStart_978583 := by decide
  rcases family_descends (prefixWord ++ tailWord_978583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978673 : List Nat := [1, 2, 2, 2, 2, 3, 2, 8]
def baseStart_978673 : Nat := 118140960795 + 978673 * 2 ^ 59
def prefixEnd_978673 : Nat := 4983230072969 + 3 ^ 40 * 978673 * 2
def baseEnd_978673 : Nat := 37224418709463308969383

theorem tailTrace_978673 : CollatzResearch.WordTrace tailWord_978673 prefixEnd_978673 37224418709463308969383 := by
  unfold tailWord_978673
  simp only [CollatzResearch.WordTrace]
  refine ⟨35695136783442339886492673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23796757855628226590995115 35695136783442339886492673)
  ·
    refine ⟨26771352587581754914869505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35695136783442339886492673 26771352587581754914869505)
    ·
      refine ⟨20078514440686316186152129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26771352587581754914869505 20078514440686316186152129)
      ·
        refine ⟨15058885830514737139614097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20078514440686316186152129 15058885830514737139614097)
        ·
          refine ⟨11294164372886052854710573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15058885830514737139614097 11294164372886052854710573)
          ·
            refine ⟨4235311639832269820516465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11294164372886052854710573 4235311639832269820516465)
            ·
              refine ⟨3176483729874202365387349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4235311639832269820516465 3176483729874202365387349)
              ·
                refine ⟨37224418709463308969383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3176483729874202365387349 37224418709463308969383)
                ·
                  rfl

theorem cell22_978673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 8].length) (baseStart_978673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_978673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_978673 prefixEnd_978673 := by exact prefixLift 978673
  have htrace : WordTrace (prefixWord ++ tailWord_978673) baseStart_978673 baseEnd_978673 := by
    simpa [prefixWord, tailWord_978673, baseEnd_978673] using wordTrace_append hprefix tailTrace_978673
  have hstable : (prefixWord ++ tailWord_978673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978673).length < 2 ^ (prefixWord ++ tailWord_978673).sum := by decide
  have hdescent : baseEnd_978673 < baseStart_978673 := by decide
  rcases family_descends (prefixWord ++ tailWord_978673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978705 : List Nat := [1, 2, 2, 1, 1, 3, 1, 5, 3, 3]
def baseStart_978705 : Nat := 118140960795 + 978705 * 2 ^ 59
def prefixEnd_978705 : Nat := 4983230072969 + 3 ^ 40 * 978705 * 2
def baseEnd_978705 : Nat := 335030722639132363924349

theorem tailTrace_978705 : CollatzResearch.WordTrace tailWord_978705 prefixEnd_978705 335030722639132363924349 := by
  unfold tailWord_978705
  simp only [CollatzResearch.WordTrace]
  refine ⟨35696303919326409351657569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23797535946217606234438379 35696303919326409351657569)
  ·
    refine ⟨26772227939494807013743177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35696303919326409351657569 26772227939494807013743177)
    ·
      refine ⟨20079170954621105260307383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26772227939494807013743177 20079170954621105260307383)
      ·
        refine ⟨30118756431931657890461075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20079170954621105260307383 30118756431931657890461075)
        ·
          refine ⟨45178134647897486835691613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30118756431931657890461075 45178134647897486835691613)
          ·
            refine ⟨16941800492961557563384355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45178134647897486835691613 16941800492961557563384355)
            ·
              refine ⟨25412700739442336345076533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16941800492961557563384355 25412700739442336345076533)
              ·
                refine ⟨2382440694322719032350925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25412700739442336345076533 2382440694322719032350925)
                ·
                  refine ⟨893415260371019637131597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2382440694322719032350925 893415260371019637131597)
                  ·
                    refine ⟨335030722639132363924349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 893415260371019637131597 335030722639132363924349)
                    ·
                      rfl

theorem cell22_978705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 3, 3].length) (baseStart_978705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_978705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_978705 prefixEnd_978705 := by exact prefixLift 978705
  have htrace : WordTrace (prefixWord ++ tailWord_978705) baseStart_978705 baseEnd_978705 := by
    simpa [prefixWord, tailWord_978705, baseEnd_978705] using wordTrace_append hprefix tailTrace_978705
  have hstable : (prefixWord ++ tailWord_978705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978705).length < 2 ^ (prefixWord ++ tailWord_978705).sum := by decide
  have hdescent : baseEnd_978705 < baseStart_978705 := by decide
  rcases family_descends (prefixWord ++ tailWord_978705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978722 : List Nat := [3, 3, 1, 1, 2, 1, 3, 2, 3, 3]
def baseStart_978722 : Nat := 118140960795 + 978722 * 2 ^ 59
def prefixEnd_978722 : Nat := 4983230072969 + 3 ^ 40 * 978722 * 2
def baseEnd_978722 : Nat := 335036542086549986249297

theorem tailTrace_978722 : CollatzResearch.WordTrace tailWord_978722 prefixEnd_978722 335036542086549986249297 := by
  unfold tailWord_978722
  simp only [CollatzResearch.WordTrace]
  refine ⟨8924230990066205313756605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23797949306843214170017613 8924230990066205313756605)
  ·
    refine ⟨3346586621274826992658727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8924230990066205313756605 3346586621274826992658727)
    ·
      refine ⟨5019879931912240488988091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3346586621274826992658727 5019879931912240488988091)
      ·
        refine ⟨7529819897868360733482137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5019879931912240488988091 7529819897868360733482137)
        ·
          refine ⟨5647364923401270550111603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7529819897868360733482137 5647364923401270550111603)
          ·
            refine ⟨8471047385101905825167405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5647364923401270550111603 8471047385101905825167405)
            ·
              refine ⟨3176642769413214684437777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8471047385101905825167405 3176642769413214684437777)
              ·
                refine ⟨2382482077059911013328333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3176642769413214684437777 2382482077059911013328333)
                ·
                  refine ⟨893430778897466629998125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2382482077059911013328333 893430778897466629998125)
                  ·
                    refine ⟨335036542086549986249297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 893430778897466629998125 335036542086549986249297)
                    ·
                      rfl

theorem cell22_978722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_978722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_978722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_978722 prefixEnd_978722 := by exact prefixLift 978722
  have htrace : WordTrace (prefixWord ++ tailWord_978722) baseStart_978722 baseEnd_978722 := by
    simpa [prefixWord, tailWord_978722, baseEnd_978722] using wordTrace_append hprefix tailTrace_978722
  have hstable : (prefixWord ++ tailWord_978722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978722).length < 2 ^ (prefixWord ++ tailWord_978722).sum := by decide
  have hdescent : baseEnd_978722 < baseStart_978722 := by decide
  rcases family_descends (prefixWord ++ tailWord_978722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978810 : List Nat := [3, 1, 1, 1, 1, 1, 5, 1, 4, 4]
def baseStart_978810 : Nat := 118140960795 + 978810 * 2 ^ 59
def prefixEnd_978810 : Nat := 4983230072969 + 3 ^ 40 * 978810 * 2
def baseEnd_978810 : Nat := 335066666284947090049027

theorem tailTrace_978810 : CollatzResearch.WordTrace tailWord_978810 prefixEnd_978810 335066666284947090049027 := by
  unfold tailWord_978810
  simp only [CollatzResearch.WordTrace]
  refine ⟨8925033395986503071057471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23800089055964008189486589 8925033395986503071057471)
  ·
    refine ⟨13387550093979754606586207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8925033395986503071057471 13387550093979754606586207)
    ·
      refine ⟨20081325140969631909879311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13387550093979754606586207 20081325140969631909879311)
      ·
        refine ⟨30121987711454447864818967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20081325140969631909879311 30121987711454447864818967)
        ·
          refine ⟨45182981567181671797228451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30121987711454447864818967 45182981567181671797228451)
          ·
            refine ⟨67774472350772507695842677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45182981567181671797228451 67774472350772507695842677)
            ·
              refine ⟨6353856782884922596485251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67774472350772507695842677 6353856782884922596485251)
              ·
                refine ⟨9530785174327383894727877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6353856782884922596485251 9530785174327383894727877)
                ·
                  refine ⟨1787022220186384480261477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9530785174327383894727877 1787022220186384480261477)
                  ·
                    refine ⟨335066666284947090049027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1787022220186384480261477 335066666284947090049027)
                    ·
                      rfl

theorem cell22_978810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_978810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_978810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_978810 prefixEnd_978810 := by exact prefixLift 978810
  have htrace : WordTrace (prefixWord ++ tailWord_978810) baseStart_978810 baseEnd_978810 := by
    simpa [prefixWord, tailWord_978810, baseEnd_978810] using wordTrace_append hprefix tailTrace_978810
  have hstable : (prefixWord ++ tailWord_978810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978810).length < 2 ^ (prefixWord ++ tailWord_978810).sum := by decide
  have hdescent : baseEnd_978810 < baseStart_978810 := by decide
  rcases family_descends (prefixWord ++ tailWord_978810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978814 : List Nat := [4, 2, 3, 1, 1, 1, 3, 1, 6]
def baseStart_978814 : Nat := 118140960795 + 978814 * 2 ^ 59
def prefixEnd_978814 : Nat := 4983230072969 + 3 ^ 40 * 978814 * 2
def baseEnd_978814 : Nat := 111689345188897470983005

theorem tailTrace_978814 : CollatzResearch.WordTrace tailWord_978814 prefixEnd_978814 111689345188897470983005 := by
  unfold tailWord_978814
  simp only [CollatzResearch.WordTrace]
  refine ⟨4462534934491440120921937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23800186317287680644916997 4462534934491440120921937)
  ·
    refine ⟨3346901200868580090691453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4462534934491440120921937 3346901200868580090691453)
    ·
      refine ⟨1255087950325717534009295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3346901200868580090691453 1255087950325717534009295)
      ·
        refine ⟨1882631925488576301013943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1255087950325717534009295 1882631925488576301013943)
        ·
          refine ⟨2823947888232864451520915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1882631925488576301013943 2823947888232864451520915)
          ·
            refine ⟨4235921832349296677281373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2823947888232864451520915 4235921832349296677281373)
            ·
              refine ⟨1588470687130986253980515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4235921832349296677281373 1588470687130986253980515)
              ·
                refine ⟨2382706030696479380970773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1588470687130986253980515 2382706030696479380970773)
                ·
                  refine ⟨111689345188897470983005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2382706030696479380970773 111689345188897470983005)
                  ·
                    rfl

theorem cell22_978814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_978814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_978814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_978814 prefixEnd_978814 := by exact prefixLift 978814
  have htrace : WordTrace (prefixWord ++ tailWord_978814) baseStart_978814 baseEnd_978814 := by
    simpa [prefixWord, tailWord_978814, baseEnd_978814] using wordTrace_append hprefix tailTrace_978814
  have hstable : (prefixWord ++ tailWord_978814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978814).length < 2 ^ (prefixWord ++ tailWord_978814).sum := by decide
  have hdescent : baseEnd_978814 < baseStart_978814 := by decide
  rcases family_descends (prefixWord ++ tailWord_978814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978825 : List Nat := [1, 2, 1, 1, 5, 1, 4, 7]
def baseStart_978825 : Nat := 118140960795 + 978825 * 2 ^ 59
def prefixEnd_978825 : Nat := 4983230072969 + 3 ^ 40 * 978825 * 2
def baseEnd_978825 : Nat := 37230200121276894547109

theorem tailTrace_978825 : CollatzResearch.WordTrace tailWord_978825 prefixEnd_978825 37230200121276894547109 := by
  unfold tailWord_978825
  simp only [CollatzResearch.WordTrace]
  refine ⟨35700680678891669846025929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23800453785927779897350619 35700680678891669846025929)
  ·
    refine ⟨26775510509168752384519447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35700680678891669846025929 26775510509168752384519447)
    ·
      refine ⟨40163265763753128576779171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26775510509168752384519447 40163265763753128576779171)
      ·
        refine ⟨60244898645629692865168757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40163265763753128576779171 60244898645629692865168757)
        ·
          refine ⟨5647959248027783706109571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60244898645629692865168757 5647959248027783706109571)
          ·
            refine ⟨8471938872041675559164357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5647959248027783706109571 8471938872041675559164357)
            ·
              refine ⟨1588488538507814167343317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8471938872041675559164357 1588488538507814167343317)
              ·
                refine ⟨37230200121276894547109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1588488538507814167343317 37230200121276894547109)
                ·
                  rfl

theorem cell22_978825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 7].length) (baseStart_978825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_978825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_978825 prefixEnd_978825 := by exact prefixLift 978825
  have htrace : WordTrace (prefixWord ++ tailWord_978825) baseStart_978825 baseEnd_978825 := by
    simpa [prefixWord, tailWord_978825, baseEnd_978825] using wordTrace_append hprefix tailTrace_978825
  have hstable : (prefixWord ++ tailWord_978825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978825).length < 2 ^ (prefixWord ++ tailWord_978825).sum := by decide
  have hdescent : baseEnd_978825 < baseStart_978825 := by decide
  rcases family_descends (prefixWord ++ tailWord_978825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978844 : List Nat := [2, 2, 3, 3, 1, 2, 2, 1, 2, 4]
def baseStart_978844 : Nat := 118140960795 + 978844 * 2 ^ 59
def prefixEnd_978844 : Nat := 4983230072969 + 3 ^ 40 * 978844 * 2
def baseEnd_978844 : Nat := 335078305179782334698923

theorem tailTrace_978844 : CollatzResearch.WordTrace tailWord_978844 prefixEnd_978844 335078305179782334698923 := by
  unfold tailWord_978844
  simp only [CollatzResearch.WordTrace]
  refine ⟨17850686832911418045483793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23800915777215224060645057 17850686832911418045483793)
  ·
    refine ⟨13388015124683563534112845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17850686832911418045483793 13388015124683563534112845)
    ·
      refine ⟨5020505671756336325292317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13388015124683563534112845 5020505671756336325292317)
      ·
        refine ⟨1882689626908626121984619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5020505671756336325292317 1882689626908626121984619)
        ·
          refine ⟨2824034440362939182976929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1882689626908626121984619 2824034440362939182976929)
          ·
            refine ⟨2118025830272204387232697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2824034440362939182976929 2118025830272204387232697)
            ·
              refine ⟨1588519372704153290424523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2118025830272204387232697 1588519372704153290424523)
              ·
                refine ⟨2382779059056229935636785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1588519372704153290424523 2382779059056229935636785)
                ·
                  refine ⟨1787084294292172451727589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2382779059056229935636785 1787084294292172451727589)
                  ·
                    refine ⟨335078305179782334698923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1787084294292172451727589 335078305179782334698923)
                    ·
                      rfl

theorem cell22_978844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_978844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_978844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_978844 prefixEnd_978844 := by exact prefixLift 978844
  have htrace : WordTrace (prefixWord ++ tailWord_978844) baseStart_978844 baseEnd_978844 := by
    simpa [prefixWord, tailWord_978844, baseEnd_978844] using wordTrace_append hprefix tailTrace_978844
  have hstable : (prefixWord ++ tailWord_978844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978844).length < 2 ^ (prefixWord ++ tailWord_978844).sum := by decide
  have hdescent : baseEnd_978844 < baseStart_978844 := by decide
  rcases family_descends (prefixWord ++ tailWord_978844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978846 : List Nat := [4, 3, 1, 3, 1, 1, 1, 2, 1, 5]
def baseStart_978846 : Nat := 118140960795 + 978846 * 2 ^ 59
def prefixEnd_978846 : Nat := 4983230072969 + 3 ^ 40 * 978846 * 2
def baseEnd_978846 : Nat := 335078989820654996148917

theorem tailTrace_978846 : CollatzResearch.WordTrace tailWord_978846 prefixEnd_978846 335078989820654996148917 := by
  unfold tailWord_978846
  simp only [CollatzResearch.WordTrace]
  refine ⟨4462680826476948804067549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23800964407877060288360261 4462680826476948804067549)
  ·
    refine ⟨1673505309928855801525331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4462680826476948804067549 1673505309928855801525331)
    ·
      refine ⟨2510257964893283702287997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1673505309928855801525331 2510257964893283702287997)
      ·
        refine ⟨941346736834981388357999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2510257964893283702287997 941346736834981388357999)
        ·
          refine ⟨1412020105252472082536999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941346736834981388357999 1412020105252472082536999)
          ·
            refine ⟨2118030157878708123805499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1412020105252472082536999 2118030157878708123805499)
            ·
              refine ⟨3177045236818062185708249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2118030157878708123805499 3177045236818062185708249)
              ·
                refine ⟨2382783927613546639281187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3177045236818062185708249 2382783927613546639281187)
                ·
                  refine ⟨3574175891420319958921781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2382783927613546639281187 3574175891420319958921781)
                  ·
                    refine ⟨335078989820654996148917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3574175891420319958921781 335078989820654996148917)
                    ·
                      rfl

theorem cell22_978846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_978846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_978846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_978846 prefixEnd_978846 := by exact prefixLift 978846
  have htrace : WordTrace (prefixWord ++ tailWord_978846) baseStart_978846 baseEnd_978846 := by
    simpa [prefixWord, tailWord_978846, baseEnd_978846] using wordTrace_append hprefix tailTrace_978846
  have hstable : (prefixWord ++ tailWord_978846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978846).length < 2 ^ (prefixWord ++ tailWord_978846).sum := by decide
  have hdescent : baseEnd_978846 < baseStart_978846 := by decide
  rcases family_descends (prefixWord ++ tailWord_978846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978876 : List Nat := [2, 2, 2, 5, 2, 1, 1, 7]
def baseStart_978876 : Nat := 118140960795 + 978876 * 2 ^ 59
def prefixEnd_978876 : Nat := 4983230072969 + 3 ^ 40 * 978876 * 2
def baseEnd_978876 : Nat := 37232139937082768655425

theorem tailTrace_978876 : CollatzResearch.WordTrace tailWord_978876 prefixEnd_978876 37232139937082768655425 := by
  unfold tailWord_978876
  simp only [CollatzResearch.WordTrace]
  refine ⟨17851270400853452778066241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23801693867804603704088321 17851270400853452778066241)
  ·
    refine ⟨13388452800640089583549681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17851270400853452778066241 13388452800640089583549681)
    ·
      refine ⟨10041339600480067187662261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13388452800640089583549681 10041339600480067187662261)
      ·
        refine ⟨941375587545006298843337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10041339600480067187662261 941375587545006298843337)
        ·
          refine ⟨706031690658754724132503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 941375587545006298843337 706031690658754724132503)
          ·
            refine ⟨1059047535988132086198755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706031690658754724132503 1059047535988132086198755)
            ·
              refine ⟨1588571303982198129298133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1059047535988132086198755 1588571303982198129298133)
              ·
                refine ⟨37232139937082768655425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1588571303982198129298133 37232139937082768655425)
                ·
                  rfl

theorem cell22_978876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 7].length) (baseStart_978876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_978876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_978876 prefixEnd_978876 := by exact prefixLift 978876
  have htrace : WordTrace (prefixWord ++ tailWord_978876) baseStart_978876 baseEnd_978876 := by
    simpa [prefixWord, tailWord_978876, baseEnd_978876] using wordTrace_append hprefix tailTrace_978876
  have hstable : (prefixWord ++ tailWord_978876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978876).length < 2 ^ (prefixWord ++ tailWord_978876).sum := by decide
  have hdescent : baseEnd_978876 < baseStart_978876 := by decide
  rcases family_descends (prefixWord ++ tailWord_978876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978960 : List Nat := [2, 1, 1, 1, 1, 1, 1, 14]
def baseStart_978960 : Nat := 118140960795 + 978960 * 2 ^ 59
def prefixEnd_978960 : Nat := 4983230072969 + 3 ^ 40 * 978960 * 2
def baseEnd_978960 : Nat := 37235334927821855422063

theorem tailTrace_978960 : CollatzResearch.WordTrace tailWord_978960 prefixEnd_978960 37235334927821855422063 := by
  unfold tailWord_978960
  simp only [CollatzResearch.WordTrace]
  refine ⟨17852802266701293951095167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23803736355601725268126889 17852802266701293951095167)
  ·
    refine ⟨26779203400051940926642751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17852802266701293951095167 26779203400051940926642751)
    ·
      refine ⟨40168805100077911389964127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26779203400051940926642751 40168805100077911389964127)
      ·
        refine ⟨60253207650116867084946191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40168805100077911389964127 60253207650116867084946191)
        ·
          refine ⟨90379811475175300627419287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60253207650116867084946191 90379811475175300627419287)
          ·
            refine ⟨135569717212762950941128931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90379811475175300627419287 135569717212762950941128931)
            ·
              refine ⟨203354575819144426411693397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135569717212762950941128931 203354575819144426411693397)
              ·
                refine ⟨37235334927821855422063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 203354575819144426411693397 37235334927821855422063)
                ·
                  rfl

theorem cell22_978960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 14].length) (baseStart_978960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_978960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_978960 prefixEnd_978960 := by exact prefixLift 978960
  have htrace : WordTrace (prefixWord ++ tailWord_978960) baseStart_978960 baseEnd_978960 := by
    simpa [prefixWord, tailWord_978960, baseEnd_978960] using wordTrace_append hprefix tailTrace_978960
  have hstable : (prefixWord ++ tailWord_978960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978960).length < 2 ^ (prefixWord ++ tailWord_978960).sum := by decide
  have hdescent : baseEnd_978960 < baseStart_978960 := by decide
  rcases family_descends (prefixWord ++ tailWord_978960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_978983 : List Nat := [1, 1, 7, 1, 3, 1, 1, 1, 6]
def baseStart_978983 : Nat := 118140960795 + 978983 * 2 ^ 59
def prefixEnd_978983 : Nat := 4983230072969 + 3 ^ 40 * 978983 * 2
def baseEnd_978983 : Nat := 111708629240144101824499

theorem tailTrace_978983 : CollatzResearch.WordTrace tailWord_978983 prefixEnd_978983 111708629240144101824499 := by
  unfold tailWord_978983
  simp only [CollatzResearch.WordTrace]
  refine ⟨35706443412319262830277603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23804295608212841886851735 35706443412319262830277603)
  ·
    refine ⟨53559665118478894245416405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35706443412319262830277603 53559665118478894245416405)
    ·
      refine ⟨1255304651214349083876947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 53559665118478894245416405 1255304651214349083876947)
      ·
        refine ⟨1882956976821523625815421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1255304651214349083876947 1882956976821523625815421)
        ·
          refine ⟨706108866308071359680783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1882956976821523625815421 706108866308071359680783)
          ·
            refine ⟨1059163299462107039521175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706108866308071359680783 1059163299462107039521175)
            ·
              refine ⟨1588744949193160559281763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1059163299462107039521175 1588744949193160559281763)
              ·
                refine ⟨2383117423789740838922645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1588744949193160559281763 2383117423789740838922645)
                ·
                  refine ⟨111708629240144101824499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2383117423789740838922645 111708629240144101824499)
                  ·
                    rfl

theorem cell22_978983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 6].length) (baseStart_978983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_978983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_978983 prefixEnd_978983 := by exact prefixLift 978983
  have htrace : WordTrace (prefixWord ++ tailWord_978983) baseStart_978983 baseEnd_978983 := by
    simpa [prefixWord, tailWord_978983, baseEnd_978983] using wordTrace_append hprefix tailTrace_978983
  have hstable : (prefixWord ++ tailWord_978983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_978983).length < 2 ^ (prefixWord ++ tailWord_978983).sum := by decide
  have hdescent : baseEnd_978983 < baseStart_978983 := by decide
  rcases family_descends (prefixWord ++ tailWord_978983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979043 : List Nat := [1, 1, 1, 5, 1, 1, 6, 2, 1, 3]
def baseStart_979043 : Nat := 118140960795 + 979043 * 2 ^ 59
def prefixEnd_979043 : Nat := 4983230072969 + 3 ^ 40 * 979043 * 2
def baseEnd_979043 : Nat := 335146426946612148973313

theorem tailTrace_979043 : CollatzResearch.WordTrace tailWord_979043 prefixEnd_979043 335146426946612148973313 := by
  unfold tailWord_979043
  simp only [CollatzResearch.WordTrace]
  refine ⟨35708631792101893077461783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23805754528067928718307855 35708631792101893077461783)
  ·
    refine ⟨53562947688152839616192675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35708631792101893077461783 53562947688152839616192675)
    ·
      refine ⟨80344421532229259424289013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53562947688152839616192675 80344421532229259424289013)
      ·
        refine ⟨7532289518646493071027095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80344421532229259424289013 7532289518646493071027095)
        ·
          refine ⟨11298434277969739606540643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7532289518646493071027095 11298434277969739606540643)
          ·
            refine ⟨16947651416954609409810965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11298434277969739606540643 16947651416954609409810965)
            ·
              refine ⟨794421160169747316084889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16947651416954609409810965 794421160169747316084889)
              ·
                refine ⟨595815870127310487063667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 794421160169747316084889 595815870127310487063667)
                ·
                  refine ⟨893723805190965730595501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 595815870127310487063667 893723805190965730595501)
                  ·
                    refine ⟨335146426946612148973313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 893723805190965730595501 335146426946612148973313)
                    ·
                      rfl

theorem cell22_979043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 2, 1, 3].length) (baseStart_979043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_979043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_979043 prefixEnd_979043 := by exact prefixLift 979043
  have htrace : WordTrace (prefixWord ++ tailWord_979043) baseStart_979043 baseEnd_979043 := by
    simpa [prefixWord, tailWord_979043, baseEnd_979043] using wordTrace_append hprefix tailTrace_979043
  have hstable : (prefixWord ++ tailWord_979043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979043).length < 2 ^ (prefixWord ++ tailWord_979043).sum := by decide
  have hdescent : baseEnd_979043 < baseStart_979043 := by decide
  rcases family_descends (prefixWord ++ tailWord_979043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979054 : List Nat := [4, 1, 2, 2, 1, 1, 3, 1, 2, 5]
def baseStart_979054 : Nat := 118140960795 + 979054 * 2 ^ 59
def prefixEnd_979054 : Nat := 4983230072969 + 3 ^ 40 * 979054 * 2
def baseEnd_979054 : Nat := 335150192471411786948279

theorem tailTrace_979054 : CollatzResearch.WordTrace tailWord_979054 prefixEnd_979054 335150192471411786948279 := by
  unfold tailWord_979054
  simp only [CollatzResearch.WordTrace]
  refine ⟨4463629124382755244514027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23806021996708027970741477 4463629124382755244514027)
  ·
    refine ⟨6695443686574132866771041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4463629124382755244514027 6695443686574132866771041)
    ·
      refine ⟨5021582764930599650078281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6695443686574132866771041 5021582764930599650078281)
      ·
        refine ⟨3766187073697949737558711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5021582764930599650078281 3766187073697949737558711)
        ·
          refine ⟨5649280610546924606338067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3766187073697949737558711 5649280610546924606338067)
          ·
            refine ⟨8473920915820386909507101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5649280610546924606338067 8473920915820386909507101)
            ·
              refine ⟨3177720343432645091065163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8473920915820386909507101 3177720343432645091065163)
              ·
                refine ⟨4766580515148967636597745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3177720343432645091065163 4766580515148967636597745)
                ·
                  refine ⟨3574935386361725727448309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4766580515148967636597745 3574935386361725727448309)
                  ·
                    refine ⟨335150192471411786948279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3574935386361725727448309 335150192471411786948279)
                    ·
                      rfl

theorem cell22_979054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_979054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_979054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_979054 prefixEnd_979054 := by exact prefixLift 979054
  have htrace : WordTrace (prefixWord ++ tailWord_979054) baseStart_979054 baseEnd_979054 := by
    simpa [prefixWord, tailWord_979054, baseEnd_979054] using wordTrace_append hprefix tailTrace_979054
  have hstable : (prefixWord ++ tailWord_979054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979054).length < 2 ^ (prefixWord ++ tailWord_979054).sum := by decide
  have hdescent : baseEnd_979054 < baseStart_979054 := by decide
  rcases family_descends (prefixWord ++ tailWord_979054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979069 : List Nat := [1, 4, 1, 1, 3, 2, 2, 1, 3, 4]
def baseStart_979069 : Nat := 118140960795 + 979069 * 2 ^ 59
def prefixEnd_979069 : Nat := 4983230072969 + 3 ^ 40 * 979069 * 2
def baseEnd_979069 : Nat := 335155327277956747823233

theorem tailTrace_979069 : CollatzResearch.WordTrace tailWord_979069 prefixEnd_979069 335155327277956747823233 := by
  unfold tailWord_979069
  simp only [CollatzResearch.WordTrace]
  refine ⟨35709580090007699517908261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23806386726671799678605507 35709580090007699517908261)
  ·
    refine ⟨6695546266876443659607799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35709580090007699517908261 6695546266876443659607799)
    ·
      refine ⟨10043319400314665489411699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6695546266876443659607799 10043319400314665489411699)
      ·
        refine ⟨15064979100471998234117549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10043319400314665489411699 15064979100471998234117549)
        ·
          refine ⟨5649367162676999337794081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15064979100471998234117549 5649367162676999337794081)
          ·
            refine ⟨4237025372007749503345561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5649367162676999337794081 4237025372007749503345561)
            ·
              refine ⟨3177769029005812127509171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4237025372007749503345561 3177769029005812127509171)
              ·
                refine ⟨4766653543508718191263757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3177769029005812127509171 4766653543508718191263757)
                ·
                  refine ⟨1787495078815769321723909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4766653543508718191263757 1787495078815769321723909)
                  ·
                    refine ⟨335155327277956747823233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1787495078815769321723909 335155327277956747823233)
                    ·
                      rfl

theorem cell22_979069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_979069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_979069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_979069 prefixEnd_979069 := by exact prefixLift 979069
  have htrace : WordTrace (prefixWord ++ tailWord_979069) baseStart_979069 baseEnd_979069 := by
    simpa [prefixWord, tailWord_979069, baseEnd_979069] using wordTrace_append hprefix tailTrace_979069
  have hstable : (prefixWord ++ tailWord_979069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979069).length < 2 ^ (prefixWord ++ tailWord_979069).sum := by decide
  have hdescent : baseEnd_979069 < baseStart_979069 := by decide
  rcases family_descends (prefixWord ++ tailWord_979069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979094 : List Nat := [5, 3, 2, 1, 1, 1, 2, 1, 3, 3]
def baseStart_979094 : Nat := 118140960795 + 979094 * 2 ^ 59
def prefixEnd_979094 : Nat := 4983230072969 + 3 ^ 40 * 979094 * 2
def baseEnd_979094 : Nat := 335163885288865015948157

theorem tailTrace_979094 : CollatzResearch.WordTrace tailWord_979094 prefixEnd_979094 335163885288865015948157 := by
  unfold tailWord_979094
  simp only [CollatzResearch.WordTrace]
  refine ⟨2231905744682320549223021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23806994609944752525045557 2231905744682320549223021)
  ·
    refine ⟨836964654255870205958633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2231905744682320549223021 836964654255870205958633)
    ·
      refine ⟨627723490691902654468975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 836964654255870205958633 627723490691902654468975)
      ·
        refine ⟨941585236037853981703463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627723490691902654468975 941585236037853981703463)
        ·
          refine ⟨1412377854056780972555195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941585236037853981703463 1412377854056780972555195)
          ·
            refine ⟨2118566781085171458832793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1412377854056780972555195 2118566781085171458832793)
            ·
              refine ⟨1588925085813878594124595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2118566781085171458832793 1588925085813878594124595)
              ·
                refine ⟨2383387628720817891186893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1588925085813878594124595 2383387628720817891186893)
                ·
                  refine ⟨893770360770306709195085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2383387628720817891186893 893770360770306709195085)
                  ·
                    refine ⟨335163885288865015948157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 893770360770306709195085 335163885288865015948157)
                    ·
                      rfl

theorem cell22_979094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_979094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_979094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_979094 prefixEnd_979094 := by exact prefixLift 979094
  have htrace : WordTrace (prefixWord ++ tailWord_979094) baseStart_979094 baseEnd_979094 := by
    simpa [prefixWord, tailWord_979094, baseEnd_979094] using wordTrace_append hprefix tailTrace_979094
  have hstable : (prefixWord ++ tailWord_979094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979094).length < 2 ^ (prefixWord ++ tailWord_979094).sum := by decide
  have hdescent : baseEnd_979094 < baseStart_979094 := by decide
  rcases family_descends (prefixWord ++ tailWord_979094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979101 : List Nat := [1, 4, 2, 1, 1, 3, 2, 4, 4]
def baseStart_979101 : Nat := 118140960795 + 979101 * 2 ^ 59
def prefixEnd_979101 : Nat := 4983230072969 + 3 ^ 40 * 979101 * 2
def baseEnd_979101 : Nat := 111722093843973110341045

theorem tailTrace_979101 : CollatzResearch.WordTrace tailWord_979101 prefixEnd_979101 111722093843973110341045 := by
  unfold tailWord_979101
  simp only [CollatzResearch.WordTrace]
  refine ⟨35710747225891768983073157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23807164817261179322048771 35710747225891768983073157)
  ·
    refine ⟨6695765104854706684326217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35710747225891768983073157 6695765104854706684326217)
    ·
      refine ⟨5021823828641030013244663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6695765104854706684326217 5021823828641030013244663)
      ·
        refine ⟨7532735742961545019866995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5021823828641030013244663 7532735742961545019866995)
        ·
          refine ⟨11299103614442317529800493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7532735742961545019866995 11299103614442317529800493)
          ·
            refine ⟨4237163855415869073675185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11299103614442317529800493 4237163855415869073675185)
            ·
              refine ⟨3177872891561901805256389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4237163855415869073675185 3177872891561901805256389)
              ·
                refine ⟨595851167167856588485573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3177872891561901805256389 595851167167856588485573)
                ·
                  refine ⟨111722093843973110341045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 595851167167856588485573 111722093843973110341045)
                  ·
                    rfl

theorem cell22_979101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_979101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_979101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_979101 prefixEnd_979101 := by exact prefixLift 979101
  have htrace : WordTrace (prefixWord ++ tailWord_979101) baseStart_979101 baseEnd_979101 := by
    simpa [prefixWord, tailWord_979101, baseEnd_979101] using wordTrace_append hprefix tailTrace_979101
  have hstable : (prefixWord ++ tailWord_979101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979101).length < 2 ^ (prefixWord ++ tailWord_979101).sum := by decide
  have hdescent : baseEnd_979101 < baseStart_979101 := by decide
  rcases family_descends (prefixWord ++ tailWord_979101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979148 : List Nat := [2, 2, 1, 6, 1, 1, 1, 2, 2, 4]
def baseStart_979148 : Nat := 118140960795 + 979148 * 2 ^ 59
def prefixEnd_979148 : Nat := 4983230072969 + 3 ^ 40 * 979148 * 2
def baseEnd_979148 : Nat := 335182370592426875097991

theorem tailTrace_979148 : CollatzResearch.WordTrace tailWord_979148 prefixEnd_979148 335182370592426875097991 := by
  unfold tailWord_979148
  simp only [CollatzResearch.WordTrace]
  refine ⟨17856230728360748005017049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23808307637814330673356065 17856230728360748005017049)
  ·
    refine ⟨13392173046270561003762787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17856230728360748005017049 13392173046270561003762787)
    ·
      refine ⟨20088259569405841505644181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13392173046270561003762787 20088259569405841505644181)
      ·
        refine ⟨941637167315898820577071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20088259569405841505644181 941637167315898820577071)
        ·
          refine ⟨1412455750973848230865607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941637167315898820577071 1412455750973848230865607)
          ·
            refine ⟨2118683626460772346298411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1412455750973848230865607 2118683626460772346298411)
            ·
              refine ⟨3178025439691158519447617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2118683626460772346298411 3178025439691158519447617)
              ·
                refine ⟨2383519079768368889585713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3178025439691158519447617 2383519079768368889585713)
                ·
                  refine ⟨1787639309826276667189285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2383519079768368889585713 1787639309826276667189285)
                  ·
                    refine ⟨335182370592426875097991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1787639309826276667189285 335182370592426875097991)
                    ·
                      rfl

theorem cell22_979148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 2, 4].length) (baseStart_979148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_979148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_979148 prefixEnd_979148 := by exact prefixLift 979148
  have htrace : WordTrace (prefixWord ++ tailWord_979148) baseStart_979148 baseEnd_979148 := by
    simpa [prefixWord, tailWord_979148, baseEnd_979148] using wordTrace_append hprefix tailTrace_979148
  have hstable : (prefixWord ++ tailWord_979148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979148).length < 2 ^ (prefixWord ++ tailWord_979148).sum := by decide
  have hdescent : baseEnd_979148 < baseStart_979148 := by decide
  rcases family_descends (prefixWord ++ tailWord_979148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979161 : List Nat := [1, 2, 1, 2, 3, 1, 5, 1, 3, 3]
def baseStart_979161 : Nat := 118140960795 + 979161 * 2 ^ 59
def prefixEnd_979161 : Nat := 4983230072969 + 3 ^ 40 * 979161 * 2
def baseEnd_979161 : Nat := 335186820758099174522951

theorem tailTrace_979161 : CollatzResearch.WordTrace tailWord_979161 prefixEnd_979161 335186820758099174522951 := by
  unfold tailWord_979161
  simp only [CollatzResearch.WordTrace]
  refine ⟨35712935605674399230257337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23808623737116266153504891 35712935605674399230257337)
  ·
    refine ⟨26784701704255799422693003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35712935605674399230257337 26784701704255799422693003)
    ·
      refine ⟨40177052556383699134039505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26784701704255799422693003 40177052556383699134039505)
      ·
        refine ⟨30132789417287774350529629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40177052556383699134039505 30132789417287774350529629)
        ·
          refine ⟨11299796031482915381448611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30132789417287774350529629 11299796031482915381448611)
          ·
            refine ⟨16949694047224373072172917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11299796031482915381448611 16949694047224373072172917)
            ·
              refine ⟨1589033816927284975516211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16949694047224373072172917 1589033816927284975516211)
              ·
                refine ⟨2383550725390927463274317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1589033816927284975516211 2383550725390927463274317)
                ·
                  refine ⟨893831522021597798727869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2383550725390927463274317 893831522021597798727869)
                  ·
                    refine ⟨335186820758099174522951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 893831522021597798727869 335186820758099174522951)
                    ·
                      rfl

theorem cell22_979161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 3, 3].length) (baseStart_979161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_979161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_979161 prefixEnd_979161 := by exact prefixLift 979161
  have htrace : WordTrace (prefixWord ++ tailWord_979161) baseStart_979161 baseEnd_979161 := by
    simpa [prefixWord, tailWord_979161, baseEnd_979161] using wordTrace_append hprefix tailTrace_979161
  have hstable : (prefixWord ++ tailWord_979161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979161).length < 2 ^ (prefixWord ++ tailWord_979161).sum := by decide
  have hdescent : baseEnd_979161 < baseStart_979161 := by decide
  rcases family_descends (prefixWord ++ tailWord_979161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979236 : List Nat := [2, 3, 1, 3, 1, 3, 1, 2, 6]
def baseStart_979236 : Nat := 118140960795 + 979236 * 2 ^ 59
def prefixEnd_979236 : Nat := 4983230072969 + 3 ^ 40 * 979236 * 2
def baseEnd_979236 : Nat := 111737498263607992965907

theorem tailTrace_979236 : CollatzResearch.WordTrace tailWord_979236 prefixEnd_979236 111737498263607992965907 := by
  unfold tailWord_979236
  simp only [CollatzResearch.WordTrace]
  refine ⟨17857835540201343519618781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23810447386935124692825041 17857835540201343519618781)
  ·
    refine ⟨6696688327575503819857043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17857835540201343519618781 6696688327575503819857043)
    ·
      refine ⟨10045032491363255729785565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6696688327575503819857043 10045032491363255729785565)
      ·
        refine ⟨3766887184261220898669587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10045032491363255729785565 3766887184261220898669587)
        ·
          refine ⟨5650330776391831348004381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3766887184261220898669587 5650330776391831348004381)
          ·
            refine ⟨2118874041146936755501643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5650330776391831348004381 2118874041146936755501643)
            ·
              refine ⟨3178311061720405133252465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2118874041146936755501643 3178311061720405133252465)
              ·
                refine ⟨2383733296290303849939349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3178311061720405133252465 2383733296290303849939349)
                ·
                  refine ⟨111737498263607992965907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2383733296290303849939349 111737498263607992965907)
                  ·
                    rfl

theorem cell22_979236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_979236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_979236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_979236 prefixEnd_979236 := by exact prefixLift 979236
  have htrace : WordTrace (prefixWord ++ tailWord_979236) baseStart_979236 baseEnd_979236 := by
    simpa [prefixWord, tailWord_979236, baseEnd_979236] using wordTrace_append hprefix tailTrace_979236
  have hstable : (prefixWord ++ tailWord_979236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979236).length < 2 ^ (prefixWord ++ tailWord_979236).sum := by decide
  have hdescent : baseEnd_979236 < baseStart_979236 := by decide
  rcases family_descends (prefixWord ++ tailWord_979236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979251 : List Nat := [1, 1, 1, 2, 5, 1, 2, 2, 4, 3]
def baseStart_979251 : Nat := 118140960795 + 979251 * 2 ^ 59
def prefixEnd_979251 : Nat := 4983230072969 + 3 ^ 40 * 979251 * 2
def baseEnd_979251 : Nat := 335217629597368939772675

theorem tailTrace_979251 : CollatzResearch.WordTrace tailWord_979251 prefixEnd_979251 335217629597368939772675 := by
  unfold tailWord_979251
  simp only [CollatzResearch.WordTrace]
  refine ⟨35716218175348344601033607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23810812116898896400689071 35716218175348344601033607)
  ·
    refine ⟨53574327263022516901550411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35716218175348344601033607 53574327263022516901550411)
    ·
      refine ⟨80361490894533775352325617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53574327263022516901550411 80361490894533775352325617)
      ·
        refine ⟨60271118170900331514244213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80361490894533775352325617 60271118170900331514244213)
        ·
          refine ⟨5650417328521906079460395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60271118170900331514244213 5650417328521906079460395)
          ·
            refine ⟨8475625992782859119190593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5650417328521906079460395 8475625992782859119190593)
            ·
              refine ⟨6356719494587144339392945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8475625992782859119190593 6356719494587144339392945)
              ·
                refine ⟨4767539620940358254544709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6356719494587144339392945 4767539620940358254544709)
                ·
                  refine ⟨893913678926317172727133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4767539620940358254544709 893913678926317172727133)
                  ·
                    refine ⟨335217629597368939772675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 893913678926317172727133 335217629597368939772675)
                    ·
                      rfl

theorem cell22_979251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 4, 3].length) (baseStart_979251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_979251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_979251 prefixEnd_979251 := by exact prefixLift 979251
  have htrace : WordTrace (prefixWord ++ tailWord_979251) baseStart_979251 baseEnd_979251 := by
    simpa [prefixWord, tailWord_979251, baseEnd_979251] using wordTrace_append hprefix tailTrace_979251
  have hstable : (prefixWord ++ tailWord_979251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979251).length < 2 ^ (prefixWord ++ tailWord_979251).sum := by decide
  have hdescent : baseEnd_979251 < baseStart_979251 := by decide
  rcases family_descends (prefixWord ++ tailWord_979251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979253 : List Nat := [1, 3, 3, 1, 2, 1, 4, 3, 4]
def baseStart_979253 : Nat := 118140960795 + 979253 * 2 ^ 59
def prefixEnd_979253 : Nat := 4983230072969 + 3 ^ 40 * 979253 * 2
def baseEnd_979253 : Nat := 111739438079413867074223

theorem tailTrace_979253 : CollatzResearch.WordTrace tailWord_979253 prefixEnd_979253 111739438079413867074223 := by
  unfold tailWord_979253
  simp only [CollatzResearch.WordTrace]
  refine ⟨35716291121341098942606413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23810860747560732628404275 35716291121341098942606413)
  ·
    refine ⟨13393609170502912103477405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35716291121341098942606413 13393609170502912103477405)
    ·
      refine ⟨5022603438938592038804027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13393609170502912103477405 5022603438938592038804027)
      ·
        refine ⟨7533905158407888058206041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5022603438938592038804027 7533905158407888058206041)
        ·
          refine ⟨5650428868805916043654531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7533905158407888058206041 5650428868805916043654531)
          ·
            refine ⟨8475643303208874065481797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5650428868805916043654531 8475643303208874065481797)
            ·
              refine ⟨1589183119351663887277837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8475643303208874065481797 1589183119351663887277837)
              ·
                refine ⟨595943669756873957729189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1589183119351663887277837 595943669756873957729189)
                ·
                  refine ⟨111739438079413867074223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 595943669756873957729189 111739438079413867074223)
                  ·
                    rfl

theorem cell22_979253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 3, 4].length) (baseStart_979253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_979253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_979253 prefixEnd_979253 := by exact prefixLift 979253
  have htrace : WordTrace (prefixWord ++ tailWord_979253) baseStart_979253 baseEnd_979253 := by
    simpa [prefixWord, tailWord_979253, baseEnd_979253] using wordTrace_append hprefix tailTrace_979253
  have hstable : (prefixWord ++ tailWord_979253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979253).length < 2 ^ (prefixWord ++ tailWord_979253).sum := by decide
  have hdescent : baseEnd_979253 < baseStart_979253 := by decide
  rcases family_descends (prefixWord ++ tailWord_979253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979285 : List Nat := [1, 3, 2, 2, 5, 1, 1, 1, 1, 5]
def baseStart_979285 : Nat := 118140960795 + 979285 * 2 ^ 59
def prefixEnd_979285 : Nat := 4983230072969 + 3 ^ 40 * 979285 * 2
def baseEnd_979285 : Nat := 335229268492204184422571

theorem tailTrace_979285 : CollatzResearch.WordTrace tailWord_979285 prefixEnd_979285 335229268492204184422571 := by
  unfold tailWord_979285
  simp only [CollatzResearch.WordTrace]
  refine ⟨35717458257225168407771309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23811638838150112271847539 35717458257225168407771309)
  ·
    refine ⟨13394046846459438152914241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35717458257225168407771309 13394046846459438152914241)
    ·
      refine ⟨10045535134844578614685681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13394046846459438152914241 10045535134844578614685681)
      ·
        refine ⟨7534151351133433961014261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10045535134844578614685681 7534151351133433961014261)
        ·
          refine ⟨706326689168759433845087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7534151351133433961014261 706326689168759433845087)
          ·
            refine ⟨1059490033753139150767631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706326689168759433845087 1059490033753139150767631)
            ·
              refine ⟨1589235050629708726151447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1059490033753139150767631 1589235050629708726151447)
              ·
                refine ⟨2383852575944563089227171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1589235050629708726151447 2383852575944563089227171)
                ·
                  refine ⟨3575778863916844633840757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2383852575944563089227171 3575778863916844633840757)
                  ·
                    refine ⟨335229268492204184422571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3575778863916844633840757 335229268492204184422571)
                    ·
                      rfl

theorem cell22_979285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 1, 5].length) (baseStart_979285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_979285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_979285 prefixEnd_979285 := by exact prefixLift 979285
  have htrace : WordTrace (prefixWord ++ tailWord_979285) baseStart_979285 baseEnd_979285 := by
    simpa [prefixWord, tailWord_979285, baseEnd_979285] using wordTrace_append hprefix tailTrace_979285
  have hstable : (prefixWord ++ tailWord_979285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979285).length < 2 ^ (prefixWord ++ tailWord_979285).sum := by decide
  have hdescent : baseEnd_979285 < baseStart_979285 := by decide
  rcases family_descends (prefixWord ++ tailWord_979285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979298 : List Nat := [3, 3, 2, 1, 1, 2, 4, 6]
def baseStart_979298 : Nat := 118140960795 + 979298 * 2 ^ 59
def prefixEnd_979298 : Nat := 4983230072969 + 3 ^ 40 * 979298 * 2
def baseEnd_979298 : Nat := 37248190961986275983059

theorem tailTrace_979298 : CollatzResearch.WordTrace tailWord_979298 prefixEnd_979298 37248190961986275983059 := by
  unfold tailWord_979298
  simp only [CollatzResearch.WordTrace]
  refine ⟨8929483101544517906998637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23811954937452047751996365 8929483101544517906998637)
  ·
    refine ⟨3348556163079194215124489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8929483101544517906998637 3348556163079194215124489)
    ·
      refine ⟨2511417122309395661343367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3348556163079194215124489 2511417122309395661343367)
      ·
        refine ⟨3767125683464093492015051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2511417122309395661343367 3767125683464093492015051)
        ·
          refine ⟨5650688525196140238022577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3767125683464093492015051 5650688525196140238022577)
          ·
            refine ⟨4238016393897105178516933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5650688525196140238022577 4238016393897105178516933)
            ·
              refine ⟨794628073855707220971925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4238016393897105178516933 794628073855707220971925)
              ·
                refine ⟨37248190961986275983059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 794628073855707220971925 37248190961986275983059)
                ·
                  rfl

theorem cell22_979298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 6].length) (baseStart_979298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_979298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_979298 prefixEnd_979298 := by exact prefixLift 979298
  have htrace : WordTrace (prefixWord ++ tailWord_979298) baseStart_979298 baseEnd_979298 := by
    simpa [prefixWord, tailWord_979298, baseEnd_979298] using wordTrace_append hprefix tailTrace_979298
  have hstable : (prefixWord ++ tailWord_979298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979298).length < 2 ^ (prefixWord ++ tailWord_979298).sum := by decide
  have hdescent : baseEnd_979298 < baseStart_979298 := by decide
  rcases family_descends (prefixWord ++ tailWord_979298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979381 : List Nat := [1, 3, 3, 2, 4, 1, 2, 2, 1, 3]
def baseStart_979381 : Nat := 118140960795 + 979381 * 2 ^ 59
def prefixEnd_979381 : Nat := 4983230072969 + 3 ^ 40 * 979381 * 2
def baseEnd_979381 : Nat := 335262131254091934022277

theorem tailTrace_979381 : CollatzResearch.WordTrace tailWord_979381 prefixEnd_979381 335262131254091934022277 := by
  unfold tailWord_979381
  simp only [CollatzResearch.WordTrace]
  refine ⟨35720959664877376803265997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23813973109918251202177331 35720959664877376803265997)
  ·
    refine ⟨13395359874329016301224749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35720959664877376803265997 13395359874329016301224749)
    ·
      refine ⟨5023259952873381112959281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13395359874329016301224749 5023259952873381112959281)
      ·
        refine ⟨3767444964655035834719461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5023259952873381112959281 3767444964655035834719461)
        ·
          refine ⟨706395930872819219009899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3767444964655035834719461 706395930872819219009899)
          ·
            refine ⟨1059593896309228828514849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706395930872819219009899 1059593896309228828514849)
            ·
              refine ⟨794695422231921621386137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1059593896309228828514849 794695422231921621386137)
              ·
                refine ⟨596021566673941216039603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 794695422231921621386137 596021566673941216039603)
                ·
                  refine ⟨894032350010911824059405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 596021566673941216039603 894032350010911824059405)
                  ·
                    refine ⟨335262131254091934022277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 894032350010911824059405 335262131254091934022277)
                    ·
                      rfl

theorem cell22_979381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_979381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_979381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_979381 prefixEnd_979381 := by exact prefixLift 979381
  have htrace : WordTrace (prefixWord ++ tailWord_979381) baseStart_979381 baseEnd_979381 := by
    simpa [prefixWord, tailWord_979381, baseEnd_979381] using wordTrace_append hprefix tailTrace_979381
  have hstable : (prefixWord ++ tailWord_979381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979381).length < 2 ^ (prefixWord ++ tailWord_979381).sum := by decide
  have hdescent : baseEnd_979381 < baseStart_979381 := by decide
  rcases family_descends (prefixWord ++ tailWord_979381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979401 : List Nat := [1, 2, 1, 1, 2, 1, 4, 2, 4, 4]
def baseStart_979401 : Nat := 118140960795 + 979401 * 2 ^ 59
def prefixEnd_979401 : Nat := 4983230072969 + 3 ^ 40 * 979401 * 2
def baseEnd_979401 : Nat := 335268977662818548522215

theorem tailTrace_979401 : CollatzResearch.WordTrace tailWord_979401 prefixEnd_979401 335268977662818548522215 := by
  unfold tailWord_979401
  simp only [CollatzResearch.WordTrace]
  refine ⟨35721689124804920218994057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23814459416536613479329371 35721689124804920218994057)
  ·
    refine ⟨26791266843603690164245543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35721689124804920218994057 26791266843603690164245543)
    ·
      refine ⟨40186900265405535246368315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26791266843603690164245543 40186900265405535246368315)
      ·
        refine ⟨60280350398108302869552473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40186900265405535246368315 60280350398108302869552473)
        ·
          refine ⟨45210262798581227152164355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60280350398108302869552473 45210262798581227152164355)
          ·
            refine ⟨67815394197871840728246533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45210262798581227152164355 67815394197871840728246533)
            ·
              refine ⟨12715386412100970136546225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67815394197871840728246533 12715386412100970136546225)
              ·
                refine ⟨9536539809075727602409669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12715386412100970136546225 9536539809075727602409669)
                ·
                  refine ⟨1788101214201698925451813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9536539809075727602409669 1788101214201698925451813)
                  ·
                    refine ⟨335268977662818548522215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1788101214201698925451813 335268977662818548522215)
                    ·
                      rfl

theorem cell22_979401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 4].length) (baseStart_979401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_979401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_979401 prefixEnd_979401 := by exact prefixLift 979401
  have htrace : WordTrace (prefixWord ++ tailWord_979401) baseStart_979401 baseEnd_979401 := by
    simpa [prefixWord, tailWord_979401, baseEnd_979401] using wordTrace_append hprefix tailTrace_979401
  have hstable : (prefixWord ++ tailWord_979401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979401).length < 2 ^ (prefixWord ++ tailWord_979401).sum := by decide
  have hdescent : baseEnd_979401 < baseStart_979401 := by decide
  rcases family_descends (prefixWord ++ tailWord_979401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979437 : List Nat := [1, 5, 1, 3, 1, 1, 3, 2, 2, 3]
def baseStart_979437 : Nat := 118140960795 + 979437 * 2 ^ 59
def prefixEnd_979437 : Nat := 4983230072969 + 3 ^ 40 * 979437 * 2
def baseEnd_979437 : Nat := 335281301198526454622105

theorem tailTrace_979437 : CollatzResearch.WordTrace tailWord_979437 prefixEnd_979437 335281301198526454622105 := by
  unfold tailWord_979437
  simp only [CollatzResearch.WordTrace]
  refine ⟨35723002152674498367304565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23815334768449665578203043 35723002152674498367304565)
  ·
    refine ⟨3349031451813234221934803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35723002152674498367304565 3349031451813234221934803)
    ·
      refine ⟨5023547177719851332902205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3349031451813234221934803 5023547177719851332902205)
      ·
        refine ⟨1883830191644944249838327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5023547177719851332902205 1883830191644944249838327)
        ·
          refine ⟨2825745287467416374757491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1883830191644944249838327 2825745287467416374757491)
          ·
            refine ⟨4238617931201124562136237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2825745287467416374757491 4238617931201124562136237)
            ·
              refine ⟨1589481724200421710801089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4238617931201124562136237 1589481724200421710801089)
              ·
                refine ⟨1192111293150316283100817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1589481724200421710801089 1192111293150316283100817)
                ·
                  refine ⟨894083469862737212325613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1192111293150316283100817 894083469862737212325613)
                  ·
                    refine ⟨335281301198526454622105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 894083469862737212325613 335281301198526454622105)
                    ·
                      rfl

theorem cell22_979437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_979437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_979437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_979437 prefixEnd_979437 := by exact prefixLift 979437
  have htrace : WordTrace (prefixWord ++ tailWord_979437) baseStart_979437 baseEnd_979437 := by
    simpa [prefixWord, tailWord_979437, baseEnd_979437] using wordTrace_append hprefix tailTrace_979437
  have hstable : (prefixWord ++ tailWord_979437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979437).length < 2 ^ (prefixWord ++ tailWord_979437).sum := by decide
  have hdescent : baseEnd_979437 < baseStart_979437 := by decide
  rcases family_descends (prefixWord ++ tailWord_979437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979482 : List Nat := [3, 1, 1, 3, 1, 1, 5, 3, 1, 3]
def baseStart_979482 : Nat := 118140960795 + 979482 * 2 ^ 59
def prefixEnd_979482 : Nat := 4983230072969 + 3 ^ 40 * 979482 * 2
def baseEnd_979482 : Nat := 335296705618161337246967

theorem tailTrace_979482 : CollatzResearch.WordTrace tailWord_979482 prefixEnd_979482 335296705618161337246967 := by
  unfold tailWord_979482
  simp only [CollatzResearch.WordTrace]
  refine ⟨8931160859377867763173175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23816428958340980701795133 8931160859377867763173175)
  ·
    refine ⟨13396741289066801644759763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8931160859377867763173175 13396741289066801644759763)
    ·
      refine ⟨20095111933600202467139645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13396741289066801644759763 20095111933600202467139645)
      ·
        refine ⟨7535666975100075925177367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20095111933600202467139645 7535666975100075925177367)
        ·
          refine ⟨11303500462650113887766051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7535666975100075925177367 11303500462650113887766051)
          ·
            refine ⟨16955250693975170831649077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11303500462650113887766051 16955250693975170831649077)
            ·
              refine ⟨1589554752560172265467101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16955250693975170831649077 1589554752560172265467101)
              ·
                refine ⟨596083032210064599550163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1589554752560172265467101 596083032210064599550163)
                ·
                  refine ⟨894124548315096899325245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 596083032210064599550163 894124548315096899325245)
                  ·
                    refine ⟨335296705618161337246967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 894124548315096899325245 335296705618161337246967)
                    ·
                      rfl

theorem cell22_979482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 3, 1, 3].length) (baseStart_979482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_979482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_979482 prefixEnd_979482 := by exact prefixLift 979482
  have htrace : WordTrace (prefixWord ++ tailWord_979482) baseStart_979482 baseEnd_979482 := by
    simpa [prefixWord, tailWord_979482, baseEnd_979482] using wordTrace_append hprefix tailTrace_979482
  have hstable : (prefixWord ++ tailWord_979482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979482).length < 2 ^ (prefixWord ++ tailWord_979482).sum := by decide
  have hdescent : baseEnd_979482 < baseStart_979482 := by decide
  rcases family_descends (prefixWord ++ tailWord_979482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979525 : List Nat := [1, 3, 1, 1, 1, 5, 3, 2, 1, 4]
def baseStart_979525 : Nat := 118140960795 + 979525 * 2 ^ 59
def prefixEnd_979525 : Nat := 4983230072969 + 3 ^ 40 * 979525 * 2
def baseEnd_979525 : Nat := 335311425396923558421835

theorem tailTrace_979525 : CollatzResearch.WordTrace tailWord_979525 prefixEnd_979525 335311425396923558421835 := by
  unfold tailWord_979525
  simp only [CollatzResearch.WordTrace]
  refine ⟨35726211776355689396508029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23817474517570459597672019 35726211776355689396508029)
  ·
    refine ⟨13397329416133383523690511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35726211776355689396508029 13397329416133383523690511)
    ·
      refine ⟨20095994124200075285535767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13397329416133383523690511 20095994124200075285535767)
      ·
        refine ⟨30143991186300112928303651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20095994124200075285535767 30143991186300112928303651)
        ·
          refine ⟨45215986779450169392455477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30143991186300112928303651 45215986779450169392455477)
          ·
            refine ⟨4238998760573453380542701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45215986779450169392455477 4238998760573453380542701)
            ·
              refine ⟨1589624535215045017703513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4238998760573453380542701 1589624535215045017703513)
              ·
                refine ⟨1192218401411283763277635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1589624535215045017703513 1192218401411283763277635)
                ·
                  refine ⟨1788327602116925644916453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1192218401411283763277635 1788327602116925644916453)
                  ·
                    refine ⟨335311425396923558421835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1788327602116925644916453 335311425396923558421835)
                    ·
                      rfl

theorem cell22_979525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 4].length) (baseStart_979525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_979525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_979525 prefixEnd_979525 := by exact prefixLift 979525
  have htrace : WordTrace (prefixWord ++ tailWord_979525) baseStart_979525 baseEnd_979525 := by
    simpa [prefixWord, tailWord_979525, baseEnd_979525] using wordTrace_append hprefix tailTrace_979525
  have hstable : (prefixWord ++ tailWord_979525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979525).length < 2 ^ (prefixWord ++ tailWord_979525).sum := by decide
  have hdescent : baseEnd_979525 < baseStart_979525 := by decide
  rcases family_descends (prefixWord ++ tailWord_979525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979557 : List Nat := [1, 3, 1, 3, 4, 1, 1, 4, 4]
def baseStart_979557 : Nat := 118140960795 + 979557 * 2 ^ 59
def prefixEnd_979557 : Nat := 4983230072969 + 3 ^ 40 * 979557 * 2
def baseEnd_979557 : Nat := 111774126550295380540579

theorem tailTrace_979557 : CollatzResearch.WordTrace tailWord_979557 prefixEnd_979557 111774126550295380540579 := by
  unfold tailWord_979557
  simp only [CollatzResearch.WordTrace]
  refine ⟨35727378912239758861672925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23818252608159839241115283 35727378912239758861672925)
  ·
    refine ⟨13397767092089909573127347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35727378912239758861672925 13397767092089909573127347)
    ·
      refine ⟨20096650638134864359691021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13397767092089909573127347 20096650638134864359691021)
      ·
        refine ⟨7536243989300574134884133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20096650638134864359691021 7536243989300574134884133)
        ·
          refine ⟨1413045747993857650290775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7536243989300574134884133 1413045747993857650290775)
          ·
            refine ⟨2119568621990786475436163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1413045747993857650290775 2119568621990786475436163)
            ·
              refine ⟨3179352932986179713154245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2119568621990786475436163 3179352932986179713154245)
              ·
                refine ⟨596128674934908696216421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3179352932986179713154245 596128674934908696216421)
                ·
                  refine ⟨111774126550295380540579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 596128674934908696216421 111774126550295380540579)
                  ·
                    rfl

theorem cell22_979557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 4, 4].length) (baseStart_979557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_979557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_979557 prefixEnd_979557 := by exact prefixLift 979557
  have htrace : WordTrace (prefixWord ++ tailWord_979557) baseStart_979557 baseEnd_979557 := by
    simpa [prefixWord, tailWord_979557, baseEnd_979557] using wordTrace_append hprefix tailTrace_979557
  have hstable : (prefixWord ++ tailWord_979557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979557).length < 2 ^ (prefixWord ++ tailWord_979557).sum := by decide
  have hdescent : baseEnd_979557 < baseStart_979557 := by decide
  rcases family_descends (prefixWord ++ tailWord_979557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979585 : List Nat := [1, 2, 4, 2, 1, 1, 5, 6]
def baseStart_979585 : Nat := 118140960795 + 979585 * 2 ^ 59
def prefixEnd_979585 : Nat := 4983230072969 + 3 ^ 40 * 979585 * 2
def baseEnd_979585 : Nat := 37259107180344822435739

theorem tailTrace_979585 : CollatzResearch.WordTrace tailWord_979585 prefixEnd_979585 37259107180344822435739 := by
  unfold tailWord_979585
  simp only [CollatzResearch.WordTrace]
  refine ⟨35728400156138319643692209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23818933437425546429128139 35728400156138319643692209)
  ·
    refine ⟨26796300117103739732769157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35728400156138319643692209 26796300117103739732769157)
    ·
      refine ⟨5024306271956951199894217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26796300117103739732769157 5024306271956951199894217)
      ·
        refine ⟨3768229703967713399920663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5024306271956951199894217 3768229703967713399920663)
        ·
          refine ⟨5652344555951570099880995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3768229703967713399920663 5652344555951570099880995)
          ·
            refine ⟨8478516833927355149821493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5652344555951570099880995 8478516833927355149821493)
            ·
              refine ⟨794860953180689545295765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8478516833927355149821493 794860953180689545295765)
              ·
                refine ⟨37259107180344822435739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 794860953180689545295765 37259107180344822435739)
                ·
                  rfl

theorem cell22_979585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 6].length) (baseStart_979585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_979585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_979585 prefixEnd_979585 := by exact prefixLift 979585
  have htrace : WordTrace (prefixWord ++ tailWord_979585) baseStart_979585 baseEnd_979585 := by
    simpa [prefixWord, tailWord_979585, baseEnd_979585] using wordTrace_append hprefix tailTrace_979585
  have hstable : (prefixWord ++ tailWord_979585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979585).length < 2 ^ (prefixWord ++ tailWord_979585).sum := by decide
  have hdescent : baseEnd_979585 < baseStart_979585 := by decide
  rcases family_descends (prefixWord ++ tailWord_979585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979668 : List Nat := [2, 4, 1, 3, 2, 1, 3, 2, 1, 3]
def baseStart_979668 : Nat := 118140960795 + 979668 * 2 ^ 59
def prefixEnd_979668 : Nat := 4983230072969 + 3 ^ 40 * 979668 * 2
def baseEnd_979668 : Nat := 335360377219318852096397

theorem tailTrace_979668 : CollatzResearch.WordTrace tailWord_979668 prefixEnd_979668 335360377219318852096397 := by
  unfold tailWord_979668
  simp only [CollatzResearch.WordTrace]
  refine ⟨17865713707418812409481829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23820951609891749879309105 17865713707418812409481829)
  ·
    refine ⟨3349821320141027326777843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17865713707418812409481829 3349821320141027326777843)
    ·
      refine ⟨5024731980211540990166765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3349821320141027326777843 5024731980211540990166765)
      ·
        refine ⟨1884274492579327871312537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5024731980211540990166765 1884274492579327871312537)
        ·
          refine ⟨1413205869434495903484403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1884274492579327871312537 1413205869434495903484403)
          ·
            refine ⟨2119808804151743855226605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1413205869434495903484403 2119808804151743855226605)
            ·
              refine ⟨794928301556903945709977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2119808804151743855226605 794928301556903945709977)
              ·
                refine ⟨596196226167677959282483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 794928301556903945709977 596196226167677959282483)
                ·
                  refine ⟨894294339251516938923725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 596196226167677959282483 894294339251516938923725)
                  ·
                    refine ⟨335360377219318852096397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 894294339251516938923725 335360377219318852096397)
                    ·
                      rfl

theorem cell22_979668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_979668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_979668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_979668 prefixEnd_979668 := by exact prefixLift 979668
  have htrace : WordTrace (prefixWord ++ tailWord_979668) baseStart_979668 baseEnd_979668 := by
    simpa [prefixWord, tailWord_979668, baseEnd_979668] using wordTrace_append hprefix tailTrace_979668
  have hstable : (prefixWord ++ tailWord_979668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979668).length < 2 ^ (prefixWord ++ tailWord_979668).sum := by decide
  have hdescent : baseEnd_979668 < baseStart_979668 := by decide
  rcases family_descends (prefixWord ++ tailWord_979668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979690 : List Nat := [3, 1, 3, 1, 1, 1, 1, 5, 1, 5]
def baseStart_979690 : Nat := 118140960795 + 979690 * 2 ^ 59
def prefixEnd_979690 : Nat := 4983230072969 + 3 ^ 40 * 979690 * 2
def baseEnd_979690 : Nat := 335367908268918128046329

theorem tailTrace_979690 : CollatzResearch.WordTrace tailWord_979690 prefixEnd_979690 335367908268918128046329 := by
  unfold tailWord_979690
  simp only [CollatzResearch.WordTrace]
  refine ⟨8933057455189480644066131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23821486547171948384176349 8933057455189480644066131)
  ·
    refine ⟨13399586182784220966099197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8933057455189480644066131 13399586182784220966099197)
    ·
      refine ⟨5024844818544082862287199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13399586182784220966099197 5024844818544082862287199)
      ·
        refine ⟨7537267227816124293430799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5024844818544082862287199 7537267227816124293430799)
        ·
          refine ⟨11305900841724186440146199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7537267227816124293430799 11305900841724186440146199)
          ·
            refine ⟨16958851262586279660219299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11305900841724186440146199 16958851262586279660219299)
            ·
              refine ⟨25438276893879419490328949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16958851262586279660219299 25438276893879419490328949)
              ·
                refine ⟨2384838458801195577218339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25438276893879419490328949 2384838458801195577218339)
                ·
                  refine ⟨3577257688201793365827509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2384838458801195577218339 3577257688201793365827509)
                  ·
                    refine ⟨335367908268918128046329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3577257688201793365827509 335367908268918128046329)
                    ·
                      rfl

theorem cell22_979690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_979690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_979690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_979690 prefixEnd_979690 := by exact prefixLift 979690
  have htrace : WordTrace (prefixWord ++ tailWord_979690) baseStart_979690 baseEnd_979690 := by
    simpa [prefixWord, tailWord_979690, baseEnd_979690] using wordTrace_append hprefix tailTrace_979690
  have hstable : (prefixWord ++ tailWord_979690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979690).length < 2 ^ (prefixWord ++ tailWord_979690).sum := by decide
  have hdescent : baseEnd_979690 < baseStart_979690 := by decide
  rcases family_descends (prefixWord ++ tailWord_979690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979694 : List Nat := [4, 1, 2, 1, 1, 5, 1, 2, 1, 4]
def baseStart_979694 : Nat := 118140960795 + 979694 * 2 ^ 59
def prefixEnd_979694 : Nat := 4983230072969 + 3 ^ 40 * 979694 * 2
def baseEnd_979694 : Nat := 335369277550663450946317

theorem tailTrace_979694 : CollatzResearch.WordTrace tailWord_979694 prefixEnd_979694 335369277550663450946317 := by
  unfold tailWord_979694
  simp only [CollatzResearch.WordTrace]
  refine ⟨4466546964092928907426267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23821583808495620839606757 4466546964092928907426267)
  ·
    refine ⟨6699820446139393361139401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4466546964092928907426267 6699820446139393361139401)
    ·
      refine ⟨5024865334604545020854551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6699820446139393361139401 5024865334604545020854551)
      ·
        refine ⟨7537298001906817531281827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5024865334604545020854551 7537298001906817531281827)
        ·
          refine ⟨11305947002860226296922741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7537298001906817531281827 11305947002860226296922741)
          ·
            refine ⟨1059932531518146215336507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11305947002860226296922741 1059932531518146215336507)
            ·
              refine ⟨1589898797277219323004761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1059932531518146215336507 1589898797277219323004761)
              ·
                refine ⟨1192424097957914492253571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1589898797277219323004761 1192424097957914492253571)
                ·
                  refine ⟨1788636146936871738380357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1192424097957914492253571 1788636146936871738380357)
                  ·
                    refine ⟨335369277550663450946317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1788636146936871738380357 335369277550663450946317)
                    ·
                      rfl

theorem cell22_979694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_979694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_979694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_979694 prefixEnd_979694 := by exact prefixLift 979694
  have htrace : WordTrace (prefixWord ++ tailWord_979694) baseStart_979694 baseEnd_979694 := by
    simpa [prefixWord, tailWord_979694, baseEnd_979694] using wordTrace_append hprefix tailTrace_979694
  have hstable : (prefixWord ++ tailWord_979694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979694).length < 2 ^ (prefixWord ++ tailWord_979694).sum := by decide
  have hdescent : baseEnd_979694 < baseStart_979694 := by decide
  rcases family_descends (prefixWord ++ tailWord_979694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979795 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 5, 4]
def baseStart_979795 : Nat := 118140960795 + 979795 * 2 ^ 59
def prefixEnd_979795 : Nat := 4983230072969 + 3 ^ 40 * 979795 * 2
def baseEnd_979795 : Nat := 335403851914732854171007

theorem tailTrace_979795 : CollatzResearch.WordTrace tailWord_979795 prefixEnd_979795 335403851914732854171007 := by
  unfold tailWord_979795
  simp only [CollatzResearch.WordTrace]
  refine ⟨35736059485377525508836839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23824039656918350339224559 35736059485377525508836839)
  ·
    refine ⟨53604089228066288263255259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35736059485377525508836839 53604089228066288263255259)
    ·
      refine ⟨80406133842099432394882889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53604089228066288263255259 80406133842099432394882889)
      ·
        refine ⟨60304600381574574296162167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80406133842099432394882889 60304600381574574296162167)
        ·
          refine ⟨90456900572361861444243251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60304600381574574296162167 90456900572361861444243251)
          ·
            refine ⟨135685350858542792166364877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90456900572361861444243251 135685350858542792166364877)
            ·
              refine ⟨50882006571953547062386829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135685350858542792166364877 50882006571953547062386829)
              ·
                refine ⟨19080752464482580148395061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50882006571953547062386829 19080752464482580148395061)
                ·
                  refine ⟨1788820543545241888912037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19080752464482580148395061 1788820543545241888912037)
                  ·
                    refine ⟨335403851914732854171007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1788820543545241888912037 335403851914732854171007)
                    ·
                      rfl

theorem cell22_979795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 4].length) (baseStart_979795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_979795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_979795 prefixEnd_979795 := by exact prefixLift 979795
  have htrace : WordTrace (prefixWord ++ tailWord_979795) baseStart_979795 baseEnd_979795 := by
    simpa [prefixWord, tailWord_979795, baseEnd_979795] using wordTrace_append hprefix tailTrace_979795
  have hstable : (prefixWord ++ tailWord_979795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979795).length < 2 ^ (prefixWord ++ tailWord_979795).sum := by decide
  have hdescent : baseEnd_979795 < baseStart_979795 := by decide
  rcases family_descends (prefixWord ++ tailWord_979795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979799 : List Nat := [1, 1, 3, 2, 4, 2, 3, 1, 5]
def baseStart_979799 : Nat := 118140960795 + 979799 * 2 ^ 59
def prefixEnd_979799 : Nat := 4983230072969 + 3 ^ 40 * 979799 * 2
def baseEnd_979799 : Nat := 111801740398826059023665

theorem tailTrace_979799 : CollatzResearch.WordTrace tailWord_979799 prefixEnd_979799 111801740398826059023665 := by
  unfold tailWord_979799
  simp only [CollatzResearch.WordTrace]
  refine ⟨35736205377363034191982451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23824136918242022794654967 35736205377363034191982451)
  ·
    refine ⟨53604308066044551287973677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35736205377363034191982451 53604308066044551287973677)
    ·
      refine ⟨20101615524766706732990129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53604308066044551287973677 20101615524766706732990129)
      ·
        refine ⟨15076211643575030049742597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20101615524766706732990129 15076211643575030049742597)
        ·
          refine ⟨2826789683170318134326737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15076211643575030049742597 2826789683170318134326737)
          ·
            refine ⟨2120092262377738600745053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2826789683170318134326737 2120092262377738600745053)
            ·
              refine ⟨795034598391651975279395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2120092262377738600745053 795034598391651975279395)
              ·
                refine ⟨1192551897587477962919093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 795034598391651975279395 1192551897587477962919093)
                ·
                  refine ⟨111801740398826059023665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1192551897587477962919093 111801740398826059023665)
                  ·
                    rfl

theorem cell22_979799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 5].length) (baseStart_979799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_979799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_979799 prefixEnd_979799 := by exact prefixLift 979799
  have htrace : WordTrace (prefixWord ++ tailWord_979799) baseStart_979799 baseEnd_979799 := by
    simpa [prefixWord, tailWord_979799, baseEnd_979799] using wordTrace_append hprefix tailTrace_979799
  have hstable : (prefixWord ++ tailWord_979799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979799).length < 2 ^ (prefixWord ++ tailWord_979799).sum := by decide
  have hdescent : baseEnd_979799 < baseStart_979799 := by decide
  rcases family_descends (prefixWord ++ tailWord_979799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979829 : List Nat := [1, 3, 4, 1, 1, 2, 2, 3, 1, 4]
def baseStart_979829 : Nat := 118140960795 + 979829 * 2 ^ 59
def prefixEnd_979829 : Nat := 4983230072969 + 3 ^ 40 * 979829 * 2
def baseEnd_979829 : Nat := 335415490809568098820903

theorem tailTrace_979829 : CollatzResearch.WordTrace tailWord_979829 prefixEnd_979829 335415490809568098820903 := by
  unfold tailWord_979829
  simp only [CollatzResearch.WordTrace]
  refine ⟨35737299567254349315574541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23824866378169566210383027 35737299567254349315574541)
  ·
    refine ⟨13401487337720380993340453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35737299567254349315574541 13401487337720380993340453)
    ·
      refine ⟨2512778875822571436251335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13401487337720380993340453 2512778875822571436251335)
      ·
        refine ⟨3769168313733857154377003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2512778875822571436251335 3769168313733857154377003)
        ·
          refine ⟨5653752470600785731565505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3769168313733857154377003 5653752470600785731565505)
          ·
            refine ⟨4240314352950589298674129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5653752470600785731565505 4240314352950589298674129)
            ·
              refine ⟨3180235764712941974005597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4240314352950589298674129 3180235764712941974005597)
              ·
                refine ⟨1192588411767353240252099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3180235764712941974005597 1192588411767353240252099)
                ·
                  refine ⟨1788882617651029860378149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1192588411767353240252099 1788882617651029860378149)
                  ·
                    refine ⟨335415490809568098820903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1788882617651029860378149 335415490809568098820903)
                    ·
                      rfl

theorem cell22_979829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_979829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_979829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_979829 prefixEnd_979829 := by exact prefixLift 979829
  have htrace : WordTrace (prefixWord ++ tailWord_979829) baseStart_979829 baseEnd_979829 := by
    simpa [prefixWord, tailWord_979829, baseEnd_979829] using wordTrace_append hprefix tailTrace_979829
  have hstable : (prefixWord ++ tailWord_979829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979829).length < 2 ^ (prefixWord ++ tailWord_979829).sum := by decide
  have hdescent : baseEnd_979829 < baseStart_979829 := by decide
  rcases family_descends (prefixWord ++ tailWord_979829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979840 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 3, 6]
def baseStart_979840 : Nat := 118140960795 + 979840 * 2 ^ 59
def prefixEnd_979840 : Nat := 4983230072969 + 3 ^ 40 * 979840 * 2
def baseEnd_979840 : Nat := 335419256334367736795869

theorem tailTrace_979840 : CollatzResearch.WordTrace tailWord_979840 prefixEnd_979840 335419256334367736795869 := by
  unfold tailWord_979840
  simp only [CollatzResearch.WordTrace]
  refine ⟨17868850385107249097112487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23825133846809665462816649 17868850385107249097112487)
  ·
    refine ⟨26803275577660873645668731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17868850385107249097112487 26803275577660873645668731)
    ·
      refine ⟨40204913366491310468503097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26803275577660873645668731 40204913366491310468503097)
      ·
        refine ⟨30153685024868482851377323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40204913366491310468503097 30153685024868482851377323)
        ·
          refine ⟨45230527537302724277065985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30153685024868482851377323 45230527537302724277065985)
          ·
            refine ⟨33922895652977043207799489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45230527537302724277065985 33922895652977043207799489)
            ·
              refine ⟨25442171739732782405849617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33922895652977043207799489 25442171739732782405849617)
              ·
                refine ⟨19081628804799586804387213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25442171739732782405849617 19081628804799586804387213)
                ·
                  refine ⟨7155610801799845051645205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19081628804799586804387213 7155610801799845051645205)
                  ·
                    refine ⟨335419256334367736795869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7155610801799845051645205 335419256334367736795869)
                    ·
                      rfl

theorem cell22_979840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 3, 6].length) (baseStart_979840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_979840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_979840 prefixEnd_979840 := by exact prefixLift 979840
  have htrace : WordTrace (prefixWord ++ tailWord_979840) baseStart_979840 baseEnd_979840 := by
    simpa [prefixWord, tailWord_979840, baseEnd_979840] using wordTrace_append hprefix tailTrace_979840
  have hstable : (prefixWord ++ tailWord_979840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979840).length < 2 ^ (prefixWord ++ tailWord_979840).sum := by decide
  have hdescent : baseEnd_979840 < baseStart_979840 := by decide
  rcases family_descends (prefixWord ++ tailWord_979840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979874 : List Nat := [3, 3, 1, 2, 2, 1, 1, 3, 2, 4]
def baseStart_979874 : Nat := 118140960795 + 979874 * 2 ^ 59
def prefixEnd_979874 : Nat := 4983230072969 + 3 ^ 40 * 979874 * 2
def baseEnd_979874 : Nat := 335430895229202981445765

theorem tailTrace_979874 : CollatzResearch.WordTrace tailWord_979874 prefixEnd_979874 335430895229202981445765 := by
  unfold tailWord_979874
  simp only [CollatzResearch.WordTrace]
  refine ⟨8934735213022830500240669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23825960568060881333975117 8934735213022830500240669)
  ·
    refine ⟨3350525704883561437590251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8934735213022830500240669 3350525704883561437590251)
    ·
      refine ⟨5025788557325342156385377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3350525704883561437590251 5025788557325342156385377)
      ·
        refine ⟨3769341417994006617289033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5025788557325342156385377 3769341417994006617289033)
        ·
          refine ⟨2827006063495504962966775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3769341417994006617289033 2827006063495504962966775)
          ·
            refine ⟨4240509095243257444450163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2827006063495504962966775 4240509095243257444450163)
            ·
              refine ⟨6360763642864886166675245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4240509095243257444450163 6360763642864886166675245)
              ·
                refine ⟨2385286366074332312503217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6360763642864886166675245 2385286366074332312503217)
                ·
                  refine ⟨1788964774555749234377413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2385286366074332312503217 1788964774555749234377413)
                  ·
                    refine ⟨335430895229202981445765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1788964774555749234377413 335430895229202981445765)
                    ·
                      rfl

theorem cell22_979874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_979874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_979874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_979874 prefixEnd_979874 := by exact prefixLift 979874
  have htrace : WordTrace (prefixWord ++ tailWord_979874) baseStart_979874 baseEnd_979874 := by
    simpa [prefixWord, tailWord_979874, baseEnd_979874] using wordTrace_append hprefix tailTrace_979874
  have hstable : (prefixWord ++ tailWord_979874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979874).length < 2 ^ (prefixWord ++ tailWord_979874).sum := by decide
  have hdescent : baseEnd_979874 < baseStart_979874 := by decide
  rcases family_descends (prefixWord ++ tailWord_979874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979887 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 7, 3]
def baseStart_979887 : Nat := 118140960795 + 979887 * 2 ^ 59
def prefixEnd_979887 : Nat := 4983230072969 + 3 ^ 40 * 979887 * 2
def baseEnd_979887 : Nat := 335435345394875280870725

theorem tailTrace_979887 : CollatzResearch.WordTrace tailWord_979887 prefixEnd_979887 335435345394875280870725 := by
  unfold tailWord_979887
  simp only [CollatzResearch.WordTrace]
  refine ⟨35739415001044225221185915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23826276667362816814123943 35739415001044225221185915)
  ·
    refine ⟨53609122501566337831778873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35739415001044225221185915 53609122501566337831778873)
    ·
      refine ⟨40206841876174753373834155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53609122501566337831778873 40206841876174753373834155)
      ·
        refine ⟨60310262814262130060751233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40206841876174753373834155 60310262814262130060751233)
        ·
          refine ⟨45232697110696597545563425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60310262814262130060751233 45232697110696597545563425)
          ·
            refine ⟨33924522833022448159172569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45232697110696597545563425 33924522833022448159172569)
            ·
              refine ⟨25443392124766836119379427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33924522833022448159172569 25443392124766836119379427)
              ·
                refine ⟨38165088187150254179069141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25443392124766836119379427 38165088187150254179069141)
                ·
                  refine ⟨894494254386334082321933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 38165088187150254179069141 894494254386334082321933)
                  ·
                    refine ⟨335435345394875280870725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 894494254386334082321933 335435345394875280870725)
                    ·
                      rfl

theorem cell22_979887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 7, 3].length) (baseStart_979887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_979887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_979887 prefixEnd_979887 := by exact prefixLift 979887
  have htrace : WordTrace (prefixWord ++ tailWord_979887) baseStart_979887 baseEnd_979887 := by
    simpa [prefixWord, tailWord_979887, baseEnd_979887] using wordTrace_append hprefix tailTrace_979887
  have hstable : (prefixWord ++ tailWord_979887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979887).length < 2 ^ (prefixWord ++ tailWord_979887).sum := by decide
  have hdescent : baseEnd_979887 < baseStart_979887 := by decide
  rcases family_descends (prefixWord ++ tailWord_979887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979902 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 1, 8]
def baseStart_979902 : Nat := 118140960795 + 979902 * 2 ^ 59
def prefixEnd_979902 : Nat := 4983230072969 + 3 ^ 40 * 979902 * 2
def baseEnd_979902 : Nat := 335440480201420241745679

theorem tailTrace_979902 : CollatzResearch.WordTrace tailWord_979902 prefixEnd_979902 335440480201420241745679 := by
  unfold tailWord_979902
  simp only [CollatzResearch.WordTrace]
  refine ⟨4467495261998735347872745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23826641397326588521987973 4467495261998735347872745)
  ·
    refine ⟨3350621446499051510904559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4467495261998735347872745 3350621446499051510904559)
    ·
      refine ⟨5025932169748577266356839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3350621446499051510904559 5025932169748577266356839)
      ·
        refine ⟨7538898254622865899535259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5025932169748577266356839 7538898254622865899535259)
        ·
          refine ⟨11308347381934298849302889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7538898254622865899535259 11308347381934298849302889)
          ·
            refine ⟨8481260536450724136977167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11308347381934298849302889 8481260536450724136977167)
            ·
              refine ⟨12721890804676086205465751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8481260536450724136977167 12721890804676086205465751)
              ·
                refine ⟨19082836207014129308198627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12721890804676086205465751 19082836207014129308198627)
                ·
                  refine ⟨28624254310521193962297941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19082836207014129308198627 28624254310521193962297941)
                  ·
                    refine ⟨335440480201420241745679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 28624254310521193962297941 335440480201420241745679)
                    ·
                      rfl

theorem cell22_979902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_979902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_979902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_979902 prefixEnd_979902 := by exact prefixLift 979902
  have htrace : WordTrace (prefixWord ++ tailWord_979902) baseStart_979902 baseEnd_979902 := by
    simpa [prefixWord, tailWord_979902, baseEnd_979902] using wordTrace_append hprefix tailTrace_979902
  have hstable : (prefixWord ++ tailWord_979902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979902).length < 2 ^ (prefixWord ++ tailWord_979902).sum := by decide
  have hdescent : baseEnd_979902 < baseStart_979902 := by decide
  rcases family_descends (prefixWord ++ tailWord_979902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_979994 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 6, 3]
def baseStart_979994 : Nat := 118140960795 + 979994 * 2 ^ 59
def prefixEnd_979994 : Nat := 4983230072969 + 3 ^ 40 * 979994 * 2
def baseEnd_979994 : Nat := 335471973681562668445397

theorem tailTrace_979994 : CollatzResearch.WordTrace tailWord_979994 prefixEnd_979994 335471973681562668445397 := by
  unfold tailWord_979994
  simp only [CollatzResearch.WordTrace]
  refine ⟨8935829402914145623832759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23828878407771054996887357 8935829402914145623832759)
  ·
    refine ⟨13403744104371218435749139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8935829402914145623832759 13403744104371218435749139)
    ·
      refine ⟨20105616156556827653623709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13403744104371218435749139 20105616156556827653623709)
      ·
        refine ⟨7539606058708810370108891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20105616156556827653623709 7539606058708810370108891)
        ·
          refine ⟨11309409088063215555163337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7539606058708810370108891 11309409088063215555163337)
          ·
            refine ⟨8482056816047411666372503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11309409088063215555163337 8482056816047411666372503)
            ·
              refine ⟨12723085224071117499558755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8482056816047411666372503 12723085224071117499558755)
              ·
                refine ⟨19084627836106676249338133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12723085224071117499558755 19084627836106676249338133)
                ·
                  refine ⟨894591929817500449187725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19084627836106676249338133 894591929817500449187725)
                  ·
                    refine ⟨335471973681562668445397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 894591929817500449187725 335471973681562668445397)
                    ·
                      rfl

theorem cell22_979994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 6, 3].length) (baseStart_979994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_979994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_979994 prefixEnd_979994 := by exact prefixLift 979994
  have htrace : WordTrace (prefixWord ++ tailWord_979994) baseStart_979994 baseEnd_979994 := by
    simpa [prefixWord, tailWord_979994, baseEnd_979994] using wordTrace_append hprefix tailTrace_979994
  have hstable : (prefixWord ++ tailWord_979994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_979994).length < 2 ^ (prefixWord ++ tailWord_979994).sum := by decide
  have hdescent : baseEnd_979994 < baseStart_979994 := by decide
  rcases family_descends (prefixWord ++ tailWord_979994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980024 : List Nat := [2, 1, 2, 1, 5, 2, 2, 7]
def baseStart_980024 : Nat := 118140960795 + 980024 * 2 ^ 59
def prefixEnd_980024 : Nat := 4983230072969 + 3 ^ 40 * 980024 * 2
def baseEnd_980024 : Nat := 37275804810516954466145

theorem tailTrace_980024 : CollatzResearch.WordTrace tailWord_980024 prefixEnd_980024 37275804810516954466145 := by
  unfold tailWord_980024
  simp only [CollatzResearch.WordTrace]
  refine ⟨17872205900773948809461563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23829607867698598412615417 17872205900773948809461563)
  ·
    refine ⟨26808308851160923214192345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17872205900773948809461563 26808308851160923214192345)
    ·
      refine ⟨20106231638370692410644259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26808308851160923214192345 20106231638370692410644259)
      ·
        refine ⟨30159347457556038615966389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20106231638370692410644259 30159347457556038615966389)
        ·
          refine ⟨2827438824145878620246849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30159347457556038615966389 2827438824145878620246849)
          ·
            refine ⟨2120579118109408965185137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2827438824145878620246849 2120579118109408965185137)
            ·
              refine ⟨1590434338582056723888853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2120579118109408965185137 1590434338582056723888853)
              ·
                refine ⟨37275804810516954466145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1590434338582056723888853 37275804810516954466145)
                ·
                  rfl

theorem cell22_980024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 7].length) (baseStart_980024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_980024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_980024 prefixEnd_980024 := by exact prefixLift 980024
  have htrace : WordTrace (prefixWord ++ tailWord_980024) baseStart_980024 baseEnd_980024 := by
    simpa [prefixWord, tailWord_980024, baseEnd_980024] using wordTrace_append hprefix tailTrace_980024
  have hstable : (prefixWord ++ tailWord_980024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980024).length < 2 ^ (prefixWord ++ tailWord_980024).sum := by decide
  have hdescent : baseEnd_980024 < baseStart_980024 := by decide
  rcases family_descends (prefixWord ++ tailWord_980024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980028 : List Nat := [2, 2, 2, 2, 2, 2, 4, 1, 2, 3]
def baseStart_980028 : Nat := 118140960795 + 980028 * 2 ^ 59
def prefixEnd_980028 : Nat := 4983230072969 + 3 ^ 40 * 980028 * 2
def baseEnd_980028 : Nat := 335483612576397913095293

theorem tailTrace_980028 : CollatzResearch.WordTrace tailWord_980028 prefixEnd_980028 335483612576397913095293 := by
  unfold tailWord_980028
  simp only [CollatzResearch.WordTrace]
  refine ⟨17872278846766703151034369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23829705129022270868045825 17872278846766703151034369)
  ·
    refine ⟨13404209135075027363275777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17872278846766703151034369 13404209135075027363275777)
    ·
      refine ⟨10053156851306270522456833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13404209135075027363275777 10053156851306270522456833)
      ·
        refine ⟨7539867638479702891842625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10053156851306270522456833 7539867638479702891842625)
        ·
          refine ⟨5654900728859777168881969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7539867638479702891842625 5654900728859777168881969)
          ·
            refine ⟨4241175546644832876661477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5654900728859777168881969 4241175546644832876661477)
            ·
              refine ⟨795220414995906164374027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4241175546644832876661477 795220414995906164374027)
              ·
                refine ⟨1192830622493859246561041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 795220414995906164374027 1192830622493859246561041)
                ·
                  refine ⟨894622966870394434920781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1192830622493859246561041 894622966870394434920781)
                  ·
                    refine ⟨335483612576397913095293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 894622966870394434920781 335483612576397913095293)
                    ·
                      rfl

theorem cell22_980028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 1, 2, 3].length) (baseStart_980028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_980028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_980028 prefixEnd_980028 := by exact prefixLift 980028
  have htrace : WordTrace (prefixWord ++ tailWord_980028) baseStart_980028 baseEnd_980028 := by
    simpa [prefixWord, tailWord_980028, baseEnd_980028] using wordTrace_append hprefix tailTrace_980028
  have hstable : (prefixWord ++ tailWord_980028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980028).length < 2 ^ (prefixWord ++ tailWord_980028).sum := by decide
  have hdescent : baseEnd_980028 < baseStart_980028 := by decide
  rcases family_descends (prefixWord ++ tailWord_980028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980062 : List Nat := [4, 4, 1, 1, 1, 2, 2, 2, 2, 3]
def baseStart_980062 : Nat := 118140960795 + 980062 * 2 ^ 59
def prefixEnd_980062 : Nat := 4983230072969 + 3 ^ 40 * 980062 * 2
def baseEnd_980062 : Nat := 335495251471233157745189

theorem tailTrace_980062 : CollatzResearch.WordTrace tailWord_980062 prefixEnd_980062 335495251471233157745189 := by
  unfold tailWord_980062
  simp only [CollatzResearch.WordTrace]
  refine ⟨4468224721926278763600805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23830531850273486739204293 4468224721926278763600805)
  ·
    refine ⟨837792135361177268175151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4468224721926278763600805 837792135361177268175151)
    ·
      refine ⟨1256688203041765902262727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 837792135361177268175151 1256688203041765902262727)
      ·
        refine ⟨1885032304562648853394091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1256688203041765902262727 1885032304562648853394091)
        ·
          refine ⟨2827548456843973280091137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1885032304562648853394091 2827548456843973280091137)
          ·
            refine ⟨2120661342632979960068353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2827548456843973280091137 2120661342632979960068353)
            ·
              refine ⟨1590496006974734970051265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2120661342632979960068353 1590496006974734970051265)
              ·
                refine ⟨1192872005231051227538449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1590496006974734970051265 1192872005231051227538449)
                ·
                  refine ⟨894654003923288420653837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1192872005231051227538449 894654003923288420653837)
                  ·
                    refine ⟨335495251471233157745189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 894654003923288420653837 335495251471233157745189)
                    ·
                      rfl

theorem cell22_980062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_980062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_980062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_980062 prefixEnd_980062 := by exact prefixLift 980062
  have htrace : WordTrace (prefixWord ++ tailWord_980062) baseStart_980062 baseEnd_980062 := by
    simpa [prefixWord, tailWord_980062, baseEnd_980062] using wordTrace_append hprefix tailTrace_980062
  have hstable : (prefixWord ++ tailWord_980062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980062).length < 2 ^ (prefixWord ++ tailWord_980062).sum := by decide
  have hdescent : baseEnd_980062 < baseStart_980062 := by decide
  rcases family_descends (prefixWord ++ tailWord_980062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980073 : List Nat := [1, 2, 1, 1, 1, 7, 1, 4, 1, 3]
def baseStart_980073 : Nat := 118140960795 + 980073 * 2 ^ 59
def prefixEnd_980073 : Nat := 4983230072969 + 3 ^ 40 * 980073 * 2
def baseEnd_980073 : Nat := 335499016996032795720155

theorem tailTrace_980073 : CollatzResearch.WordTrace tailWord_980073 prefixEnd_980073 335499016996032795720155 := by
  unfold tailWord_980073
  simp only [CollatzResearch.WordTrace]
  refine ⟨35746198978370378987456873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23830799318913585991637915 35746198978370378987456873)
  ·
    refine ⟨26809649233777784240592655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35746198978370378987456873 26809649233777784240592655)
    ·
      refine ⟨40214473850666676360888983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26809649233777784240592655 40214473850666676360888983)
      ·
        refine ⟨60321710776000014541333475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40214473850666676360888983 60321710776000014541333475)
        ·
          refine ⟨90482566164000021812000213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60321710776000014541333475 90482566164000021812000213)
          ·
            refine ⟨2120685144468750511218755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 90482566164000021812000213 2120685144468750511218755)
            ·
              refine ⟨3181027716703125766828133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2120685144468750511218755 3181027716703125766828133)
              ·
                refine ⟨596442696881836081280275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3181027716703125766828133 596442696881836081280275)
                ·
                  refine ⟨894664045322754121920413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 596442696881836081280275 894664045322754121920413)
                  ·
                    refine ⟨335499016996032795720155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 894664045322754121920413 335499016996032795720155)
                    ·
                      rfl

theorem cell22_980073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 4, 1, 3].length) (baseStart_980073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_980073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_980073 prefixEnd_980073 := by exact prefixLift 980073
  have htrace : WordTrace (prefixWord ++ tailWord_980073) baseStart_980073 baseEnd_980073 := by
    simpa [prefixWord, tailWord_980073, baseEnd_980073] using wordTrace_append hprefix tailTrace_980073
  have hstable : (prefixWord ++ tailWord_980073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980073).length < 2 ^ (prefixWord ++ tailWord_980073).sum := by decide
  have hdescent : baseEnd_980073 < baseStart_980073 := by decide
  rcases family_descends (prefixWord ++ tailWord_980073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980086 : List Nat := [5, 1, 1, 2, 1, 1, 1, 5, 5]
def baseStart_980086 : Nat := 118140960795 + 980086 * 2 ^ 59
def prefixEnd_980086 : Nat := 4983230072969 + 3 ^ 40 * 980086 * 2
def baseEnd_980086 : Nat := 111834489053901698381705

theorem tailTrace_980086 : CollatzResearch.WordTrace tailWord_980086 prefixEnd_980086 111834489053901698381705 := by
  unfold tailWord_980086
  simp only [CollatzResearch.WordTrace]
  refine ⟨2234167070457705137980007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23831115418215521471786741 2234167070457705137980007)
  ·
    refine ⟨3351250605686557706970011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2234167070457705137980007 3351250605686557706970011)
    ·
      refine ⟨5026875908529836560455017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3351250605686557706970011 5026875908529836560455017)
      ·
        refine ⟨3770156931397377420341263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5026875908529836560455017 3770156931397377420341263)
        ·
          refine ⟨5655235397096066130511895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3770156931397377420341263 5655235397096066130511895)
          ·
            refine ⟨8482853095644099195767843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5655235397096066130511895 8482853095644099195767843)
            ·
              refine ⟨12724279643466148793651765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8482853095644099195767843 12724279643466148793651765)
              ·
                refine ⟨1192901216574951449404853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12724279643466148793651765 1192901216574951449404853)
                ·
                  refine ⟨111834489053901698381705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1192901216574951449404853 111834489053901698381705)
                  ·
                    rfl

theorem cell22_980086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_980086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_980086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_980086 prefixEnd_980086 := by exact prefixLift 980086
  have htrace : WordTrace (prefixWord ++ tailWord_980086) baseStart_980086 baseEnd_980086 := by
    simpa [prefixWord, tailWord_980086, baseEnd_980086] using wordTrace_append hprefix tailTrace_980086
  have hstable : (prefixWord ++ tailWord_980086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980086).length < 2 ^ (prefixWord ++ tailWord_980086).sum := by decide
  have hdescent : baseEnd_980086 < baseStart_980086 := by decide
  rcases family_descends (prefixWord ++ tailWord_980086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980094 : List Nat := [4, 2, 4, 1, 2, 1, 1, 1, 2, 4]
def baseStart_980094 : Nat := 118140960795 + 980094 * 2 ^ 59
def prefixEnd_980094 : Nat := 4983230072969 + 3 ^ 40 * 980094 * 2
def baseEnd_980094 : Nat := 335506205725195740945091

theorem tailTrace_980094 : CollatzResearch.WordTrace tailWord_980094 prefixEnd_980094 335506205725195740945091 := by
  unfold tailWord_980094
  simp only [CollatzResearch.WordTrace]
  refine ⟨4468370613911787446746417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23831309940862866382647557 4468370613911787446746417)
  ·
    refine ⟨3351277960433840585059813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4468370613911787446746417 3351277960433840585059813)
    ·
      refine ⟨628364617581345109698715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3351277960433840585059813 628364617581345109698715)
      ·
        refine ⟨942546926372017664548073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628364617581345109698715 942546926372017664548073)
        ·
          refine ⟨706910194779013248411055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 942546926372017664548073 706910194779013248411055)
          ·
            refine ⟨1060365292168519872616583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706910194779013248411055 1060365292168519872616583)
            ·
              refine ⟨1590547938252779808924875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1060365292168519872616583 1590547938252779808924875)
              ·
                refine ⟨2385821907379169713387313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1590547938252779808924875 2385821907379169713387313)
                ·
                  refine ⟨1789366430534377285040485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2385821907379169713387313 1789366430534377285040485)
                  ·
                    refine ⟨335506205725195740945091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1789366430534377285040485 335506205725195740945091)
                    ·
                      rfl

theorem cell22_980094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_980094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_980094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_980094 prefixEnd_980094 := by exact prefixLift 980094
  have htrace : WordTrace (prefixWord ++ tailWord_980094) baseStart_980094 baseEnd_980094 := by
    simpa [prefixWord, tailWord_980094, baseEnd_980094] using wordTrace_append hprefix tailTrace_980094
  have hstable : (prefixWord ++ tailWord_980094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980094).length < 2 ^ (prefixWord ++ tailWord_980094).sum := by decide
  have hdescent : baseEnd_980094 < baseStart_980094 := by decide
  rcases family_descends (prefixWord ++ tailWord_980094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980099 : List Nat := [1, 1, 1, 3, 3, 2, 1, 3, 3, 4]
def baseStart_980099 : Nat := 118140960795 + 980099 * 2 ^ 59
def prefixEnd_980099 : Nat := 4983230072969 + 3 ^ 40 * 980099 * 2
def baseEnd_980099 : Nat := 335507917327377394570075

theorem tailTrace_980099 : CollatzResearch.WordTrace tailWord_980099 prefixEnd_980099 335507917327377394570075 := by
  unfold tailWord_980099
  simp only [CollatzResearch.WordTrace]
  refine ⟨35747147276276185427903351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23831431517517456951935567 35747147276276185427903351)
  ·
    refine ⟨53620720914414278141855027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35747147276276185427903351 53620720914414278141855027)
    ·
      refine ⟨80431081371621417212782541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53620720914414278141855027 80431081371621417212782541)
      ·
        refine ⟨30161655514358031454793453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80431081371621417212782541 30161655514358031454793453)
        ·
          refine ⟨11310620817884261795547545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30161655514358031454793453 11310620817884261795547545)
          ·
            refine ⟨8482965613413196346660659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11310620817884261795547545 8482965613413196346660659)
            ·
              refine ⟨12724448420119794519990989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8482965613413196346660659 12724448420119794519990989)
              ·
                refine ⟨4771668157544922944996621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12724448420119794519990989 4771668157544922944996621)
                ·
                  refine ⟨1789375559079346104373733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4771668157544922944996621 1789375559079346104373733)
                  ·
                    refine ⟨335507917327377394570075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1789375559079346104373733 335507917327377394570075)
                    ·
                      rfl

theorem cell22_980099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 4].length) (baseStart_980099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_980099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_980099 prefixEnd_980099 := by exact prefixLift 980099
  have htrace : WordTrace (prefixWord ++ tailWord_980099) baseStart_980099 baseEnd_980099 := by
    simpa [prefixWord, tailWord_980099, baseEnd_980099] using wordTrace_append hprefix tailTrace_980099
  have hstable : (prefixWord ++ tailWord_980099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980099).length < 2 ^ (prefixWord ++ tailWord_980099).sum := by decide
  have hdescent : baseEnd_980099 < baseStart_980099 := by decide
  rcases family_descends (prefixWord ++ tailWord_980099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980144 : List Nat := [2, 1, 1, 1, 2, 1, 2, 4, 4, 4]
def baseStart_980144 : Nat := 118140960795 + 980144 * 2 ^ 59
def prefixEnd_980144 : Nat := 4983230072969 + 3 ^ 40 * 980144 * 2
def baseEnd_980144 : Nat := 335523321747012277194937

theorem tailTrace_980144 : CollatzResearch.WordTrace tailWord_980144 prefixEnd_980144 335523321747012277194937 := by
  unfold tailWord_980144
  simp only [CollatzResearch.WordTrace]
  refine ⟨17874394280556579056645743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23832525707408772075527657 17874394280556579056645743)
  ·
    refine ⟨26811591420834868584968615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17874394280556579056645743 26811591420834868584968615)
    ·
      refine ⟨40217387131252302877452923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26811591420834868584968615 40217387131252302877452923)
      ·
        refine ⟨60326080696878454316179385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40217387131252302877452923 60326080696878454316179385)
        ·
          refine ⟨45244560522658840737134539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60326080696878454316179385 45244560522658840737134539)
          ·
            refine ⟨67866840783988261105701809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45244560522658840737134539 67866840783988261105701809)
            ·
              refine ⟨50900130587991195829276357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67866840783988261105701809 50900130587991195829276357)
              ·
                refine ⟨9543774485248349217989317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50900130587991195829276357 9543774485248349217989317)
                ·
                  refine ⟨1789457715984065478372997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9543774485248349217989317 1789457715984065478372997)
                  ·
                    refine ⟨335523321747012277194937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1789457715984065478372997 335523321747012277194937)
                    ·
                      rfl

theorem cell22_980144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 4, 4].length) (baseStart_980144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_980144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_980144 prefixEnd_980144 := by exact prefixLift 980144
  have htrace : WordTrace (prefixWord ++ tailWord_980144) baseStart_980144 baseEnd_980144 := by
    simpa [prefixWord, tailWord_980144, baseEnd_980144] using wordTrace_append hprefix tailTrace_980144
  have hstable : (prefixWord ++ tailWord_980144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980144).length < 2 ^ (prefixWord ++ tailWord_980144).sum := by decide
  have hdescent : baseEnd_980144 < baseStart_980144 := by decide
  rcases family_descends (prefixWord ++ tailWord_980144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980146 : List Nat := [3, 2, 1, 1, 1, 4, 3, 1, 1, 5]
def baseStart_980146 : Nat := 118140960795 + 980146 * 2 ^ 59
def prefixEnd_980146 : Nat := 4983230072969 + 3 ^ 40 * 980146 * 2
def baseEnd_980146 : Nat := 335524006387884938644931

theorem tailTrace_980146 : CollatzResearch.WordTrace tailWord_980146 prefixEnd_980146 335524006387884938644931 := by
  unfold tailWord_980146
  simp only [CollatzResearch.WordTrace]
  refine ⟨8937215376776478113716073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23832574338070608303242861 8937215376776478113716073)
  ·
    refine ⟨6702911532582358585287055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8937215376776478113716073 6702911532582358585287055)
    ·
      refine ⟨10054367298873537877930583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6702911532582358585287055 10054367298873537877930583)
      ·
        refine ⟨15081550948310306816895875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10054367298873537877930583 15081550948310306816895875)
        ·
          refine ⟨22622326422465460225343813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15081550948310306816895875 22622326422465460225343813)
          ·
            refine ⟨4241686204212273792251965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22622326422465460225343813 4241686204212273792251965)
            ·
              refine ⟨1590632326579602672094487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4241686204212273792251965 1590632326579602672094487)
              ·
                refine ⟨2385948489869404008141731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1590632326579602672094487 2385948489869404008141731)
                ·
                  refine ⟨3578922734804106012212597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2385948489869404008141731 3578922734804106012212597)
                  ·
                    refine ⟨335524006387884938644931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3578922734804106012212597 335524006387884938644931)
                    ·
                      rfl

theorem cell22_980146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_980146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_980146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_980146 prefixEnd_980146 := by exact prefixLift 980146
  have htrace : WordTrace (prefixWord ++ tailWord_980146) baseStart_980146 baseEnd_980146 := by
    simpa [prefixWord, tailWord_980146, baseEnd_980146] using wordTrace_append hprefix tailTrace_980146
  have hstable : (prefixWord ++ tailWord_980146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980146).length < 2 ^ (prefixWord ++ tailWord_980146).sum := by decide
  have hdescent : baseEnd_980146 < baseStart_980146 := by decide
  rcases family_descends (prefixWord ++ tailWord_980146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980182 : List Nat := [5, 2, 1, 2, 3, 1, 1, 1, 6]
def baseStart_980182 : Nat := 118140960795 + 980182 * 2 ^ 59
def prefixEnd_980182 : Nat := 4983230072969 + 3 ^ 40 * 980182 * 2
def baseEnd_980182 : Nat := 111845443307864281581607

theorem tailTrace_980182 : CollatzResearch.WordTrace tailWord_980182 prefixEnd_980182 111845443307864281581607 := by
  unfold tailWord_980182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2234385908435968162698425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23833449689983660402116533 2234385908435968162698425)
  ·
    refine ⟨1675789431326976122023819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2234385908435968162698425 1675789431326976122023819)
    ·
      refine ⟨2513684146990464183035729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1675789431326976122023819 2513684146990464183035729)
      ·
        refine ⟨1885263110242848137276797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2513684146990464183035729 1885263110242848137276797)
        ·
          refine ⟨706973666341068051478799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1885263110242848137276797 706973666341068051478799)
          ·
            refine ⟨1060460499511602077218199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706973666341068051478799 1060460499511602077218199)
            ·
              refine ⟨1590690749267403115827299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1060460499511602077218199 1590690749267403115827299)
              ·
                refine ⟨2386036123901104673740949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1590690749267403115827299 2386036123901104673740949)
                ·
                  refine ⟨111845443307864281581607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2386036123901104673740949 111845443307864281581607)
                  ·
                    rfl

theorem cell22_980182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_980182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_980182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_980182 prefixEnd_980182 := by exact prefixLift 980182
  have htrace : WordTrace (prefixWord ++ tailWord_980182) baseStart_980182 baseEnd_980182 := by
    simpa [prefixWord, tailWord_980182, baseEnd_980182] using wordTrace_append hprefix tailTrace_980182
  have hstable : (prefixWord ++ tailWord_980182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980182).length < 2 ^ (prefixWord ++ tailWord_980182).sum := by decide
  have hdescent : baseEnd_980182 < baseStart_980182 := by decide
  rcases family_descends (prefixWord ++ tailWord_980182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980197 : List Nat := [1, 3, 1, 4, 3, 2, 2, 1, 2, 3]
def baseStart_980197 : Nat := 118140960795 + 980197 * 2 ^ 59
def prefixEnd_980197 : Nat := 4983230072969 + 3 ^ 40 * 980197 * 2
def baseEnd_980197 : Nat := 335541464730137805619775

theorem tailTrace_980197 : CollatzResearch.WordTrace tailWord_980197 prefixEnd_980197 335541464730137805619775 := by
  unfold tailWord_980197
  simp only [CollatzResearch.WordTrace]
  refine ⟨35750721629921148164970845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23833814419947432109980563 35750721629921148164970845)
  ·
    refine ⟨13406520611220430561864067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35750721629921148164970845 13406520611220430561864067)
    ·
      refine ⟨20109780916830645842796101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13406520611220430561864067 20109780916830645842796101)
      ·
        refine ⟨3770583921905746095524269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20109780916830645842796101 3770583921905746095524269)
        ·
          refine ⟨1413968970714654785821601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3770583921905746095524269 1413968970714654785821601)
          ·
            refine ⟨1060476728035991089366201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1413968970714654785821601 1060476728035991089366201)
            ·
              refine ⟨795357546026993317024651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1060476728035991089366201 795357546026993317024651)
              ·
                refine ⟨1193036319040489975536977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 795357546026993317024651 1193036319040489975536977)
                ·
                  refine ⟨894777239280367481652733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1193036319040489975536977 894777239280367481652733)
                  ·
                    refine ⟨335541464730137805619775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 894777239280367481652733 335541464730137805619775)
                    ·
                      rfl

theorem cell22_980197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 2, 3].length) (baseStart_980197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_980197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_980197 prefixEnd_980197 := by exact prefixLift 980197
  have htrace : WordTrace (prefixWord ++ tailWord_980197) baseStart_980197 baseEnd_980197 := by
    simpa [prefixWord, tailWord_980197, baseEnd_980197] using wordTrace_append hprefix tailTrace_980197
  have hstable : (prefixWord ++ tailWord_980197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980197).length < 2 ^ (prefixWord ++ tailWord_980197).sum := by decide
  have hdescent : baseEnd_980197 < baseStart_980197 := by decide
  rcases family_descends (prefixWord ++ tailWord_980197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980238 : List Nat := [4, 1, 1, 2, 1, 4, 2, 2, 5]
def baseStart_980238 : Nat := 118140960795 + 980238 * 2 ^ 59
def prefixEnd_980238 : Nat := 4983230072969 + 3 ^ 40 * 980238 * 2
def baseEnd_980238 : Nat := 111851833289342455114883

theorem tailTrace_980238 : CollatzResearch.WordTrace tailWord_980238 prefixEnd_980238 111851833289342455114883 := by
  unfold tailWord_980238
  simp only [CollatzResearch.WordTrace]
  refine ⟨4469027127846576520901671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23834811348515074778142245 4469027127846576520901671)
  ·
    refine ⟨6703540691769864781352507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4469027127846576520901671 6703540691769864781352507)
    ·
      refine ⟨10055311037654797172028761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6703540691769864781352507 10055311037654797172028761)
      ·
        refine ⟨7541483278241097879021571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10055311037654797172028761 7541483278241097879021571)
        ·
          refine ⟨11312224917361646818532357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7541483278241097879021571 11312224917361646818532357)
          ·
            refine ⟨2121042172005308778474817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11312224917361646818532357 2121042172005308778474817)
            ·
              refine ⟨1590781629003981583856113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2121042172005308778474817 1590781629003981583856113)
              ·
                refine ⟨1193086221752986187892085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1590781629003981583856113 1193086221752986187892085)
                ·
                  refine ⟨111851833289342455114883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1193086221752986187892085 111851833289342455114883)
                  ·
                    rfl

theorem cell22_980238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_980238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_980238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_980238 prefixEnd_980238 := by exact prefixLift 980238
  have htrace : WordTrace (prefixWord ++ tailWord_980238) baseStart_980238 baseEnd_980238 := by
    simpa [prefixWord, tailWord_980238, baseEnd_980238] using wordTrace_append hprefix tailTrace_980238
  have hstable : (prefixWord ++ tailWord_980238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980238).length < 2 ^ (prefixWord ++ tailWord_980238).sum := by decide
  have hdescent : baseEnd_980238 < baseStart_980238 := by decide
  rcases family_descends (prefixWord ++ tailWord_980238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980249 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 12]
def baseStart_980249 : Nat := 118140960795 + 980249 * 2 ^ 59
def prefixEnd_980249 : Nat := 4983230072969 + 3 ^ 40 * 980249 * 2
def baseEnd_980249 : Nat := 111853088464275667773205

theorem tailTrace_980249 : CollatzResearch.WordTrace tailWord_980249 prefixEnd_980249 111853088464275667773205 := by
  unfold tailWord_980249
  simp only [CollatzResearch.WordTrace]
  refine ⟨35752618225732761045863801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23835078817155174030575867 35752618225732761045863801)
  ·
    refine ⟨26814463669299570784397851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35752618225732761045863801 26814463669299570784397851)
    ·
      refine ⟨40221695503949356176596777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26814463669299570784397851 40221695503949356176596777)
      ·
        refine ⟨30166271627962017132447583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40221695503949356176596777 30166271627962017132447583)
        ·
          refine ⟨45249407441943025698671375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30166271627962017132447583 45249407441943025698671375)
          ·
            refine ⟨67874111162914538548007063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45249407441943025698671375 67874111162914538548007063)
            ·
              refine ⟨101811166744371807822010595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67874111162914538548007063 101811166744371807822010595)
              ·
                refine ⟨152716750116557711733015893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101811166744371807822010595 152716750116557711733015893)
                ·
                  refine ⟨111853088464275667773205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 152716750116557711733015893 111853088464275667773205)
                  ·
                    rfl

theorem cell22_980249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 12].length) (baseStart_980249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_980249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_980249 prefixEnd_980249 := by exact prefixLift 980249
  have htrace : WordTrace (prefixWord ++ tailWord_980249) baseStart_980249 baseEnd_980249 := by
    simpa [prefixWord, tailWord_980249, baseEnd_980249] using wordTrace_append hprefix tailTrace_980249
  have hstable : (prefixWord ++ tailWord_980249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980249).length < 2 ^ (prefixWord ++ tailWord_980249).sum := by decide
  have hdescent : baseEnd_980249 < baseStart_980249 := by decide
  rcases family_descends (prefixWord ++ tailWord_980249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980253 : List Nat := [1, 4, 2, 3, 1, 2, 1, 1, 2, 5]
def baseStart_980253 : Nat := 118140960795 + 980253 * 2 ^ 59
def prefixEnd_980253 : Nat := 4983230072969 + 3 ^ 40 * 980253 * 2
def baseEnd_980253 : Nat := 335560634674572326219603

theorem tailTrace_980253 : CollatzResearch.WordTrace tailWord_980253 prefixEnd_980253 335560634674572326219603 := by
  unfold tailWord_980253
  simp only [CollatzResearch.WordTrace]
  refine ⟨35752764117718269729009413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23835176078478846486006275 35752764117718269729009413)
  ·
    refine ⟨6703643272072175574189265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35752764117718269729009413 6703643272072175574189265)
    ·
      refine ⟨5027732454054131680641949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6703643272072175574189265 5027732454054131680641949)
      ·
        refine ⟨1885399670270299380240731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5027732454054131680641949 1885399670270299380240731)
        ·
          refine ⟨2828099505405449070361097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1885399670270299380240731 2828099505405449070361097)
          ·
            refine ⟨2121074629054086802770823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2828099505405449070361097 2121074629054086802770823)
            ·
              refine ⟨3181611943581130204156235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2121074629054086802770823 3181611943581130204156235)
              ·
                refine ⟨4772417915371695306234353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3181611943581130204156235 4772417915371695306234353)
                ·
                  refine ⟨3579313436528771479675765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4772417915371695306234353 3579313436528771479675765)
                  ·
                    refine ⟨335560634674572326219603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3579313436528771479675765 335560634674572326219603)
                    ·
                      rfl

theorem cell22_980253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_980253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_980253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_980253 prefixEnd_980253 := by exact prefixLift 980253
  have htrace : WordTrace (prefixWord ++ tailWord_980253) baseStart_980253 baseEnd_980253 := by
    simpa [prefixWord, tailWord_980253, baseEnd_980253] using wordTrace_append hprefix tailTrace_980253
  have hstable : (prefixWord ++ tailWord_980253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980253).length < 2 ^ (prefixWord ++ tailWord_980253).sum := by decide
  have hdescent : baseEnd_980253 < baseStart_980253 := by decide
  rcases family_descends (prefixWord ++ tailWord_980253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980296 : List Nat := [2, 1, 3, 1, 1, 2, 1, 3, 4, 4]
def baseStart_980296 : Nat := 118140960795 + 980296 * 2 ^ 59
def prefixEnd_980296 : Nat := 4983230072969 + 3 ^ 40 * 980296 * 2
def baseEnd_980296 : Nat := 335575354453334547394471

theorem tailTrace_980296 : CollatzResearch.WordTrace tailWord_980296 prefixEnd_980296 335575354453334547394471 := by
  unfold tailWord_980296
  simp only [CollatzResearch.WordTrace]
  refine ⟨17877166228281244036412371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23836221637708325381883161 17877166228281244036412371)
  ·
    refine ⟨26815749342421866054618557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17877166228281244036412371 26815749342421866054618557)
    ·
      refine ⟨10055906003408199770481959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26815749342421866054618557 10055906003408199770481959)
      ·
        refine ⟨15083859005112299655722939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10055906003408199770481959 15083859005112299655722939)
        ·
          refine ⟨22625788507668449483584409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15083859005112299655722939 22625788507668449483584409)
          ·
            refine ⟨16969341380751337112688307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22625788507668449483584409 16969341380751337112688307)
            ·
              refine ⟨25454012071127005669032461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16969341380751337112688307 25454012071127005669032461)
              ·
                refine ⟨9545254526672627125887173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25454012071127005669032461 9545254526672627125887173)
                ·
                  refine ⟨1789735223751117586103845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9545254526672627125887173 1789735223751117586103845)
                  ·
                    refine ⟨335575354453334547394471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1789735223751117586103845 335575354453334547394471)
                    ·
                      rfl

theorem cell22_980296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_980296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_980296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_980296 prefixEnd_980296 := by exact prefixLift 980296
  have htrace : WordTrace (prefixWord ++ tailWord_980296) baseStart_980296 baseEnd_980296 := by
    simpa [prefixWord, tailWord_980296, baseEnd_980296] using wordTrace_append hprefix tailTrace_980296
  have hstable : (prefixWord ++ tailWord_980296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980296).length < 2 ^ (prefixWord ++ tailWord_980296).sum := by decide
  have hdescent : baseEnd_980296 < baseStart_980296 := by decide
  rcases family_descends (prefixWord ++ tailWord_980296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980328 : List Nat := [2, 1, 4, 2, 3, 1, 1, 8]
def baseStart_980328 : Nat := 118140960795 + 980328 * 2 ^ 59
def prefixEnd_980328 : Nat := 4983230072969 + 3 ^ 40 * 980328 * 2
def baseEnd_980328 : Nat := 37287367634144125621597

theorem tailTrace_980328 : CollatzResearch.WordTrace tailWord_980328 prefixEnd_980328 37287367634144125621597 := by
  unfold tailWord_980328
  simp only [CollatzResearch.WordTrace]
  refine ⟨17877749796223278768994819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23836999728297705025326425 17877749796223278768994819)
  ·
    refine ⟨26816624694334918153492229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17877749796223278768994819 26816624694334918153492229)
    ·
      refine ⟨5028117130187797153779793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26816624694334918153492229 5028117130187797153779793)
      ·
        refine ⟨3771087847640847865334845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5028117130187797153779793 3771087847640847865334845)
        ·
          refine ⟨1414157942865317949500567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3771087847640847865334845 1414157942865317949500567)
          ·
            refine ⟨2121236914297976924250851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1414157942865317949500567 2121236914297976924250851)
            ·
              refine ⟨3181855371446965386376277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2121236914297976924250851 3181855371446965386376277)
              ·
                refine ⟨37287367634144125621597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3181855371446965386376277 37287367634144125621597)
                ·
                  rfl

theorem cell22_980328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 8].length) (baseStart_980328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_980328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_980328 prefixEnd_980328 := by exact prefixLift 980328
  have htrace : WordTrace (prefixWord ++ tailWord_980328) baseStart_980328 baseEnd_980328 := by
    simpa [prefixWord, tailWord_980328, baseEnd_980328] using wordTrace_append hprefix tailTrace_980328
  have hstable : (prefixWord ++ tailWord_980328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980328).length < 2 ^ (prefixWord ++ tailWord_980328).sum := by decide
  have hdescent : baseEnd_980328 < baseStart_980328 := by decide
  rcases family_descends (prefixWord ++ tailWord_980328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980334 : List Nat := [4, 1, 2, 4, 1, 2, 1, 3, 4]
def baseStart_980334 : Nat := 118140960795 + 980334 * 2 ^ 59
def prefixEnd_980334 : Nat := 4983230072969 + 3 ^ 40 * 980334 * 2
def baseEnd_980334 : Nat := 111862787543305038314785

theorem tailTrace_980334 : CollatzResearch.WordTrace tailWord_980334 prefixEnd_980334 111862787543305038314785 := by
  unfold tailWord_980334
  simp only [CollatzResearch.WordTrace]
  refine ⟨4469464803803102570338507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23837145620283213708472037 4469464803803102570338507)
  ·
    refine ⟨6704197205704653855507761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4469464803803102570338507 6704197205704653855507761)
    ·
      refine ⟨5028147904278490391630821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6704197205704653855507761 5028147904278490391630821)
      ·
        refine ⟨942777732052216948430779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5028147904278490391630821 942777732052216948430779)
        ·
          refine ⟨1414166598078325422646169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 942777732052216948430779 1414166598078325422646169)
          ·
            refine ⟨1060624948558744066984627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1414166598078325422646169 1060624948558744066984627)
            ·
              refine ⟨1590937422838116100476941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1060624948558744066984627 1590937422838116100476941)
              ·
                refine ⟨596601533564293537678853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1590937422838116100476941 596601533564293537678853)
                ·
                  refine ⟨111862787543305038314785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 596601533564293537678853 111862787543305038314785)
                  ·
                    rfl

theorem cell22_980334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_980334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_980334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_980334 prefixEnd_980334 := by exact prefixLift 980334
  have htrace : WordTrace (prefixWord ++ tailWord_980334) baseStart_980334 baseEnd_980334 := by
    simpa [prefixWord, tailWord_980334, baseEnd_980334] using wordTrace_append hprefix tailTrace_980334
  have hstable : (prefixWord ++ tailWord_980334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980334).length < 2 ^ (prefixWord ++ tailWord_980334).sum := by decide
  have hdescent : baseEnd_980334 < baseStart_980334 := by decide
  rcases family_descends (prefixWord ++ tailWord_980334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980360 : List Nat := [2, 1, 3, 3, 1, 2, 3, 1, 3, 3]
def baseStart_980360 : Nat := 118140960795 + 980360 * 2 ^ 59
def prefixEnd_980360 : Nat := 4983230072969 + 3 ^ 40 * 980360 * 2
def baseEnd_980360 : Nat := 335597262961259713794275

theorem tailTrace_980360 : CollatzResearch.WordTrace tailWord_980360 prefixEnd_980360 335597262961259713794275 := by
  unfold tailWord_980360
  simp only [CollatzResearch.WordTrace]
  refine ⟨17878333364165313501577267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23837777818887084668769689 17878333364165313501577267)
  ·
    refine ⟨26817500046247970252365901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17878333364165313501577267 26817500046247970252365901)
    ·
      refine ⟨10056562517342988844637213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26817500046247970252365901 10056562517342988844637213)
      ·
        refine ⟨3771210944003620816738955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10056562517342988844637213 3771210944003620816738955)
        ·
          refine ⟨5656816416005431225108433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3771210944003620816738955 5656816416005431225108433)
          ·
            refine ⟨4242612312004073418831325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5656816416005431225108433 4242612312004073418831325)
            ·
              refine ⟨1590979617001527532061747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4242612312004073418831325 1590979617001527532061747)
              ·
                refine ⟨2386469425502291298092621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1590979617001527532061747 2386469425502291298092621)
                ·
                  refine ⟨894926034563359236784733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2386469425502291298092621 894926034563359236784733)
                  ·
                    refine ⟨335597262961259713794275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 894926034563359236784733 335597262961259713794275)
                    ·
                      rfl

theorem cell22_980360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_980360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_980360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_980360 prefixEnd_980360 := by exact prefixLift 980360
  have htrace : WordTrace (prefixWord ++ tailWord_980360) baseStart_980360 baseEnd_980360 := by
    simpa [prefixWord, tailWord_980360, baseEnd_980360] using wordTrace_append hprefix tailTrace_980360
  have hstable : (prefixWord ++ tailWord_980360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980360).length < 2 ^ (prefixWord ++ tailWord_980360).sum := by decide
  have hdescent : baseEnd_980360 < baseStart_980360 := by decide
  rcases family_descends (prefixWord ++ tailWord_980360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980366 : List Nat := [4, 1, 1, 4, 3, 1, 2, 1, 2, 3]
def baseStart_980366 : Nat := 118140960795 + 980366 * 2 ^ 59
def prefixEnd_980366 : Nat := 4983230072969 + 3 ^ 40 * 980366 * 2
def baseEnd_980366 : Nat := 335599316883877698144257

theorem tailTrace_980366 : CollatzResearch.WordTrace tailWord_980366 prefixEnd_980366 335599316883877698144257 := by
  unfold tailWord_980366
  simp only [CollatzResearch.WordTrace]
  refine ⟨4469610695788611253484119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23837923710872593351915301 4469610695788611253484119)
  ·
    refine ⟨6704416043682916880226179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4469610695788611253484119 6704416043682916880226179)
    ·
      refine ⟨10056624065524375320339269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6704416043682916880226179 10056624065524375320339269)
      ·
        refine ⟨1885617012285820372563613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10056624065524375320339269 1885617012285820372563613)
        ·
          refine ⟨707106379607182639711355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1885617012285820372563613 707106379607182639711355)
          ·
            refine ⟨1060659569410773959567033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 707106379607182639711355 1060659569410773959567033)
            ·
              refine ⟨795494677058080469675275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1060659569410773959567033 795494677058080469675275)
              ·
                refine ⟨1193242015587120704512913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 795494677058080469675275 1193242015587120704512913)
                ·
                  refine ⟨894931511690340528384685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1193242015587120704512913 894931511690340528384685)
                  ·
                    refine ⟨335599316883877698144257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 894931511690340528384685 335599316883877698144257)
                    ·
                      rfl

theorem cell22_980366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 2, 3].length) (baseStart_980366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_980366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_980366 prefixEnd_980366 := by exact prefixLift 980366
  have htrace : WordTrace (prefixWord ++ tailWord_980366) baseStart_980366 baseEnd_980366 := by
    simpa [prefixWord, tailWord_980366, baseEnd_980366] using wordTrace_append hprefix tailTrace_980366
  have hstable : (prefixWord ++ tailWord_980366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980366).length < 2 ^ (prefixWord ++ tailWord_980366).sum := by decide
  have hdescent : baseEnd_980366 < baseStart_980366 := by decide
  rcases family_descends (prefixWord ++ tailWord_980366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980403 : List Nat := [1, 1, 1, 2, 3, 1, 1, 7, 1, 4]
def baseStart_980403 : Nat := 118140960795 + 980403 * 2 ^ 59
def prefixEnd_980403 : Nat := 4983230072969 + 3 ^ 40 * 980403 * 2
def baseEnd_980403 : Nat := 335611982740021934969143

theorem tailTrace_980403 : CollatzResearch.WordTrace tailWord_980403 prefixEnd_980403 335611982740021934969143 := by
  unfold tailWord_980403
  simp only [CollatzResearch.WordTrace]
  refine ⟨35758235067174845346969863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23838823378116563564646575 35758235067174845346969863)
  ·
    refine ⟨53637352600762268020454795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35758235067174845346969863 53637352600762268020454795)
    ·
      refine ⟨80456028901143402030682193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53637352600762268020454795 80456028901143402030682193)
      ·
        refine ⟨60342021675857551523011645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80456028901143402030682193 60342021675857551523011645)
        ·
          refine ⟨22628258128446581821129367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60342021675857551523011645 22628258128446581821129367)
          ·
            refine ⟨33942387192669872731694051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22628258128446581821129367 33942387192669872731694051)
            ·
              refine ⟨50913580789004809097541077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33942387192669872731694051 50913580789004809097541077)
              ·
                refine ⟨1193287049742300213223619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 50913580789004809097541077 1193287049742300213223619)
                ·
                  refine ⟨1789930574613450319835429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1193287049742300213223619 1789930574613450319835429)
                  ·
                    refine ⟨335611982740021934969143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1789930574613450319835429 335611982740021934969143)
                    ·
                      rfl

theorem cell22_980403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 4].length) (baseStart_980403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_980403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_980403 prefixEnd_980403 := by exact prefixLift 980403
  have htrace : WordTrace (prefixWord ++ tailWord_980403) baseStart_980403 baseEnd_980403 := by
    simpa [prefixWord, tailWord_980403, baseEnd_980403] using wordTrace_append hprefix tailTrace_980403
  have hstable : (prefixWord ++ tailWord_980403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980403).length < 2 ^ (prefixWord ++ tailWord_980403).sum := by decide
  have hdescent : baseEnd_980403 < baseStart_980403 := by decide
  rcases family_descends (prefixWord ++ tailWord_980403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980420 : List Nat := [2, 3, 3, 2, 1, 1, 1, 2, 3, 4]
def baseStart_980420 : Nat := 118140960795 + 980420 * 2 ^ 59
def prefixEnd_980420 : Nat := 4983230072969 + 3 ^ 40 * 980420 * 2
def baseEnd_980420 : Nat := 335617802187439557294091

theorem tailTrace_980420 : CollatzResearch.WordTrace tailWord_980420 prefixEnd_980420 335617802187439557294091 := by
  unfold tailWord_980420
  simp only [CollatzResearch.WordTrace]
  refine ⟨17879427554056628625169357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23839236738742171500225809 17879427554056628625169357)
  ·
    refine ⟨6704785332771235734438509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17879427554056628625169357 6704785332771235734438509)
    ·
      refine ⟨2514294499789213400414441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6704785332771235734438509 2514294499789213400414441)
      ·
        refine ⟨1885720874841910050310831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2514294499789213400414441 1885720874841910050310831)
        ·
          refine ⟨2828581312262865075466247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1885720874841910050310831 2828581312262865075466247)
          ·
            refine ⟨4242871968394297613199371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2828581312262865075466247 4242871968394297613199371)
            ·
              refine ⟨6364307952591446419799057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4242871968394297613199371 6364307952591446419799057)
              ·
                refine ⟨4773230964443584814849293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6364307952591446419799057 4773230964443584814849293)
                ·
                  refine ⟨1789961611666344305568485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4773230964443584814849293 1789961611666344305568485)
                  ·
                    refine ⟨335617802187439557294091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1789961611666344305568485 335617802187439557294091)
                    ·
                      rfl

theorem cell22_980420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_980420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_980420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_980420 prefixEnd_980420 := by exact prefixLift 980420
  have htrace : WordTrace (prefixWord ++ tailWord_980420) baseStart_980420 baseEnd_980420 := by
    simpa [prefixWord, tailWord_980420, baseEnd_980420] using wordTrace_append hprefix tailTrace_980420
  have hstable : (prefixWord ++ tailWord_980420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980420).length < 2 ^ (prefixWord ++ tailWord_980420).sum := by decide
  have hdescent : baseEnd_980420 < baseStart_980420 := by decide
  rcases family_descends (prefixWord ++ tailWord_980420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980433 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 8, 3]
def baseStart_980433 : Nat := 118140960795 + 980433 * 2 ^ 59
def prefixEnd_980433 : Nat := 4983230072969 + 3 ^ 40 * 980433 * 2
def baseEnd_980433 : Nat := 335622252353111856719051

theorem tailTrace_980433 : CollatzResearch.WordTrace tailWord_980433 prefixEnd_980433 335622252353111856719051 := by
  unfold tailWord_980433
  simp only [CollatzResearch.WordTrace]
  refine ⟨35759329257066160470561953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23839552838044106980374635 35759329257066160470561953)
  ·
    refine ⟨26819496942799620352921465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35759329257066160470561953 26819496942799620352921465)
    ·
      refine ⟨20114622707099715264691099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26819496942799620352921465 20114622707099715264691099)
      ·
        refine ⟨30171934060649572897036649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20114622707099715264691099 30171934060649572897036649)
        ·
          refine ⟨22628950545487179672777487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30171934060649572897036649 22628950545487179672777487)
          ·
            refine ⟨33943425818230769509166231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22628950545487179672777487 33943425818230769509166231)
            ·
              refine ⟨50915138727346154263749347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33943425818230769509166231 50915138727346154263749347)
              ·
                refine ⟨76372708091019231395624021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50915138727346154263749347 76372708091019231395624021)
                ·
                  refine ⟨894992672941631617917469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 76372708091019231395624021 894992672941631617917469)
                  ·
                    refine ⟨335622252353111856719051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 894992672941631617917469 335622252353111856719051)
                    ·
                      rfl

theorem cell22_980433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 8, 3].length) (baseStart_980433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_980433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_980433 prefixEnd_980433 := by exact prefixLift 980433
  have htrace : WordTrace (prefixWord ++ tailWord_980433) baseStart_980433 baseEnd_980433 := by
    simpa [prefixWord, tailWord_980433, baseEnd_980433] using wordTrace_append hprefix tailTrace_980433
  have hstable : (prefixWord ++ tailWord_980433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980433).length < 2 ^ (prefixWord ++ tailWord_980433).sum := by decide
  have hdescent : baseEnd_980433 < baseStart_980433 := by decide
  rcases family_descends (prefixWord ++ tailWord_980433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980448 : List Nat := [2, 1, 1, 3, 1, 1, 2, 5, 2, 4]
def baseStart_980448 : Nat := 118140960795 + 980448 * 2 ^ 59
def prefixEnd_980448 : Nat := 4983230072969 + 3 ^ 40 * 980448 * 2
def baseEnd_980448 : Nat := 335627387159656817594005

theorem tailTrace_980448 : CollatzResearch.WordTrace tailWord_980448 prefixEnd_980448 335627387159656817594005 := by
  unfold tailWord_980448
  simp only [CollatzResearch.WordTrace]
  refine ⟨17879938176005909016178999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23839917568007878688238665 17879938176005909016178999)
  ·
    refine ⟨26819907264008863524268499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17879938176005909016178999 26819907264008863524268499)
    ·
      refine ⟨40229860896013295286402749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26819907264008863524268499 40229860896013295286402749)
      ·
        refine ⟨15086197836004985732401031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40229860896013295286402749 15086197836004985732401031)
        ·
          refine ⟨22629296754007478598601547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15086197836004985732401031 22629296754007478598601547)
          ·
            refine ⟨33943945131011217897902321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22629296754007478598601547 33943945131011217897902321)
            ·
              refine ⟨25457958848258413423426741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33943945131011217897902321 25457958848258413423426741)
              ·
                refine ⟨2386683642024226258446257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25457958848258413423426741 2386683642024226258446257)
                ·
                  refine ⟨1790012731518169693834693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2386683642024226258446257 1790012731518169693834693)
                  ·
                    refine ⟨335627387159656817594005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1790012731518169693834693 335627387159656817594005)
                    ·
                      rfl

theorem cell22_980448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 2, 4].length) (baseStart_980448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_980448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_980448 prefixEnd_980448 := by exact prefixLift 980448
  have htrace : WordTrace (prefixWord ++ tailWord_980448) baseStart_980448 baseEnd_980448 := by
    simpa [prefixWord, tailWord_980448, baseEnd_980448] using wordTrace_append hprefix tailTrace_980448
  have hstable : (prefixWord ++ tailWord_980448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980448).length < 2 ^ (prefixWord ++ tailWord_980448).sum := by decide
  have hdescent : baseEnd_980448 < baseStart_980448 := by decide
  rcases family_descends (prefixWord ++ tailWord_980448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980484 : List Nat := [2, 3, 2, 3, 3, 1, 1, 1, 1, 5]
def baseStart_980484 : Nat := 118140960795 + 980484 * 2 ^ 59
def prefixEnd_980484 : Nat := 4983230072969 + 3 ^ 40 * 980484 * 2
def baseEnd_980484 : Nat := 335639710695364723693895

theorem tailTrace_980484 : CollatzResearch.WordTrace tailWord_980484 prefixEnd_980484 335639710695364723693895 := by
  unfold tailWord_980484
  simp only [CollatzResearch.WordTrace]
  refine ⟨17880594689940698090334253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23840792919920930787112337 17880594689940698090334253)
  ·
    refine ⟨6705223008727761783875345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17880594689940698090334253 6705223008727761783875345)
    ·
      refine ⟨5028917256545821337906509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6705223008727761783875345 5028917256545821337906509)
      ·
        refine ⟨1885843971204683001714941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5028917256545821337906509 1885843971204683001714941)
        ·
          refine ⟨707191489201756125643103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1885843971204683001714941 707191489201756125643103)
          ·
            refine ⟨1060787233802634188464655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 707191489201756125643103 1060787233802634188464655)
            ·
              refine ⟨1591180850703951282696983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1060787233802634188464655 1591180850703951282696983)
              ·
                refine ⟨2386771276055926924045475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1591180850703951282696983 2386771276055926924045475)
                ·
                  refine ⟨3580156914083890386068213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2386771276055926924045475 3580156914083890386068213)
                  ·
                    refine ⟨335639710695364723693895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3580156914083890386068213 335639710695364723693895)
                    ·
                      rfl

theorem cell22_980484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_980484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_980484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_980484 prefixEnd_980484 := by exact prefixLift 980484
  have htrace : WordTrace (prefixWord ++ tailWord_980484) baseStart_980484 baseEnd_980484 := by
    simpa [prefixWord, tailWord_980484, baseEnd_980484] using wordTrace_append hprefix tailTrace_980484
  have hstable : (prefixWord ++ tailWord_980484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980484).length < 2 ^ (prefixWord ++ tailWord_980484).sum := by decide
  have hdescent : baseEnd_980484 < baseStart_980484 := by decide
  rcases family_descends (prefixWord ++ tailWord_980484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980508 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 9]
def baseStart_980508 : Nat := 118140960795 + 980508 * 2 ^ 59
def prefixEnd_980508 : Nat := 4983230072969 + 3 ^ 40 * 980508 * 2
def baseEnd_980508 : Nat := 111882642128612220364607

theorem tailTrace_980508 : CollatzResearch.WordTrace tailWord_980508 prefixEnd_980508 111882642128612220364607 := by
  unfold tailWord_980508
  simp only [CollatzResearch.WordTrace]
  refine ⟨17881032365897224139771089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23841376487862965519694785 17881032365897224139771089)
  ·
    refine ⟨13410774274422918104828317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17881032365897224139771089 13410774274422918104828317)
    ·
      refine ⟨5029040352908594289310619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13410774274422918104828317 5029040352908594289310619)
      ·
        refine ⟨7543560529362891433965929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5029040352908594289310619 7543560529362891433965929)
        ·
          refine ⟨5657670397022168575474447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7543560529362891433965929 5657670397022168575474447)
          ·
            refine ⟨8486505595533252863211671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5657670397022168575474447 8486505595533252863211671)
            ·
              refine ⟨12729758393299879294817507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8486505595533252863211671 12729758393299879294817507)
              ·
                refine ⟨19094637589949818942226261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12729758393299879294817507 19094637589949818942226261)
                ·
                  refine ⟨111882642128612220364607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19094637589949818942226261 111882642128612220364607)
                  ·
                    rfl

theorem cell22_980508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 9].length) (baseStart_980508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_980508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_980508 prefixEnd_980508 := by exact prefixLift 980508
  have htrace : WordTrace (prefixWord ++ tailWord_980508) baseStart_980508 baseEnd_980508 := by
    simpa [prefixWord, tailWord_980508, baseEnd_980508] using wordTrace_append hprefix tailTrace_980508
  have hstable : (prefixWord ++ tailWord_980508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980508).length < 2 ^ (prefixWord ++ tailWord_980508).sum := by decide
  have hdescent : baseEnd_980508 < baseStart_980508 := by decide
  rcases family_descends (prefixWord ++ tailWord_980508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980553 : List Nat := [1, 2, 1, 1, 2, 2, 1, 6, 6]
def baseStart_980553 : Nat := 118140960795 + 980553 * 2 ^ 59
def prefixEnd_980553 : Nat := 4983230072969 + 3 ^ 40 * 980553 * 2
def baseEnd_980553 : Nat := 111887776935157181239561

theorem tailTrace_980553 : CollatzResearch.WordTrace tailWord_980553 prefixEnd_980553 111887776935157181239561 := by
  unfold tailWord_980553
  simp only [CollatzResearch.WordTrace]
  refine ⟨35763706016631420964930313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23842470677754280643286875 35763706016631420964930313)
  ·
    refine ⟨26822779512473565723697735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35763706016631420964930313 26822779512473565723697735)
    ·
      refine ⟨40234169268710348585546603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26822779512473565723697735 40234169268710348585546603)
      ·
        refine ⟨60351253903065522878319905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40234169268710348585546603 60351253903065522878319905)
        ·
          refine ⟨45263440427299142158739929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60351253903065522878319905 45263440427299142158739929)
          ·
            refine ⟨33947580320474356619054947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45263440427299142158739929 33947580320474356619054947)
            ·
              refine ⟨50921370480711534928582421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33947580320474356619054947 50921370480711534928582421)
              ·
                refine ⟨2386939241283353199777301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50921370480711534928582421 2386939241283353199777301)
                ·
                  refine ⟨111887776935157181239561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2386939241283353199777301 111887776935157181239561)
                  ·
                    rfl

theorem cell22_980553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 6].length) (baseStart_980553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_980553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_980553 prefixEnd_980553 := by exact prefixLift 980553
  have htrace : WordTrace (prefixWord ++ tailWord_980553) baseStart_980553 baseEnd_980553 := by
    simpa [prefixWord, tailWord_980553, baseEnd_980553] using wordTrace_append hprefix tailTrace_980553
  have hstable : (prefixWord ++ tailWord_980553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980553).length < 2 ^ (prefixWord ++ tailWord_980553).sum := by decide
  have hdescent : baseEnd_980553 < baseStart_980553 := by decide
  rcases family_descends (prefixWord ++ tailWord_980553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980585 : List Nat := [1, 2, 1, 1, 1, 4, 2, 3, 4, 3]
def baseStart_980585 : Nat := 118140960795 + 980585 * 2 ^ 59
def prefixEnd_980585 : Nat := 4983230072969 + 3 ^ 40 * 980585 * 2
def baseEnd_980585 : Nat := 335674285059434126918585

theorem tailTrace_980585 : CollatzResearch.WordTrace tailWord_980585 prefixEnd_980585 335674285059434126918585 := by
  unfold tailWord_980585
  simp only [CollatzResearch.WordTrace]
  refine ⟨35764873152515490430095209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23843248768343660286730139 35764873152515490430095209)
  ·
    refine ⟨26823654864386617822571407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35764873152515490430095209 26823654864386617822571407)
    ·
      refine ⟨40235482296579926733857111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26823654864386617822571407 40235482296579926733857111)
      ·
        refine ⟨60353223444869890100785667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40235482296579926733857111 60353223444869890100785667)
        ·
          refine ⟨90529835167304835151178501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60353223444869890100785667 90529835167304835151178501)
          ·
            refine ⟨16974344093869656590845969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90529835167304835151178501 16974344093869656590845969)
            ·
              refine ⟨12730758070402242443134477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16974344093869656590845969 12730758070402242443134477)
              ·
                refine ⟨4774034276400840916175429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12730758070402242443134477 4774034276400840916175429)
                ·
                  refine ⟨895131426825157671782893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4774034276400840916175429 895131426825157671782893)
                  ·
                    refine ⟨335674285059434126918585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 895131426825157671782893 335674285059434126918585)
                    ·
                      rfl

theorem cell22_980585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 4, 3].length) (baseStart_980585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_980585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_980585 prefixEnd_980585 := by exact prefixLift 980585
  have htrace : WordTrace (prefixWord ++ tailWord_980585) baseStart_980585 baseEnd_980585 := by
    simpa [prefixWord, tailWord_980585, baseEnd_980585] using wordTrace_append hprefix tailTrace_980585
  have hstable : (prefixWord ++ tailWord_980585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980585).length < 2 ^ (prefixWord ++ tailWord_980585).sum := by decide
  have hdescent : baseEnd_980585 < baseStart_980585 := by decide
  rcases family_descends (prefixWord ++ tailWord_980585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980636 : List Nat := [2, 2, 3, 2, 3, 2, 1, 2, 2, 3]
def baseStart_980636 : Nat := 118140960795 + 980636 * 2 ^ 59
def prefixEnd_980636 : Nat := 4983230072969 + 3 ^ 40 * 980636 * 2
def baseEnd_980636 : Nat := 335691743401686993893429

theorem tailTrace_980636 : CollatzResearch.WordTrace tailWord_980636 prefixEnd_980636 335691743401686993893429 := by
  unfold tailWord_980636
  simp only [CollatzResearch.WordTrace]
  refine ⟨17883366637665363070100881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23844488850220484093467841 17883366637665363070100881)
  ·
    refine ⟨13412524978249022302575661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17883366637665363070100881 13412524978249022302575661)
    ·
      refine ⟨5029696866843383363465873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13412524978249022302575661 5029696866843383363465873)
      ·
        refine ⟨3772272650132537522599405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5029696866843383363465873 3772272650132537522599405)
        ·
          refine ⟨1414602243799701570974777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3772272650132537522599405 1414602243799701570974777)
          ·
            refine ⟨1060951682849776178231083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1414602243799701570974777 1060951682849776178231083)
            ·
              refine ⟨1591427524274664267346625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1060951682849776178231083 1591427524274664267346625)
              ·
                refine ⟨1193570643205998200509969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1591427524274664267346625 1193570643205998200509969)
                ·
                  refine ⟨895177982404498650382477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1193570643205998200509969 895177982404498650382477)
                  ·
                    refine ⟨335691743401686993893429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 895177982404498650382477 335691743401686993893429)
                    ·
                      rfl

theorem cell22_980636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_980636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_980636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_980636 prefixEnd_980636 := by exact prefixLift 980636
  have htrace : WordTrace (prefixWord ++ tailWord_980636) baseStart_980636 baseEnd_980636 := by
    simpa [prefixWord, tailWord_980636, baseEnd_980636] using wordTrace_append hprefix tailTrace_980636
  have hstable : (prefixWord ++ tailWord_980636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980636).length < 2 ^ (prefixWord ++ tailWord_980636).sum := by decide
  have hdescent : baseEnd_980636 < baseStart_980636 := by decide
  rcases family_descends (prefixWord ++ tailWord_980636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980735 : List Nat := [1, 1, 2, 2, 1, 3, 2, 3, 1, 6]
def baseStart_980735 : Nat := 118140960795 + 980735 * 2 ^ 59
def prefixEnd_980735 : Nat := 4983230072969 + 3 ^ 40 * 980735 * 2
def baseEnd_980735 : Nat := 335725633124883735668125

theorem tailTrace_980735 : CollatzResearch.WordTrace tailWord_980735 prefixEnd_980735 335725633124883735668125 := by
  unfold tailWord_980735
  simp only [CollatzResearch.WordTrace]
  refine ⟨35770344101972066048055659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23846896067981377365370439 35770344101972066048055659)
  ·
    refine ⟨53655516152958099072083489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35770344101972066048055659 53655516152958099072083489)
    ·
      refine ⟨40241637114718574304062617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53655516152958099072083489 40241637114718574304062617)
      ·
        refine ⟨30181227836038930728046963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40241637114718574304062617 30181227836038930728046963)
        ·
          refine ⟨45271841754058396092070445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30181227836038930728046963 45271841754058396092070445)
          ·
            refine ⟨16976940657771898534526417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45271841754058396092070445 16976940657771898534526417)
            ·
              refine ⟨12732705493328923900894813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16976940657771898534526417 12732705493328923900894813)
              ·
                refine ⟨4774764559998346462835555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12732705493328923900894813 4774764559998346462835555)
                ·
                  refine ⟨7162146839997519694253333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4774764559998346462835555 7162146839997519694253333)
                  ·
                    refine ⟨335725633124883735668125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7162146839997519694253333 335725633124883735668125)
                    ·
                      rfl

theorem cell22_980735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 6].length) (baseStart_980735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_980735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_980735 prefixEnd_980735 := by exact prefixLift 980735
  have htrace : WordTrace (prefixWord ++ tailWord_980735) baseStart_980735 baseEnd_980735 := by
    simpa [prefixWord, tailWord_980735, baseEnd_980735] using wordTrace_append hprefix tailTrace_980735
  have hstable : (prefixWord ++ tailWord_980735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980735).length < 2 ^ (prefixWord ++ tailWord_980735).sum := by decide
  have hdescent : baseEnd_980735 < baseStart_980735 := by decide
  rcases family_descends (prefixWord ++ tailWord_980735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_980737 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 6, 3]
def baseStart_980737 : Nat := 118140960795 + 980737 * 2 ^ 59
def prefixEnd_980737 : Nat := 4983230072969 + 3 ^ 40 * 980737 * 2
def baseEnd_980737 : Nat := 335726317765756397118119

theorem tailTrace_980737 : CollatzResearch.WordTrace tailWord_980737 prefixEnd_980737 335726317765756397118119 := by
  unfold tailWord_980737
  simp only [CollatzResearch.WordTrace]
  refine ⟨35770417047964820389628465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23846944698643213593085643 35770417047964820389628465)
  ·
    refine ⟨26827812785973615292221349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35770417047964820389628465 26827812785973615292221349)
    ·
      refine ⟨5030214897370052867291503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26827812785973615292221349 5030214897370052867291503)
      ·
        refine ⟨7545322346055079300937255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5030214897370052867291503 7545322346055079300937255)
        ·
          refine ⟨11317983519082618951405883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7545322346055079300937255 11317983519082618951405883)
          ·
            refine ⟨16976975278623928427108825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11317983519082618951405883 16976975278623928427108825)
            ·
              refine ⟨12732731458967946320331619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16976975278623928427108825 12732731458967946320331619)
              ·
                refine ⟨19099097188451919480497429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12732731458967946320331619 19099097188451919480497429)
                ·
                  refine ⟨895270180708683725648317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19099097188451919480497429 895270180708683725648317)
                  ·
                    refine ⟨335726317765756397118119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 895270180708683725648317 335726317765756397118119)
                    ·
                      rfl

theorem cell22_980737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_980737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_980737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_980737 prefixEnd_980737 := by exact prefixLift 980737
  have htrace : WordTrace (prefixWord ++ tailWord_980737) baseStart_980737 baseEnd_980737 := by
    simpa [prefixWord, tailWord_980737, baseEnd_980737] using wordTrace_append hprefix tailTrace_980737
  have hstable : (prefixWord ++ tailWord_980737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_980737).length < 2 ^ (prefixWord ++ tailWord_980737).sum := by decide
  have hdescent : baseEnd_980737 < baseStart_980737 := by decide
  rcases family_descends (prefixWord ++ tailWord_980737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981041 : List Nat := [1, 2, 2, 3, 1, 3, 2, 1, 4, 3]
def baseStart_981041 : Nat := 118140960795 + 981041 * 2 ^ 59
def prefixEnd_981041 : Nat := 4983230072969 + 3 ^ 40 * 981041 * 2
def baseEnd_981041 : Nat := 335830383178400937517187

theorem tailTrace_981041 : CollatzResearch.WordTrace tailWord_981041 prefixEnd_981041 335830383178400937517187 := by
  unfold tailWord_981041
  simp only [CollatzResearch.WordTrace]
  refine ⟨35781504838863480308694977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23854336559242320205796651 35781504838863480308694977)
  ·
    refine ⟨26836128629147610231521233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35781504838863480308694977 26836128629147610231521233)
    ·
      refine ⟨20127096471860707673640925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26836128629147610231521233 20127096471860707673640925)
      ·
        refine ⟨7547661176947765377615347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20127096471860707673640925 7547661176947765377615347)
        ·
          refine ⟨11321491765421648066423021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7547661176947765377615347 11321491765421648066423021)
          ·
            refine ⟨4245559412033118024908633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11321491765421648066423021 4245559412033118024908633)
            ·
              refine ⟨3184169559024838518681475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4245559412033118024908633 3184169559024838518681475)
              ·
                refine ⟨4776254338537257778022213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3184169559024838518681475 4776254338537257778022213)
                ·
                  refine ⟨895547688475735833379165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4776254338537257778022213 895547688475735833379165)
                  ·
                    refine ⟨335830383178400937517187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 895547688475735833379165 335830383178400937517187)
                    ·
                      rfl

theorem cell22_981041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 4, 3].length) (baseStart_981041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_981041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_981041 prefixEnd_981041 := by exact prefixLift 981041
  have htrace : WordTrace (prefixWord ++ tailWord_981041) baseStart_981041 baseEnd_981041 := by
    simpa [prefixWord, tailWord_981041, baseEnd_981041] using wordTrace_append hprefix tailTrace_981041
  have hstable : (prefixWord ++ tailWord_981041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981041).length < 2 ^ (prefixWord ++ tailWord_981041).sum := by decide
  have hdescent : baseEnd_981041 < baseStart_981041 := by decide
  rcases family_descends (prefixWord ++ tailWord_981041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981116 : List Nat := [2, 2, 2, 1, 1, 4, 2, 3, 5]
def baseStart_981116 : Nat := 118140960795 + 981116 * 2 ^ 59
def prefixEnd_981116 : Nat := 4983230072969 + 3 ^ 40 * 981116 * 2
def baseEnd_981116 : Nat := 111952019070375247297319

theorem tailTrace_981116 : CollatzResearch.WordTrace tailWord_981116 prefixEnd_981116 111952019070375247297319 := by
  unfold tailWord_981116
  simp only [CollatzResearch.WordTrace]
  refine ⟨17892120156795884058837601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23856160209061178745116801 17892120156795884058837601)
  ·
    refine ⟨13419090117596913044128201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17892120156795884058837601 13419090117596913044128201)
    ·
      refine ⟨10064317588197684783096151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13419090117596913044128201 10064317588197684783096151)
      ·
        refine ⟨15096476382296527174644227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10064317588197684783096151 15096476382296527174644227)
        ·
          refine ⟨22644714573444790761966341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15096476382296527174644227 22644714573444790761966341)
          ·
            refine ⟨4245883982520898267868689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22644714573444790761966341 4245883982520898267868689)
            ·
              refine ⟨3184412986890673700901517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4245883982520898267868689 3184412986890673700901517)
              ·
                refine ⟨1194154870084002637838069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3184412986890673700901517 1194154870084002637838069)
                ·
                  refine ⟨111952019070375247297319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1194154870084002637838069 111952019070375247297319)
                  ·
                    rfl

theorem cell22_981116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 5].length) (baseStart_981116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_981116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_981116 prefixEnd_981116 := by exact prefixLift 981116
  have htrace : WordTrace (prefixWord ++ tailWord_981116) baseStart_981116 baseEnd_981116 := by
    simpa [prefixWord, tailWord_981116, baseEnd_981116] using wordTrace_append hprefix tailTrace_981116
  have hstable : (prefixWord ++ tailWord_981116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981116).length < 2 ^ (prefixWord ++ tailWord_981116).sum := by decide
  have hdescent : baseEnd_981116 < baseStart_981116 := by decide
  rcases family_descends (prefixWord ++ tailWord_981116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981180 : List Nat := [2, 2, 2, 3, 3, 1, 2, 2, 1, 4]
def baseStart_981180 : Nat := 118140960795 + 981180 * 2 ^ 59
def prefixEnd_981180 : Nat := 4983230072969 + 3 ^ 40 * 981180 * 2
def baseEnd_981180 : Nat := 335877965719050908291761

theorem tailTrace_981180 : CollatzResearch.WordTrace tailWord_981180 prefixEnd_981180 335877965719050908291761 := by
  unfold tailWord_981180
  simp only [CollatzResearch.WordTrace]
  refine ⟨17893287292679953524002497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23857716390239938032003329 17893287292679953524002497)
  ·
    refine ⟨13419965469509965143001873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17893287292679953524002497 13419965469509965143001873)
    ·
      refine ⟨10064974102132473857251405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13419965469509965143001873 10064974102132473857251405)
      ·
        refine ⟨3774365288299677696469277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10064974102132473857251405 3774365288299677696469277)
        ·
          refine ⟨1415386983112379136175979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3774365288299677696469277 1415386983112379136175979)
          ·
            refine ⟨2123080474668568704263969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1415386983112379136175979 2123080474668568704263969)
            ·
              refine ⟨1592310356001426528197977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2123080474668568704263969 1592310356001426528197977)
              ·
                refine ⟨1194232767001069896148483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1592310356001426528197977 1194232767001069896148483)
                ·
                  refine ⟨1791349150501604844222725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1194232767001069896148483 1791349150501604844222725)
                  ·
                    refine ⟨335877965719050908291761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1791349150501604844222725 335877965719050908291761)
                    ·
                      rfl

theorem cell22_981180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_981180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_981180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_981180 prefixEnd_981180 := by exact prefixLift 981180
  have htrace : WordTrace (prefixWord ++ tailWord_981180) baseStart_981180 baseEnd_981180 := by
    simpa [prefixWord, tailWord_981180, baseEnd_981180] using wordTrace_append hprefix tailTrace_981180
  have hstable : (prefixWord ++ tailWord_981180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981180).length < 2 ^ (prefixWord ++ tailWord_981180).sum := by decide
  have hdescent : baseEnd_981180 < baseStart_981180 := by decide
  rcases family_descends (prefixWord ++ tailWord_981180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981208 : List Nat := [2, 1, 2, 2, 4, 2, 1, 2, 2, 4]
def baseStart_981208 : Nat := 118140960795 + 981208 * 2 ^ 59
def prefixEnd_981208 : Nat := 4983230072969 + 3 ^ 40 * 981208 * 2
def baseEnd_981208 : Nat := 335887550691268168591675

theorem tailTrace_981208 : CollatzResearch.WordTrace tailWord_981208 prefixEnd_981208 335887550691268168591675 := by
  unfold tailWord_981208
  simp only [CollatzResearch.WordTrace]
  refine ⟨17893797914629233915012139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23858397219505645220016185 17893797914629233915012139)
  ·
    refine ⟨26840696871943850872518209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17893797914629233915012139 26840696871943850872518209)
    ·
      refine ⟨20130522653957888154388657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26840696871943850872518209 20130522653957888154388657)
      ·
        refine ⟨15097891990468416115791493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20130522653957888154388657 15097891990468416115791493)
        ·
          refine ⟨2830854748212828021710905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15097891990468416115791493 2830854748212828021710905)
          ·
            refine ⟨2123141061159621016283179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2830854748212828021710905 2123141061159621016283179)
            ·
              refine ⟨3184711591739431524424769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2123141061159621016283179 3184711591739431524424769)
              ·
                refine ⟨2388533693804573643318577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3184711591739431524424769 2388533693804573643318577)
                ·
                  refine ⟨1791400270353430232488933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2388533693804573643318577 1791400270353430232488933)
                  ·
                    refine ⟨335887550691268168591675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1791400270353430232488933 335887550691268168591675)
                    ·
                      rfl

theorem cell22_981208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_981208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_981208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_981208 prefixEnd_981208 := by exact prefixLift 981208
  have htrace : WordTrace (prefixWord ++ tailWord_981208) baseStart_981208 baseEnd_981208 := by
    simpa [prefixWord, tailWord_981208, baseEnd_981208] using wordTrace_append hprefix tailTrace_981208
  have hstable : (prefixWord ++ tailWord_981208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981208).length < 2 ^ (prefixWord ++ tailWord_981208).sum := by decide
  have hdescent : baseEnd_981208 < baseStart_981208 := by decide
  rcases family_descends (prefixWord ++ tailWord_981208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981212 : List Nat := [2, 2, 5, 2, 1, 2, 1, 1, 6]
def baseStart_981212 : Nat := 118140960795 + 981212 * 2 ^ 59
def prefixEnd_981212 : Nat := 4983230072969 + 3 ^ 40 * 981212 * 2
def baseEnd_981212 : Nat := 111962973324337830497221

theorem tailTrace_981212 : CollatzResearch.WordTrace tailWord_981212 prefixEnd_981212 111962973324337830497221 := by
  unfold tailWord_981212
  simp only [CollatzResearch.WordTrace]
  refine ⟨17893870860621988256584945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23858494480829317675446593 17893870860621988256584945)
  ·
    refine ⟨13420403145466491192438709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17893870860621988256584945 13420403145466491192438709)
    ·
      refine ⟨1258162794887483549291129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13420403145466491192438709 1258162794887483549291129)
      ·
        refine ⟨943622096165612661968347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1258162794887483549291129 943622096165612661968347)
        ·
          refine ⟨1415433144248418992952521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 943622096165612661968347 1415433144248418992952521)
          ·
            refine ⟨1061574858186314244714391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1415433144248418992952521 1061574858186314244714391)
            ·
              refine ⟨1592362287279471367071587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1061574858186314244714391 1592362287279471367071587)
              ·
                refine ⟨2388543430919207050607381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1592362287279471367071587 2388543430919207050607381)
                ·
                  refine ⟨111962973324337830497221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2388543430919207050607381 111962973324337830497221)
                  ·
                    rfl

theorem cell22_981212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 6].length) (baseStart_981212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_981212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_981212 prefixEnd_981212 := by exact prefixLift 981212
  have htrace : WordTrace (prefixWord ++ tailWord_981212) baseStart_981212 baseEnd_981212 := by
    simpa [prefixWord, tailWord_981212, baseEnd_981212] using wordTrace_append hprefix tailTrace_981212
  have hstable : (prefixWord ++ tailWord_981212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981212).length < 2 ^ (prefixWord ++ tailWord_981212).sum := by decide
  have hdescent : baseEnd_981212 < baseStart_981212 := by decide
  rcases family_descends (prefixWord ++ tailWord_981212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981223 : List Nat := [1, 1, 5, 3, 1, 2, 2, 7]
def baseStart_981223 : Nat := 118140960795 + 981223 * 2 ^ 59
def prefixEnd_981223 : Nat := 4983230072969 + 3 ^ 40 * 981223 * 2
def baseEnd_981223 : Nat := 37321409499757014385181

theorem tailTrace_981223 : CollatzResearch.WordTrace tailWord_981223 prefixEnd_981223 37321409499757014385181 := by
  unfold tailWord_981223
  simp only [CollatzResearch.WordTrace]
  refine ⟨35788142924204125391820323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23858761949469416927880215 35788142924204125391820323)
  ·
    refine ⟨53682214386306188087730485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35788142924204125391820323 53682214386306188087730485)
    ·
      refine ⟨5032707598716205133224733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53682214386306188087730485 5032707598716205133224733)
      ·
        refine ⟨1887265349518576924959275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5032707598716205133224733 1887265349518576924959275)
        ·
          refine ⟨2830898024277865387438913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1887265349518576924959275 2830898024277865387438913)
          ·
            refine ⟨2123173518208399040579185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2830898024277865387438913 2123173518208399040579185)
            ·
              refine ⟨1592380138656299280434389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2123173518208399040579185 1592380138656299280434389)
              ·
                refine ⟨37321409499757014385181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1592380138656299280434389 37321409499757014385181)
                ·
                  rfl

theorem cell22_981223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 7].length) (baseStart_981223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_981223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_981223 prefixEnd_981223 := by exact prefixLift 981223
  have htrace : WordTrace (prefixWord ++ tailWord_981223) baseStart_981223 baseEnd_981223 := by
    simpa [prefixWord, tailWord_981223, baseEnd_981223] using wordTrace_append hprefix tailTrace_981223
  have hstable : (prefixWord ++ tailWord_981223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981223).length < 2 ^ (prefixWord ++ tailWord_981223).sum := by decide
  have hdescent : baseEnd_981223 < baseStart_981223 := by decide
  rcases family_descends (prefixWord ++ tailWord_981223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981315 : List Nat := [1, 1, 1, 3, 1, 3, 6, 1, 1, 4]
def baseStart_981315 : Nat := 118140960795 + 981315 * 2 ^ 59
def prefixEnd_981315 : Nat := 4983230072969 + 3 ^ 40 * 981315 * 2
def baseEnd_981315 : Nat := 335924178977955556166347

theorem tailTrace_981315 : CollatzResearch.WordTrace tailWord_981315 prefixEnd_981315 335924178977955556166347 := by
  unfold tailWord_981315
  simp only [CollatzResearch.WordTrace]
  refine ⟨35791498439870825104169399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23860998959913883402779599 35791498439870825104169399)
  ·
    refine ⟨53687247659806237656254099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35791498439870825104169399 53687247659806237656254099)
    ·
      refine ⟨80530871489709356484381149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53687247659806237656254099 80530871489709356484381149)
      ·
        refine ⟨30199076808641008681642931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80530871489709356484381149 30199076808641008681642931)
        ·
          refine ⟨45298615212961513022464397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30199076808641008681642931 45298615212961513022464397)
          ·
            refine ⟨16986980704860567383424149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45298615212961513022464397 16986980704860567383424149)
            ·
              refine ⟨796264720540339096098007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16986980704860567383424149 796264720540339096098007)
              ·
                refine ⟨1194397080810508644147011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 796264720540339096098007 1194397080810508644147011)
                ·
                  refine ⟨1791595621215762966220517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1194397080810508644147011 1791595621215762966220517)
                  ·
                    refine ⟨335924178977955556166347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1791595621215762966220517 335924178977955556166347)
                    ·
                      rfl

theorem cell22_981315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 1, 4].length) (baseStart_981315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_981315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_981315 prefixEnd_981315 := by exact prefixLift 981315
  have htrace : WordTrace (prefixWord ++ tailWord_981315) baseStart_981315 baseEnd_981315 := by
    simpa [prefixWord, tailWord_981315, baseEnd_981315] using wordTrace_append hprefix tailTrace_981315
  have hstable : (prefixWord ++ tailWord_981315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981315).length < 2 ^ (prefixWord ++ tailWord_981315).sum := by decide
  have hdescent : baseEnd_981315 < baseStart_981315 := by decide
  rcases family_descends (prefixWord ++ tailWord_981315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981330 : List Nat := [3, 2, 2, 1, 1, 1, 4, 4, 4]
def baseStart_981330 : Nat := 118140960795 + 981330 * 2 ^ 59
def prefixEnd_981330 : Nat := 4983230072969 + 3 ^ 40 * 981330 * 2
def baseEnd_981330 : Nat := 111976437928166839013767

theorem tailTrace_981330 : CollatzResearch.WordTrace tailWord_981330 prefixEnd_981330 111976437928166839013767 := by
  unfold tailWord_981330
  simp only [CollatzResearch.WordTrace]
  refine ⟨8948011383704120666491361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23861363689877655110643629 8948011383704120666491361)
  ·
    refine ⟨6711008537778090499868521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8948011383704120666491361 6711008537778090499868521)
    ·
      refine ⟨5033256403333567874901391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6711008537778090499868521 5033256403333567874901391)
      ·
        refine ⟨7549884605000351812352087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5033256403333567874901391 7549884605000351812352087)
        ·
          refine ⟨11324826907500527718528131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7549884605000351812352087 11324826907500527718528131)
          ·
            refine ⟨16987240361250791577792197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11324826907500527718528131 16987240361250791577792197)
            ·
              refine ⟨3185107567734523420836037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16987240361250791577792197 3185107567734523420836037)
              ·
                refine ⟨597207668950223141406757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3185107567734523420836037 597207668950223141406757)
                ·
                  refine ⟨111976437928166839013767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 597207668950223141406757 111976437928166839013767)
                  ·
                    rfl

theorem cell22_981330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_981330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_981330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_981330 prefixEnd_981330 := by exact prefixLift 981330
  have htrace : WordTrace (prefixWord ++ tailWord_981330) baseStart_981330 baseEnd_981330 := by
    simpa [prefixWord, tailWord_981330, baseEnd_981330] using wordTrace_append hprefix tailTrace_981330
  have hstable : (prefixWord ++ tailWord_981330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981330).length < 2 ^ (prefixWord ++ tailWord_981330).sum := by decide
  have hdescent : baseEnd_981330 < baseStart_981330 := by decide
  rcases family_descends (prefixWord ++ tailWord_981330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981396 : List Nat := [2, 4, 2, 1, 3, 2, 2, 1, 2, 3]
def baseStart_981396 : Nat := 118140960795 + 981396 * 2 ^ 59
def prefixEnd_981396 : Nat := 4983230072969 + 3 ^ 40 * 981396 * 2
def baseEnd_981396 : Nat := 335951906933298344891099

theorem tailTrace_981396 : CollatzResearch.WordTrace tailWord_981396 prefixEnd_981396 335951906933298344891099 := by
  unfold tailWord_981396
  simp only [CollatzResearch.WordTrace]
  refine ⟨17897226376288687968934021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23862968501718250625245361 17897226376288687968934021)
  ·
    refine ⟨3355729945554128994175129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17897226376288687968934021 3355729945554128994175129)
    ·
      refine ⟨2516797459165596745631347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3355729945554128994175129 2516797459165596745631347)
      ·
        refine ⟨3775196188748395118447021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2516797459165596745631347 3775196188748395118447021)
        ·
          refine ⟨1415698570780648169417633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3775196188748395118447021 1415698570780648169417633)
          ·
            refine ⟨1061773928085486127063225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1415698570780648169417633 1061773928085486127063225)
            ·
              refine ⟨796330446064114595297419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1061773928085486127063225 796330446064114595297419)
              ·
                refine ⟨1194495669096171892946129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 796330446064114595297419 1194495669096171892946129)
                ·
                  refine ⟨895871751822128919709597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1194495669096171892946129 895871751822128919709597)
                  ·
                    refine ⟨335951906933298344891099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 895871751822128919709597 335951906933298344891099)
                    ·
                      rfl

theorem cell22_981396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_981396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_981396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_981396 prefixEnd_981396 := by exact prefixLift 981396
  have htrace : WordTrace (prefixWord ++ tailWord_981396) baseStart_981396 baseEnd_981396 := by
    simpa [prefixWord, tailWord_981396, baseEnd_981396] using wordTrace_append hprefix tailTrace_981396
  have hstable : (prefixWord ++ tailWord_981396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981396).length < 2 ^ (prefixWord ++ tailWord_981396).sum := by decide
  have hdescent : baseEnd_981396 < baseStart_981396 := by decide
  rcases family_descends (prefixWord ++ tailWord_981396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981480 : List Nat := [2, 1, 4, 1, 1, 3, 2, 2, 1, 5]
def baseStart_981480 : Nat := 118140960795 + 981480 * 2 ^ 59
def prefixEnd_981480 : Nat := 4983230072969 + 3 ^ 40 * 981480 * 2
def baseEnd_981480 : Nat := 335980661849950125790841

theorem tailTrace_981480 : CollatzResearch.WordTrace tailWord_981480 prefixEnd_981480 335980661849950125790841 := by
  unfold tailWord_981480
  simp only [CollatzResearch.WordTrace]
  refine ⟨17898758242136529141962947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23865010989515372189283929 17898758242136529141962947)
  ·
    refine ⟨26848137363204793712944421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17898758242136529141962947 26848137363204793712944421)
    ·
      refine ⟨5034025755600898821177079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26848137363204793712944421 5034025755600898821177079)
      ·
        refine ⟨7551038633401348231765619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5034025755600898821177079 7551038633401348231765619)
        ·
          refine ⟨11326557950102022347648429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7551038633401348231765619 11326557950102022347648429)
          ·
            refine ⟨4247459231288258380368161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11326557950102022347648429 4247459231288258380368161)
            ·
              refine ⟨3185594423466193785276121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4247459231288258380368161 3185594423466193785276121)
              ·
                refine ⟨2389195817599645338957091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3185594423466193785276121 2389195817599645338957091)
                ·
                  refine ⟨3583793726399468008435637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2389195817599645338957091 3583793726399468008435637)
                  ·
                    refine ⟨335980661849950125790841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3583793726399468008435637 335980661849950125790841)
                    ·
                      rfl

theorem cell22_981480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_981480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_981480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_981480 prefixEnd_981480 := by exact prefixLift 981480
  have htrace : WordTrace (prefixWord ++ tailWord_981480) baseStart_981480 baseEnd_981480 := by
    simpa [prefixWord, tailWord_981480, baseEnd_981480] using wordTrace_append hprefix tailTrace_981480
  have hstable : (prefixWord ++ tailWord_981480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981480).length < 2 ^ (prefixWord ++ tailWord_981480).sum := by decide
  have hdescent : baseEnd_981480 < baseStart_981480 := by decide
  rcases family_descends (prefixWord ++ tailWord_981480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981482 : List Nat := [3, 1, 3, 1, 3, 1, 1, 5, 4]
def baseStart_981482 : Nat := 118140960795 + 981482 * 2 ^ 59
def prefixEnd_981482 : Nat := 4983230072969 + 3 ^ 40 * 981482 * 2
def baseEnd_981482 : Nat := 111993782163607595746945

theorem tailTrace_981482 : CollatzResearch.WordTrace tailWord_981482 prefixEnd_981482 111993782163607595746945 := by
  unfold tailWord_981482
  simp only [CollatzResearch.WordTrace]
  refine ⟨8949397357566453156374675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23865059620177208416999133 8949397357566453156374675)
  ·
    refine ⟨13424096036349679734562013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8949397357566453156374675 13424096036349679734562013)
    ·
      refine ⟨5034036013631129900460755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13424096036349679734562013 5034036013631129900460755)
      ·
        refine ⟨7551054020446694850691133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5034036013631129900460755 7551054020446694850691133)
        ·
          refine ⟨2831645257667510569009175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7551054020446694850691133 2831645257667510569009175)
          ·
            refine ⟨4247467886501265853513763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2831645257667510569009175 4247467886501265853513763)
            ·
              refine ⟨6371201829751898780270645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4247467886501265853513763 6371201829751898780270645)
              ·
                refine ⟨597300171539240510650373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6371201829751898780270645 597300171539240510650373)
                ·
                  refine ⟨111993782163607595746945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 597300171539240510650373 111993782163607595746945)
                  ·
                    rfl

theorem cell22_981482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 5, 4].length) (baseStart_981482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_981482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_981482 prefixEnd_981482 := by exact prefixLift 981482
  have htrace : WordTrace (prefixWord ++ tailWord_981482) baseStart_981482 baseEnd_981482 := by
    simpa [prefixWord, tailWord_981482, baseEnd_981482] using wordTrace_append hprefix tailTrace_981482
  have hstable : (prefixWord ++ tailWord_981482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981482).length < 2 ^ (prefixWord ++ tailWord_981482).sum := by decide
  have hdescent : baseEnd_981482 < baseStart_981482 := by decide
  rcases family_descends (prefixWord ++ tailWord_981482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981497 : List Nat := [1, 2, 1, 3, 1, 2, 5, 2, 2, 3]
def baseStart_981497 : Nat := 118140960795 + 981497 * 2 ^ 59
def prefixEnd_981497 : Nat := 4983230072969 + 3 ^ 40 * 981497 * 2
def baseEnd_981497 : Nat := 335986481297367748115789

theorem tailTrace_981497 : CollatzResearch.WordTrace tailWord_981497 prefixEnd_981497 335986481297367748115789 := by
  unfold tailWord_981497
  simp only [CollatzResearch.WordTrace]
  refine ⟨35798136525211470187294745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23865424350140980124863163 35798136525211470187294745)
  ·
    refine ⟨26848602393908602640471059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35798136525211470187294745 26848602393908602640471059)
    ·
      refine ⟨40272903590862903960706589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26848602393908602640471059 40272903590862903960706589)
      ·
        refine ⟨15102338846573588985264971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40272903590862903960706589 15102338846573588985264971)
        ·
          refine ⟨22653508269860383477897457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15102338846573588985264971 22653508269860383477897457)
          ·
            refine ⟨16990131202395287608423093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22653508269860383477897457 16990131202395287608423093)
            ·
              refine ⟨1592824800224558213289665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16990131202395287608423093 1592824800224558213289665)
              ·
                refine ⟨1194618600168418659967249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1592824800224558213289665 1194618600168418659967249)
                ·
                  refine ⟨895963950126313994975437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1194618600168418659967249 895963950126313994975437)
                  ·
                    refine ⟨335986481297367748115789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 895963950126313994975437 335986481297367748115789)
                    ·
                      rfl

theorem cell22_981497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 2, 3].length) (baseStart_981497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_981497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_981497 prefixEnd_981497 := by exact prefixLift 981497
  have htrace : WordTrace (prefixWord ++ tailWord_981497) baseStart_981497 baseEnd_981497 := by
    simpa [prefixWord, tailWord_981497, baseEnd_981497] using wordTrace_append hprefix tailTrace_981497
  have hstable : (prefixWord ++ tailWord_981497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981497).length < 2 ^ (prefixWord ++ tailWord_981497).sum := by decide
  have hdescent : baseEnd_981497 < baseStart_981497 := by decide
  rcases family_descends (prefixWord ++ tailWord_981497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981514 : List Nat := [3, 1, 2, 2, 2, 1, 5, 1, 2, 3]
def baseStart_981514 : Nat := 118140960795 + 981514 * 2 ^ 59
def prefixEnd_981514 : Nat := 4983230072969 + 3 ^ 40 * 981514 * 2
def baseEnd_981514 : Nat := 335992300744785370440737

theorem tailTrace_981514 : CollatzResearch.WordTrace tailWord_981514 prefixEnd_981514 335992300744785370440737 := by
  unfold tailWord_981514
  simp only [CollatzResearch.WordTrace]
  refine ⟨8949689141537470522665899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23865837710766588060442397 8949689141537470522665899)
  ·
    refine ⟨13424533712306205783998849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8949689141537470522665899 13424533712306205783998849)
    ·
      refine ⟨10068400284229654337999137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13424533712306205783998849 10068400284229654337999137)
      ·
        refine ⟨7551300213172240753499353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10068400284229654337999137 7551300213172240753499353)
        ·
          refine ⟨5663475159879180565124515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7551300213172240753499353 5663475159879180565124515)
          ·
            refine ⟨8495212739818770847686773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5663475159879180565124515 8495212739818770847686773)
            ·
              refine ⟨796426194358009766970635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8495212739818770847686773 796426194358009766970635)
              ·
                refine ⟨1194639291537014650455953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 796426194358009766970635 1194639291537014650455953)
                ·
                  refine ⟨895979468652760987841965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1194639291537014650455953 895979468652760987841965)
                  ·
                    refine ⟨335992300744785370440737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 895979468652760987841965 335992300744785370440737)
                    ·
                      rfl

theorem cell22_981514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 2, 3].length) (baseStart_981514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_981514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_981514 prefixEnd_981514 := by exact prefixLift 981514
  have htrace : WordTrace (prefixWord ++ tailWord_981514) baseStart_981514 baseEnd_981514 := by
    simpa [prefixWord, tailWord_981514, baseEnd_981514] using wordTrace_append hprefix tailTrace_981514
  have hstable : (prefixWord ++ tailWord_981514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981514).length < 2 ^ (prefixWord ++ tailWord_981514).sum := by decide
  have hdescent : baseEnd_981514 < baseStart_981514 := by decide
  rcases family_descends (prefixWord ++ tailWord_981514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981527 : List Nat := [1, 1, 3, 6, 1, 1, 1, 8]
def baseStart_981527 : Nat := 118140960795 + 981527 * 2 ^ 59
def prefixEnd_981527 : Nat := 4983230072969 + 3 ^ 40 * 981527 * 2
def baseEnd_981527 : Nat := 37332972323384185540633

theorem tailTrace_981527 : CollatzResearch.WordTrace tailWord_981527 prefixEnd_981527 37332972323384185540633 := by
  unfold tailWord_981527
  simp only [CollatzResearch.WordTrace]
  refine ⟨35799230715102785310886835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23866153810068523540591223 35799230715102785310886835)
  ·
    refine ⟨53698846072654177966330253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35799230715102785310886835 53698846072654177966330253)
    ·
      refine ⟨20137067277245316737373845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53698846072654177966330253 20137067277245316737373845)
      ·
        refine ⟨943925028620874222064399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20137067277245316737373845 943925028620874222064399)
        ·
          refine ⟨1415887542931311333096599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 943925028620874222064399 1415887542931311333096599)
          ·
            refine ⟨2123831314396966999644899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1415887542931311333096599 2123831314396966999644899)
            ·
              refine ⟨3185746971595450499467349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2123831314396966999644899 3185746971595450499467349)
              ·
                refine ⟨37332972323384185540633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3185746971595450499467349 37332972323384185540633)
                ·
                  rfl

theorem cell22_981527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 8].length) (baseStart_981527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_981527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_981527 prefixEnd_981527 := by exact prefixLift 981527
  have htrace : WordTrace (prefixWord ++ tailWord_981527) baseStart_981527 baseEnd_981527 := by
    simpa [prefixWord, tailWord_981527, baseEnd_981527] using wordTrace_append hprefix tailTrace_981527
  have hstable : (prefixWord ++ tailWord_981527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981527).length < 2 ^ (prefixWord ++ tailWord_981527).sum := by decide
  have hdescent : baseEnd_981527 < baseStart_981527 := by decide
  rcases family_descends (prefixWord ++ tailWord_981527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981555 : List Nat := [1, 1, 1, 2, 4, 2, 2, 4, 5]
def baseStart_981555 : Nat := 118140960795 + 981555 * 2 ^ 59
def prefixEnd_981555 : Nat := 4983230072969 + 3 ^ 40 * 981555 * 2
def baseEnd_981555 : Nat := 112002111960891643388537

theorem tailTrace_981555 : CollatzResearch.WordTrace tailWord_981555 prefixEnd_981555 112002111960891643388537 := by
  unfold tailWord_981555
  simp only [CollatzResearch.WordTrace]
  refine ⟨35800251959001346092906119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23866834639334230728604079 35800251959001346092906119)
  ·
    refine ⟨53700377938502019139359179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35800251959001346092906119 53700377938502019139359179)
    ·
      refine ⟨80550566907753028709038769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53700377938502019139359179 80550566907753028709038769)
      ·
        refine ⟨60412925180814771531779077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80550566907753028709038769 60412925180814771531779077)
        ·
          refine ⟨11327423471402769662208577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60412925180814771531779077 11327423471402769662208577)
          ·
            refine ⟨8495567603552077246656433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11327423471402769662208577 8495567603552077246656433)
            ·
              refine ⟨6371675702664057934992325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8495567603552077246656433 6371675702664057934992325)
              ·
                refine ⟨1194689194249510862811061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6371675702664057934992325 1194689194249510862811061)
                ·
                  refine ⟨112002111960891643388537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1194689194249510862811061 112002111960891643388537)
                  ·
                    rfl

theorem cell22_981555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 5].length) (baseStart_981555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_981555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_981555 prefixEnd_981555 := by exact prefixLift 981555
  have htrace : WordTrace (prefixWord ++ tailWord_981555) baseStart_981555 baseEnd_981555 := by
    simpa [prefixWord, tailWord_981555, baseEnd_981555] using wordTrace_append hprefix tailTrace_981555
  have hstable : (prefixWord ++ tailWord_981555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981555).length < 2 ^ (prefixWord ++ tailWord_981555).sum := by decide
  have hdescent : baseEnd_981555 < baseStart_981555 := by decide
  rcases family_descends (prefixWord ++ tailWord_981555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981632 : List Nat := [2, 1, 1, 2, 1, 6, 2, 1, 1, 5]
def baseStart_981632 : Nat := 118140960795 + 981632 * 2 ^ 59
def prefixEnd_981632 : Nat := 4983230072969 + 3 ^ 40 * 981632 * 2
def baseEnd_981632 : Nat := 336032694556272395990375

theorem tailTrace_981632 : CollatzResearch.WordTrace tailWord_981632 prefixEnd_981632 336032694556272395990375 := by
  unfold tailWord_981632
  simp only [CollatzResearch.WordTrace]
  refine ⟨17901530189861194121729575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23868706919814925495639433 17901530189861194121729575)
  ·
    refine ⟨26852295284791791182594363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17901530189861194121729575 26852295284791791182594363)
    ·
      refine ⟨40278442927187686773891545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26852295284791791182594363 40278442927187686773891545)
      ·
        refine ⟨30208832195390765080418659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40278442927187686773891545 30208832195390765080418659)
        ·
          refine ⟨45313248293086147620627989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30208832195390765080418659 45313248293086147620627989)
          ·
            refine ⟨2124058513738413169716937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 45313248293086147620627989 2124058513738413169716937)
            ·
              refine ⟨1593043885303809877287703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2124058513738413169716937 1593043885303809877287703)
              ·
                refine ⟨2389565827955714815931555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1593043885303809877287703 2389565827955714815931555)
                ·
                  refine ⟨3584348741933572223897333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2389565827955714815931555 3584348741933572223897333)
                  ·
                    refine ⟨336032694556272395990375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3584348741933572223897333 336032694556272395990375)
                    ·
                      rfl

theorem cell22_981632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 1, 5].length) (baseStart_981632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_981632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_981632 prefixEnd_981632 := by exact prefixLift 981632
  have htrace : WordTrace (prefixWord ++ tailWord_981632) baseStart_981632 baseEnd_981632 := by
    simpa [prefixWord, tailWord_981632, baseEnd_981632] using wordTrace_append hprefix tailTrace_981632
  have hstable : (prefixWord ++ tailWord_981632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981632).length < 2 ^ (prefixWord ++ tailWord_981632).sum := by decide
  have hdescent : baseEnd_981632 < baseStart_981632 := by decide
  rcases family_descends (prefixWord ++ tailWord_981632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981662 : List Nat := [4, 3, 1, 1, 1, 1, 11]
def baseStart_981662 : Nat := 118140960795 + 981662 * 2 ^ 59
def prefixEnd_981662 : Nat := 4983230072969 + 3 ^ 40 * 981662 * 2
def baseEnd_981662 : Nat := 12446035709976382138529

theorem tailTrace_981662 : CollatzResearch.WordTrace tailWord_981662 prefixEnd_981662 12446035709976382138529 := by
  unfold tailWord_981662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4475519321201712920881405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23869436379742468911367493 4475519321201712920881405)
  ·
    refine ⟨1678319745450642345330527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4475519321201712920881405 1678319745450642345330527)
    ·
      refine ⟨2517479618175963517995791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1678319745450642345330527 2517479618175963517995791)
      ·
        refine ⟨3776219427263945276993687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2517479618175963517995791 3776219427263945276993687)
        ·
          refine ⟨5664329140895917915490531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3776219427263945276993687 5664329140895917915490531)
          ·
            refine ⟨8496493711343876873235797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5664329140895917915490531 8496493711343876873235797)
            ·
              refine ⟨12446035709976382138529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 8496493711343876873235797 12446035709976382138529)
              ·
                rfl

theorem cell22_981662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 11].length) (baseStart_981662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_981662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_981662 prefixEnd_981662 := by exact prefixLift 981662
  have htrace : WordTrace (prefixWord ++ tailWord_981662) baseStart_981662 baseEnd_981662 := by
    simpa [prefixWord, tailWord_981662, baseEnd_981662] using wordTrace_append hprefix tailTrace_981662
  have hstable : (prefixWord ++ tailWord_981662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981662).length < 2 ^ (prefixWord ++ tailWord_981662).sum := by decide
  have hdescent : baseEnd_981662 < baseStart_981662 := by decide
  rcases family_descends (prefixWord ++ tailWord_981662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981694 : List Nat := [4, 2, 1, 1, 2, 1, 1, 4, 3, 3]
def baseStart_981694 : Nat := 118140960795 + 981694 * 2 ^ 59
def prefixEnd_981694 : Nat := 4983230072969 + 3 ^ 40 * 981694 * 2
def baseEnd_981694 : Nat := 336053918423324900940185

theorem tailTrace_981694 : CollatzResearch.WordTrace tailWord_981694 prefixEnd_981694 336053918423324900940185 := by
  unfold tailWord_981694
  simp only [CollatzResearch.WordTrace]
  refine ⟨4475665213187221604027017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23870214470331848554810757 4475665213187221604027017)
  ·
    refine ⟨3356748909890416203020263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4475665213187221604027017 3356748909890416203020263)
    ·
      refine ⟨5035123364835624304530395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3356748909890416203020263 5035123364835624304530395)
      ·
        refine ⟨7552685047253436456795593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5035123364835624304530395 7552685047253436456795593)
        ·
          refine ⟨5664513785440077342596695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7552685047253436456795593 5664513785440077342596695)
          ·
            refine ⟨8496770678160116013895043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5664513785440077342596695 8496770678160116013895043)
            ·
              refine ⟨12745156017240174020842565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8496770678160116013895043 12745156017240174020842565)
              ·
                refine ⟨2389716753232532628907981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12745156017240174020842565 2389716753232532628907981)
                ·
                  refine ⟨896143782462199735840493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2389716753232532628907981 896143782462199735840493)
                  ·
                    refine ⟨336053918423324900940185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 896143782462199735840493 336053918423324900940185)
                    ·
                      rfl

theorem cell22_981694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_981694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_981694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_981694 prefixEnd_981694 := by exact prefixLift 981694
  have htrace : WordTrace (prefixWord ++ tailWord_981694) baseStart_981694 baseEnd_981694 := by
    simpa [prefixWord, tailWord_981694, baseEnd_981694] using wordTrace_append hprefix tailTrace_981694
  have hstable : (prefixWord ++ tailWord_981694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981694).length < 2 ^ (prefixWord ++ tailWord_981694).sum := by decide
  have hdescent : baseEnd_981694 < baseStart_981694 := by decide
  rcases family_descends (prefixWord ++ tailWord_981694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981702 : List Nat := [6, 1, 2, 1, 3, 1, 1, 3, 4]
def baseStart_981702 : Nat := 118140960795 + 981702 * 2 ^ 59
def prefixEnd_981702 : Nat := 4983230072969 + 3 ^ 40 * 981702 * 2
def baseEnd_981702 : Nat := 112018885662271848913387

theorem tailTrace_981702 : CollatzResearch.WordTrace tailWord_981702 prefixEnd_981702 112018885662271848913387 := by
  unfold tailWord_981702
  simp only [CollatzResearch.WordTrace]
  refine ⟨1118925421545899693703355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23870408992979193465671573 1118925421545899693703355)
  ·
    refine ⟨1678388132318849540555033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1118925421545899693703355 1678388132318849540555033)
    ·
      refine ⟨1258791099239137155416275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1678388132318849540555033 1258791099239137155416275)
      ·
        refine ⟨1888186648858705733124413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1258791099239137155416275 1888186648858705733124413)
        ·
          refine ⟨708069993322014649921655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1888186648858705733124413 708069993322014649921655)
          ·
            refine ⟨1062104989983021974882483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708069993322014649921655 1062104989983021974882483)
            ·
              refine ⟨1593157484974532962323725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1062104989983021974882483 1593157484974532962323725)
              ·
                refine ⟨597434056865449860871397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1593157484974532962323725 597434056865449860871397)
                ·
                  refine ⟨112018885662271848913387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 597434056865449860871397 112018885662271848913387)
                  ·
                    rfl

theorem cell22_981702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_981702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_981702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_981702 prefixEnd_981702 := by exact prefixLift 981702
  have htrace : WordTrace (prefixWord ++ tailWord_981702) baseStart_981702 baseEnd_981702 := by
    simpa [prefixWord, tailWord_981702, baseEnd_981702] using wordTrace_append hprefix tailTrace_981702
  have hstable : (prefixWord ++ tailWord_981702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981702).length < 2 ^ (prefixWord ++ tailWord_981702).sum := by decide
  have hdescent : baseEnd_981702 < baseStart_981702 := by decide
  rcases family_descends (prefixWord ++ tailWord_981702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981724 : List Nat := [2, 2, 5, 1, 1, 1, 2, 1, 7]
def baseStart_981724 : Nat := 118140960795 + 981724 * 2 ^ 59
def prefixEnd_981724 : Nat := 4983230072969 + 3 ^ 40 * 981724 * 2
def baseEnd_981724 : Nat := 112021396012138274230031

theorem tailTrace_981724 : CollatzResearch.WordTrace tailWord_981724 prefixEnd_981724 112021396012138274230031 := by
  unfold tailWord_981724
  simp only [CollatzResearch.WordTrace]
  refine ⟨17903207947694543977904113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23870943930259391970538817 17903207947694543977904113)
  ·
    refine ⟨13427405960770907983428085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17903207947694543977904113 13427405960770907983428085)
    ·
      refine ⟨1258819308822272623446383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13427405960770907983428085 1258819308822272623446383)
      ·
        refine ⟨1888228963233408935169575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1258819308822272623446383 1888228963233408935169575)
        ·
          refine ⟨2832343444850113402754363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1888228963233408935169575 2832343444850113402754363)
          ·
            refine ⟨4248515167275170104131545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2832343444850113402754363 4248515167275170104131545)
            ·
              refine ⟨3186386375456377578098659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4248515167275170104131545 3186386375456377578098659)
              ·
                refine ⟨4779579563184566367147989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3186386375456377578098659 4779579563184566367147989)
                ·
                  refine ⟨112021396012138274230031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4779579563184566367147989 112021396012138274230031)
                  ·
                    rfl

theorem cell22_981724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 7].length) (baseStart_981724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_981724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_981724 prefixEnd_981724 := by exact prefixLift 981724
  have htrace : WordTrace (prefixWord ++ tailWord_981724) baseStart_981724 baseEnd_981724 := by
    simpa [prefixWord, tailWord_981724, baseEnd_981724] using wordTrace_append hprefix tailTrace_981724
  have hstable : (prefixWord ++ tailWord_981724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981724).length < 2 ^ (prefixWord ++ tailWord_981724).sum := by decide
  have hdescent : baseEnd_981724 < baseStart_981724 := by decide
  rcases family_descends (prefixWord ++ tailWord_981724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981754 : List Nat := [3, 1, 1, 1, 1, 3, 5, 2, 1, 4]
def baseStart_981754 : Nat := 118140960795 + 981754 * 2 ^ 59
def prefixEnd_981754 : Nat := 4983230072969 + 3 ^ 40 * 981754 * 2
def baseEnd_981754 : Nat := 336074457649504744440001

theorem tailTrace_981754 : CollatzResearch.WordTrace tailWord_981754 prefixEnd_981754 336074457649504744440001 := by
  unfold tailWord_981754
  simp only [CollatzResearch.WordTrace]
  refine ⟨8951877521320100769850079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23871673390186935386266877 8951877521320100769850079)
  ·
    refine ⟨13427816281980151154775119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8951877521320100769850079 13427816281980151154775119)
    ·
      refine ⟨20141724422970226732162679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13427816281980151154775119 20141724422970226732162679)
      ·
        refine ⟨30212586634455340098244019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20141724422970226732162679 30212586634455340098244019)
        ·
          refine ⟨45318879951683010147366029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30212586634455340098244019 45318879951683010147366029)
          ·
            refine ⟨16994579981881128805262261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45318879951683010147366029 16994579981881128805262261)
            ·
              refine ⟨1593241873301355825493337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16994579981881128805262261 1593241873301355825493337)
              ·
                refine ⟨1194931404976016869120003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1593241873301355825493337 1194931404976016869120003)
                ·
                  refine ⟨1792397107464025303680005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1194931404976016869120003 1792397107464025303680005)
                  ·
                    refine ⟨336074457649504744440001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1792397107464025303680005 336074457649504744440001)
                    ·
                      rfl

theorem cell22_981754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 1, 4].length) (baseStart_981754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_981754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_981754 prefixEnd_981754 := by exact prefixLift 981754
  have htrace : WordTrace (prefixWord ++ tailWord_981754) baseStart_981754 baseEnd_981754 := by
    simpa [prefixWord, tailWord_981754, baseEnd_981754] using wordTrace_append hprefix tailTrace_981754
  have hstable : (prefixWord ++ tailWord_981754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981754).length < 2 ^ (prefixWord ++ tailWord_981754).sum := by decide
  have hdescent : baseEnd_981754 < baseStart_981754 := by decide
  rcases family_descends (prefixWord ++ tailWord_981754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981857 : List Nat := [1, 2, 3, 1, 1, 1, 2, 3, 1, 7]
def baseStart_981857 : Nat := 118140960795 + 981857 * 2 ^ 59
def prefixEnd_981857 : Nat := 4983230072969 + 3 ^ 40 * 981857 * 2
def baseEnd_981857 : Nat := 336109716654446809114685

theorem tailTrace_981857 : CollatzResearch.WordTrace tailWord_981857 prefixEnd_981857 336109716654446809114685 := by
  unfold tailWord_981857
  simp only [CollatzResearch.WordTrace]
  refine ⟨35811266803907251670399825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23874177869271501113599883 35811266803907251670399825)
  ·
    refine ⟨26858450102930438752799869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35811266803907251670399825 26858450102930438752799869)
    ·
      refine ⟨10071918788598914532299951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26858450102930438752799869 10071918788598914532299951)
      ·
        refine ⟨15107878182898371798449927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10071918788598914532299951 15107878182898371798449927)
        ·
          refine ⟨22661817274347557697674891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15107878182898371798449927 22661817274347557697674891)
          ·
            refine ⟨33992725911521336546512337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22661817274347557697674891 33992725911521336546512337)
            ·
              refine ⟨25494544433641002409884253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33992725911521336546512337 25494544433641002409884253)
              ·
                refine ⟨9560454162615375903706595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25494544433641002409884253 9560454162615375903706595)
                ·
                  refine ⟨14340681243923063855559893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9560454162615375903706595 14340681243923063855559893)
                  ·
                    refine ⟨336109716654446809114685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14340681243923063855559893 336109716654446809114685)
                    ·
                      rfl

theorem cell22_981857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_981857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_981857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_981857 prefixEnd_981857 := by exact prefixLift 981857
  have htrace : WordTrace (prefixWord ++ tailWord_981857) baseStart_981857 baseEnd_981857 := by
    simpa [prefixWord, tailWord_981857, baseEnd_981857] using wordTrace_append hprefix tailTrace_981857
  have hstable : (prefixWord ++ tailWord_981857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981857).length < 2 ^ (prefixWord ++ tailWord_981857).sum := by decide
  have hdescent : baseEnd_981857 < baseStart_981857 := by decide
  rcases family_descends (prefixWord ++ tailWord_981857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981887 : List Nat := [1, 1, 2, 2, 1, 1, 4, 2, 8]
def baseStart_981887 : Nat := 118140960795 + 981887 * 2 ^ 59
def prefixEnd_981887 : Nat := 4983230072969 + 3 ^ 40 * 981887 * 2
def baseEnd_981887 : Nat := 112039995422512243621531

theorem tailTrace_981887 : CollatzResearch.WordTrace tailWord_981887 prefixEnd_981887 112039995422512243621531 := by
  unfold tailWord_981887
  simp only [CollatzResearch.WordTrace]
  refine ⟨35812360993798566793991915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23874907329199044529327943 35812360993798566793991915)
  ·
    refine ⟨53718541490697850190987873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35812360993798566793991915 53718541490697850190987873)
    ·
      refine ⟨40288906118023387643240905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53718541490697850190987873 40288906118023387643240905)
      ·
        refine ⟨30216679588517540732430679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40288906118023387643240905 30216679588517540732430679)
        ·
          refine ⟨45325019382776311098646019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30216679588517540732430679 45325019382776311098646019)
          ·
            refine ⟨67987529074164466647969029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45325019382776311098646019 67987529074164466647969029)
            ·
              refine ⟨12747661701405837496494193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67987529074164466647969029 12747661701405837496494193)
              ·
                refine ⟨9560746276054378122370645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12747661701405837496494193 9560746276054378122370645)
                ·
                  refine ⟨112039995422512243621531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9560746276054378122370645 112039995422512243621531)
                  ·
                    rfl

theorem cell22_981887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 8].length) (baseStart_981887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_981887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_981887 prefixEnd_981887 := by exact prefixLift 981887
  have htrace : WordTrace (prefixWord ++ tailWord_981887) baseStart_981887 baseEnd_981887 := by
    simpa [prefixWord, tailWord_981887, baseEnd_981887] using wordTrace_append hprefix tailTrace_981887
  have hstable : (prefixWord ++ tailWord_981887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981887).length < 2 ^ (prefixWord ++ tailWord_981887).sum := by decide
  have hdescent : baseEnd_981887 < baseStart_981887 := by decide
  rcases family_descends (prefixWord ++ tailWord_981887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981910 : List Nat := [5, 3, 1, 1, 1, 2, 1, 3, 5]
def baseStart_981910 : Nat := 118140960795 + 981910 * 2 ^ 59
def prefixEnd_981910 : Nat := 4983230072969 + 3 ^ 40 * 981910 * 2
def baseEnd_981910 : Nat := 112042619879190779179841

theorem tailTrace_981910 : CollatzResearch.WordTrace tailWord_981910 prefixEnd_981910 112042619879190779179841 := by
  unfold tailWord_981910
  simp only [CollatzResearch.WordTrace]
  refine ⟨2238324992044702607629949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23875466581810161148052789 2238324992044702607629949)
  ·
    refine ⟨839371872016763477861231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2238324992044702607629949 839371872016763477861231)
    ·
      refine ⟨1259057808025145216791847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 839371872016763477861231 1259057808025145216791847)
      ·
        refine ⟨1888586712037717825187771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1259057808025145216791847 1888586712037717825187771)
        ·
          refine ⟨2832880068056576737781657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1888586712037717825187771 2832880068056576737781657)
          ·
            refine ⟨2124660051042432553336243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2832880068056576737781657 2124660051042432553336243)
            ·
              refine ⟨3186990076563648830004365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2124660051042432553336243 3186990076563648830004365)
              ·
                refine ⟨1195121278711368311251637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3186990076563648830004365 1195121278711368311251637)
                ·
                  refine ⟨112042619879190779179841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1195121278711368311251637 112042619879190779179841)
                  ·
                    rfl

theorem cell22_981910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_981910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_981910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_981910 prefixEnd_981910 := by exact prefixLift 981910
  have htrace : WordTrace (prefixWord ++ tailWord_981910) baseStart_981910 baseEnd_981910 := by
    simpa [prefixWord, tailWord_981910, baseEnd_981910] using wordTrace_append hprefix tailTrace_981910
  have hstable : (prefixWord ++ tailWord_981910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981910).length < 2 ^ (prefixWord ++ tailWord_981910).sum := by decide
  have hdescent : baseEnd_981910 < baseStart_981910 := by decide
  rcases family_descends (prefixWord ++ tailWord_981910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981949 : List Nat := [1, 4, 1, 2, 4, 10]
def baseStart_981949 : Nat := 118140960795 + 981949 * 2 ^ 59
def prefixEnd_981949 : Nat := 4983230072969 + 3 ^ 40 * 981949 * 2
def baseEnd_981949 : Nat := 4149891483143076985363

theorem tailTrace_981949 : CollatzResearch.WordTrace tailWord_981949 prefixEnd_981949 4149891483143076985363 := by
  unfold tailWord_981949
  simp only [CollatzResearch.WordTrace]
  refine ⟨35814622319573951382748901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23876414879715967588499267 35814622319573951382748901)
  ·
    refine ⟨6715241684920115884265419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35814622319573951382748901 6715241684920115884265419)
    ·
      refine ⟨10072862527380173826398129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6715241684920115884265419 10072862527380173826398129)
      ·
        refine ⟨7554646895535130369798597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10072862527380173826398129 7554646895535130369798597)
        ·
          refine ⟨1416496292912836944337237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7554646895535130369798597 1416496292912836944337237)
          ·
            refine ⟨4149891483143076985363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1416496292912836944337237 4149891483143076985363)
            ·
              rfl

theorem cell22_981949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 10].length) (baseStart_981949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_981949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_981949 prefixEnd_981949 := by exact prefixLift 981949
  have htrace : WordTrace (prefixWord ++ tailWord_981949) baseStart_981949 baseEnd_981949 := by
    simpa [prefixWord, tailWord_981949, baseEnd_981949] using wordTrace_append hprefix tailTrace_981949
  have hstable : (prefixWord ++ tailWord_981949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981949).length < 2 ^ (prefixWord ++ tailWord_981949).sum := by decide
  have hdescent : baseEnd_981949 < baseStart_981949 := by decide
  rcases family_descends (prefixWord ++ tailWord_981949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_981966 : List Nat := [4, 1, 1, 1, 2, 5, 1, 7]
def baseStart_981966 : Nat := 118140960795 + 981966 * 2 ^ 59
def prefixEnd_981966 : Nat := 4983230072969 + 3 ^ 40 * 981966 * 2
def baseEnd_981966 : Nat := 37349669953556317571039

theorem tailTrace_981966 : CollatzResearch.WordTrace tailWord_981966 prefixEnd_981966 37349669953556317571039 := by
  unfold tailWord_981966
  simp only [CollatzResearch.WordTrace]
  refine ⟨4476905295064045410764719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23876828240341575524078501 4476905295064045410764719)
  ·
    refine ⟨6715357942596068116147079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4476905295064045410764719 6715357942596068116147079)
    ·
      refine ⟨10073036913894102174220619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6715357942596068116147079 10073036913894102174220619)
      ·
        refine ⟨15109555370841153261330929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10073036913894102174220619 15109555370841153261330929)
        ·
          refine ⟨11332166528130864945998197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15109555370841153261330929 11332166528130864945998197)
          ·
            refine ⟨1062390612012268588687331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11332166528130864945998197 1062390612012268588687331)
            ·
              refine ⟨1593585918018402883030997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1062390612012268588687331 1593585918018402883030997)
              ·
                refine ⟨37349669953556317571039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1593585918018402883030997 37349669953556317571039)
                ·
                  rfl

theorem cell22_981966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 7].length) (baseStart_981966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_981966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_981966 prefixEnd_981966 := by exact prefixLift 981966
  have htrace : WordTrace (prefixWord ++ tailWord_981966) baseStart_981966 baseEnd_981966 := by
    simpa [prefixWord, tailWord_981966, baseEnd_981966] using wordTrace_append hprefix tailTrace_981966
  have hstable : (prefixWord ++ tailWord_981966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_981966).length < 2 ^ (prefixWord ++ tailWord_981966).sum := by decide
  have hdescent : baseEnd_981966 < baseStart_981966 := by decide
  rcases family_descends (prefixWord ++ tailWord_981966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982004 : List Nat := [2, 6, 2, 1, 1, 1, 1, 1, 4, 3]
def baseStart_982004 : Nat := 118140960795 + 982004 * 2 ^ 59
def prefixEnd_982004 : Nat := 4983230072969 + 3 ^ 40 * 982004 * 2
def baseEnd_982004 : Nat := 336160037758587425689235

theorem tailTrace_982004 : CollatzResearch.WordTrace tailWord_982004 prefixEnd_982004 336160037758587425689235 := by
  unfold tailWord_982004
  simp only [CollatzResearch.WordTrace]
  refine ⟨17908314167187347888000533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23877752222916463850667377 17908314167187347888000533)
  ·
    refine ⟨839452226586906932250025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17908314167187347888000533 839452226586906932250025)
    ·
      refine ⟨629589169940180199187519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 839452226586906932250025 629589169940180199187519)
      ·
        refine ⟨944383754910270298781279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629589169940180199187519 944383754910270298781279)
        ·
          refine ⟨1416575632365405448171919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 944383754910270298781279 1416575632365405448171919)
          ·
            refine ⟨2124863448548108172257879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1416575632365405448171919 2124863448548108172257879)
            ·
              refine ⟨3187295172822162258386819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2124863448548108172257879 3187295172822162258386819)
              ·
                refine ⟨4780942759233243387580229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3187295172822162258386819 4780942759233243387580229)
                ·
                  refine ⟨896426767356233135171293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4780942759233243387580229 896426767356233135171293)
                  ·
                    refine ⟨336160037758587425689235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 896426767356233135171293 336160037758587425689235)
                    ·
                      rfl

theorem cell22_982004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_982004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_982004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_982004 prefixEnd_982004 := by exact prefixLift 982004
  have htrace : WordTrace (prefixWord ++ tailWord_982004) baseStart_982004 baseEnd_982004 := by
    simpa [prefixWord, tailWord_982004, baseEnd_982004] using wordTrace_append hprefix tailTrace_982004
  have hstable : (prefixWord ++ tailWord_982004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982004).length < 2 ^ (prefixWord ++ tailWord_982004).sum := by decide
  have hdescent : baseEnd_982004 < baseStart_982004 := by decide
  rcases family_descends (prefixWord ++ tailWord_982004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982009 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 4, 5]
def baseStart_982009 : Nat := 118140960795 + 982009 * 2 ^ 59
def prefixEnd_982009 : Nat := 4983230072969 + 3 ^ 40 * 982009 * 2
def baseEnd_982009 : Nat := 336161749360769079314219

theorem tailTrace_982009 : CollatzResearch.WordTrace tailWord_982009 prefixEnd_982009 336161749360769079314219 := by
  unfold tailWord_982009
  simp only [CollatzResearch.WordTrace]
  refine ⟨35816810699356581629933081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23877873799571054419955387 35816810699356581629933081)
  ·
    refine ⟨26862608024517436222449811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35816810699356581629933081 26862608024517436222449811)
    ·
      refine ⟨40293912036776154333674717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26862608024517436222449811 40293912036776154333674717)
      ·
        refine ⟨15110217013791057875128019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40293912036776154333674717 15110217013791057875128019)
        ·
          refine ⟨22665325520686586812692029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15110217013791057875128019 22665325520686586812692029)
          ·
            refine ⟨8499497070257470054759511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22665325520686586812692029 8499497070257470054759511)
            ·
              refine ⟨12749245605386205082139267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8499497070257470054759511 12749245605386205082139267)
              ·
                refine ⟨19123868408079307623208901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12749245605386205082139267 19123868408079307623208901)
                ·
                  refine ⟨3585725326514870179351669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19123868408079307623208901 3585725326514870179351669)
                  ·
                    refine ⟨336161749360769079314219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3585725326514870179351669 336161749360769079314219)
                    ·
                      rfl

theorem cell22_982009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 5].length) (baseStart_982009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_982009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_982009 prefixEnd_982009 := by exact prefixLift 982009
  have htrace : WordTrace (prefixWord ++ tailWord_982009) baseStart_982009 baseEnd_982009 := by
    simpa [prefixWord, tailWord_982009, baseEnd_982009] using wordTrace_append hprefix tailTrace_982009
  have hstable : (prefixWord ++ tailWord_982009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982009).length < 2 ^ (prefixWord ++ tailWord_982009).sum := by decide
  have hdescent : baseEnd_982009 < baseStart_982009 := by decide
  rcases family_descends (prefixWord ++ tailWord_982009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982026 : List Nat := [3, 1, 2, 2, 3, 1, 2, 1, 2, 5]
def baseStart_982026 : Nat := 118140960795 + 982026 * 2 ^ 59
def prefixEnd_982026 : Nat := 4983230072969 + 3 ^ 40 * 982026 * 2
def baseEnd_982026 : Nat := 336167568808186701639167

theorem tailTrace_982026 : CollatzResearch.WordTrace tailWord_982026 prefixEnd_982026 336167568808186701639167 := by
  unfold tailWord_982026
  simp only [CollatzResearch.WordTrace]
  refine ⟨8954357685073748383325483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23878287160196662355534621 8954357685073748383325483)
  ·
    refine ⟨13431536527610622574988225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8954357685073748383325483 13431536527610622574988225)
    ·
      refine ⟨10073652395707966931241169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13431536527610622574988225 10073652395707966931241169)
      ·
        refine ⟨7555239296780975198430877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10073652395707966931241169 7555239296780975198430877)
        ·
          refine ⟨2833214736292865699411579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7555239296780975198430877 2833214736292865699411579)
          ·
            refine ⟨4249822104439298549117369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2833214736292865699411579 4249822104439298549117369)
            ·
              refine ⟨3187366578329473911838027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4249822104439298549117369 3187366578329473911838027)
              ·
                refine ⟨4781049867494210867757041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3187366578329473911838027 4781049867494210867757041)
                ·
                  refine ⟨3585787400620658150817781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4781049867494210867757041 3585787400620658150817781)
                  ·
                    refine ⟨336167568808186701639167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3585787400620658150817781 336167568808186701639167)
                    ·
                      rfl

theorem cell22_982026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_982026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_982026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_982026 prefixEnd_982026 := by exact prefixLift 982026
  have htrace : WordTrace (prefixWord ++ tailWord_982026) baseStart_982026 baseEnd_982026 := by
    simpa [prefixWord, tailWord_982026, baseEnd_982026] using wordTrace_append hprefix tailTrace_982026
  have hstable : (prefixWord ++ tailWord_982026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982026).length < 2 ^ (prefixWord ++ tailWord_982026).sum := by decide
  have hdescent : baseEnd_982026 < baseStart_982026 := by decide
  rcases family_descends (prefixWord ++ tailWord_982026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982028 : List Nat := [2, 2, 1, 2, 3, 3, 3, 1, 5]
def baseStart_982028 : Nat := 118140960795 + 982028 * 2 ^ 59
def prefixEnd_982028 : Nat := 4983230072969 + 3 ^ 40 * 982028 * 2
def baseEnd_982028 : Nat := 112056084483019787696387

theorem tailTrace_982028 : CollatzResearch.WordTrace tailWord_982028 prefixEnd_982028 112056084483019787696387 := by
  unfold tailWord_982028
  simp only [CollatzResearch.WordTrace]
  refine ⟨17908751843143873937437369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23878335790858498583249825 17908751843143873937437369)
  ·
    refine ⟨13431563882357905453078027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17908751843143873937437369 13431563882357905453078027)
    ·
      refine ⟨20147345823536858179617041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13431563882357905453078027 20147345823536858179617041)
      ·
        refine ⟨15110509367652643634712781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20147345823536858179617041 15110509367652643634712781)
        ·
          refine ⟨5666441012869741363017293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15110509367652643634712781 5666441012869741363017293)
          ·
            refine ⟨2124915379826153011131485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5666441012869741363017293 2124915379826153011131485)
            ·
              refine ⟨796843267434807379174307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2124915379826153011131485 796843267434807379174307)
              ·
                refine ⟨1195264901152211068761461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 796843267434807379174307 1195264901152211068761461)
                ·
                  refine ⟨112056084483019787696387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1195264901152211068761461 112056084483019787696387)
                  ·
                    rfl

theorem cell22_982028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 5].length) (baseStart_982028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_982028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_982028 prefixEnd_982028 := by exact prefixLift 982028
  have htrace : WordTrace (prefixWord ++ tailWord_982028) baseStart_982028 baseEnd_982028 := by
    simpa [prefixWord, tailWord_982028, baseEnd_982028] using wordTrace_append hprefix tailTrace_982028
  have hstable : (prefixWord ++ tailWord_982028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982028).length < 2 ^ (prefixWord ++ tailWord_982028).sum := by decide
  have hdescent : baseEnd_982028 < baseStart_982028 := by decide
  rcases family_descends (prefixWord ++ tailWord_982028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982034 : List Nat := [3, 2, 5, 1, 2, 1, 2, 6]
def baseStart_982034 : Nat := 118140960795 + 982034 * 2 ^ 59
def prefixEnd_982034 : Nat := 4983230072969 + 3 ^ 40 * 982034 * 2
def baseEnd_982034 : Nat := 37352256374630816382127

theorem tailTrace_982034 : CollatzResearch.WordTrace tailWord_982034 prefixEnd_982034 37352256374630816382127 := by
  unfold tailWord_982034
  simp only [CollatzResearch.WordTrace]
  refine ⟨8954430631066502724898289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23878481682844007266395437 8954430631066502724898289)
  ·
    refine ⟨6715822973299877043673717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8954430631066502724898289 6715822973299877043673717)
    ·
      refine ⟨629608403746863472844411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6715822973299877043673717 629608403746863472844411)
      ·
        refine ⟨944412605620295209266617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629608403746863472844411 944412605620295209266617)
        ·
          refine ⟨708309454215221406949963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 944412605620295209266617 708309454215221406949963)
          ·
            refine ⟨1062464181322832110424945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708309454215221406949963 1062464181322832110424945)
            ·
              refine ⟨796848135992124082818709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1062464181322832110424945 796848135992124082818709)
              ·
                refine ⟨37352256374630816382127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 796848135992124082818709 37352256374630816382127)
                ·
                  rfl

theorem cell22_982034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 6].length) (baseStart_982034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_982034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_982034 prefixEnd_982034 := by exact prefixLift 982034
  have htrace : WordTrace (prefixWord ++ tailWord_982034) baseStart_982034 baseEnd_982034 := by
    simpa [prefixWord, tailWord_982034, baseEnd_982034] using wordTrace_append hprefix tailTrace_982034
  have hstable : (prefixWord ++ tailWord_982034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982034).length < 2 ^ (prefixWord ++ tailWord_982034).sum := by decide
  have hdescent : baseEnd_982034 < baseStart_982034 := by decide
  rcases family_descends (prefixWord ++ tailWord_982034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982041 : List Nat := [1, 2, 1, 2, 1, 1, 5, 4, 1, 4]
def baseStart_982041 : Nat := 118140960795 + 982041 * 2 ^ 59
def prefixEnd_982041 : Nat := 4983230072969 + 3 ^ 40 * 982041 * 2
def baseEnd_982041 : Nat := 336172703614731662514121

theorem tailTrace_982041 : CollatzResearch.WordTrace tailWord_982041 prefixEnd_982041 336172703614731662514121 := by
  unfold tailWord_982041
  simp only [CollatzResearch.WordTrace]
  refine ⟨35817977835240651095097977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23878651890160434063398651 35817977835240651095097977)
  ·
    refine ⟨26863483376430488321323483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35817977835240651095097977 26863483376430488321323483)
    ·
      refine ⟨40295225064645732481985225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26863483376430488321323483 40295225064645732481985225)
      ·
        refine ⟨30221418798484299361488919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40295225064645732481985225 30221418798484299361488919)
        ·
          refine ⟨45332128197726449042233379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30221418798484299361488919 45332128197726449042233379)
          ·
            refine ⟨67998192296589673563350069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45332128197726449042233379 67998192296589673563350069)
            ·
              refine ⟨6374830527805281896564069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67998192296589673563350069 6374830527805281896564069)
              ·
                refine ⟨1195280723963490355605763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6374830527805281896564069 1195280723963490355605763)
                ·
                  refine ⟨1792921085945235533408645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1195280723963490355605763 1792921085945235533408645)
                  ·
                    refine ⟨336172703614731662514121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1792921085945235533408645 336172703614731662514121)
                    ·
                      rfl

theorem cell22_982041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 4].length) (baseStart_982041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_982041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_982041 prefixEnd_982041 := by exact prefixLift 982041
  have htrace : WordTrace (prefixWord ++ tailWord_982041) baseStart_982041 baseEnd_982041 := by
    simpa [prefixWord, tailWord_982041, baseEnd_982041] using wordTrace_append hprefix tailTrace_982041
  have hstable : (prefixWord ++ tailWord_982041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982041).length < 2 ^ (prefixWord ++ tailWord_982041).sum := by decide
  have hdescent : baseEnd_982041 < baseStart_982041 := by decide
  rcases family_descends (prefixWord ++ tailWord_982041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982073 : List Nat := [1, 2, 1, 5, 2, 3, 1, 1, 6]
def baseStart_982073 : Nat := 118140960795 + 982073 * 2 ^ 59
def prefixEnd_982073 : Nat := 4983230072969 + 3 ^ 40 * 982073 * 2
def baseEnd_982073 : Nat := 112061219289564748571341

theorem tailTrace_982073 : CollatzResearch.WordTrace tailWord_982073 prefixEnd_982073 112061219289564748571341 := by
  unfold tailWord_982073
  simp only [CollatzResearch.WordTrace]
  refine ⟨35819144971124720560262873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23879429980749813706841915 35819144971124720560262873)
  ·
    refine ⟨26864358728343540420197155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35819144971124720560262873 26864358728343540420197155)
    ·
      refine ⟨40296538092515310630295733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26864358728343540420197155 40296538092515310630295733)
      ·
        refine ⟨3777800446173310371590225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40296538092515310630295733 3777800446173310371590225)
        ·
          refine ⟨2833350334629982778692669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3777800446173310371590225 2833350334629982778692669)
          ·
            refine ⟨1062506375486243542009751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2833350334629982778692669 1062506375486243542009751)
            ·
              refine ⟨1593759563229365313014627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1062506375486243542009751 1593759563229365313014627)
              ·
                refine ⟨2390639344844047969521941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1593759563229365313014627 2390639344844047969521941)
                ·
                  refine ⟨112061219289564748571341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2390639344844047969521941 112061219289564748571341)
                  ·
                    rfl

theorem cell22_982073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 6].length) (baseStart_982073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_982073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_982073 prefixEnd_982073 := by exact prefixLift 982073
  have htrace : WordTrace (prefixWord ++ tailWord_982073) baseStart_982073 baseEnd_982073 := by
    simpa [prefixWord, tailWord_982073, baseEnd_982073] using wordTrace_append hprefix tailTrace_982073
  have hstable : (prefixWord ++ tailWord_982073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982073).length < 2 ^ (prefixWord ++ tailWord_982073).sum := by decide
  have hdescent : baseEnd_982073 < baseStart_982073 := by decide
  rcases family_descends (prefixWord ++ tailWord_982073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982088 : List Nat := [2, 1, 3, 1, 1, 1, 5, 3, 2, 3]
def baseStart_982088 : Nat := 118140960795 + 982088 * 2 ^ 59
def prefixEnd_982088 : Nat := 4983230072969 + 3 ^ 40 * 982088 * 2
def baseEnd_982088 : Nat := 336188792675239206588977

theorem tailTrace_982088 : CollatzResearch.WordTrace tailWord_982088 prefixEnd_982088 336188792675239206588977 := by
  unfold tailWord_982088
  simp only [CollatzResearch.WordTrace]
  refine ⟨17909846033035189061029459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23879794710713585414705945 17909846033035189061029459)
  ·
    refine ⟨26864769049552783591544189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17909846033035189061029459 26864769049552783591544189)
    ·
      refine ⟨10074288393582293846829071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26864769049552783591544189 10074288393582293846829071)
      ·
        refine ⟨15111432590373440770243607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10074288393582293846829071 15111432590373440770243607)
        ·
          refine ⟨22667148885560161155365411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15111432590373440770243607 22667148885560161155365411)
          ·
            refine ⟨34000723328340241733048117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22667148885560161155365411 34000723328340241733048117)
            ·
              refine ⟨3187567812031897662473261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34000723328340241733048117 3187567812031897662473261)
              ·
                refine ⟨1195337929511961623427473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3187567812031897662473261 1195337929511961623427473)
                ·
                  refine ⟨896503447133971217570605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1195337929511961623427473 896503447133971217570605)
                  ·
                    refine ⟨336188792675239206588977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 896503447133971217570605 336188792675239206588977)
                    ·
                      rfl

theorem cell22_982088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_982088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_982088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_982088 prefixEnd_982088 := by exact prefixLift 982088
  have htrace : WordTrace (prefixWord ++ tailWord_982088) baseStart_982088 baseEnd_982088 := by
    simpa [prefixWord, tailWord_982088, baseEnd_982088] using wordTrace_append hprefix tailTrace_982088
  have hstable : (prefixWord ++ tailWord_982088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982088).length < 2 ^ (prefixWord ++ tailWord_982088).sum := by decide
  have hdescent : baseEnd_982088 < baseStart_982088 := by decide
  rcases family_descends (prefixWord ++ tailWord_982088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982099 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 1, 9]
def baseStart_982099 : Nat := 118140960795 + 982099 * 2 ^ 59
def prefixEnd_982099 : Nat := 4983230072969 + 3 ^ 40 * 982099 * 2
def baseEnd_982099 : Nat := 336192558200038844563943

theorem tailTrace_982099 : CollatzResearch.WordTrace tailWord_982099 prefixEnd_982099 336192558200038844563943 := by
  unfold tailWord_982099
  simp only [CollatzResearch.WordTrace]
  refine ⟨35820093269030527000709351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23880062179353684667139567 35820093269030527000709351)
  ·
    refine ⟨53730139903545790501064027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35820093269030527000709351 53730139903545790501064027)
    ·
      refine ⟨80595209855318685751596041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53730139903545790501064027 80595209855318685751596041)
      ·
        refine ⟨60446407391489014313697031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80595209855318685751596041 60446407391489014313697031)
        ·
          refine ⟨90669611087233521470545547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60446407391489014313697031 90669611087233521470545547)
          ·
            refine ⟨136004416630850282205818321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90669611087233521470545547 136004416630850282205818321)
            ·
              refine ⟨102003312473137711654363741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136004416630850282205818321 102003312473137711654363741)
              ·
                refine ⟨38251242177426641870386403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102003312473137711654363741 38251242177426641870386403)
                ·
                  refine ⟨57376863266139962805579605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38251242177426641870386403 57376863266139962805579605)
                  ·
                    refine ⟨336192558200038844563943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 57376863266139962805579605 336192558200038844563943)
                    ·
                      rfl

theorem cell22_982099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 9].length) (baseStart_982099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_982099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_982099 prefixEnd_982099 := by exact prefixLift 982099
  have htrace : WordTrace (prefixWord ++ tailWord_982099) baseStart_982099 baseEnd_982099 := by
    simpa [prefixWord, tailWord_982099, baseEnd_982099] using wordTrace_append hprefix tailTrace_982099
  have hstable : (prefixWord ++ tailWord_982099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982099).length < 2 ^ (prefixWord ++ tailWord_982099).sum := by decide
  have hdescent : baseEnd_982099 < baseStart_982099 := by decide
  rcases family_descends (prefixWord ++ tailWord_982099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982167 : List Nat := [1, 1, 3, 3, 3, 2, 2, 3, 1, 3]
def baseStart_982167 : Nat := 118140960795 + 982167 * 2 ^ 59
def prefixEnd_982167 : Nat := 4983230072969 + 3 ^ 40 * 982167 * 2
def baseEnd_982167 : Nat := 336215835989709333863735

theorem tailTrace_982167 : CollatzResearch.WordTrace tailWord_982167 prefixEnd_982167 336215835989709333863735 := by
  unfold tailWord_982167
  simp only [CollatzResearch.WordTrace]
  refine ⟨35822573432784174614184755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23881715621856116409456503 35822573432784174614184755)
  ·
    refine ⟨53733860149176261921277133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35822573432784174614184755 53733860149176261921277133)
    ·
      refine ⟨20150197555941098220478925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53733860149176261921277133 20150197555941098220478925)
      ·
        refine ⟨7556324083477911832679597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20150197555941098220478925 7556324083477911832679597)
        ·
          refine ⟨2833621531304216937254849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7556324083477911832679597 2833621531304216937254849)
          ·
            refine ⟨2125216148478162702941137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2833621531304216937254849 2125216148478162702941137)
            ·
              refine ⟨1593912111358622027205853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2125216148478162702941137 1593912111358622027205853)
              ·
                refine ⟨597717041759483260202195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1593912111358622027205853 597717041759483260202195)
                ·
                  refine ⟨896575562639224890303293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 597717041759483260202195 896575562639224890303293)
                  ·
                    refine ⟨336215835989709333863735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 896575562639224890303293 336215835989709333863735)
                    ·
                      rfl

theorem cell22_982167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 3, 1, 3].length) (baseStart_982167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_982167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_982167 prefixEnd_982167 := by exact prefixLift 982167
  have htrace : WordTrace (prefixWord ++ tailWord_982167) baseStart_982167 baseEnd_982167 := by
    simpa [prefixWord, tailWord_982167, baseEnd_982167] using wordTrace_append hprefix tailTrace_982167
  have hstable : (prefixWord ++ tailWord_982167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982167).length < 2 ^ (prefixWord ++ tailWord_982167).sum := by decide
  have hdescent : baseEnd_982167 < baseStart_982167 := by decide
  rcases family_descends (prefixWord ++ tailWord_982167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982180 : List Nat := [2, 3, 1, 2, 3, 3, 1, 2, 5]
def baseStart_982180 : Nat := 118140960795 + 982180 * 2 ^ 59
def prefixEnd_982180 : Nat := 4983230072969 + 3 ^ 40 * 982180 * 2
def baseEnd_982180 : Nat := 112073428718460544429565

theorem tailTrace_982180 : CollatzResearch.WordTrace tailWord_982180 prefixEnd_982180 112073428718460544429565 := by
  unfold tailWord_982180
  simp only [CollatzResearch.WordTrace]
  refine ⟨17911523790868538917203997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23882031721158051889605329 17911523790868538917203997)
  ·
    refine ⟨6716821421575702093951499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17911523790868538917203997 6716821421575702093951499)
    ·
      refine ⟨10075232132363553140927249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6716821421575702093951499 10075232132363553140927249)
      ·
        refine ⟨7556424099272664855695437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10075232132363553140927249 7556424099272664855695437)
        ·
          refine ⟨2833659037227249320885789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7556424099272664855695437 2833659037227249320885789)
          ·
            refine ⟨1062622138960218495332171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2833659037227249320885789 1062622138960218495332171)
            ·
              refine ⟨1593933208440327742998257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1062622138960218495332171 1593933208440327742998257)
              ·
                refine ⟨1195449906330245807248693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1593933208440327742998257 1195449906330245807248693)
                ·
                  refine ⟨112073428718460544429565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1195449906330245807248693 112073428718460544429565)
                  ·
                    rfl

theorem cell22_982180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_982180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_982180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_982180 prefixEnd_982180 := by exact prefixLift 982180
  have htrace : WordTrace (prefixWord ++ tailWord_982180) baseStart_982180 baseEnd_982180 := by
    simpa [prefixWord, tailWord_982180, baseEnd_982180] using wordTrace_append hprefix tailTrace_982180
  have hstable : (prefixWord ++ tailWord_982180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982180).length < 2 ^ (prefixWord ++ tailWord_982180).sum := by decide
  have hdescent : baseEnd_982180 < baseStart_982180 := by decide
  rcases family_descends (prefixWord ++ tailWord_982180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982191 : List Nat := [1, 1, 2, 1, 2, 3, 3, 3, 6]
def baseStart_982191 : Nat := 118140960795 + 982191 * 2 ^ 59
def prefixEnd_982191 : Nat := 4983230072969 + 3 ^ 40 * 982191 * 2
def baseEnd_982191 : Nat := 112074683893393757087887

theorem tailTrace_982191 : CollatzResearch.WordTrace tailWord_982191 prefixEnd_982191 112074683893393757087887 := by
  unfold tailWord_982191
  simp only [CollatzResearch.WordTrace]
  refine ⟨35823448784697226713058427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23882299189798151142038951 35823448784697226713058427)
  ·
    refine ⟨53735173177045840069587641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35823448784697226713058427 53735173177045840069587641)
    ·
      refine ⟨40301379882784380052190731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53735173177045840069587641 40301379882784380052190731)
      ·
        refine ⟨60452069824176570078286097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40301379882784380052190731 60452069824176570078286097)
        ·
          refine ⟨45339052368132427558714573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60452069824176570078286097 45339052368132427558714573)
          ·
            refine ⟨17002144638049660334517965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45339052368132427558714573 17002144638049660334517965)
            ·
              refine ⟨6375804239268622625444237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17002144638049660334517965 6375804239268622625444237)
              ·
                refine ⟨2390926589725733484541589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6375804239268622625444237 2390926589725733484541589)
                ·
                  refine ⟨112074683893393757087887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2390926589725733484541589 112074683893393757087887)
                  ·
                    rfl

theorem cell22_982191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 6].length) (baseStart_982191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_982191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_982191 prefixEnd_982191 := by exact prefixLift 982191
  have htrace : WordTrace (prefixWord ++ tailWord_982191) baseStart_982191 baseEnd_982191 := by
    simpa [prefixWord, tailWord_982191, baseEnd_982191] using wordTrace_append hprefix tailTrace_982191
  have hstable : (prefixWord ++ tailWord_982191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982191).length < 2 ^ (prefixWord ++ tailWord_982191).sum := by decide
  have hdescent : baseEnd_982191 < baseStart_982191 := by decide
  rcases family_descends (prefixWord ++ tailWord_982191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982253 : List Nat := [1, 5, 1, 2, 2, 1, 1, 9]
def baseStart_982253 : Nat := 118140960795 + 982253 * 2 ^ 59
def prefixEnd_982253 : Nat := 4983230072969 + 3 ^ 40 * 982253 * 2
def baseEnd_982253 : Nat := 37360586171914864023719

theorem tailTrace_982253 : CollatzResearch.WordTrace tailWord_982253 prefixEnd_982253 37360586171914864023719 := by
  unfold tailWord_982253
  simp only [CollatzResearch.WordTrace]
  refine ⟨35825710110472611301815413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23883806740315074201210275 35825710110472611301815413)
  ·
    refine ⟨3358660322856807309545195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35825710110472611301815413 3358660322856807309545195)
    ·
      refine ⟨5037990484285210964317793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3358660322856807309545195 5037990484285210964317793)
      ·
        refine ⟨3778492863213908223238345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5037990484285210964317793 3778492863213908223238345)
        ·
          refine ⟨2833869647410431167428759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3778492863213908223238345 2833869647410431167428759)
          ·
            refine ⟨4250804471115646751143139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2833869647410431167428759 4250804471115646751143139)
            ·
              refine ⟨6376206706673470126714709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4250804471115646751143139 6376206706673470126714709)
              ·
                refine ⟨37360586171914864023719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6376206706673470126714709 37360586171914864023719)
                ·
                  rfl

theorem cell22_982253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 9].length) (baseStart_982253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_982253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_982253 prefixEnd_982253 := by exact prefixLift 982253
  have htrace : WordTrace (prefixWord ++ tailWord_982253) baseStart_982253 baseEnd_982253 := by
    simpa [prefixWord, tailWord_982253, baseEnd_982253] using wordTrace_append hprefix tailTrace_982253
  have hstable : (prefixWord ++ tailWord_982253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982253).length < 2 ^ (prefixWord ++ tailWord_982253).sum := by decide
  have hdescent : baseEnd_982253 < baseStart_982253 := by decide
  rcases family_descends (prefixWord ++ tailWord_982253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982360 : List Nat := [2, 1, 2, 2, 1, 1, 3, 6, 4]
def baseStart_982360 : Nat := 118140960795 + 982360 * 2 ^ 59
def prefixEnd_982360 : Nat := 4983230072969 + 3 ^ 40 * 982360 * 2
def baseEnd_982360 : Nat := 112093967944640387929381

theorem tailTrace_982360 : CollatzResearch.WordTrace tailWord_982360 prefixEnd_982360 112093967944640387929381 := by
  unfold tailWord_982360
  simp only [CollatzResearch.WordTrace]
  refine ⟨17914806360542484287980267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23886408480723312383973689 17914806360542484287980267)
  ·
    refine ⟨26872209540813726431970401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17914806360542484287980267 26872209540813726431970401)
    ·
      refine ⟨20154157155610294823977801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26872209540813726431970401 20154157155610294823977801)
      ·
        refine ⟨15115617866707721117983351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20154157155610294823977801 15115617866707721117983351)
        ·
          refine ⟨22673426800061581676975027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15115617866707721117983351 22673426800061581676975027)
          ·
            refine ⟨34010140200092372515462541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22673426800061581676975027 34010140200092372515462541)
            ·
              refine ⟨12753802575034639693298453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34010140200092372515462541 12753802575034639693298453)
              ·
                refine ⟨597834495704748735623365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12753802575034639693298453 597834495704748735623365)
                ·
                  refine ⟨112093967944640387929381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 597834495704748735623365 112093967944640387929381)
                  ·
                    rfl

theorem cell22_982360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 6, 4].length) (baseStart_982360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_982360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_982360 prefixEnd_982360 := by exact prefixLift 982360
  have htrace : WordTrace (prefixWord ++ tailWord_982360) baseStart_982360 baseEnd_982360 := by
    simpa [prefixWord, tailWord_982360, baseEnd_982360] using wordTrace_append hprefix tailTrace_982360
  have hstable : (prefixWord ++ tailWord_982360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982360).length < 2 ^ (prefixWord ++ tailWord_982360).sum := by decide
  have hdescent : baseEnd_982360 < baseStart_982360 := by decide
  rcases family_descends (prefixWord ++ tailWord_982360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982373 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 3, 6]
def baseStart_982373 : Nat := 118140960795 + 982373 * 2 ^ 59
def prefixEnd_982373 : Nat := 4983230072969 + 3 ^ 40 * 982373 * 2
def baseEnd_982373 : Nat := 336286353999593463213103

theorem tailTrace_982373 : CollatzResearch.WordTrace tailWord_982373 prefixEnd_982373 336286353999593463213103 := by
  unfold tailWord_982373
  simp only [CollatzResearch.WordTrace]
  refine ⟨35830086870037871796183773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23886724580025247864122515 35830086870037871796183773)
  ·
    refine ⟨13436282576264201923568915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35830086870037871796183773 13436282576264201923568915)
    ·
      refine ⟨20154423864396302885353373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13436282576264201923568915 20154423864396302885353373)
      ·
        refine ⟨7557908949148613582007515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20154423864396302885353373 7557908949148613582007515)
        ·
          refine ⟨11336863423722920373011273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7557908949148613582007515 11336863423722920373011273)
          ·
            refine ⟨8502647567792190279758455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11336863423722920373011273 8502647567792190279758455)
            ·
              refine ⟨12753971351688285419637683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8502647567792190279758455 12753971351688285419637683)
              ·
                refine ⟨19130957027532428129456525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12753971351688285419637683 19130957027532428129456525)
                ·
                  refine ⟨7174108885324660548546197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19130957027532428129456525 7174108885324660548546197)
                  ·
                    refine ⟨336286353999593463213103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7174108885324660548546197 336286353999593463213103)
                    ·
                      rfl

theorem cell22_982373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_982373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_982373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_982373 prefixEnd_982373 := by exact prefixLift 982373
  have htrace : WordTrace (prefixWord ++ tailWord_982373) baseStart_982373 baseEnd_982373 := by
    simpa [prefixWord, tailWord_982373, baseEnd_982373] using wordTrace_append hprefix tailTrace_982373
  have hstable : (prefixWord ++ tailWord_982373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982373).length < 2 ^ (prefixWord ++ tailWord_982373).sum := by decide
  have hdescent : baseEnd_982373 < baseStart_982373 := by decide
  rcases family_descends (prefixWord ++ tailWord_982373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982448 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 3, 7]
def baseStart_982448 : Nat := 118140960795 + 982448 * 2 ^ 59
def prefixEnd_982448 : Nat := 4983230072969 + 3 ^ 40 * 982448 * 2
def baseEnd_982448 : Nat := 336312028032318267587873

theorem tailTrace_982448 : CollatzResearch.WordTrace tailWord_982448 prefixEnd_982448 336312028032318267587873 := by
  unfold tailWord_982448
  simp only [CollatzResearch.WordTrace]
  refine ⟨17916411172383079802581999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23888548229844106403442665 17916411172383079802581999)
  ·
    refine ⟨26874616758574619703872999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17916411172383079802581999 26874616758574619703872999)
    ·
      refine ⟨40311925137861929555809499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26874616758574619703872999 40311925137861929555809499)
      ·
        refine ⟨60467887706792894333714249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40311925137861929555809499 60467887706792894333714249)
        ·
          refine ⟨45350915780094670750285687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60467887706792894333714249 45350915780094670750285687)
          ·
            refine ⟨68026373670142006125428531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45350915780094670750285687 68026373670142006125428531)
            ·
              refine ⟨102039560505213009188142797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68026373670142006125428531 102039560505213009188142797)
              ·
                refine ⟨38264835189454878445553549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102039560505213009188142797 38264835189454878445553549)
                ·
                  refine ⟨14349313196045579417082581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38264835189454878445553549 14349313196045579417082581)
                  ·
                    refine ⟨336312028032318267587873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14349313196045579417082581 336312028032318267587873)
                    ·
                      rfl

theorem cell22_982448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 3, 7].length) (baseStart_982448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_982448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_982448 prefixEnd_982448 := by exact prefixLift 982448
  have htrace : WordTrace (prefixWord ++ tailWord_982448) baseStart_982448 baseEnd_982448 := by
    simpa [prefixWord, tailWord_982448, baseEnd_982448] using wordTrace_append hprefix tailTrace_982448
  have hstable : (prefixWord ++ tailWord_982448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982448).length < 2 ^ (prefixWord ++ tailWord_982448).sum := by decide
  have hdescent : baseEnd_982448 < baseStart_982448 := by decide
  rcases family_descends (prefixWord ++ tailWord_982448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982495 : List Nat := [1, 1, 2, 3, 3, 1, 3, 2, 6]
def baseStart_982495 : Nat := 118140960795 + 982495 * 2 ^ 59
def prefixEnd_982495 : Nat := 4983230072969 + 3 ^ 40 * 982495 * 2
def baseEnd_982495 : Nat := 112109372364275270554243

theorem tailTrace_982495 : CollatzResearch.WordTrace tailWord_982495 prefixEnd_982495 112109372364275270554243 := by
  unfold tailWord_982495
  simp only [CollatzResearch.WordTrace]
  refine ⟨35834536575595886632124939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23889691050397257754749959 35834536575595886632124939)
  ·
    refine ⟨53751804863393829948187409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35834536575595886632124939 53751804863393829948187409)
    ·
      refine ⟨40313853647545372461140557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53751804863393829948187409 40313853647545372461140557)
      ·
        refine ⟨15117695117829514672927709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40313853647545372461140557 15117695117829514672927709)
        ·
          refine ⟨5669135669186068002347891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15117695117829514672927709 5669135669186068002347891)
          ·
            refine ⟨8503703503779102003521837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5669135669186068002347891 8503703503779102003521837)
            ·
              refine ⟨3188888813917163251320689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8503703503779102003521837 3188888813917163251320689)
              ·
                refine ⟨2391666610437872438490517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3188888813917163251320689 2391666610437872438490517)
                ·
                  refine ⟨112109372364275270554243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2391666610437872438490517 112109372364275270554243)
                  ·
                    rfl

theorem cell22_982495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 6].length) (baseStart_982495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_982495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_982495 prefixEnd_982495 := by exact prefixLift 982495
  have htrace : WordTrace (prefixWord ++ tailWord_982495) baseStart_982495 baseEnd_982495 := by
    simpa [prefixWord, tailWord_982495, baseEnd_982495] using wordTrace_append hprefix tailTrace_982495
  have hstable : (prefixWord ++ tailWord_982495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982495).length < 2 ^ (prefixWord ++ tailWord_982495).sum := by decide
  have hdescent : baseEnd_982495 < baseStart_982495 := by decide
  rcases family_descends (prefixWord ++ tailWord_982495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982512 : List Nat := [2, 1, 1, 1, 3, 4, 1, 5, 4]
def baseStart_982512 : Nat := 118140960795 + 982512 * 2 ^ 59
def prefixEnd_982512 : Nat := 4983230072969 + 3 ^ 40 * 982512 * 2
def baseEnd_982512 : Nat := 112111312180081144662559

theorem tailTrace_982512 : CollatzResearch.WordTrace tailWord_982512 prefixEnd_982512 112111312180081144662559 := by
  unfold tailWord_982512
  simp only [CollatzResearch.WordTrace]
  refine ⟨17917578308267149267746895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23890104411022865690329193 17917578308267149267746895)
  ·
    refine ⟨26876367462400723901620343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17917578308267149267746895 26876367462400723901620343)
    ·
      refine ⟨40314551193601085852430515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26876367462400723901620343 40314551193601085852430515)
      ·
        refine ⟨60471826790401628778645773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40314551193601085852430515 60471826790401628778645773)
        ·
          refine ⟨22676935046400610791992165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60471826790401628778645773 22676935046400610791992165)
          ·
            refine ⟨4251925321200114523498531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22676935046400610791992165 4251925321200114523498531)
            ·
              refine ⟨6377887981800171785247797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4251925321200114523498531 6377887981800171785247797)
              ·
                refine ⟨597926998293766104866981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6377887981800171785247797 597926998293766104866981)
                ·
                  refine ⟨112111312180081144662559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 597926998293766104866981 112111312180081144662559)
                  ·
                    rfl

theorem cell22_982512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 5, 4].length) (baseStart_982512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_982512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_982512 prefixEnd_982512 := by exact prefixLift 982512
  have htrace : WordTrace (prefixWord ++ tailWord_982512) baseStart_982512 baseEnd_982512 := by
    simpa [prefixWord, tailWord_982512, baseEnd_982512] using wordTrace_append hprefix tailTrace_982512
  have hstable : (prefixWord ++ tailWord_982512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982512).length < 2 ^ (prefixWord ++ tailWord_982512).sum := by decide
  have hdescent : baseEnd_982512 < baseStart_982512 := by decide
  rcases family_descends (prefixWord ++ tailWord_982512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982514 : List Nat := [3, 2, 1, 4, 1, 2, 1, 3, 1, 4]
def baseStart_982514 : Nat := 118140960795 + 982514 * 2 ^ 59
def prefixEnd_982514 : Nat := 4983230072969 + 3 ^ 40 * 982514 * 2
def baseEnd_982514 : Nat := 336334621181116095437671

theorem tailTrace_982514 : CollatzResearch.WordTrace tailWord_982514 prefixEnd_982514 336334621181116095437671 := by
  unfold tailWord_982514
  simp only [CollatzResearch.WordTrace]
  refine ⟨8958807390631763219266649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23890153041684701918044397 8958807390631763219266649)
  ·
    refine ⟨6719105542973822414449987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8958807390631763219266649 6719105542973822414449987)
    ·
      refine ⟨10078658314460733621674981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6719105542973822414449987 10078658314460733621674981)
      ·
        refine ⟨1889748433961387554064059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10078658314460733621674981 1889748433961387554064059)
        ·
          refine ⟨2834622650942081331096089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1889748433961387554064059 2834622650942081331096089)
          ·
            refine ⟨2125966988206560998322067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2834622650942081331096089 2125966988206560998322067)
            ·
              refine ⟨3188950482309841497483101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2125966988206560998322067 3188950482309841497483101)
              ·
                refine ⟨1195856430866190561556163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3188950482309841497483101 1195856430866190561556163)
                ·
                  refine ⟨1793784646299285842334245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1195856430866190561556163 1793784646299285842334245)
                  ·
                    refine ⟨336334621181116095437671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1793784646299285842334245 336334621181116095437671)
                    ·
                      rfl

theorem cell22_982514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_982514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_982514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_982514 prefixEnd_982514 := by exact prefixLift 982514
  have htrace : WordTrace (prefixWord ++ tailWord_982514) baseStart_982514 baseEnd_982514 := by
    simpa [prefixWord, tailWord_982514, baseEnd_982514] using wordTrace_append hprefix tailTrace_982514
  have hstable : (prefixWord ++ tailWord_982514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982514).length < 2 ^ (prefixWord ++ tailWord_982514).sum := by decide
  have hdescent : baseEnd_982514 < baseStart_982514 := by decide
  rcases family_descends (prefixWord ++ tailWord_982514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982527 : List Nat := [1, 1, 2, 2, 1, 2, 2, 6, 2, 3]
def baseStart_982527 : Nat := 118140960795 + 982527 * 2 ^ 59
def prefixEnd_982527 : Nat := 4983230072969 + 3 ^ 40 * 982527 * 2
def baseEnd_982527 : Nat := 336339071346788394862631

theorem tailTrace_982527 : CollatzResearch.WordTrace tailWord_982527 prefixEnd_982527 336339071346788394862631 := by
  unfold tailWord_982527
  simp only [CollatzResearch.WordTrace]
  refine ⟨35835703711479956097289835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23890469140986637398193223 35835703711479956097289835)
  ·
    refine ⟨53753555567219934145934753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35835703711479956097289835 53753555567219934145934753)
    ·
      refine ⟨40315166675414950609451065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53753555567219934145934753 40315166675414950609451065)
      ·
        refine ⟨30236375006561212957088299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40315166675414950609451065 30236375006561212957088299)
        ·
          refine ⟨45354562509841819435632449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30236375006561212957088299 45354562509841819435632449)
          ·
            refine ⟨34015921882381364576724337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45354562509841819435632449 34015921882381364576724337)
            ·
              refine ⟨25511941411786023432543253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34015921882381364576724337 25511941411786023432543253)
              ·
                refine ⟨1195872253677469848400465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25511941411786023432543253 1195872253677469848400465)
                ·
                  refine ⟨896904190258102386300349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1195872253677469848400465 896904190258102386300349)
                  ·
                    refine ⟨336339071346788394862631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 896904190258102386300349 336339071346788394862631)
                    ·
                      rfl

theorem cell22_982527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 2, 3].length) (baseStart_982527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_982527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_982527 prefixEnd_982527 := by exact prefixLift 982527
  have htrace : WordTrace (prefixWord ++ tailWord_982527) baseStart_982527 baseEnd_982527 := by
    simpa [prefixWord, tailWord_982527, baseEnd_982527] using wordTrace_append hprefix tailTrace_982527
  have hstable : (prefixWord ++ tailWord_982527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982527).length < 2 ^ (prefixWord ++ tailWord_982527).sum := by decide
  have hdescent : baseEnd_982527 < baseStart_982527 := by decide
  rcases family_descends (prefixWord ++ tailWord_982527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982602 : List Nat := [3, 1, 2, 1, 1, 3, 3, 3, 5]
def baseStart_982602 : Nat := 118140960795 + 982602 * 2 ^ 59
def prefixEnd_982602 : Nat := 4983230072969 + 3 ^ 40 * 982602 * 2
def baseEnd_982602 : Nat := 112121581793171066412467

theorem tailTrace_982602 : CollatzResearch.WordTrace tailWord_982602 prefixEnd_982602 112121581793171066412467 := by
  unfold tailWord_982602
  simp only [CollatzResearch.WordTrace]
  refine ⟨8959609796552060976567515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23892292790805495937513373 8959609796552060976567515)
  ·
    refine ⟨13439414694828091464851273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8959609796552060976567515 13439414694828091464851273)
    ·
      refine ⟨10079561021121068598638455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13439414694828091464851273 10079561021121068598638455)
      ·
        refine ⟨15119341531681602897957683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10079561021121068598638455 15119341531681602897957683)
        ·
          refine ⟨22679012297522404346936525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15119341531681602897957683 22679012297522404346936525)
          ·
            refine ⟨8504629611570901630101197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22679012297522404346936525 8504629611570901630101197)
            ·
              refine ⟨3189236104339088111287949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8504629611570901630101197 3189236104339088111287949)
              ·
                refine ⟨1195963539127158041732981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3189236104339088111287949 1195963539127158041732981)
                ·
                  refine ⟨112121581793171066412467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1195963539127158041732981 112121581793171066412467)
                  ·
                    rfl

theorem cell22_982602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 5].length) (baseStart_982602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_982602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_982602 prefixEnd_982602 := by exact prefixLift 982602
  have htrace : WordTrace (prefixWord ++ tailWord_982602) baseStart_982602 baseEnd_982602 := by
    simpa [prefixWord, tailWord_982602, baseEnd_982602] using wordTrace_append hprefix tailTrace_982602
  have hstable : (prefixWord ++ tailWord_982602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982602).length < 2 ^ (prefixWord ++ tailWord_982602).sum := by decide
  have hdescent : baseEnd_982602 < baseStart_982602 := by decide
  rcases family_descends (prefixWord ++ tailWord_982602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982692 : List Nat := [2, 3, 1, 2, 2, 3, 9]
def baseStart_982692 : Nat := 118140960795 + 982692 * 2 ^ 59
def prefixEnd_982692 : Nat := 4983230072969 + 3 ^ 40 * 982692 * 2
def baseEnd_982692 : Nat := 12459094600695665351375

theorem tailTrace_982692 : CollatzResearch.WordTrace tailWord_982692 prefixEnd_982692 12459094600695665351375 := by
  unfold tailWord_982692
  simp only [CollatzResearch.WordTrace]
  refine ⟨17920860877941094638523165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23894481170588126184697553 17920860877941094638523165)
  ·
    refine ⟨6720322829227910489446187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17920860877941094638523165 6720322829227910489446187)
    ·
      refine ⟨10080484243841865734169281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6720322829227910489446187 10080484243841865734169281)
      ·
        refine ⟨7560363182881399300626961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10080484243841865734169281 7560363182881399300626961)
        ·
          refine ⟨5670272387161049475470221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7560363182881399300626961 5670272387161049475470221)
          ·
            refine ⟨2126352145185393553301333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5670272387161049475470221 2126352145185393553301333)
            ·
              refine ⟨12459094600695665351375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2126352145185393553301333 12459094600695665351375)
              ·
                rfl

theorem cell22_982692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 9].length) (baseStart_982692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_982692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_982692 prefixEnd_982692 := by exact prefixLift 982692
  have htrace : WordTrace (prefixWord ++ tailWord_982692) baseStart_982692 baseEnd_982692 := by
    simpa [prefixWord, tailWord_982692, baseEnd_982692] using wordTrace_append hprefix tailTrace_982692
  have hstable : (prefixWord ++ tailWord_982692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982692).length < 2 ^ (prefixWord ++ tailWord_982692).sum := by decide
  have hdescent : baseEnd_982692 < baseStart_982692 := by decide
  rcases family_descends (prefixWord ++ tailWord_982692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982737 : List Nat := [1, 2, 2, 1, 2, 4, 1, 2, 7]
def baseStart_982737 : Nat := 118140960795 + 982737 * 2 ^ 59
def prefixEnd_982737 : Nat := 4983230072969 + 3 ^ 40 * 982737 * 2
def baseEnd_982737 : Nat := 112136986212805949037329

theorem tailTrace_982737 : CollatzResearch.WordTrace tailWord_982737 prefixEnd_982737 112136986212805949037329 := by
  unfold tailWord_982737
  simp only [CollatzResearch.WordTrace]
  refine ⟨35843363040719161962434465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23895575360479441308289643 35843363040719161962434465)
  ·
    refine ⟨26882522280539371471825849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35843363040719161962434465 26882522280539371471825849)
    ·
      refine ⟨20161891710404528603869387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26882522280539371471825849 20161891710404528603869387)
      ·
        refine ⟨30242837565606792905804081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20161891710404528603869387 30242837565606792905804081)
        ·
          refine ⟨22682128174205094679353061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30242837565606792905804081 22682128174205094679353061)
          ·
            refine ⟨4252899032663455252378699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22682128174205094679353061 4252899032663455252378699)
            ·
              refine ⟨6379348548995182878568049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4252899032663455252378699 6379348548995182878568049)
              ·
                refine ⟨4784511411746387158926037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6379348548995182878568049 4784511411746387158926037)
                ·
                  refine ⟨112136986212805949037329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4784511411746387158926037 112136986212805949037329)
                  ·
                    rfl

theorem cell22_982737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 7].length) (baseStart_982737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_982737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_982737 prefixEnd_982737 := by exact prefixLift 982737
  have htrace : WordTrace (prefixWord ++ tailWord_982737) baseStart_982737 baseEnd_982737 := by
    simpa [prefixWord, tailWord_982737, baseEnd_982737] using wordTrace_append hprefix tailTrace_982737
  have hstable : (prefixWord ++ tailWord_982737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982737).length < 2 ^ (prefixWord ++ tailWord_982737).sum := by decide
  have hdescent : baseEnd_982737 < baseStart_982737 := by decide
  rcases family_descends (prefixWord ++ tailWord_982737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982752 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 4, 5]
def baseStart_982752 : Nat := 118140960795 + 982752 * 2 ^ 59
def prefixEnd_982752 : Nat := 4983230072969 + 3 ^ 40 * 982752 * 2
def baseEnd_982752 : Nat := 336416093444962807986941

theorem tailTrace_982752 : CollatzResearch.WordTrace tailWord_982752 prefixEnd_982752 336416093444962807986941 := by
  unfold tailWord_982752
  simp only [CollatzResearch.WordTrace]
  refine ⟨17921955067832409762115255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23895940090443213016153673 17921955067832409762115255)
  ·
    refine ⟨26882932601748614643172883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17921955067832409762115255 26882932601748614643172883)
    ·
      refine ⟨40324398902622921964759325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26882932601748614643172883 40324398902622921964759325)
      ·
        refine ⟨15121649588483595736784747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40324398902622921964759325 15121649588483595736784747)
        ·
          refine ⟨22682474382725393605177121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15121649588483595736784747 22682474382725393605177121)
          ·
            refine ⟨17011855787044045203882841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22682474382725393605177121 17011855787044045203882841)
            ·
              refine ⟨12758891840283033902912131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17011855787044045203882841 12758891840283033902912131)
              ·
                refine ⟨19138337760424550854368197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12758891840283033902912131 19138337760424550854368197)
                ·
                  refine ⟨3588438330079603285194037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19138337760424550854368197 3588438330079603285194037)
                  ·
                    refine ⟨336416093444962807986941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3588438330079603285194037 336416093444962807986941)
                    ·
                      rfl

theorem cell22_982752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 4, 5].length) (baseStart_982752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_982752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_982752 prefixEnd_982752 := by exact prefixLift 982752
  have htrace : WordTrace (prefixWord ++ tailWord_982752) baseStart_982752 baseEnd_982752 := by
    simpa [prefixWord, tailWord_982752, baseEnd_982752] using wordTrace_append hprefix tailTrace_982752
  have hstable : (prefixWord ++ tailWord_982752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982752).length < 2 ^ (prefixWord ++ tailWord_982752).sum := by decide
  have hdescent : baseEnd_982752 < baseStart_982752 := by decide
  rcases family_descends (prefixWord ++ tailWord_982752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982816 : List Nat := [2, 1, 1, 5, 1, 1, 3, 4, 4]
def baseStart_982816 : Nat := 118140960795 + 982816 * 2 ^ 59
def prefixEnd_982816 : Nat := 4983230072969 + 3 ^ 40 * 982816 * 2
def baseEnd_982816 : Nat := 112146000650962658128915

theorem tailTrace_982816 : CollatzResearch.WordTrace tailWord_982816 prefixEnd_982816 112146000650962658128915 := by
  unfold tailWord_982816
  simp only [CollatzResearch.WordTrace]
  refine ⟨17923122203716479227280151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23897496271621972303040201 17923122203716479227280151)
  ·
    refine ⟨26884683305574718840920227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17923122203716479227280151 26884683305574718840920227)
    ·
      refine ⟨40327024958362078261380341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26884683305574718840920227 40327024958362078261380341)
      ·
        refine ⟨3780658589846444837004407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40327024958362078261380341 3780658589846444837004407)
        ·
          refine ⟨5670987884769667255506611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3780658589846444837004407 5670987884769667255506611)
          ·
            refine ⟨8506481827154500883259917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5670987884769667255506611 8506481827154500883259917)
            ·
              refine ⟨3189930685182937831222469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8506481827154500883259917 3189930685182937831222469)
              ·
                refine ⟨598112003471800843354213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3189930685182937831222469 598112003471800843354213)
                ·
                  refine ⟨112146000650962658128915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 598112003471800843354213 112146000650962658128915)
                  ·
                    rfl

theorem cell22_982816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 4, 4].length) (baseStart_982816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_982816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_982816 prefixEnd_982816 := by exact prefixLift 982816
  have htrace : WordTrace (prefixWord ++ tailWord_982816) baseStart_982816 baseEnd_982816 := by
    simpa [prefixWord, tailWord_982816, baseEnd_982816] using wordTrace_append hprefix tailTrace_982816
  have hstable : (prefixWord ++ tailWord_982816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982816).length < 2 ^ (prefixWord ++ tailWord_982816).sum := by decide
  have hdescent : baseEnd_982816 < baseStart_982816 := by decide
  rcases family_descends (prefixWord ++ tailWord_982816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982846 : List Nat := [4, 2, 1, 2, 2, 2, 1, 1, 1, 6]
def baseStart_982846 : Nat := 118140960795 + 982846 * 2 ^ 59
def prefixEnd_982846 : Nat := 4983230072969 + 3 ^ 40 * 982846 * 2
def baseEnd_982846 : Nat := 336448271565977896136653

theorem tailTrace_982846 : CollatzResearch.WordTrace tailWord_982846 prefixEnd_982846 336448271565977896136653 := by
  unfold tailWord_982846
  simp only [CollatzResearch.WordTrace]
  refine ⟨4480917324665534197269049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23898225731549515718768261 4480917324665534197269049)
  ·
    refine ⟨3360687993499150647951787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4480917324665534197269049 3360687993499150647951787)
    ·
      refine ⟨5041031990248725971927681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3360687993499150647951787 5041031990248725971927681)
      ·
        refine ⟨3780773992686544478945761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5041031990248725971927681 3780773992686544478945761)
        ·
          refine ⟨2835580494514908359209321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3780773992686544478945761 2835580494514908359209321)
          ·
            refine ⟨2126685370886181269406991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2835580494514908359209321 2126685370886181269406991)
            ·
              refine ⟨3190028056329271904110487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2126685370886181269406991 3190028056329271904110487)
              ·
                refine ⟨4785042084493907856165731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3190028056329271904110487 4785042084493907856165731)
                ·
                  refine ⟨7177563126740861784248597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4785042084493907856165731 7177563126740861784248597)
                  ·
                    refine ⟨336448271565977896136653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7177563126740861784248597 336448271565977896136653)
                    ·
                      rfl

theorem cell22_982846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_982846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_982846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_982846 prefixEnd_982846 := by exact prefixLift 982846
  have htrace : WordTrace (prefixWord ++ tailWord_982846) baseStart_982846 baseEnd_982846 := by
    simpa [prefixWord, tailWord_982846, baseEnd_982846] using wordTrace_append hprefix tailTrace_982846
  have hstable : (prefixWord ++ tailWord_982846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982846).length < 2 ^ (prefixWord ++ tailWord_982846).sum := by decide
  have hdescent : baseEnd_982846 < baseStart_982846 := by decide
  rcases family_descends (prefixWord ++ tailWord_982846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982861 : List Nat := [1, 6, 1, 2, 1, 2, 9]
def baseStart_982861 : Nat := 118140960795 + 982861 * 2 ^ 59
def prefixEnd_982861 : Nat := 4983230072969 + 3 ^ 40 * 982861 * 2
def baseEnd_982861 : Nat := 12461237273056402111541

theorem tailTrace_982861 : CollatzResearch.WordTrace tailWord_982861 prefixEnd_982861 12461237273056402111541 := by
  unfold tailWord_982861
  simp only [CollatzResearch.WordTrace]
  refine ⟨35847885692269931139948437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23898590461513287426632291 35847885692269931139948437)
  ·
    refine ⟨1680369641825153022185083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35847885692269931139948437 1680369641825153022185083)
    ·
      refine ⟨2520554462737729533277625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1680369641825153022185083 2520554462737729533277625)
      ·
        refine ⟨1890415847053297149958219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2520554462737729533277625 1890415847053297149958219)
        ·
          refine ⟨2835623770579945724937329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1890415847053297149958219 2835623770579945724937329)
          ·
            refine ⟨2126717827934959293702997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2835623770579945724937329 2126717827934959293702997)
            ·
              refine ⟨12461237273056402111541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2126717827934959293702997 12461237273056402111541)
              ·
                rfl

theorem cell22_982861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 9].length) (baseStart_982861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_982861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_982861 prefixEnd_982861 := by exact prefixLift 982861
  have htrace : WordTrace (prefixWord ++ tailWord_982861) baseStart_982861 baseEnd_982861 := by
    simpa [prefixWord, tailWord_982861, baseEnd_982861] using wordTrace_append hprefix tailTrace_982861
  have hstable : (prefixWord ++ tailWord_982861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982861).length < 2 ^ (prefixWord ++ tailWord_982861).sum := by decide
  have hdescent : baseEnd_982861 < baseStart_982861 := by decide
  rcases family_descends (prefixWord ++ tailWord_982861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982889 : List Nat := [1, 2, 1, 1, 1, 3, 1, 7, 5]
def baseStart_982889 : Nat := 118140960795 + 982889 * 2 ^ 59
def prefixEnd_982889 : Nat := 4983230072969 + 3 ^ 40 * 982889 * 2
def baseEnd_982889 : Nat := 112154330448246705770507

theorem tailTrace_982889 : CollatzResearch.WordTrace tailWord_982889 prefixEnd_982889 112154330448246705770507 := by
  unfold tailWord_982889
  simp only [CollatzResearch.WordTrace]
  refine ⟨35848906936168491921967721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23899271290778994614645147 35848906936168491921967721)
  ·
    refine ⟨26886680202126368941475791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35848906936168491921967721 26886680202126368941475791)
    ·
      refine ⟨40330020303189553412213687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26886680202126368941475791 40330020303189553412213687)
      ·
        refine ⟨60495030454784330118320531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40330020303189553412213687 60495030454784330118320531)
        ·
          refine ⟨90742545682176495177480797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60495030454784330118320531 90742545682176495177480797)
          ·
            refine ⟨34028454630816185691555299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90742545682176495177480797 34028454630816185691555299)
            ·
              refine ⟨51042681946224278537332949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34028454630816185691555299 51042681946224278537332949)
              ·
                refine ⟨1196312858114631528218741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 51042681946224278537332949 1196312858114631528218741)
                ·
                  refine ⟨112154330448246705770507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1196312858114631528218741 112154330448246705770507)
                  ·
                    rfl

theorem cell22_982889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 5].length) (baseStart_982889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_982889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_982889 prefixEnd_982889 := by exact prefixLift 982889
  have htrace : WordTrace (prefixWord ++ tailWord_982889) baseStart_982889 baseEnd_982889 := by
    simpa [prefixWord, tailWord_982889, baseEnd_982889] using wordTrace_append hprefix tailTrace_982889
  have hstable : (prefixWord ++ tailWord_982889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982889).length < 2 ^ (prefixWord ++ tailWord_982889).sum := by decide
  have hdescent : baseEnd_982889 < baseStart_982889 := by decide
  rcases family_descends (prefixWord ++ tailWord_982889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982940 : List Nat := [2, 2, 3, 3, 1, 3, 2, 1, 5]
def baseStart_982940 : Nat := 118140960795 + 982940 * 2 ^ 59
def prefixEnd_982940 : Nat := 4983230072969 + 3 ^ 40 * 982940 * 2
def baseEnd_982940 : Nat := 112160149895664328095455

theorem tailTrace_982940 : CollatzResearch.WordTrace tailWord_982940 prefixEnd_982940 112160149895664328095455 := by
  unfold tailWord_982940
  simp only [CollatzResearch.WordTrace]
  refine ⟨17925383529491863816037137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23900511372655818421382849 17925383529491863816037137)
  ·
    refine ⟨13444037647118897862027853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17925383529491863816037137 13444037647118897862027853)
    ·
      refine ⟨5041514117669586698260445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13444037647118897862027853 5041514117669586698260445)
      ·
        refine ⟨1890567794126095011847667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5041514117669586698260445 1890567794126095011847667)
        ·
          refine ⟨2835851691189142517771501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1890567794126095011847667 2835851691189142517771501)
          ·
            refine ⟨1063444384195928444164313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2835851691189142517771501 1063444384195928444164313)
            ·
              refine ⟨797583288146946333123235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1063444384195928444164313 797583288146946333123235)
              ·
                refine ⟨1196374932220419499684853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 797583288146946333123235 1196374932220419499684853)
                ·
                  refine ⟨112160149895664328095455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1196374932220419499684853 112160149895664328095455)
                  ·
                    rfl

theorem cell22_982940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 5].length) (baseStart_982940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_982940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_982940 prefixEnd_982940 := by exact prefixLift 982940
  have htrace : WordTrace (prefixWord ++ tailWord_982940) baseStart_982940 baseEnd_982940 := by
    simpa [prefixWord, tailWord_982940, baseEnd_982940] using wordTrace_append hprefix tailTrace_982940
  have hstable : (prefixWord ++ tailWord_982940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982940).length < 2 ^ (prefixWord ++ tailWord_982940).sum := by decide
  have hdescent : baseEnd_982940 < baseStart_982940 := by decide
  rcases family_descends (prefixWord ++ tailWord_982940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_982949 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 5, 5]
def baseStart_982949 : Nat := 118140960795 + 982949 * 2 ^ 59
def prefixEnd_982949 : Nat := 4983230072969 + 3 ^ 40 * 982949 * 2
def baseEnd_982949 : Nat := 336483530570919960811337

theorem tailTrace_982949 : CollatzResearch.WordTrace tailWord_982949 prefixEnd_982949 336483530570919960811337 := by
  unfold tailWord_982949
  simp only [CollatzResearch.WordTrace]
  refine ⟨35851095315951122169151901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23900730210634081446101267 35851095315951122169151901)
  ·
    refine ⟨13444160743481670813431963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35851095315951122169151901 13444160743481670813431963)
    ·
      refine ⟨20166241115222506220147945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13444160743481670813431963 20166241115222506220147945)
      ·
        refine ⟨15124680836416879665110959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20166241115222506220147945 15124680836416879665110959)
        ·
          refine ⟨22687021254625319497666439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15124680836416879665110959 22687021254625319497666439)
          ·
            refine ⟨34030531881937979246499659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22687021254625319497666439 34030531881937979246499659)
            ·
              refine ⟨51045797822906968869749489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34030531881937979246499659 51045797822906968869749489)
              ·
                refine ⟨38284348367180226652312117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51045797822906968869749489 38284348367180226652312117)
                ·
                  refine ⟨3589157659423146248654261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38284348367180226652312117 3589157659423146248654261)
                  ·
                    refine ⟨336483530570919960811337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3589157659423146248654261 336483530570919960811337)
                    ·
                      rfl

theorem cell22_982949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_982949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_982949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_982949 prefixEnd_982949 := by exact prefixLift 982949
  have htrace : WordTrace (prefixWord ++ tailWord_982949) baseStart_982949 baseEnd_982949 := by
    simpa [prefixWord, tailWord_982949, baseEnd_982949] using wordTrace_append hprefix tailTrace_982949
  have hstable : (prefixWord ++ tailWord_982949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_982949).length < 2 ^ (prefixWord ++ tailWord_982949).sum := by decide
  have hdescent : baseEnd_982949 < baseStart_982949 := by decide
  rcases family_descends (prefixWord ++ tailWord_982949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983015 : List Nat := [1, 1, 5, 2, 3, 2, 1, 1, 2, 4]
def baseStart_983015 : Nat := 118140960795 + 983015 * 2 ^ 59
def prefixEnd_983015 : Nat := 4983230072969 + 3 ^ 40 * 983015 * 2
def baseEnd_983015 : Nat := 336506123719717788661135

theorem tailTrace_983015 : CollatzResearch.WordTrace tailWord_983015 prefixEnd_983015 336506123719717788661135 := by
  unfold tailWord_983015
  simp only [CollatzResearch.WordTrace]
  refine ⟨35853502533712015441054499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23902335022474676960702999 35853502533712015441054499)
  ·
    refine ⟨53780253800568023161581749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35853502533712015441054499 53780253800568023161581749)
    ·
      refine ⟨5041898793803252171398289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53780253800568023161581749 5041898793803252171398289)
      ·
        refine ⟨3781424095352439128548717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5041898793803252171398289 3781424095352439128548717)
        ·
          refine ⟨1418034035757164673205769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3781424095352439128548717 1418034035757164673205769)
          ·
            refine ⟨1063525526817873504904327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1418034035757164673205769 1063525526817873504904327)
            ·
              refine ⟨1595288290226810257356491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1063525526817873504904327 1595288290226810257356491)
              ·
                refine ⟨2392932435340215386034737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1595288290226810257356491 2392932435340215386034737)
                ·
                  refine ⟨1794699326505161539526053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2392932435340215386034737 1794699326505161539526053)
                  ·
                    refine ⟨336506123719717788661135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1794699326505161539526053 336506123719717788661135)
                    ·
                      rfl

theorem cell22_983015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_983015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_983015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_983015 prefixEnd_983015 := by exact prefixLift 983015
  have htrace : WordTrace (prefixWord ++ tailWord_983015) baseStart_983015 baseEnd_983015 := by
    simpa [prefixWord, tailWord_983015, baseEnd_983015] using wordTrace_append hprefix tailTrace_983015
  have hstable : (prefixWord ++ tailWord_983015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983015).length < 2 ^ (prefixWord ++ tailWord_983015).sum := by decide
  have hdescent : baseEnd_983015 < baseStart_983015 := by decide
  rcases family_descends (prefixWord ++ tailWord_983015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983041 : List Nat := [1, 2, 4, 1, 2, 1, 3, 1, 7]
def baseStart_983041 : Nat := 118140960795 + 983041 * 2 ^ 59
def prefixEnd_983041 : Nat := 4983230072969 + 3 ^ 40 * 983041 * 2
def baseEnd_983041 : Nat := 112171674683687462503685

theorem tailTrace_983041 : CollatzResearch.WordTrace tailWord_983041 prefixEnd_983041 112171674683687462503685 := by
  unfold tailWord_983041
  simp only [CollatzResearch.WordTrace]
  refine ⟨35854450831617821881500977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23902967221078547921000651 35854450831617821881500977)
  ·
    refine ⟨26890838123713366411125733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35854450831617821881500977 26890838123713366411125733)
    ·
      refine ⟨5042032148196256202086075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26890838123713366411125733 5042032148196256202086075)
      ·
        refine ⟨7563048222294384303129113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5042032148196256202086075 7563048222294384303129113)
        ·
          refine ⟨5672286166720788227346835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7563048222294384303129113 5672286166720788227346835)
          ·
            refine ⟨8508429250081182341020253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5672286166720788227346835 8508429250081182341020253)
            ·
              refine ⟨3190660968780443377882595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8508429250081182341020253 3190660968780443377882595)
              ·
                refine ⟨4785991453170665066823893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3190660968780443377882595 4785991453170665066823893)
                ·
                  refine ⟨112171674683687462503685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4785991453170665066823893 112171674683687462503685)
                  ·
                    rfl

theorem cell22_983041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 7].length) (baseStart_983041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_983041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_983041 prefixEnd_983041 := by exact prefixLift 983041
  have htrace : WordTrace (prefixWord ++ tailWord_983041) baseStart_983041 baseEnd_983041 := by
    simpa [prefixWord, tailWord_983041, baseEnd_983041] using wordTrace_append hprefix tailTrace_983041
  have hstable : (prefixWord ++ tailWord_983041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983041).length < 2 ^ (prefixWord ++ tailWord_983041).sum := by decide
  have hdescent : baseEnd_983041 < baseStart_983041 := by decide
  rcases family_descends (prefixWord ++ tailWord_983041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983045 : List Nat := [1, 3, 1, 1, 2, 4, 2, 4, 1, 3]
def baseStart_983045 : Nat := 118140960795 + 983045 * 2 ^ 59
def prefixEnd_983045 : Nat := 4983230072969 + 3 ^ 40 * 983045 * 2
def baseEnd_983045 : Nat := 336516393332807710411043

theorem tailTrace_983045 : CollatzResearch.WordTrace tailWord_983045 prefixEnd_983045 336516393332807710411043 := by
  unfold tailWord_983045
  simp only [CollatzResearch.WordTrace]
  refine ⟨35854596723603330564646589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23903064482402220376431059 35854596723603330564646589)
  ·
    refine ⟨13445473771351248961742471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35854596723603330564646589 13445473771351248961742471)
    ·
      refine ⟨20168210657026873442613707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13445473771351248961742471 20168210657026873442613707)
      ·
        refine ⟨30252315985540310163920561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20168210657026873442613707 30252315985540310163920561)
        ·
          refine ⟨22689236989155232622940421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30252315985540310163920561 22689236989155232622940421)
          ·
            refine ⟨4254231935466606116801329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22689236989155232622940421 4254231935466606116801329)
            ·
              refine ⟨3190673951599954587600997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4254231935466606116801329 3190673951599954587600997)
              ·
                refine ⟨598251365924991485175187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3190673951599954587600997 598251365924991485175187)
                ·
                  refine ⟨897377048887487227762781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 598251365924991485175187 897377048887487227762781)
                  ·
                    refine ⟨336516393332807710411043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 897377048887487227762781 336516393332807710411043)
                    ·
                      rfl

theorem cell22_983045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 4, 1, 3].length) (baseStart_983045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_983045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_983045 prefixEnd_983045 := by exact prefixLift 983045
  have htrace : WordTrace (prefixWord ++ tailWord_983045) baseStart_983045 baseEnd_983045 := by
    simpa [prefixWord, tailWord_983045, baseEnd_983045] using wordTrace_append hprefix tailTrace_983045
  have hstable : (prefixWord ++ tailWord_983045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983045).length < 2 ^ (prefixWord ++ tailWord_983045).sum := by decide
  have hdescent : baseEnd_983045 < baseStart_983045 := by decide
  rcases family_descends (prefixWord ++ tailWord_983045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983088 : List Nat := [2, 1, 1, 1, 2, 5, 2, 3, 1, 4]
def baseStart_983088 : Nat := 118140960795 + 983088 * 2 ^ 59
def prefixEnd_983088 : Nat := 4983230072969 + 3 ^ 40 * 983088 * 2
def baseEnd_983088 : Nat := 336531113111569931585911

theorem tailTrace_983088 : CollatzResearch.WordTrace tailWord_983088 prefixEnd_983088 336531113111569931585911 := by
  unfold tailWord_983088
  simp only [CollatzResearch.WordTrace]
  refine ⟨17928082531223774454230959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23904110041631699272307945 17928082531223774454230959)
  ·
    refine ⟨26892123796835661681346439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17928082531223774454230959 26892123796835661681346439)
    ·
      refine ⟨40338185695253492522019659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26892123796835661681346439 40338185695253492522019659)
      ·
        refine ⟨60507278542880238783029489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40338185695253492522019659 60507278542880238783029489)
        ·
          refine ⟨45380458907160179087272117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60507278542880238783029489 45380458907160179087272117)
          ·
            refine ⟨4254418022546266789431761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45380458907160179087272117 4254418022546266789431761)
            ·
              refine ⟨3190813516909700092073821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4254418022546266789431761 3190813516909700092073821)
              ·
                refine ⟨1196555068841137534527683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3190813516909700092073821 1196555068841137534527683)
                ·
                  refine ⟨1794832603261706301791525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1196555068841137534527683 1794832603261706301791525)
                  ·
                    refine ⟨336531113111569931585911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1794832603261706301791525 336531113111569931585911)
                    ·
                      rfl

theorem cell22_983088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 1, 4].length) (baseStart_983088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_983088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_983088 prefixEnd_983088 := by exact prefixLift 983088
  have htrace : WordTrace (prefixWord ++ tailWord_983088) baseStart_983088 baseEnd_983088 := by
    simpa [prefixWord, tailWord_983088, baseEnd_983088] using wordTrace_append hprefix tailTrace_983088
  have hstable : (prefixWord ++ tailWord_983088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983088).length < 2 ^ (prefixWord ++ tailWord_983088).sum := by decide
  have hdescent : baseEnd_983088 < baseStart_983088 := by decide
  rcases family_descends (prefixWord ++ tailWord_983088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983103 : List Nat := [1, 1, 2, 2, 3, 1, 2, 6, 4]
def baseStart_983103 : Nat := 118140960795 + 983103 * 2 ^ 59
def prefixEnd_983103 : Nat := 4983230072969 + 3 ^ 40 * 983103 * 2
def baseEnd_983103 : Nat := 112178749306038297486955

theorem tailTrace_983103 : CollatzResearch.WordTrace tailWord_983103 prefixEnd_983103 112178749306038297486955 := by
  unfold tailWord_983103
  simp only [CollatzResearch.WordTrace]
  refine ⟨35856712157393206470257963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23904474771595470980171975 35856712157393206470257963)
  ·
    refine ⟨53785068236089809705386945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35856712157393206470257963 53785068236089809705386945)
    ·
      refine ⟨40338801177067357279040209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53785068236089809705386945 40338801177067357279040209)
      ·
        refine ⟨30254100882800517959280157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40338801177067357279040209 30254100882800517959280157)
        ·
          refine ⟨11345287831050194234730059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30254100882800517959280157 11345287831050194234730059)
          ·
            refine ⟨17017931746575291352095089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11345287831050194234730059 17017931746575291352095089)
            ·
              refine ⟨12763448809931468514071317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17017931746575291352095089 12763448809931468514071317)
              ·
                refine ⟨598286662965537586597093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12763448809931468514071317 598286662965537586597093)
                ·
                  refine ⟨112178749306038297486955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 598286662965537586597093 112178749306038297486955)
                  ·
                    rfl

theorem cell22_983103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 6, 4].length) (baseStart_983103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_983103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_983103 prefixEnd_983103 := by exact prefixLift 983103
  have htrace : WordTrace (prefixWord ++ tailWord_983103) baseStart_983103 baseEnd_983103 := by
    simpa [prefixWord, tailWord_983103, baseEnd_983103] using wordTrace_append hprefix tailTrace_983103
  have hstable : (prefixWord ++ tailWord_983103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983103).length < 2 ^ (prefixWord ++ tailWord_983103).sum := by decide
  have hdescent : baseEnd_983103 < baseStart_983103 := by decide
  rcases family_descends (prefixWord ++ tailWord_983103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983116 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 3, 6]
def baseStart_983116 : Nat := 118140960795 + 983116 * 2 ^ 59
def prefixEnd_983116 : Nat := 4983230072969 + 3 ^ 40 * 983116 * 2
def baseEnd_983116 : Nat := 336540698083787191885825

theorem tailTrace_983116 : CollatzResearch.WordTrace tailWord_983116 prefixEnd_983116 336540698083787191885825 := by
  unfold tailWord_983116
  simp only [CollatzResearch.WordTrace]
  refine ⟨17928593153173054845240601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23904790870897406460320801 17928593153173054845240601)
  ·
    refine ⟨13446444864879791133930451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17928593153173054845240601 13446444864879791133930451)
    ·
      refine ⟨20169667297319686700895677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13446444864879791133930451 20169667297319686700895677)
      ·
        refine ⟨7563625236494882512835879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20169667297319686700895677 7563625236494882512835879)
        ·
          refine ⟨11345437854742323769253819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7563625236494882512835879 11345437854742323769253819)
          ·
            refine ⟨17018156782113485653880729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11345437854742323769253819 17018156782113485653880729)
            ·
              refine ⟨12763617586585114240410547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17018156782113485653880729 12763617586585114240410547)
              ·
                refine ⟨19145426379877671360615821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12763617586585114240410547 19145426379877671360615821)
                ·
                  refine ⟨7179534892454126760230933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19145426379877671360615821 7179534892454126760230933)
                  ·
                    refine ⟨336540698083787191885825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7179534892454126760230933 336540698083787191885825)
                    ·
                      rfl

theorem cell22_983116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_983116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_983116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_983116 prefixEnd_983116 := by exact prefixLift 983116
  have htrace : WordTrace (prefixWord ++ tailWord_983116) baseStart_983116 baseEnd_983116 := by
    simpa [prefixWord, tailWord_983116, baseEnd_983116] using wordTrace_append hprefix tailTrace_983116
  have hstable : (prefixWord ++ tailWord_983116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983116).length < 2 ^ (prefixWord ++ tailWord_983116).sum := by decide
  have hdescent : baseEnd_983116 < baseStart_983116 := by decide
  rcases family_descends (prefixWord ++ tailWord_983116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983122 : List Nat := [3, 2, 2, 1, 4, 2, 1, 2, 1, 4]
def baseStart_983122 : Nat := 118140960795 + 983122 * 2 ^ 59
def prefixEnd_983122 : Nat := 4983230072969 + 3 ^ 40 * 983122 * 2
def baseEnd_983122 : Nat := 336542752006405176235807

theorem tailTrace_983122 : CollatzResearch.WordTrace tailWord_983122 prefixEnd_983122 336542752006405176235807 := by
  unfold tailWord_983122
  simp only [CollatzResearch.WordTrace]
  refine ⟨8964351286081093178799905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23904936762882915143466413 8964351286081093178799905)
  ·
    refine ⟨6723263464560819884099929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8964351286081093178799905 6723263464560819884099929)
    ·
      refine ⟨5042447598420614913074947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6723263464560819884099929 5042447598420614913074947)
      ·
        refine ⟨7563671397630922369612421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5042447598420614913074947 7563671397630922369612421)
        ·
          refine ⟨1418188387055797944302329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7563671397630922369612421 1418188387055797944302329)
          ·
            refine ⟨1063641290291848458226747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1418188387055797944302329 1063641290291848458226747)
            ·
              refine ⟨1595461935437772687340121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1063641290291848458226747 1595461935437772687340121)
              ·
                refine ⟨1196596451578329515505091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1595461935437772687340121 1196596451578329515505091)
                ·
                  refine ⟨1794894677367494273257637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1196596451578329515505091 1794894677367494273257637)
                  ·
                    refine ⟨336542752006405176235807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1794894677367494273257637 336542752006405176235807)
                    ·
                      rfl

theorem cell22_983122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_983122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_983122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_983122 prefixEnd_983122 := by exact prefixLift 983122
  have htrace : WordTrace (prefixWord ++ tailWord_983122) baseStart_983122 baseEnd_983122 := by
    simpa [prefixWord, tailWord_983122, baseEnd_983122] using wordTrace_append hprefix tailTrace_983122
  have hstable : (prefixWord ++ tailWord_983122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983122).length < 2 ^ (prefixWord ++ tailWord_983122).sum := by decide
  have hdescent : baseEnd_983122 < baseStart_983122 := by decide
  rcases family_descends (prefixWord ++ tailWord_983122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983190 : List Nat := [5, 3, 2, 1, 1, 2, 2, 1, 1, 4]
def baseStart_983190 : Nat := 118140960795 + 983190 * 2 ^ 59
def prefixEnd_983190 : Nat := 4983230072969 + 3 ^ 40 * 983190 * 2
def baseEnd_983190 : Nat := 336566029796075665535599

theorem tailTrace_983190 : CollatzResearch.WordTrace tailWord_983190 prefixEnd_983190 336566029796075665535599 := by
  unfold tailWord_983190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2241242831754876270542189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23906590205385346885783349 2241242831754876270542189)
  ·
    refine ⟨840466061908078601453321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2241242831754876270542189 840466061908078601453321)
    ·
      refine ⟨630349546431058951089991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 840466061908078601453321 630349546431058951089991)
      ·
        refine ⟨945524319646588426634987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630349546431058951089991 945524319646588426634987)
        ·
          refine ⟨1418286479469882639952481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 945524319646588426634987 1418286479469882639952481)
          ·
            refine ⟨1063714859602411979964361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1418286479469882639952481 1063714859602411979964361)
            ·
              refine ⟨797786144701808984973271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1063714859602411979964361 797786144701808984973271)
              ·
                refine ⟨1196679217052713477459907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 797786144701808984973271 1196679217052713477459907)
                ·
                  refine ⟨1795018825579070216189861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1196679217052713477459907 1795018825579070216189861)
                  ·
                    refine ⟨336566029796075665535599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1795018825579070216189861 336566029796075665535599)
                    ·
                      rfl

theorem cell22_983190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_983190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_983190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_983190 prefixEnd_983190 := by exact prefixLift 983190
  have htrace : WordTrace (prefixWord ++ tailWord_983190) baseStart_983190 baseEnd_983190 := by
    simpa [prefixWord, tailWord_983190, baseEnd_983190] using wordTrace_append hprefix tailTrace_983190
  have hstable : (prefixWord ++ tailWord_983190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983190).length < 2 ^ (prefixWord ++ tailWord_983190).sum := by decide
  have hdescent : baseEnd_983190 < baseStart_983190 := by decide
  rcases family_descends (prefixWord ++ tailWord_983190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983197 : List Nat := [1, 4, 2, 1, 1, 3, 1, 5, 1, 3]
def baseStart_983197 : Nat := 118140960795 + 983197 * 2 ^ 59
def prefixEnd_983197 : Nat := 4983230072969 + 3 ^ 40 * 983197 * 2
def baseEnd_983197 : Nat := 336568426039129980610577

theorem tailTrace_983197 : CollatzResearch.WordTrace tailWord_983197 prefixEnd_983197 336568426039129980610577 := by
  unfold tailWord_983197
  simp only [CollatzResearch.WordTrace]
  refine ⟨35860140619052660524179845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23906760412701773682786563 35860140619052660524179845)
  ·
    refine ⟨6723776366072373848283721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35860140619052660524179845 6723776366072373848283721)
    ·
      refine ⟨5042832274554280386212791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6723776366072373848283721 5042832274554280386212791)
      ·
        refine ⟨7564248411831420579319187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5042832274554280386212791 7564248411831420579319187)
        ·
          refine ⟨11346372617747130868978781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7564248411831420579319187 11346372617747130868978781)
          ·
            refine ⟨4254889731655174075867043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11346372617747130868978781 4254889731655174075867043)
            ·
              refine ⟨6382334597482761113800565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4254889731655174075867043 6382334597482761113800565)
              ·
                refine ⟨598343868514008854418803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6382334597482761113800565 598343868514008854418803)
                ·
                  refine ⟨897515802771013281628205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 598343868514008854418803 897515802771013281628205)
                  ·
                    refine ⟨336568426039129980610577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 897515802771013281628205 336568426039129980610577)
                    ·
                      rfl

theorem cell22_983197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_983197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_983197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_983197 prefixEnd_983197 := by exact prefixLift 983197
  have htrace : WordTrace (prefixWord ++ tailWord_983197) baseStart_983197 baseEnd_983197 := by
    simpa [prefixWord, tailWord_983197, baseEnd_983197] using wordTrace_append hprefix tailTrace_983197
  have hstable : (prefixWord ++ tailWord_983197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983197).length < 2 ^ (prefixWord ++ tailWord_983197).sum := by decide
  have hdescent : baseEnd_983197 < baseStart_983197 := by decide
  rcases family_descends (prefixWord ++ tailWord_983197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983283 : List Nat := [1, 1, 1, 2, 2, 4, 4, 7]
def baseStart_983283 : Nat := 118140960795 + 983283 * 2 ^ 59
def prefixEnd_983283 : Nat := 4983230072969 + 3 ^ 40 * 983283 * 2
def baseEnd_983283 : Nat := 37399762844072713662257

theorem tailTrace_983283 : CollatzResearch.WordTrace tailWord_983283 prefixEnd_983283 37399762844072713662257 := by
  unfold tailWord_983283
  simp only [CollatzResearch.WordTrace]
  refine ⟨35863277296741097211810503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23908851531160731474540335 35863277296741097211810503)
  ·
    refine ⟨53794915945111645817715755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35863277296741097211810503 53794915945111645817715755)
    ·
      refine ⟨80692373917667468726573633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53794915945111645817715755 80692373917667468726573633)
      ·
        refine ⟨60519280438250601544930225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80692373917667468726573633 60519280438250601544930225)
        ·
          refine ⟨45389460328687951158697669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60519280438250601544930225 45389460328687951158697669)
          ·
            refine ⟨8510523811628990842255813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45389460328687951158697669 8510523811628990842255813)
            ·
              refine ⟨1595723214680435782922965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8510523811628990842255813 1595723214680435782922965)
              ·
                refine ⟨37399762844072713662257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1595723214680435782922965 37399762844072713662257)
                ·
                  rfl

theorem cell22_983283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 7].length) (baseStart_983283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_983283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_983283 prefixEnd_983283 := by exact prefixLift 983283
  have htrace : WordTrace (prefixWord ++ tailWord_983283) baseStart_983283 baseEnd_983283 := by
    simpa [prefixWord, tailWord_983283, baseEnd_983283] using wordTrace_append hprefix tailTrace_983283
  have hstable : (prefixWord ++ tailWord_983283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983283).length < 2 ^ (prefixWord ++ tailWord_983283).sum := by decide
  have hdescent : baseEnd_983283 < baseStart_983283 := by decide
  rcases family_descends (prefixWord ++ tailWord_983283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983330 : List Nat := [3, 3, 1, 1, 3, 1, 1, 1, 2, 6]
def baseStart_983330 : Nat := 118140960795 + 983330 * 2 ^ 59
def prefixEnd_983330 : Nat := 4983230072969 + 3 ^ 40 * 983330 * 2
def baseEnd_983330 : Nat := 336613954657161967035169

theorem tailTrace_983330 : CollatzResearch.WordTrace tailWord_983330 prefixEnd_983330 336613954657161967035169 := by
  unfold tailWord_983330
  simp only [CollatzResearch.WordTrace]
  refine ⟨8966247881892706059692861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23909994351713882825847629 8966247881892706059692861)
  ·
    refine ⟨3362342955709764772384823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8966247881892706059692861 3362342955709764772384823)
    ·
      refine ⟨5043514433564647158577235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3362342955709764772384823 5043514433564647158577235)
      ·
        refine ⟨7565271650346970737865853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5043514433564647158577235 7565271650346970737865853)
        ·
          refine ⟨2836976868880114026699695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7565271650346970737865853 2836976868880114026699695)
          ·
            refine ⟨4255465303320171040049543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2836976868880114026699695 4255465303320171040049543)
            ·
              refine ⟨6383197954980256560074315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4255465303320171040049543 6383197954980256560074315)
              ·
                refine ⟨9574796932470384840111473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6383197954980256560074315 9574796932470384840111473)
                ·
                  refine ⟨7181097699352788630083605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9574796932470384840111473 7181097699352788630083605)
                  ·
                    refine ⟨336613954657161967035169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7181097699352788630083605 336613954657161967035169)
                    ·
                      rfl

theorem cell22_983330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_983330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_983330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_983330 prefixEnd_983330 := by exact prefixLift 983330
  have htrace : WordTrace (prefixWord ++ tailWord_983330) baseStart_983330 baseEnd_983330 := by
    simpa [prefixWord, tailWord_983330, baseEnd_983330] using wordTrace_append hprefix tailTrace_983330
  have hstable : (prefixWord ++ tailWord_983330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983330).length < 2 ^ (prefixWord ++ tailWord_983330).sum := by decide
  have hdescent : baseEnd_983330 < baseStart_983330 := by decide
  rcases family_descends (prefixWord ++ tailWord_983330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983343 : List Nat := [1, 1, 2, 1, 2, 1, 5, 1, 1, 7]
def baseStart_983343 : Nat := 118140960795 + 983343 * 2 ^ 59
def prefixEnd_983343 : Nat := 4983230072969 + 3 ^ 40 * 983343 * 2
def baseEnd_983343 : Nat := 336618404822834266460129

theorem tailTrace_983343 : CollatzResearch.WordTrace tailWord_983343 prefixEnd_983343 336618404822834266460129 := by
  unfold tailWord_983343
  simp only [CollatzResearch.WordTrace]
  refine ⟨35865465676523727458994683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23910310451015818305996455 35865465676523727458994683)
  ·
    refine ⟨53798198514785591188492025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35865465676523727458994683 53798198514785591188492025)
    ·
      refine ⟨40348648886089193391369019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53798198514785591188492025 40348648886089193391369019)
      ·
        refine ⟨60522973329133790087053529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40348648886089193391369019 60522973329133790087053529)
        ·
          refine ⟨45392229996850342565290147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60522973329133790087053529 45392229996850342565290147)
          ·
            refine ⟨68088344995275513847935221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45392229996850342565290147 68088344995275513847935221)
            ·
              refine ⟨6383282343307079423243927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68088344995275513847935221 6383282343307079423243927)
              ·
                refine ⟨9574923514960619134865891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6383282343307079423243927 9574923514960619134865891)
                ·
                  refine ⟨14362385272440928702298837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9574923514960619134865891 14362385272440928702298837)
                  ·
                    refine ⟨336618404822834266460129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14362385272440928702298837 336618404822834266460129)
                    ·
                      rfl

theorem cell22_983343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 7].length) (baseStart_983343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_983343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_983343 prefixEnd_983343 := by exact prefixLift 983343
  have htrace : WordTrace (prefixWord ++ tailWord_983343) baseStart_983343 baseEnd_983343 := by
    simpa [prefixWord, tailWord_983343, baseEnd_983343] using wordTrace_append hprefix tailTrace_983343
  have hstable : (prefixWord ++ tailWord_983343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983343).length < 2 ^ (prefixWord ++ tailWord_983343).sum := by decide
  have hdescent : baseEnd_983343 < baseStart_983343 := by decide
  rcases family_descends (prefixWord ++ tailWord_983343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983435 : List Nat := [1, 1, 1, 1, 4, 6, 8]
def baseStart_983435 : Nat := 118140960795 + 983435 * 2 ^ 59
def prefixEnd_983435 : Nat := 4983230072969 + 3 ^ 40 * 983435 * 2
def baseEnd_983435 : Nat := 12468514751962099746661

theorem tailTrace_983435 : CollatzResearch.WordTrace tailWord_983435 prefixEnd_983435 12468514751962099746661 := by
  unfold tailWord_983435
  simp only [CollatzResearch.WordTrace]
  refine ⟨35868821192190427171343759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23912547461460284780895839 35868821192190427171343759)
  ·
    refine ⟨53803231788285640757015639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35868821192190427171343759 53803231788285640757015639)
    ·
      refine ⟨80704847682428461135523459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53803231788285640757015639 80704847682428461135523459)
      ·
        refine ⟨121057271523642691703285189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80704847682428461135523459 121057271523642691703285189)
        ·
          refine ⟨22698238410683004694365973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121057271523642691703285189 22698238410683004694365973)
          ·
            refine ⟨1063979925500765845048405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22698238410683004694365973 1063979925500765845048405)
            ·
              refine ⟨12468514751962099746661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1063979925500765845048405 12468514751962099746661)
              ·
                rfl

theorem cell22_983435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 8].length) (baseStart_983435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_983435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_983435 prefixEnd_983435 := by exact prefixLift 983435
  have htrace : WordTrace (prefixWord ++ tailWord_983435) baseStart_983435 baseEnd_983435 := by
    simpa [prefixWord, tailWord_983435, baseEnd_983435] using wordTrace_append hprefix tailTrace_983435
  have hstable : (prefixWord ++ tailWord_983435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983435).length < 2 ^ (prefixWord ++ tailWord_983435).sum := by decide
  have hdescent : baseEnd_983435 < baseStart_983435 := by decide
  rcases family_descends (prefixWord ++ tailWord_983435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983456 : List Nat := [2, 1, 1, 4, 1, 5, 2, 1, 2, 3]
def baseStart_983456 : Nat := 118140960795 + 983456 * 2 ^ 59
def prefixEnd_983456 : Nat := 4983230072969 + 3 ^ 40 * 983456 * 2
def baseEnd_983456 : Nat := 336657087032139638384783

theorem tailTrace_983456 : CollatzResearch.WordTrace tailWord_983456 prefixEnd_983456 336657087032139638384783 := by
  unfold tailWord_983456
  simp only [CollatzResearch.WordTrace]
  refine ⟨17934793562557173878929111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23913058083409565171905481 17934793562557173878929111)
  ·
    refine ⟨26902190343835760818393667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17934793562557173878929111 26902190343835760818393667)
    ·
      refine ⟨40353285515753641227590501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26902190343835760818393667 40353285515753641227590501)
      ·
        refine ⟨7566241034203807730173219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40353285515753641227590501 7566241034203807730173219)
        ·
          refine ⟨11349361551305711595259829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7566241034203807730173219 11349361551305711595259829)
          ·
            refine ⟨1064002645434910462055609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11349361551305711595259829 1064002645434910462055609)
            ·
              refine ⟨798001984076182846541707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1064002645434910462055609 798001984076182846541707)
              ·
                refine ⟨1197002976114274269812561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 798001984076182846541707 1197002976114274269812561)
                ·
                  refine ⟨897752232085705702359421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1197002976114274269812561 897752232085705702359421)
                  ·
                    refine ⟨336657087032139638384783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 897752232085705702359421 336657087032139638384783)
                    ·
                      rfl

theorem cell22_983456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 2, 3].length) (baseStart_983456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_983456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_983456 prefixEnd_983456 := by exact prefixLift 983456
  have htrace : WordTrace (prefixWord ++ tailWord_983456) baseStart_983456 baseEnd_983456 := by
    simpa [prefixWord, tailWord_983456, baseEnd_983456] using wordTrace_append hprefix tailTrace_983456
  have hstable : (prefixWord ++ tailWord_983456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983456).length < 2 ^ (prefixWord ++ tailWord_983456).sum := by decide
  have hdescent : baseEnd_983456 < baseStart_983456 := by decide
  rcases family_descends (prefixWord ++ tailWord_983456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983527 : List Nat := [1, 1, 5, 2, 1, 1, 1, 3, 3, 4]
def baseStart_983527 : Nat := 118140960795 + 983527 * 2 ^ 59
def prefixEnd_983527 : Nat := 4983230072969 + 3 ^ 40 * 983527 * 2
def baseEnd_983527 : Nat := 336681391783119119859565

theorem tailTrace_983527 : CollatzResearch.WordTrace tailWord_983527 prefixEnd_983527 336681391783119119859565 := by
  unfold tailWord_983527
  simp only [CollatzResearch.WordTrace]
  refine ⟨35872176707857126883692835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23914784471904751255795223 35872176707857126883692835)
  ·
    refine ⟨53808265061785690325539253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35872176707857126883692835 53808265061785690325539253)
    ·
      refine ⟨5044524849542408468019305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53808265061785690325539253 5044524849542408468019305)
      ·
        refine ⟨3783393637156806351014479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5044524849542408468019305 3783393637156806351014479)
        ·
          refine ⟨5675090455735209526521719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3783393637156806351014479 5675090455735209526521719)
          ·
            refine ⟨8512635683602814289782579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5675090455735209526521719 8512635683602814289782579)
            ·
              refine ⟨12768953525404221434673869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8512635683602814289782579 12768953525404221434673869)
              ·
                refine ⟨4788357572026583038002701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12768953525404221434673869 4788357572026583038002701)
                ·
                  refine ⟨1795634089509968639251013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4788357572026583038002701 1795634089509968639251013)
                  ·
                    refine ⟨336681391783119119859565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1795634089509968639251013 336681391783119119859565)
                    ·
                      rfl

theorem cell22_983527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_983527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_983527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_983527 prefixEnd_983527 := by exact prefixLift 983527
  have htrace : WordTrace (prefixWord ++ tailWord_983527) baseStart_983527 baseEnd_983527 := by
    simpa [prefixWord, tailWord_983527, baseEnd_983527] using wordTrace_append hprefix tailTrace_983527
  have hstable : (prefixWord ++ tailWord_983527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983527).length < 2 ^ (prefixWord ++ tailWord_983527).sum := by decide
  have hdescent : baseEnd_983527 < baseStart_983527 := by decide
  rcases family_descends (prefixWord ++ tailWord_983527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983542 : List Nat := [5, 1, 1, 1, 2, 1, 1, 2, 8]
def baseStart_983542 : Nat := 118140960795 + 983542 * 2 ^ 59
def prefixEnd_983542 : Nat := 4983230072969 + 3 ^ 40 * 983542 * 2
def baseEnd_983542 : Nat := 112228842196554693578173

theorem tailTrace_983542 : CollatzResearch.WordTrace tailWord_983542 prefixEnd_983542 112228842196554693578173 := by
  unfold tailWord_983542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2242045237675174027843055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23915149201868522963659253 2242045237675174027843055)
  ·
    refine ⟨3363067856512761041764583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2242045237675174027843055 3363067856512761041764583)
    ·
      refine ⟨5044601784769141562646875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3363067856512761041764583 5044601784769141562646875)
      ·
        refine ⟨7566902677153712343970313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5044601784769141562646875 7566902677153712343970313)
        ·
          refine ⟨5675177007865284257977735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7566902677153712343970313 5675177007865284257977735)
          ·
            refine ⟨8512765511797926386966603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5675177007865284257977735 8512765511797926386966603)
            ·
              refine ⟨12769148267696889580449905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8512765511797926386966603 12769148267696889580449905)
              ·
                refine ⟨9576861200772667185337429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12769148267696889580449905 9576861200772667185337429)
                ·
                  refine ⟨112228842196554693578173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9576861200772667185337429 112228842196554693578173)
                  ·
                    rfl

theorem cell22_983542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_983542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_983542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_983542 prefixEnd_983542 := by exact prefixLift 983542
  have htrace : WordTrace (prefixWord ++ tailWord_983542) baseStart_983542 baseEnd_983542 := by
    simpa [prefixWord, tailWord_983542, baseEnd_983542] using wordTrace_append hprefix tailTrace_983542
  have hstable : (prefixWord ++ tailWord_983542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983542).length < 2 ^ (prefixWord ++ tailWord_983542).sum := by decide
  have hdescent : baseEnd_983542 < baseStart_983542 := by decide
  rcases family_descends (prefixWord ++ tailWord_983542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983559 : List Nat := [1, 1, 4, 3, 3, 1, 2, 1, 6]
def baseStart_983559 : Nat := 118140960795 + 983559 * 2 ^ 59
def prefixEnd_983559 : Nat := 4983230072969 + 3 ^ 40 * 983559 * 2
def baseEnd_983559 : Nat := 112230782012360567686489

theorem tailTrace_983559 : CollatzResearch.WordTrace tailWord_983559 prefixEnd_983559 112230782012360567686489 := by
  unfold tailWord_983559
  simp only [CollatzResearch.WordTrace]
  refine ⟨35873343843741196348857731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23915562562494130899238487 35873343843741196348857731)
  ·
    refine ⟨53810015765611794523286597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35873343843741196348857731 53810015765611794523286597)
    ·
      refine ⟨10089377956052211473116237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53810015765611794523286597 10089377956052211473116237)
      ·
        refine ⟨3783516733519579302418589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10089377956052211473116237 3783516733519579302418589)
        ·
          refine ⟨1418818775069842238406971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3783516733519579302418589 1418818775069842238406971)
          ·
            refine ⟨2128228162604763357610457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1418818775069842238406971 2128228162604763357610457)
            ·
              refine ⟨1596171121953572518207843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2128228162604763357610457 1596171121953572518207843)
              ·
                refine ⟨2394256682930358777311765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1596171121953572518207843 2394256682930358777311765)
                ·
                  refine ⟨112230782012360567686489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2394256682930358777311765 112230782012360567686489)
                  ·
                    rfl

theorem cell22_983559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 6].length) (baseStart_983559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_983559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_983559 prefixEnd_983559 := by exact prefixLift 983559
  have htrace : WordTrace (prefixWord ++ tailWord_983559) baseStart_983559 baseEnd_983559 := by
    simpa [prefixWord, tailWord_983559, baseEnd_983559] using wordTrace_append hprefix tailTrace_983559
  have hstable : (prefixWord ++ tailWord_983559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983559).length < 2 ^ (prefixWord ++ tailWord_983559).sum := by decide
  have hdescent : baseEnd_983559 < baseStart_983559 := by decide
  rcases family_descends (prefixWord ++ tailWord_983559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983587 : List Nat := [1, 1, 1, 4, 4, 2, 1, 8]
def baseStart_983587 : Nat := 118140960795 + 983587 * 2 ^ 59
def prefixEnd_983587 : Nat := 4983230072969 + 3 ^ 40 * 983587 * 2
def baseEnd_983587 : Nat := 37411325667699884817709

theorem tailTrace_983587 : CollatzResearch.WordTrace tailWord_983587 prefixEnd_983587 37411325667699884817709 := by
  unfold tailWord_983587
  simp only [CollatzResearch.WordTrace]
  refine ⟨35874365087639757130877015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23916243391759838087251343 35874365087639757130877015)
  ·
    refine ⟨53811547631459635696315523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35874365087639757130877015 53811547631459635696315523)
    ·
      refine ⟨80717321447189453544473285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53811547631459635696315523 80717321447189453544473285)
      ·
        refine ⟨15134497771348022539588741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80717321447189453544473285 15134497771348022539588741)
        ·
          refine ⟨2837718332127754226172889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15134497771348022539588741 2837718332127754226172889)
          ·
            refine ⟨2128288749095815669629667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2837718332127754226172889 2128288749095815669629667)
            ·
              refine ⟨3192433123643723504444501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2128288749095815669629667 3192433123643723504444501)
              ·
                refine ⟨37411325667699884817709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3192433123643723504444501 37411325667699884817709)
                ·
                  rfl

theorem cell22_983587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 8].length) (baseStart_983587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_983587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_983587 prefixEnd_983587 := by exact prefixLift 983587
  have htrace : WordTrace (prefixWord ++ tailWord_983587) baseStart_983587 baseEnd_983587 := by
    simpa [prefixWord, tailWord_983587, baseEnd_983587] using wordTrace_append hprefix tailTrace_983587
  have hstable : (prefixWord ++ tailWord_983587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983587).length < 2 ^ (prefixWord ++ tailWord_983587).sum := by decide
  have hdescent : baseEnd_983587 < baseStart_983587 := by decide
  rcases family_descends (prefixWord ++ tailWord_983587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983606 : List Nat := [5, 1, 2, 1, 2, 2, 1, 2, 2, 4]
def baseStart_983606 : Nat := 118140960795 + 983606 * 2 ^ 59
def prefixEnd_983606 : Nat := 4983230072969 + 3 ^ 40 * 983606 * 2
def baseEnd_983606 : Nat := 336708435097589247134323

theorem tailTrace_983606 : CollatzResearch.WordTrace tailWord_983606 prefixEnd_983606 336708435097589247134323 := by
  unfold tailWord_983606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2242191129660682710988667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23916705383047282250545781 2242191129660682710988667)
  ·
    refine ⟨3363286694491024066483001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2242191129660682710988667 3363286694491024066483001)
    ·
      refine ⟨2522465020868268049862251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3363286694491024066483001 2522465020868268049862251)
      ·
        refine ⟨3783697531302402074793377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2522465020868268049862251 3783697531302402074793377)
        ·
          refine ⟨2837773148476801556095033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3783697531302402074793377 2837773148476801556095033)
          ·
            refine ⟨2128329861357601167071275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2837773148476801556095033 2128329861357601167071275)
            ·
              refine ⟨3192494792036401750606913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2128329861357601167071275 3192494792036401750606913)
              ·
                refine ⟨2394371094027301312955185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3192494792036401750606913 2394371094027301312955185)
                ·
                  refine ⟨1795778320520475984716389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2394371094027301312955185 1795778320520475984716389)
                  ·
                    refine ⟨336708435097589247134323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1795778320520475984716389 336708435097589247134323)
                    ·
                      rfl

theorem cell22_983606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_983606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_983606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_983606 prefixEnd_983606 := by exact prefixLift 983606
  have htrace : WordTrace (prefixWord ++ tailWord_983606) baseStart_983606 baseEnd_983606 := by
    simpa [prefixWord, tailWord_983606, baseEnd_983606] using wordTrace_append hprefix tailTrace_983606
  have hstable : (prefixWord ++ tailWord_983606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983606).length < 2 ^ (prefixWord ++ tailWord_983606).sum := by decide
  have hdescent : baseEnd_983606 < baseStart_983606 := by decide
  rcases family_descends (prefixWord ++ tailWord_983606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983666 : List Nat := [3, 2, 1, 2, 4, 1, 2, 2, 5]
def baseStart_983666 : Nat := 118140960795 + 983666 * 2 ^ 59
def prefixEnd_983666 : Nat := 4983230072969 + 3 ^ 40 * 983666 * 2
def baseEnd_983666 : Nat := 112242991441256363544713

theorem tailTrace_983666 : CollatzResearch.WordTrace tailWord_983666 prefixEnd_983666 112242991441256363544713 := by
  unfold tailWord_983666
  simp only [CollatzResearch.WordTrace]
  refine ⟨8969311613588388405750713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23918164302902369082001901 8969311613588388405750713)
  ·
    refine ⟨6726983710191291304313035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8969311613588388405750713 6726983710191291304313035)
    ·
      refine ⟨10090475565286936956469553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6726983710191291304313035 10090475565286936956469553)
      ·
        refine ⟨7567856673965202717352165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10090475565286936956469553 7567856673965202717352165)
        ·
          refine ⟨1418973126368475509503531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7567856673965202717352165 1418973126368475509503531)
          ·
            refine ⟨2128459689552713264255297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1418973126368475509503531 2128459689552713264255297)
            ·
              refine ⟨1596344767164534948191473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2128459689552713264255297 1596344767164534948191473)
              ·
                refine ⟨1197258575373401211143605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1596344767164534948191473 1197258575373401211143605)
                ·
                  refine ⟨112242991441256363544713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1197258575373401211143605 112242991441256363544713)
                  ·
                    rfl

theorem cell22_983666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_983666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_983666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_983666 prefixEnd_983666 := by exact prefixLift 983666
  have htrace : WordTrace (prefixWord ++ tailWord_983666) baseStart_983666 baseEnd_983666 := by
    simpa [prefixWord, tailWord_983666, baseEnd_983666] using wordTrace_append hprefix tailTrace_983666
  have hstable : (prefixWord ++ tailWord_983666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983666).length < 2 ^ (prefixWord ++ tailWord_983666).sum := by decide
  have hdescent : baseEnd_983666 < baseStart_983666 := by decide
  rcases family_descends (prefixWord ++ tailWord_983666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983670 : List Nat := [5, 1, 1, 2, 3, 1, 1, 4, 1, 3]
def baseStart_983670 : Nat := 118140960795 + 983670 * 2 ^ 59
def prefixEnd_983670 : Nat := 4983230072969 + 3 ^ 40 * 983670 * 2
def baseEnd_983670 : Nat := 336730343605514413534127

theorem tailTrace_983670 : CollatzResearch.WordTrace tailWord_983670 prefixEnd_983670 336730343605514413534127 := by
  unfold tailWord_983670
  simp only [CollatzResearch.WordTrace]
  refine ⟨2242337021646191394134279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23918261564226041537432309 2242337021646191394134279)
  ·
    refine ⟨3363505532469287091201419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2242337021646191394134279 3363505532469287091201419)
    ·
      refine ⟨5045258298703930636802129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3363505532469287091201419 5045258298703930636802129)
      ·
        refine ⟨3783943724027947977601597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5045258298703930636802129 3783943724027947977601597)
        ·
          refine ⟨1418978896510480491600599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3783943724027947977601597 1418978896510480491600599)
          ·
            refine ⟨2128468344765720737400899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1418978896510480491600599 2128468344765720737400899)
            ·
              refine ⟨3192702517148581106101349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2128468344765720737400899 3192702517148581106101349)
              ·
                refine ⟨598631721965358957394003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3192702517148581106101349 598631721965358957394003)
                ·
                  refine ⟨897947582948038436091005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 598631721965358957394003 897947582948038436091005)
                  ·
                    refine ⟨336730343605514413534127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 897947582948038436091005 336730343605514413534127)
                    ·
                      rfl

theorem cell22_983670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_983670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_983670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_983670 prefixEnd_983670 := by exact prefixLift 983670
  have htrace : WordTrace (prefixWord ++ tailWord_983670) baseStart_983670 baseEnd_983670 := by
    simpa [prefixWord, tailWord_983670, baseEnd_983670] using wordTrace_append hprefix tailTrace_983670
  have hstable : (prefixWord ++ tailWord_983670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983670).length < 2 ^ (prefixWord ++ tailWord_983670).sum := by decide
  have hdescent : baseEnd_983670 < baseStart_983670 := by decide
  rcases family_descends (prefixWord ++ tailWord_983670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983694 : List Nat := [4, 1, 1, 3, 1, 1, 3, 2, 6]
def baseStart_983694 : Nat := 118140960795 + 983694 * 2 ^ 59
def prefixEnd_983694 : Nat := 4983230072969 + 3 ^ 40 * 983694 * 2
def baseEnd_983694 : Nat := 112246186431995450311351

theorem tailTrace_983694 : CollatzResearch.WordTrace tailWord_983694 prefixEnd_983694 112246186431995450311351 := by
  unfold tailWord_983694
  simp only [CollatzResearch.WordTrace]
  refine ⟨4484783462281514300627767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23918845132168076270014757 4484783462281514300627767)
  ·
    refine ⟨6727175193422271450941651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4484783462281514300627767 6727175193422271450941651)
    ·
      refine ⟨10090762790133407176412477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6727175193422271450941651 10090762790133407176412477)
      ·
        refine ⟨3784036046300027691154679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10090762790133407176412477 3784036046300027691154679)
        ·
          refine ⟨5676054069450041536732019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3784036046300027691154679 5676054069450041536732019)
          ·
            refine ⟨8514081104175062305098029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5676054069450041536732019 8514081104175062305098029)
            ·
              refine ⟨3192780414065648364411761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8514081104175062305098029 3192780414065648364411761)
              ·
                refine ⟨2394585310549236273308821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3192780414065648364411761 2394585310549236273308821)
                ·
                  refine ⟨112246186431995450311351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2394585310549236273308821 112246186431995450311351)
                  ·
                    rfl

theorem cell22_983694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_983694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_983694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_983694 prefixEnd_983694 := by exact prefixLift 983694
  have htrace : WordTrace (prefixWord ++ tailWord_983694) baseStart_983694 baseEnd_983694 := by
    simpa [prefixWord, tailWord_983694, baseEnd_983694] using wordTrace_append hprefix tailTrace_983694
  have hstable : (prefixWord ++ tailWord_983694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983694).length < 2 ^ (prefixWord ++ tailWord_983694).sum := by decide
  have hdescent : baseEnd_983694 < baseStart_983694 := by decide
  rcases family_descends (prefixWord ++ tailWord_983694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983709 : List Nat := [1, 4, 2, 1, 1, 1, 4, 2, 1, 5]
def baseStart_983709 : Nat := 118140960795 + 983709 * 2 ^ 59
def prefixEnd_983709 : Nat := 4983230072969 + 3 ^ 40 * 983709 * 2
def baseEnd_983709 : Nat := 336743694102531311809007

theorem tailTrace_983709 : CollatzResearch.WordTrace tailWord_983709 prefixEnd_983709 336743694102531311809007 := by
  unfold tailWord_983709
  simp only [CollatzResearch.WordTrace]
  refine ⟨35878814793197771966818181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23919209862131847977878787 35878814793197771966818181)
  ·
    refine ⟨6727277773724582243778409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35878814793197771966818181 6727277773724582243778409)
    ·
      refine ⟨5045458330293436682833807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6727277773724582243778409 5045458330293436682833807)
      ·
        refine ⟨7568187495440155024250711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5045458330293436682833807 7568187495440155024250711)
        ·
          refine ⟨11352281243160232536376067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7568187495440155024250711 11352281243160232536376067)
          ·
            refine ⟨17028421864740348804564101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11352281243160232536376067 17028421864740348804564101)
            ·
              refine ⟨3192829099638815400855769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17028421864740348804564101 3192829099638815400855769)
              ·
                refine ⟨2394621824729111550641827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3192829099638815400855769 2394621824729111550641827)
                ·
                  refine ⟨3591932737093667325962741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2394621824729111550641827 3591932737093667325962741)
                  ·
                    refine ⟨336743694102531311809007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3591932737093667325962741 336743694102531311809007)
                    ·
                      rfl

theorem cell22_983709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_983709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_983709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_983709 prefixEnd_983709 := by exact prefixLift 983709
  have htrace : WordTrace (prefixWord ++ tailWord_983709) baseStart_983709 baseEnd_983709 := by
    simpa [prefixWord, tailWord_983709, baseEnd_983709] using wordTrace_append hprefix tailTrace_983709
  have hstable : (prefixWord ++ tailWord_983709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983709).length < 2 ^ (prefixWord ++ tailWord_983709).sum := by decide
  have hdescent : baseEnd_983709 < baseStart_983709 := by decide
  rcases family_descends (prefixWord ++ tailWord_983709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983743 : List Nat := [1, 1, 2, 2, 2, 5, 3, 1, 2, 3]
def baseStart_983743 : Nat := 118140960795 + 983743 * 2 ^ 59
def prefixEnd_983743 : Nat := 4983230072969 + 3 ^ 40 * 983743 * 2
def baseEnd_983743 : Nat := 336755332997366556458903

theorem tailTrace_983743 : CollatzResearch.WordTrace tailWord_983743 prefixEnd_983743 336755332997366556458903 := by
  unfold tailWord_983743
  simp only [CollatzResearch.WordTrace]
  refine ⟨35880054875074595773555883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23920036583383063849037255 35880054875074595773555883)
  ·
    refine ⟨53820082312611893660333825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35880054875074595773555883 53820082312611893660333825)
    ·
      refine ⟨40365061734458920245250369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53820082312611893660333825 40365061734458920245250369)
      ·
        refine ⟨30273796300844190183937777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40365061734458920245250369 30273796300844190183937777)
        ·
          refine ⟨22705347225633142637953333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30273796300844190183937777 22705347225633142637953333)
          ·
            refine ⟨2128626302403107122308125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22705347225633142637953333 2128626302403107122308125)
            ·
              refine ⟨798234863401165170865547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2128626302403107122308125 798234863401165170865547)
              ·
                refine ⟨1197352295101747756298321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 798234863401165170865547 1197352295101747756298321)
                ·
                  refine ⟨898014221326310817223741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1197352295101747756298321 898014221326310817223741)
                  ·
                    refine ⟨336755332997366556458903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 898014221326310817223741 336755332997366556458903)
                    ·
                      rfl

theorem cell22_983743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 2, 3].length) (baseStart_983743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_983743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_983743 prefixEnd_983743 := by exact prefixLift 983743
  have htrace : WordTrace (prefixWord ++ tailWord_983743) baseStart_983743 baseEnd_983743 := by
    simpa [prefixWord, tailWord_983743, baseEnd_983743] using wordTrace_append hprefix tailTrace_983743
  have hstable : (prefixWord ++ tailWord_983743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983743).length < 2 ^ (prefixWord ++ tailWord_983743).sum := by decide
  have hdescent : baseEnd_983743 < baseStart_983743 := by decide
  rcases family_descends (prefixWord ++ tailWord_983743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983756 : List Nat := [2, 2, 1, 5, 1, 1, 4, 6]
def baseStart_983756 : Nat := 118140960795 + 983756 * 2 ^ 59
def prefixEnd_983756 : Nat := 4983230072969 + 3 ^ 40 * 983756 * 2
def baseEnd_983756 : Nat := 37417753684782095098207

theorem tailTrace_983756 : CollatzResearch.WordTrace tailWord_983756 prefixEnd_983756 37417753684782095098207 := by
  unfold tailWord_983756
  simp only [CollatzResearch.WordTrace]
  refine ⟨17940264512013749496889561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23920352682684999329186081 17940264512013749496889561)
  ·
    refine ⟨13455198384010312122667171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17940264512013749496889561 13455198384010312122667171)
    ·
      refine ⟨20182797576015468184000757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13455198384010312122667171 20182797576015468184000757)
      ·
        refine ⟨1892137272751450142250071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20182797576015468184000757 1892137272751450142250071)
        ·
          refine ⟨2838205909127175213375107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1892137272751450142250071 2838205909127175213375107)
          ·
            refine ⟨4257308863690762820062661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2838205909127175213375107 4257308863690762820062661)
            ·
              refine ⟨798245411942018028761749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4257308863690762820062661 798245411942018028761749)
              ·
                refine ⟨37417753684782095098207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 798245411942018028761749 37417753684782095098207)
                ·
                  rfl

theorem cell22_983756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 6].length) (baseStart_983756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_983756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_983756 prefixEnd_983756 := by exact prefixLift 983756
  have htrace : WordTrace (prefixWord ++ tailWord_983756) baseStart_983756 baseEnd_983756 := by
    simpa [prefixWord, tailWord_983756, baseEnd_983756] using wordTrace_append hprefix tailTrace_983756
  have hstable : (prefixWord ++ tailWord_983756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983756).length < 2 ^ (prefixWord ++ tailWord_983756).sum := by decide
  have hdescent : baseEnd_983756 < baseStart_983756 := by decide
  rcases family_descends (prefixWord ++ tailWord_983756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983861 : List Nat := [1, 3, 3, 1, 3, 1, 1, 3, 1, 5]
def baseStart_983861 : Nat := 118140960795 + 983861 * 2 ^ 59
def prefixEnd_983861 : Nat := 4983230072969 + 3 ^ 40 * 983861 * 2
def baseEnd_983861 : Nat := 336795726808853582008541

theorem tailTrace_983861 : CollatzResearch.WordTrace tailWord_983861 prefixEnd_983861 336795726808853582008541 := by
  unfold tailWord_983861
  simp only [CollatzResearch.WordTrace]
  refine ⟨35884358688647101926351437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23922905792431401284234291 35884358688647101926351437)
  ·
    refine ⟨13456634508242663222381789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35884358688647101926351437 13456634508242663222381789)
    ·
      refine ⟨5046237940590998708393171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13456634508242663222381789 5046237940590998708393171)
      ·
        refine ⟨7569356910886498062589757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5046237940590998708393171 7569356910886498062589757)
        ·
          refine ⟨2838508841582436773471159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7569356910886498062589757 2838508841582436773471159)
          ·
            refine ⟨4257763262373655160206739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2838508841582436773471159 4257763262373655160206739)
            ·
              refine ⟨6386644893560482740310109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4257763262373655160206739 6386644893560482740310109)
              ·
                refine ⟨2394991835085181027616291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6386644893560482740310109 2394991835085181027616291)
                ·
                  refine ⟨3592487752627771541424437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2394991835085181027616291 3592487752627771541424437)
                  ·
                    refine ⟨336795726808853582008541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3592487752627771541424437 336795726808853582008541)
                    ·
                      rfl

theorem cell22_983861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_983861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_983861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_983861 prefixEnd_983861 := by exact prefixLift 983861
  have htrace : WordTrace (prefixWord ++ tailWord_983861) baseStart_983861 baseEnd_983861 := by
    simpa [prefixWord, tailWord_983861, baseEnd_983861] using wordTrace_append hprefix tailTrace_983861
  have hstable : (prefixWord ++ tailWord_983861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983861).length < 2 ^ (prefixWord ++ tailWord_983861).sum := by decide
  have hdescent : baseEnd_983861 < baseStart_983861 := by decide
  rcases family_descends (prefixWord ++ tailWord_983861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983895 : List Nat := [1, 1, 3, 2, 4, 3, 1, 2, 2, 3]
def baseStart_983895 : Nat := 118140960795 + 983895 * 2 ^ 59
def prefixEnd_983895 : Nat := 4983230072969 + 3 ^ 40 * 983895 * 2
def baseEnd_983895 : Nat := 336807365703688826658437

theorem tailTrace_983895 : CollatzResearch.WordTrace tailWord_983895 prefixEnd_983895 336807365703688826658437 := by
  unfold tailWord_983895
  simp only [CollatzResearch.WordTrace]
  refine ⟨35885598770523925733089139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23923732513682617155392759 35885598770523925733089139)
  ·
    refine ⟨53828398155785888599633709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35885598770523925733089139 53828398155785888599633709)
    ·
      refine ⟨20185649308419708224862641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53828398155785888599633709 20185649308419708224862641)
      ·
        refine ⟨15139236981314781168646981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20185649308419708224862641 15139236981314781168646981)
        ·
          refine ⟨2838606933996521469121309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15139236981314781168646981 2838606933996521469121309)
          ·
            refine ⟨1064477600248695550920491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2838606933996521469121309 1064477600248695550920491)
            ·
              refine ⟨1596716400373043326380737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1064477600248695550920491 1596716400373043326380737)
              ·
                refine ⟨1197537300279782494785553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1596716400373043326380737 1197537300279782494785553)
                ·
                  refine ⟨898152975209836871089165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1197537300279782494785553 898152975209836871089165)
                  ·
                    refine ⟨336807365703688826658437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 898152975209836871089165 336807365703688826658437)
                    ·
                      rfl

theorem cell22_983895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 2, 3].length) (baseStart_983895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_983895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_983895 prefixEnd_983895 := by exact prefixLift 983895
  have htrace : WordTrace (prefixWord ++ tailWord_983895) baseStart_983895 baseEnd_983895 := by
    simpa [prefixWord, tailWord_983895, baseEnd_983895] using wordTrace_append hprefix tailTrace_983895
  have hstable : (prefixWord ++ tailWord_983895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983895).length < 2 ^ (prefixWord ++ tailWord_983895).sum := by decide
  have hdescent : baseEnd_983895 < baseStart_983895 := by decide
  rcases family_descends (prefixWord ++ tailWord_983895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983957 : List Nat := [1, 3, 2, 1, 1, 5, 3, 2, 1, 3]
def baseStart_983957 : Nat := 118140960795 + 983957 * 2 ^ 59
def prefixEnd_983957 : Nat := 4983230072969 + 3 ^ 40 * 983957 * 2
def baseEnd_983957 : Nat := 336828589570741331608247

theorem tailTrace_983957 : CollatzResearch.WordTrace tailWord_983957 prefixEnd_983957 336828589570741331608247 := by
  unfold tailWord_983957
  simp only [CollatzResearch.WordTrace]
  refine ⟨35887860096299310321846125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23925240064199540214564083 35887860096299310321846125)
  ·
    refine ⟨13457947536112241370692297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35887860096299310321846125 13457947536112241370692297)
    ·
      refine ⟨10093460652084181028019223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13457947536112241370692297 10093460652084181028019223)
      ·
        refine ⟨15140190978126271542028835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10093460652084181028019223 15140190978126271542028835)
        ·
          refine ⟨22710286467189407313043253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15140190978126271542028835 22710286467189407313043253)
          ·
            refine ⟨2129089356299006935597805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22710286467189407313043253 2129089356299006935597805)
            ·
              refine ⟨798408508612127600849177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2129089356299006935597805 798408508612127600849177)
              ·
                refine ⟨598806381459095700636883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 798408508612127600849177 598806381459095700636883)
                ·
                  refine ⟨898209572188643550955325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 598806381459095700636883 898209572188643550955325)
                  ·
                    refine ⟨336828589570741331608247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 898209572188643550955325 336828589570741331608247)
                    ·
                      rfl

theorem cell22_983957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 2, 1, 3].length) (baseStart_983957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_983957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_983957 prefixEnd_983957 := by exact prefixLift 983957
  have htrace : WordTrace (prefixWord ++ tailWord_983957) baseStart_983957 baseEnd_983957 := by
    simpa [prefixWord, tailWord_983957, baseEnd_983957] using wordTrace_append hprefix tailTrace_983957
  have hstable : (prefixWord ++ tailWord_983957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983957).length < 2 ^ (prefixWord ++ tailWord_983957).sum := by decide
  have hdescent : baseEnd_983957 < baseStart_983957 := by decide
  rcases family_descends (prefixWord ++ tailWord_983957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_983970 : List Nat := [3, 3, 1, 2, 2, 1, 4, 1, 5]
def baseStart_983970 : Nat := 118140960795 + 983970 * 2 ^ 59
def prefixEnd_983970 : Nat := 4983230072969 + 3 ^ 40 * 983970 * 2
def baseEnd_983970 : Nat := 112277679912137877011069

theorem tailTrace_983970 : CollatzResearch.WordTrace tailWord_983970 prefixEnd_983970 112277679912137877011069 := by
  unfold tailWord_983970
  simp only [CollatzResearch.WordTrace]
  refine ⟨8972083561313053385517341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23925556163501475694712909 8972083561313053385517341)
  ·
    refine ⟨3364531335492395019569003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8972083561313053385517341 3364531335492395019569003)
    ·
      refine ⟨5046797003238592529353505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3364531335492395019569003 5046797003238592529353505)
      ·
        refine ⟨3785097752428944397015129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5046797003238592529353505 3785097752428944397015129)
        ·
          refine ⟨2838823314321708297761347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3785097752428944397015129 2838823314321708297761347)
          ·
            refine ⟨4258234971482562446642021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2838823314321708297761347 4258234971482562446642021)
            ·
              refine ⟨798419057152980458745379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4258234971482562446642021 798419057152980458745379)
              ·
                refine ⟨1197628585729470688118069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 798419057152980458745379 1197628585729470688118069)
                ·
                  refine ⟨112277679912137877011069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1197628585729470688118069 112277679912137877011069)
                  ·
                    rfl

theorem cell22_983970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_983970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_983970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_983970 prefixEnd_983970 := by exact prefixLift 983970
  have htrace : WordTrace (prefixWord ++ tailWord_983970) baseStart_983970 baseEnd_983970 := by
    simpa [prefixWord, tailWord_983970, baseEnd_983970] using wordTrace_append hprefix tailTrace_983970
  have hstable : (prefixWord ++ tailWord_983970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_983970).length < 2 ^ (prefixWord ++ tailWord_983970).sum := by decide
  have hdescent : baseEnd_983970 < baseStart_983970 := by decide
  rcases family_descends (prefixWord ++ tailWord_983970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984000 : List Nat := [2, 1, 1, 2, 3, 4, 3, 1, 1, 4]
def baseStart_984000 : Nat := 118140960795 + 984000 * 2 ^ 59
def prefixEnd_984000 : Nat := 4983230072969 + 3 ^ 40 * 984000 * 2
def baseEnd_984000 : Nat := 336843309349503552783115

theorem tailTrace_984000 : CollatzResearch.WordTrace tailWord_984000 prefixEnd_984000 336843309349503552783115 := by
  unfold tailWord_984000
  simp only [CollatzResearch.WordTrace]
  refine ⟨17944714217571764332830727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23926285623429019110440969 17944714217571764332830727)
  ·
    refine ⟨26917071326357646499246091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17944714217571764332830727 26917071326357646499246091)
    ·
      refine ⟨40375606989536469748869137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26917071326357646499246091 40375606989536469748869137)
      ·
        refine ⟨30281705242152352311651853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40375606989536469748869137 30281705242152352311651853)
        ·
          refine ⟨11355639465807132116869445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30281705242152352311651853 11355639465807132116869445)
          ·
            refine ⟨2129182399838837271913021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11355639465807132116869445 2129182399838837271913021)
            ·
              refine ⟨798443399939563976967383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2129182399838837271913021 798443399939563976967383)
              ·
                refine ⟨1197665099909345965451075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 798443399939563976967383 1197665099909345965451075)
                ·
                  refine ⟨1796497649864018948176613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1197665099909345965451075 1796497649864018948176613)
                  ·
                    refine ⟨336843309349503552783115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1796497649864018948176613 336843309349503552783115)
                    ·
                      rfl

theorem cell22_984000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 1, 4].length) (baseStart_984000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_984000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_984000 prefixEnd_984000 := by exact prefixLift 984000
  have htrace : WordTrace (prefixWord ++ tailWord_984000) baseStart_984000 baseEnd_984000 := by
    simpa [prefixWord, tailWord_984000, baseEnd_984000] using wordTrace_append hprefix tailTrace_984000
  have hstable : (prefixWord ++ tailWord_984000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984000).length < 2 ^ (prefixWord ++ tailWord_984000).sum := by decide
  have hdescent : baseEnd_984000 < baseStart_984000 := by decide
  rcases family_descends (prefixWord ++ tailWord_984000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984015 : List Nat := [1, 1, 2, 1, 1, 6, 4, 2, 4]
def baseStart_984015 : Nat := 118140960795 + 984015 * 2 ^ 59
def prefixEnd_984015 : Nat := 4983230072969 + 3 ^ 40 * 984015 * 2
def baseEnd_984015 : Nat := 112282814718682837886023

theorem tailTrace_984015 : CollatzResearch.WordTrace tailWord_984015 prefixEnd_984015 112282814718682837886023 := by
  unfold tailWord_984015
  simp only [CollatzResearch.WordTrace]
  refine ⟨35889975530089186227457499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23926650353392790818304999 35889975530089186227457499)
  ·
    refine ⟨53834963295133779341186249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35889975530089186227457499 53834963295133779341186249)
    ·
      refine ⟨40376222471350334505889687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53834963295133779341186249 40376222471350334505889687)
      ·
        refine ⟨60564333707025501758834531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40376222471350334505889687 60564333707025501758834531)
        ·
          refine ⟨90846500560538252638251797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60564333707025501758834531 90846500560538252638251797)
          ·
            refine ⟨4258429713775230592418053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 90846500560538252638251797 4258429713775230592418053)
            ·
              refine ⟨798455571332855736078385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4258429713775230592418053 798455571332855736078385)
              ·
                refine ⟨598841678499641802058789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 798455571332855736078385 598841678499641802058789)
                ·
                  refine ⟨112282814718682837886023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 598841678499641802058789 112282814718682837886023)
                  ·
                    rfl

theorem cell22_984015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 2, 4].length) (baseStart_984015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_984015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_984015 prefixEnd_984015 := by exact prefixLift 984015
  have htrace : WordTrace (prefixWord ++ tailWord_984015) baseStart_984015 baseEnd_984015 := by
    simpa [prefixWord, tailWord_984015, baseEnd_984015] using wordTrace_append hprefix tailTrace_984015
  have hstable : (prefixWord ++ tailWord_984015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984015).length < 2 ^ (prefixWord ++ tailWord_984015).sum := by decide
  have hdescent : baseEnd_984015 < baseStart_984015 := by decide
  rcases family_descends (prefixWord ++ tailWord_984015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984075 : List Nat := [1, 1, 1, 1, 6, 3, 2, 1, 3, 3]
def baseStart_984075 : Nat := 118140960795 + 984075 * 2 ^ 59
def prefixEnd_984075 : Nat := 4983230072969 + 3 ^ 40 * 984075 * 2
def baseEnd_984075 : Nat := 336868983382228357157885

theorem tailTrace_984075 : CollatzResearch.WordTrace tailWord_984075 prefixEnd_984075 336868983382228357157885 := by
  unfold tailWord_984075
  simp only [CollatzResearch.WordTrace]
  refine ⟨35892163909871816474641679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23928109273247877649761119 35892163909871816474641679)
  ·
    refine ⟨53838245864807724711962519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35892163909871816474641679 53838245864807724711962519)
    ·
      refine ⟨80757368797211587067943779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53838245864807724711962519 80757368797211587067943779)
      ·
        refine ⟨121136053195817380601915669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80757368797211587067943779 121136053195817380601915669)
        ·
          refine ⟨5678252493553939715714797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 121136053195817380601915669 5678252493553939715714797)
          ·
            refine ⟨2129344685082727393393049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5678252493553939715714797 2129344685082727393393049)
            ·
              refine ⟨1597008513812045545044787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2129344685082727393393049 1597008513812045545044787)
              ·
                refine ⟨2395512770718068317567181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1597008513812045545044787 2395512770718068317567181)
                ·
                  refine ⟨898317289019275619087693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2395512770718068317567181 898317289019275619087693)
                  ·
                    refine ⟨336868983382228357157885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 898317289019275619087693 336868983382228357157885)
                    ·
                      rfl

theorem cell22_984075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 3, 3].length) (baseStart_984075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_984075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_984075 prefixEnd_984075 := by exact prefixLift 984075
  have htrace : WordTrace (prefixWord ++ tailWord_984075) baseStart_984075 baseEnd_984075 := by
    simpa [prefixWord, tailWord_984075, baseEnd_984075] using wordTrace_append hprefix tailTrace_984075
  have hstable : (prefixWord ++ tailWord_984075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984075).length < 2 ^ (prefixWord ++ tailWord_984075).sum := by decide
  have hdescent : baseEnd_984075 < baseStart_984075 := by decide
  rcases family_descends (prefixWord ++ tailWord_984075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984126 : List Nat := [4, 2, 1, 3, 1, 2, 3, 2, 1, 3]
def baseStart_984126 : Nat := 118140960795 + 984126 * 2 ^ 59
def prefixEnd_984126 : Nat := 4983230072969 + 3 ^ 40 * 984126 * 2
def baseEnd_984126 : Nat := 336886441724481224132729

theorem tailTrace_984126 : CollatzResearch.WordTrace tailWord_984126 prefixEnd_984126 336886441724481224132729 := by
  unfold tailWord_984126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4486753004085881523093529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23929349355124701456498821 4486753004085881523093529)
  ·
    refine ⟨3365064753064411142320147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4486753004085881523093529 3365064753064411142320147)
    ·
      refine ⟨5047597129596616713480221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3365064753064411142320147 5047597129596616713480221)
      ·
        refine ⟨1892848923598731267555083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5047597129596616713480221 1892848923598731267555083)
        ·
          refine ⟨2839273385398096901332625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1892848923598731267555083 2839273385398096901332625)
          ·
            refine ⟨2129455039048572675999469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2839273385398096901332625 2129455039048572675999469)
            ·
              refine ⟨798545639643214753499801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2129455039048572675999469 798545639643214753499801)
              ·
                refine ⟨598909229732411065124851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 798545639643214753499801 598909229732411065124851)
                ·
                  refine ⟨898363844598616597687277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 598909229732411065124851 898363844598616597687277)
                  ·
                    refine ⟨336886441724481224132729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 898363844598616597687277 336886441724481224132729)
                    ·
                      rfl

theorem cell22_984126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_984126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_984126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_984126 prefixEnd_984126 := by exact prefixLift 984126
  have htrace : WordTrace (prefixWord ++ tailWord_984126) baseStart_984126 baseEnd_984126 := by
    simpa [prefixWord, tailWord_984126, baseEnd_984126] using wordTrace_append hprefix tailTrace_984126
  have hstable : (prefixWord ++ tailWord_984126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984126).length < 2 ^ (prefixWord ++ tailWord_984126).sum := by decide
  have hdescent : baseEnd_984126 < baseStart_984126 := by decide
  rcases family_descends (prefixWord ++ tailWord_984126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984133 : List Nat := [1, 3, 1, 1, 1, 3, 5, 1, 6]
def baseStart_984133 : Nat := 118140960795 + 984133 * 2 ^ 59
def prefixEnd_984133 : Nat := 4983230072969 + 3 ^ 40 * 984133 * 2
def baseEnd_984133 : Nat := 112296279322511846402569

theorem tailTrace_984133 : CollatzResearch.WordTrace tailWord_984133 prefixEnd_984133 112296279322511846402569 := by
  unfold tailWord_984133
  simp only [CollatzResearch.WordTrace]
  refine ⟨35894279343661692380253053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23929519562441128253502035 35894279343661692380253053)
  ·
    refine ⟨13460354753873134642594895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35894279343661692380253053 13460354753873134642594895)
    ·
      refine ⟨20190532130809701963892343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13460354753873134642594895 20190532130809701963892343)
      ·
        refine ⟨30285798196214552945838515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20190532130809701963892343 30285798196214552945838515)
        ·
          refine ⟨45428697294321829418757773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30285798196214552945838515 45428697294321829418757773)
          ·
            refine ⟨17035761485370686032034165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45428697294321829418757773 17035761485370686032034165)
            ·
              refine ⟨1597102639253501815503203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17035761485370686032034165 1597102639253501815503203)
              ·
                refine ⟨2395653958880252723254805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1597102639253501815503203 2395653958880252723254805)
                ·
                  refine ⟨112296279322511846402569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2395653958880252723254805 112296279322511846402569)
                  ·
                    rfl

theorem cell22_984133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 6].length) (baseStart_984133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_984133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_984133 prefixEnd_984133 := by exact prefixLift 984133
  have htrace : WordTrace (prefixWord ++ tailWord_984133) baseStart_984133 baseEnd_984133 := by
    simpa [prefixWord, tailWord_984133, baseEnd_984133] using wordTrace_append hprefix tailTrace_984133
  have hstable : (prefixWord ++ tailWord_984133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984133).length < 2 ^ (prefixWord ++ tailWord_984133).sum := by decide
  have hdescent : baseEnd_984133 < baseStart_984133 := by decide
  rcases family_descends (prefixWord ++ tailWord_984133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984302 : List Nat := [4, 1, 2, 1, 1, 1, 2, 6, 4]
def baseStart_984302 : Nat := 118140960795 + 984302 * 2 ^ 59
def prefixEnd_984302 : Nat := 4983230072969 + 3 ^ 40 * 984302 * 2
def baseEnd_984302 : Nat := 112315563373758477244063

theorem tailTrace_984302 : CollatzResearch.WordTrace tailWord_984302 prefixEnd_984302 112315563373758477244063 := by
  unfold tailWord_984302
  simp only [CollatzResearch.WordTrace]
  refine ⟨4487555410006179280394395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23933628853366289495436773 4487555410006179280394395)
  ·
    refine ⟨6731333115009268920591593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4487555410006179280394395 6731333115009268920591593)
    ·
      refine ⟨5048499836256951690443695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6731333115009268920591593 5048499836256951690443695)
      ·
        refine ⟨7572749754385427535665543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5048499836256951690443695 7572749754385427535665543)
        ·
          refine ⟨11359124631578141303498315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7572749754385427535665543 11359124631578141303498315)
          ·
            refine ⟨17038686947367211955247473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11359124631578141303498315 17038686947367211955247473)
            ·
              refine ⟨12779015210525408966435605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17038686947367211955247473 12779015210525408966435605)
              ·
                refine ⟨599016337993378545301669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12779015210525408966435605 599016337993378545301669)
                ·
                  refine ⟨112315563373758477244063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 599016337993378545301669 112315563373758477244063)
                  ·
                    rfl

theorem cell22_984302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_984302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_984302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_984302 prefixEnd_984302 := by exact prefixLift 984302
  have htrace : WordTrace (prefixWord ++ tailWord_984302) baseStart_984302 baseEnd_984302 := by
    simpa [prefixWord, tailWord_984302, baseEnd_984302] using wordTrace_append hprefix tailTrace_984302
  have hstable : (prefixWord ++ tailWord_984302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984302).length < 2 ^ (prefixWord ++ tailWord_984302).sum := by decide
  have hdescent : baseEnd_984302 < baseStart_984302 := by decide
  rcases family_descends (prefixWord ++ tailWord_984302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984332 : List Nat := [2, 2, 1, 2, 2, 4, 2, 1, 2, 4]
def baseStart_984332 : Nat := 118140960795 + 984332 * 2 ^ 59
def prefixEnd_984332 : Nat := 4983230072969 + 3 ^ 40 * 984332 * 2
def baseEnd_984332 : Nat := 336956959734365353482097

theorem tailTrace_984332 : CollatzResearch.WordTrace tailWord_984332 prefixEnd_984332 336956959734365353482097 := by
  unfold tailWord_984332
  simp only [CollatzResearch.WordTrace]
  refine ⟨17950768734970374683373625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23934358313293832911164833 17950768734970374683373625)
  ·
    refine ⟨13463076551227781012530219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17950768734970374683373625 13463076551227781012530219)
    ·
      refine ⟨20194614826841671518795329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13463076551227781012530219 20194614826841671518795329)
      ·
        refine ⟨15145961120131253639096497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20194614826841671518795329 15145961120131253639096497)
        ·
          refine ⟨11359470840098440229322373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15145961120131253639096497 11359470840098440229322373)
          ·
            refine ⟨2129900782518457542997945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11359470840098440229322373 2129900782518457542997945)
            ·
              refine ⟨1597425586888843157248459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2129900782518457542997945 1597425586888843157248459)
              ·
                refine ⟨2396138380333264735872689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1597425586888843157248459 2396138380333264735872689)
                ·
                  refine ⟨1797103785249948551904517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2396138380333264735872689 1797103785249948551904517)
                  ·
                    refine ⟨336956959734365353482097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1797103785249948551904517 336956959734365353482097)
                    ·
                      rfl

theorem cell22_984332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 2, 4].length) (baseStart_984332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_984332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_984332 prefixEnd_984332 := by exact prefixLift 984332
  have htrace : WordTrace (prefixWord ++ tailWord_984332) baseStart_984332 baseEnd_984332 := by
    simpa [prefixWord, tailWord_984332, baseEnd_984332] using wordTrace_append hprefix tailTrace_984332
  have hstable : (prefixWord ++ tailWord_984332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984332).length < 2 ^ (prefixWord ++ tailWord_984332).sum := by decide
  have hdescent : baseEnd_984332 < baseStart_984332 := by decide
  rcases family_descends (prefixWord ++ tailWord_984332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984338 : List Nat := [3, 2, 4, 2, 1, 1, 3, 1, 1, 4]
def baseStart_984338 : Nat := 118140960795 + 984338 * 2 ^ 59
def prefixEnd_984338 : Nat := 4983230072969 + 3 ^ 40 * 984338 * 2
def baseEnd_984338 : Nat := 336959013656983337832079

theorem tailTrace_984338 : CollatzResearch.WordTrace tailWord_984338 prefixEnd_984338 336959013656983337832079 := by
  unfold tailWord_984338
  simp only [CollatzResearch.WordTrace]
  refine ⟨8975439076979753097866417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23934504205279341594310445 8975439076979753097866417)
  ·
    refine ⟨6731579307734814823399813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8975439076979753097866417 6731579307734814823399813)
    ·
      refine ⟨1262171120200277779387465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6731579307734814823399813 1262171120200277779387465)
      ·
        refine ⟨946628340150208334540599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1262171120200277779387465 946628340150208334540599)
        ·
          refine ⟨1419942510225312501810899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 946628340150208334540599 1419942510225312501810899)
          ·
            refine ⟨2129913765337968752716349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1419942510225312501810899 2129913765337968752716349)
            ·
              refine ⟨798717662001738282268631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2129913765337968752716349 798717662001738282268631)
              ·
                refine ⟨1198076493002607423402947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 798717662001738282268631 1198076493002607423402947)
                ·
                  refine ⟨1797114739503911135104421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1198076493002607423402947 1797114739503911135104421)
                  ·
                    refine ⟨336959013656983337832079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1797114739503911135104421 336959013656983337832079)
                    ·
                      rfl

theorem cell22_984338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_984338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_984338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_984338 prefixEnd_984338 := by exact prefixLift 984338
  have htrace : WordTrace (prefixWord ++ tailWord_984338) baseStart_984338 baseEnd_984338 := by
    simpa [prefixWord, tailWord_984338, baseEnd_984338] using wordTrace_append hprefix tailTrace_984338
  have hstable : (prefixWord ++ tailWord_984338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984338).length < 2 ^ (prefixWord ++ tailWord_984338).sum := by decide
  have hdescent : baseEnd_984338 < baseStart_984338 := by decide
  rcases family_descends (prefixWord ++ tailWord_984338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984396 : List Nat := [2, 2, 1, 3, 2, 3, 2, 3, 1, 3]
def baseStart_984396 : Nat := 118140960795 + 984396 * 2 ^ 59
def prefixEnd_984396 : Nat := 4983230072969 + 3 ^ 40 * 984396 * 2
def baseEnd_984396 : Nat := 336978868242290519881901

theorem tailTrace_984396 : CollatzResearch.WordTrace tailWord_984396 prefixEnd_984396 336978868242290519881901 := by
  unfold tailWord_984396
  simp only [CollatzResearch.WordTrace]
  refine ⟨17951935870854444148538521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23935914494472592198051361 17951935870854444148538521)
  ·
    refine ⟨13463951903140833111403891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17951935870854444148538521 13463951903140833111403891)
    ·
      refine ⟨20195927854711249667105837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13463951903140833111403891 20195927854711249667105837)
      ·
        refine ⟨7573472945516718625164689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20195927854711249667105837 7573472945516718625164689)
        ·
          refine ⟨5680104709137538968873517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7573472945516718625164689 5680104709137538968873517)
          ·
            refine ⟨2130039265926577113327569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5680104709137538968873517 2130039265926577113327569)
            ·
              refine ⟨1597529449444932834995677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2130039265926577113327569 1597529449444932834995677)
              ·
                refine ⟨599073543541849813123379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1597529449444932834995677 599073543541849813123379)
                ·
                  refine ⟨898610315312774719685069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 599073543541849813123379 898610315312774719685069)
                  ·
                    refine ⟨336978868242290519881901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 898610315312774719685069 336978868242290519881901)
                    ·
                      rfl

theorem cell22_984396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 3, 1, 3].length) (baseStart_984396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_984396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_984396 prefixEnd_984396 := by exact prefixLift 984396
  have htrace : WordTrace (prefixWord ++ tailWord_984396) baseStart_984396 baseEnd_984396 := by
    simpa [prefixWord, tailWord_984396, baseEnd_984396] using wordTrace_append hprefix tailTrace_984396
  have hstable : (prefixWord ++ tailWord_984396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984396).length < 2 ^ (prefixWord ++ tailWord_984396).sum := by decide
  have hdescent : baseEnd_984396 < baseStart_984396 := by decide
  rcases family_descends (prefixWord ++ tailWord_984396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984426 : List Nat := [3, 1, 3, 3, 2, 1, 3, 1, 5]
def baseStart_984426 : Nat := 118140960795 + 984426 * 2 ^ 59
def prefixEnd_984426 : Nat := 4983230072969 + 3 ^ 40 * 984426 * 2
def baseEnd_984426 : Nat := 112329712618460147210603

theorem tailTrace_984426 : CollatzResearch.WordTrace tailWord_984426 prefixEnd_984426 112329712618460147210603 := by
  unfold tailWord_984426
  simp only [CollatzResearch.WordTrace]
  refine ⟨8976241482900050855167283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23936643954400135613779421 8976241482900050855167283)
  ·
    refine ⟨13464362224350076282750925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8976241482900050855167283 13464362224350076282750925)
    ·
      refine ⟨5049135834131278606031597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13464362224350076282750925 5049135834131278606031597)
      ·
        refine ⟨1893425937799229477261849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5049135834131278606031597 1893425937799229477261849)
        ·
          refine ⟨1420069453349422107946387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1893425937799229477261849 1420069453349422107946387)
          ·
            refine ⟨2130104180024133161919581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420069453349422107946387 2130104180024133161919581)
            ·
              refine ⟨798789067509049935719843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2130104180024133161919581 798789067509049935719843)
              ·
                refine ⟨1198183601263574903579765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 798789067509049935719843 1198183601263574903579765)
                ·
                  refine ⟨112329712618460147210603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1198183601263574903579765 112329712618460147210603)
                  ·
                    rfl

theorem cell22_984426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 5].length) (baseStart_984426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_984426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_984426 prefixEnd_984426 := by exact prefixLift 984426
  have htrace : WordTrace (prefixWord ++ tailWord_984426) baseStart_984426 baseEnd_984426 := by
    simpa [prefixWord, tailWord_984426, baseEnd_984426] using wordTrace_append hprefix tailTrace_984426
  have hstable : (prefixWord ++ tailWord_984426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984426).length < 2 ^ (prefixWord ++ tailWord_984426).sum := by decide
  have hdescent : baseEnd_984426 < baseStart_984426 := by decide
  rcases family_descends (prefixWord ++ tailWord_984426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984482 : List Nat := [3, 3, 1, 2, 1, 2, 1, 9]
def baseStart_984482 : Nat := 118140960795 + 984482 * 2 ^ 59
def prefixEnd_984482 : Nat := 4983230072969 + 3 ^ 40 * 984482 * 2
def baseEnd_984482 : Nat := 37445367533312773581293

theorem tailTrace_984482 : CollatzResearch.WordTrace tailWord_984482 prefixEnd_984482 37445367533312773581293 := by
  unfold tailWord_984482
  simp only [CollatzResearch.WordTrace]
  refine ⟨8976752104849331246176925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23938005612931549989805133 8976752104849331246176925)
  ·
    refine ⟨3366282039318499217316347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8976752104849331246176925 3366282039318499217316347)
    ·
      refine ⟨5049423058977748825974521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3366282039318499217316347 5049423058977748825974521)
      ·
        refine ⟨3787067294233311619480891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5049423058977748825974521 3787067294233311619480891)
        ·
          refine ⟨5680600941349967429221337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3787067294233311619480891 5680600941349967429221337)
          ·
            refine ⟨4260450706012475571916003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5680600941349967429221337 4260450706012475571916003)
            ·
              refine ⟨6390676059018713357874005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4260450706012475571916003 6390676059018713357874005)
              ·
                refine ⟨37445367533312773581293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6390676059018713357874005 37445367533312773581293)
                ·
                  rfl

theorem cell22_984482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 9].length) (baseStart_984482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_984482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_984482 prefixEnd_984482 := by exact prefixLift 984482
  have htrace : WordTrace (prefixWord ++ tailWord_984482) baseStart_984482 baseEnd_984482 := by
    simpa [prefixWord, tailWord_984482, baseEnd_984482] using wordTrace_append hprefix tailTrace_984482
  have hstable : (prefixWord ++ tailWord_984482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984482).length < 2 ^ (prefixWord ++ tailWord_984482).sum := by decide
  have hdescent : baseEnd_984482 < baseStart_984482 := by decide
  rcases family_descends (prefixWord ++ tailWord_984482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984527 : List Nat := [1, 1, 2, 1, 1, 4, 3, 4, 5]
def baseStart_984527 : Nat := 118140960795 + 984527 * 2 ^ 59
def prefixEnd_984527 : Nat := 4983230072969 + 3 ^ 40 * 984527 * 2
def baseEnd_984527 : Nat := 112341237406483281618833

theorem tailTrace_984527 : CollatzResearch.WordTrace tailWord_984527 prefixEnd_984527 112341237406483281618833 := by
  unfold tailWord_984527
  simp only [CollatzResearch.WordTrace]
  refine ⟨35908649704234297670095835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23939099802822865113397223 35908649704234297670095835)
  ·
    refine ⟨53862974556351446505143753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35908649704234297670095835 53862974556351446505143753)
    ·
      refine ⟨40397230917263584878857815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53862974556351446505143753 40397230917263584878857815)
      ·
        refine ⟨60595846375895377318286723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40397230917263584878857815 60595846375895377318286723)
        ·
          refine ⟨90893769563843065977430085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60595846375895377318286723 90893769563843065977430085)
          ·
            refine ⟨17042581793220574870768141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90893769563843065977430085 17042581793220574870768141)
            ·
              refine ⟨6390968172457715576538053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17042581793220574870768141 6390968172457715576538053)
              ·
                refine ⟨1198306532335821670600885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6390968172457715576538053 1198306532335821670600885)
                ·
                  refine ⟨112341237406483281618833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1198306532335821670600885 112341237406483281618833)
                  ·
                    rfl

theorem cell22_984527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 5].length) (baseStart_984527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_984527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_984527 prefixEnd_984527 := by exact prefixLift 984527
  have htrace : WordTrace (prefixWord ++ tailWord_984527) baseStart_984527 baseEnd_984527 := by
    simpa [prefixWord, tailWord_984527, baseEnd_984527] using wordTrace_append hprefix tailTrace_984527
  have hstable : (prefixWord ++ tailWord_984527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984527).length < 2 ^ (prefixWord ++ tailWord_984527).sum := by decide
  have hdescent : baseEnd_984527 < baseStart_984527 := by decide
  rcases family_descends (prefixWord ++ tailWord_984527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984565 : List Nat := [1, 3, 5, 1, 1, 2, 2, 3, 1, 3]
def baseStart_984565 : Nat := 118140960795 + 984565 * 2 ^ 59
def prefixEnd_984565 : Nat := 4983230072969 + 3 ^ 40 * 984565 * 2
def baseEnd_984565 : Nat := 337036720396030412406383

theorem tailTrace_984565 : CollatzResearch.WordTrace tailWord_984565 prefixEnd_984565 337036720396030412406383 := by
  unfold tailWord_984565
  simp only [CollatzResearch.WordTrace]
  refine ⟨35910035678096630159979149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23940023785397753439986099 35910035678096630159979149)
  ·
    refine ⟨13466263379286236309992181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35910035678096630159979149 13466263379286236309992181)
    ·
      refine ⟨1262462191808084654061767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13466263379286236309992181 1262462191808084654061767)
      ·
        refine ⟨1893693287712126981092651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1262462191808084654061767 1893693287712126981092651)
        ·
          refine ⟨2840539931568190471638977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1893693287712126981092651 2840539931568190471638977)
          ·
            refine ⟨2130404948676142853729233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2840539931568190471638977 2130404948676142853729233)
            ·
              refine ⟨1597803711507107140296925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2130404948676142853729233 1597803711507107140296925)
              ·
                refine ⟨599176391815165177611347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1597803711507107140296925 599176391815165177611347)
                ·
                  refine ⟨898764587722747766417021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 599176391815165177611347 898764587722747766417021)
                  ·
                    refine ⟨337036720396030412406383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 898764587722747766417021 337036720396030412406383)
                    ·
                      rfl

theorem cell22_984565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_984565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_984565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_984565 prefixEnd_984565 := by exact prefixLift 984565
  have htrace : WordTrace (prefixWord ++ tailWord_984565) baseStart_984565 baseEnd_984565 := by
    simpa [prefixWord, tailWord_984565, baseEnd_984565] using wordTrace_append hprefix tailTrace_984565
  have hstable : (prefixWord ++ tailWord_984565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984565).length < 2 ^ (prefixWord ++ tailWord_984565).sum := by decide
  have hdescent : baseEnd_984565 < baseStart_984565 := by decide
  rcases family_descends (prefixWord ++ tailWord_984565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984578 : List Nat := [3, 4, 1, 2, 1, 3, 1, 2, 5]
def baseStart_984578 : Nat := 118140960795 + 984578 * 2 ^ 59
def prefixEnd_984578 : Nat := 4983230072969 + 3 ^ 40 * 984578 * 2
def baseEnd_984578 : Nat := 112347056853900903943781

theorem tailTrace_984578 : CollatzResearch.WordTrace tailWord_984578 prefixEnd_984578 112347056853900903943781 := by
  unfold tailWord_984578
  simp only [CollatzResearch.WordTrace]
  refine ⟨8977627456762383345050597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23940339884699688920134925 8977627456762383345050597)
  ·
    refine ⟨1683305148142946877196987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8977627456762383345050597 1683305148142946877196987)
    ·
      refine ⟨2524957722214420315795481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1683305148142946877196987 2524957722214420315795481)
      ·
        refine ⟨1893718291660815236846611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2524957722214420315795481 1893718291660815236846611)
        ·
          refine ⟨2840577437491222855269917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1893718291660815236846611 2840577437491222855269917)
          ·
            refine ⟨1065216539059208570726219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2840577437491222855269917 1065216539059208570726219)
            ·
              refine ⟨1597824808588812856089329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1065216539059208570726219 1597824808588812856089329)
              ·
                refine ⟨1198368606441609642066997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1597824808588812856089329 1198368606441609642066997)
                ·
                  refine ⟨112347056853900903943781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1198368606441609642066997 112347056853900903943781)
                  ·
                    rfl

theorem cell22_984578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_984578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_984578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_984578 prefixEnd_984578 := by exact prefixLift 984578
  have htrace : WordTrace (prefixWord ++ tailWord_984578) baseStart_984578 baseEnd_984578 := by
    simpa [prefixWord, tailWord_984578, baseEnd_984578] using wordTrace_append hprefix tailTrace_984578
  have hstable : (prefixWord ++ tailWord_984578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984578).length < 2 ^ (prefixWord ++ tailWord_984578).sum := by decide
  have hdescent : baseEnd_984578 < baseStart_984578 := by decide
  rcases family_descends (prefixWord ++ tailWord_984578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984582 : List Nat := [6, 2, 1, 1, 2, 1, 2, 1, 3, 3]
def baseStart_984582 : Nat := 118140960795 + 984582 * 2 ^ 59
def prefixEnd_984582 : Nat := 4983230072969 + 3 ^ 40 * 984582 * 2
def baseEnd_984582 : Nat := 337042539843448034731331

theorem tailTrace_984582 : CollatzResearch.WordTrace tailWord_984582 prefixEnd_984582 337042539843448034731331 := by
  unfold tailWord_984582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1122207991219845064479625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23940437146023361375565333 1122207991219845064479625)
  ·
    refine ⟨841655993414883798359719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1122207991219845064479625 841655993414883798359719)
    ·
      refine ⟨1262483990122325697539579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 841655993414883798359719 1262483990122325697539579)
      ·
        refine ⟨1893725985183488546309369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1262483990122325697539579 1893725985183488546309369)
        ·
          refine ⟨1420294488887616409732027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1893725985183488546309369 1420294488887616409732027)
          ·
            refine ⟨2130441733331424614598041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420294488887616409732027 2130441733331424614598041)
            ·
              refine ⟨1597831299998568460948531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2130441733331424614598041 1597831299998568460948531)
              ·
                refine ⟨2396746949997852691422797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1597831299998568460948531 2396746949997852691422797)
                ·
                  refine ⟨898780106249194759283549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2396746949997852691422797 898780106249194759283549)
                  ·
                    refine ⟨337042539843448034731331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 898780106249194759283549 337042539843448034731331)
                    ·
                      rfl

theorem cell22_984582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_984582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_984582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_984582 prefixEnd_984582 := by exact prefixLift 984582
  have htrace : WordTrace (prefixWord ++ tailWord_984582) baseStart_984582 baseEnd_984582 := by
    simpa [prefixWord, tailWord_984582, baseEnd_984582] using wordTrace_append hprefix tailTrace_984582
  have hstable : (prefixWord ++ tailWord_984582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984582).length < 2 ^ (prefixWord ++ tailWord_984582).sum := by decide
  have hdescent : baseEnd_984582 < baseStart_984582 := by decide
  rcases family_descends (prefixWord ++ tailWord_984582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984636 : List Nat := [2, 2, 2, 2, 4, 1, 1, 2, 2, 4]
def baseStart_984636 : Nat := 118140960795 + 984636 * 2 ^ 59
def prefixEnd_984636 : Nat := 4983230072969 + 3 ^ 40 * 984636 * 2
def baseEnd_984636 : Nat := 337061025147009893881165

theorem tailTrace_984636 : CollatzResearch.WordTrace tailWord_984636 prefixEnd_984636 337061025147009893881165 := by
  unfold tailWord_984636
  simp only [CollatzResearch.WordTrace]
  refine ⟨17956312630419704642906881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23941750173892939523875841 17956312630419704642906881)
  ·
    refine ⟨13467234472814778482180161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17956312630419704642906881 13467234472814778482180161)
    ·
      refine ⟨10100425854611083861635121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13467234472814778482180161 10100425854611083861635121)
      ·
        refine ⟨7575319390958312896226341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10100425854611083861635121 7575319390958312896226341)
        ·
          refine ⟨1420372385804683668042439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7575319390958312896226341 1420372385804683668042439)
          ·
            refine ⟨2130558578707025502063659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420372385804683668042439 2130558578707025502063659)
            ·
              refine ⟨3195837868060538253095489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2130558578707025502063659 3195837868060538253095489)
              ·
                refine ⟨2396878401045403689821617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3195837868060538253095489 2396878401045403689821617)
                ·
                  refine ⟨1797658800784052767366213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2396878401045403689821617 1797658800784052767366213)
                  ·
                    refine ⟨337061025147009893881165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1797658800784052767366213 337061025147009893881165)
                    ·
                      rfl

theorem cell22_984636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_984636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_984636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_984636 prefixEnd_984636 := by exact prefixLift 984636
  have htrace : WordTrace (prefixWord ++ tailWord_984636) baseStart_984636 baseEnd_984636 := by
    simpa [prefixWord, tailWord_984636, baseEnd_984636] using wordTrace_append hprefix tailTrace_984636
  have hstable : (prefixWord ++ tailWord_984636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984636).length < 2 ^ (prefixWord ++ tailWord_984636).sum := by decide
  have hdescent : baseEnd_984636 < baseStart_984636 := by decide
  rcases family_descends (prefixWord ++ tailWord_984636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984709 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 5, 4]
def baseStart_984709 : Nat := 118140960795 + 984709 * 2 ^ 59
def prefixEnd_984709 : Nat := 4983230072969 + 3 ^ 40 * 984709 * 2
def baseEnd_984709 : Nat := 337086014538862036805941

theorem tailTrace_984709 : CollatzResearch.WordTrace tailWord_984709 prefixEnd_984709 337086014538862036805941 := by
  unfold tailWord_984709
  simp only [CollatzResearch.WordTrace]
  refine ⟨35915287789574942753221181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23943525193049961835480787 35915287789574942753221181)
  ·
    refine ⟨13468232921090603532457943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35915287789574942753221181 13468232921090603532457943)
    ·
      refine ⟨20202349381635905298686915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13468232921090603532457943 20202349381635905298686915)
      ·
        refine ⟨30303524072453857948030373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20202349381635905298686915 30303524072453857948030373)
        ·
          refine ⟨5681910763585098365255695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30303524072453857948030373 5681910763585098365255695)
          ·
            refine ⟨8522866145377647547883543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5681910763585098365255695 8522866145377647547883543)
            ·
              refine ⟨12784299218066471321825315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8522866145377647547883543 12784299218066471321825315)
              ·
                refine ⟨19176448827099706982737973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12784299218066471321825315 19176448827099706982737973)
                ·
                  refine ⟨1797792077540597529631685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19176448827099706982737973 1797792077540597529631685)
                  ·
                    refine ⟨337086014538862036805941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1797792077540597529631685 337086014538862036805941)
                    ·
                      rfl

theorem cell22_984709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_984709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_984709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_984709 prefixEnd_984709 := by exact prefixLift 984709
  have htrace : WordTrace (prefixWord ++ tailWord_984709) baseStart_984709 baseEnd_984709 := by
    simpa [prefixWord, tailWord_984709, baseEnd_984709] using wordTrace_append hprefix tailTrace_984709
  have hstable : (prefixWord ++ tailWord_984709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984709).length < 2 ^ (prefixWord ++ tailWord_984709).sum := by decide
  have hdescent : baseEnd_984709 < baseStart_984709 := by decide
  rcases family_descends (prefixWord ++ tailWord_984709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984739 : List Nat := [1, 1, 1, 4, 1, 1, 3, 4, 1, 5]
def baseStart_984739 : Nat := 118140960795 + 984739 * 2 ^ 59
def prefixEnd_984739 : Nat := 4983230072969 + 3 ^ 40 * 984739 * 2
def baseEnd_984739 : Nat := 337096284151951958555849

theorem tailTrace_984739 : CollatzResearch.WordTrace tailWord_984739 prefixEnd_984739 337096284151951958555849 := by
  unfold tailWord_984739
  simp only [CollatzResearch.WordTrace]
  refine ⟨35916381979466257876813271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23944254652977505251208847 35916381979466257876813271)
  ·
    refine ⟨53874572969199386815219907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35916381979466257876813271 53874572969199386815219907)
    ·
      refine ⟨80811859453799080222829861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53874572969199386815219907 80811859453799080222829861)
      ·
        refine ⟨15152223647587327541780599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80811859453799080222829861 15152223647587327541780599)
        ·
          refine ⟨22728335471380991312670899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15152223647587327541780599 22728335471380991312670899)
          ·
            refine ⟨34092503207071486969006349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22728335471380991312670899 34092503207071486969006349)
            ·
              refine ⟨12784688702651807613377381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34092503207071486969006349 12784688702651807613377381)
              ·
                refine ⟨2397129131747213927508259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12784688702651807613377381 2397129131747213927508259)
                ·
                  refine ⟨3595693697620820891262389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2397129131747213927508259 3595693697620820891262389)
                  ·
                    refine ⟨337096284151951958555849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3595693697620820891262389 337096284151951958555849)
                    ·
                      rfl

theorem cell22_984739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 5].length) (baseStart_984739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_984739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_984739 prefixEnd_984739 := by exact prefixLift 984739
  have htrace : WordTrace (prefixWord ++ tailWord_984739) baseStart_984739 baseEnd_984739 := by
    simpa [prefixWord, tailWord_984739, baseEnd_984739] using wordTrace_append hprefix tailTrace_984739
  have hstable : (prefixWord ++ tailWord_984739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984739).length < 2 ^ (prefixWord ++ tailWord_984739).sum := by decide
  have hdescent : baseEnd_984739 < baseStart_984739 := by decide
  rcases family_descends (prefixWord ++ tailWord_984739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984741 : List Nat := [1, 3, 1, 2, 1, 2, 3, 5, 4]
def baseStart_984741 : Nat := 118140960795 + 984741 * 2 ^ 59
def prefixEnd_984741 : Nat := 4983230072969 + 3 ^ 40 * 984741 * 2
def baseEnd_984741 : Nat := 112365656264274873335281

theorem tailTrace_984741 : CollatzResearch.WordTrace tailWord_984741 prefixEnd_984741 112365656264274873335281 := by
  unfold tailWord_984741
  simp only [CollatzResearch.WordTrace]
  refine ⟨35916454925459012218386077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23944303283639341478924051 35916454925459012218386077)
  ·
    refine ⟨13468670597047129581894779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35916454925459012218386077 13468670597047129581894779)
    ·
      refine ⟨20203005895570694372842169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13468670597047129581894779 20203005895570694372842169)
      ·
        refine ⟨15152254421678020779631627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20203005895570694372842169 15152254421678020779631627)
        ·
          refine ⟨22728381632517031169447441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15152254421678020779631627 22728381632517031169447441)
          ·
            refine ⟨17046286224387773377085581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22728381632517031169447441 17046286224387773377085581)
            ·
              refine ⟨6392357334145415016407093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17046286224387773377085581 6392357334145415016407093)
              ·
                refine ⟨599283500076132657788165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6392357334145415016407093 599283500076132657788165)
                ·
                  refine ⟨112365656264274873335281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 599283500076132657788165 112365656264274873335281)
                  ·
                    rfl

theorem cell22_984741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 5, 4].length) (baseStart_984741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_984741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_984741 prefixEnd_984741 := by exact prefixLift 984741
  have htrace : WordTrace (prefixWord ++ tailWord_984741) baseStart_984741 baseEnd_984741 := by
    simpa [prefixWord, tailWord_984741, baseEnd_984741] using wordTrace_append hprefix tailTrace_984741
  have hstable : (prefixWord ++ tailWord_984741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984741).length < 2 ^ (prefixWord ++ tailWord_984741).sum := by decide
  have hdescent : baseEnd_984741 < baseStart_984741 := by decide
  rcases family_descends (prefixWord ++ tailWord_984741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984758 : List Nat := [5, 1, 3, 1, 1, 1, 1, 3, 6]
def baseStart_984758 : Nat := 118140960795 + 984758 * 2 ^ 59
def prefixEnd_984758 : Nat := 4983230072969 + 3 ^ 40 * 984758 * 2
def baseEnd_984758 : Nat := 112367596080080747443597

theorem tailTrace_984758 : CollatzResearch.WordTrace tailWord_984758 prefixEnd_984758 112367596080080747443597 := by
  unfold tailWord_984758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2244817185399839007609683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23944716644264949414503285 2244817185399839007609683)
  ·
    refine ⟨3367225778099758511414525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2244817185399839007609683 3367225778099758511414525)
    ·
      refine ⟨1262709666787409441780447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3367225778099758511414525 1262709666787409441780447)
      ·
        refine ⟨1894064500181114162670671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1262709666787409441780447 1894064500181114162670671)
        ·
          refine ⟨2841096750271671244006007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1894064500181114162670671 2841096750271671244006007)
          ·
            refine ⟨4261645125407506866009011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2841096750271671244006007 4261645125407506866009011)
            ·
              refine ⟨6392467688111260299013517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4261645125407506866009011 6392467688111260299013517)
              ·
                refine ⟨2397175383041722612130069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6392467688111260299013517 2397175383041722612130069)
                ·
                  refine ⟨112367596080080747443597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2397175383041722612130069 112367596080080747443597)
                  ·
                    rfl

theorem cell22_984758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_984758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_984758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_984758 prefixEnd_984758 := by exact prefixLift 984758
  have htrace : WordTrace (prefixWord ++ tailWord_984758) baseStart_984758 baseEnd_984758 := by
    simpa [prefixWord, tailWord_984758, baseEnd_984758] using wordTrace_append hprefix tailTrace_984758
  have hstable : (prefixWord ++ tailWord_984758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984758).length < 2 ^ (prefixWord ++ tailWord_984758).sum := by decide
  have hdescent : baseEnd_984758 < baseStart_984758 := by decide
  rcases family_descends (prefixWord ++ tailWord_984758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984786 : List Nat := [3, 2, 2, 2, 2, 2, 1, 8]
def baseStart_984786 : Nat := 118140960795 + 984786 * 2 ^ 59
def prefixEnd_984786 : Nat := 4983230072969 + 3 ^ 40 * 984786 * 2
def baseEnd_984786 : Nat := 37456930356939944736745

theorem tailTrace_984786 : CollatzResearch.WordTrace tailWord_984786 prefixEnd_984786 37456930356939944736745 := by
  unfold tailWord_984786
  simp only [CollatzResearch.WordTrace]
  refine ⟨8979524052573996225943553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23945397473530656602516141 8979524052573996225943553)
  ·
    refine ⟨6734643039430497169457665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8979524052573996225943553 6734643039430497169457665)
    ·
      refine ⟨5050982279572872877093249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6734643039430497169457665 5050982279572872877093249)
      ·
        refine ⟨3788236709679654657819937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5050982279572872877093249 3788236709679654657819937)
        ·
          refine ⟨2841177532259740993364953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3788236709679654657819937 2841177532259740993364953)
          ·
            refine ⟨2130883149194805745023715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2841177532259740993364953 2130883149194805745023715)
            ·
              refine ⟨3196324723792208617535573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2130883149194805745023715 3196324723792208617535573)
              ·
                refine ⟨37456930356939944736745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3196324723792208617535573 37456930356939944736745)
                ·
                  rfl

theorem cell22_984786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 8].length) (baseStart_984786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_984786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_984786 prefixEnd_984786 := by exact prefixLift 984786
  have htrace : WordTrace (prefixWord ++ tailWord_984786) baseStart_984786 baseEnd_984786 := by
    simpa [prefixWord, tailWord_984786, baseEnd_984786] using wordTrace_append hprefix tailTrace_984786
  have hstable : (prefixWord ++ tailWord_984786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984786).length < 2 ^ (prefixWord ++ tailWord_984786).sum := by decide
  have hdescent : baseEnd_984786 < baseStart_984786 := by decide
  rcases family_descends (prefixWord ++ tailWord_984786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984803 : List Nat := [1, 1, 1, 7, 3, 1, 8]
def baseStart_984803 : Nat := 118140960795 + 984803 * 2 ^ 59
def prefixEnd_984803 : Nat := 4983230072969 + 3 ^ 40 * 984803 * 2
def baseEnd_984803 : Nat := 12485858987402856479839

theorem tailTrace_984803 : CollatzResearch.WordTrace tailWord_984803 prefixEnd_984803 12485858987402856479839 := by
  unfold tailWord_984803
  simp only [CollatzResearch.WordTrace]
  refine ⟨35918716251234396807143063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23945810834156264538095375 35918716251234396807143063)
  ·
    refine ⟨53878074376851595210714595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35918716251234396807143063 53878074376851595210714595)
    ·
      refine ⟨80817111565277392816071893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53878074376851595210714595 80817111565277392816071893)
      ·
        refine ⟨1894151052311188894126685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 80817111565277392816071893 1894151052311188894126685)
        ·
          refine ⟨710306644616695835297507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1894151052311188894126685 710306644616695835297507)
          ·
            refine ⟨1065459966925043752946261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710306644616695835297507 1065459966925043752946261)
            ·
              refine ⟨12485858987402856479839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1065459966925043752946261 12485858987402856479839)
              ·
                rfl

theorem cell22_984803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 8].length) (baseStart_984803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_984803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_984803 prefixEnd_984803 := by exact prefixLift 984803
  have htrace : WordTrace (prefixWord ++ tailWord_984803) baseStart_984803 baseEnd_984803 := by
    simpa [prefixWord, tailWord_984803, baseEnd_984803] using wordTrace_append hprefix tailTrace_984803
  have hstable : (prefixWord ++ tailWord_984803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984803).length < 2 ^ (prefixWord ++ tailWord_984803).sum := by decide
  have hdescent : baseEnd_984803 < baseStart_984803 := by decide
  rcases family_descends (prefixWord ++ tailWord_984803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984820 : List Nat := [2, 6, 1, 1, 1, 2, 2, 7]
def baseStart_984820 : Nat := 118140960795 + 984820 * 2 ^ 59
def prefixEnd_984820 : Nat := 4983230072969 + 3 ^ 40 * 984820 * 2
def baseEnd_984820 : Nat := 37458223567477194142289

theorem tailTrace_984820 : CollatzResearch.WordTrace tailWord_984820 prefixEnd_984820 37458223567477194142289 := by
  unfold tailWord_984820
  simp only [CollatzResearch.WordTrace]
  refine ⟨17959668146086404355255957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23946224194781872473674609 17959668146086404355255957)
  ·
    refine ⟨841859444347800204152623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17959668146086404355255957 841859444347800204152623)
    ·
      refine ⟨1262789166521700306228935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 841859444347800204152623 1262789166521700306228935)
      ·
        refine ⟨1894183749782550459343403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1262789166521700306228935 1894183749782550459343403)
        ·
          refine ⟨2841275624673825689015105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1894183749782550459343403 2841275624673825689015105)
          ·
            refine ⟨2130956718505369266761329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2841275624673825689015105 2130956718505369266761329)
            ·
              refine ⟨1598217538879026950070997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2130956718505369266761329 1598217538879026950070997)
              ·
                refine ⟨37458223567477194142289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1598217538879026950070997 37458223567477194142289)
                ·
                  rfl

theorem cell22_984820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 7].length) (baseStart_984820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_984820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_984820 prefixEnd_984820 := by exact prefixLift 984820
  have htrace : WordTrace (prefixWord ++ tailWord_984820) baseStart_984820 baseEnd_984820 := by
    simpa [prefixWord, tailWord_984820, baseEnd_984820] using wordTrace_append hprefix tailTrace_984820
  have hstable : (prefixWord ++ tailWord_984820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984820).length < 2 ^ (prefixWord ++ tailWord_984820).sum := by decide
  have hdescent : baseEnd_984820 < baseStart_984820 := by decide
  rcases family_descends (prefixWord ++ tailWord_984820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984859 : List Nat := [1, 1, 1, 1, 1, 1, 4, 4, 8]
def baseStart_984859 : Nat := 118140960795 + 984859 * 2 ^ 59
def prefixEnd_984859 : Nat := 4983230072969 + 3 ^ 40 * 984859 * 2
def baseEnd_984859 : Nat := 112379120868103881851827

theorem tailTrace_984859 : CollatzResearch.WordTrace tailWord_984859 prefixEnd_984859 112379120868103881851827 := by
  unfold tailWord_984859
  simp only [CollatzResearch.WordTrace]
  refine ⟨35920758739031518371181631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23947172492687678914121087 35920758739031518371181631)
  ·
    refine ⟨53881138108547277556772447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35920758739031518371181631 53881138108547277556772447)
    ·
      refine ⟨80821707162820916335158671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53881138108547277556772447 80821707162820916335158671)
      ·
        refine ⟨121232560744231374502738007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80821707162820916335158671 121232560744231374502738007)
        ·
          refine ⟨181848841116347061754107011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121232560744231374502738007 181848841116347061754107011)
          ·
            refine ⟨272773261674520592631160517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181848841116347061754107011 272773261674520592631160517)
            ·
              refine ⟨51144986563972611118342597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 272773261674520592631160517 51144986563972611118342597)
              ·
                refine ⟨9589684980744864584689237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51144986563972611118342597 9589684980744864584689237)
                ·
                  refine ⟨112379120868103881851827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9589684980744864584689237 112379120868103881851827)
                  ·
                    rfl

theorem cell22_984859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 8].length) (baseStart_984859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_984859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_984859 prefixEnd_984859 := by exact prefixLift 984859
  have htrace : WordTrace (prefixWord ++ tailWord_984859) baseStart_984859 baseEnd_984859 := by
    simpa [prefixWord, tailWord_984859, baseEnd_984859] using wordTrace_append hprefix tailTrace_984859
  have hstable : (prefixWord ++ tailWord_984859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984859).length < 2 ^ (prefixWord ++ tailWord_984859).sum := by decide
  have hdescent : baseEnd_984859 < baseStart_984859 := by decide
  rcases family_descends (prefixWord ++ tailWord_984859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984893 : List Nat := [1, 4, 1, 4, 1, 2, 1, 2, 6]
def baseStart_984893 : Nat := 118140960795 + 984893 * 2 ^ 59
def prefixEnd_984893 : Nat := 4983230072969 + 3 ^ 40 * 984893 * 2
def baseEnd_984893 : Nat := 112383000499715630068459

theorem tailTrace_984893 : CollatzResearch.WordTrace tailWord_984893 prefixEnd_984893 112383000499715630068459 := by
  unfold tailWord_984893
  simp only [CollatzResearch.WordTrace]
  refine ⟨35921998820908342177919333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23947999213938894785279555 35921998820908342177919333)
  ·
    refine ⟨6735374778920314158359875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35921998820908342177919333 6735374778920314158359875)
    ·
      refine ⟨10103062168380471237539813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6735374778920314158359875 10103062168380471237539813)
      ·
        refine ⟨1894324156571338357038715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10103062168380471237539813 1894324156571338357038715)
        ·
          refine ⟨2841486234857007535558073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1894324156571338357038715 2841486234857007535558073)
          ·
            refine ⟨2131114676142755651668555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2841486234857007535558073 2131114676142755651668555)
            ·
              refine ⟨3196672014214133477502833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2131114676142755651668555 3196672014214133477502833)
              ·
                refine ⟨2397504010660600108127125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3196672014214133477502833 2397504010660600108127125)
                ·
                  refine ⟨112383000499715630068459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2397504010660600108127125 112383000499715630068459)
                  ·
                    rfl

theorem cell22_984893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_984893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_984893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_984893 prefixEnd_984893 := by exact prefixLift 984893
  have htrace : WordTrace (prefixWord ++ tailWord_984893) baseStart_984893 baseEnd_984893 := by
    simpa [prefixWord, tailWord_984893, baseEnd_984893] using wordTrace_append hprefix tailTrace_984893
  have hstable : (prefixWord ++ tailWord_984893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984893).length < 2 ^ (prefixWord ++ tailWord_984893).sum := by decide
  have hdescent : baseEnd_984893 < baseStart_984893 := by decide
  rcases family_descends (prefixWord ++ tailWord_984893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984906 : List Nat := [3, 1, 2, 1, 1, 1, 5, 1, 1, 6]
def baseStart_984906 : Nat := 118140960795 + 984906 * 2 ^ 59
def prefixEnd_984906 : Nat := 4983230072969 + 3 ^ 40 * 984906 * 2
def baseEnd_984906 : Nat := 337153451664819189630337

theorem tailTrace_984906 : CollatzResearch.WordTrace tailWord_984906 prefixEnd_984906 337153451664819189630337 := by
  unfold tailWord_984906
  simp only [CollatzResearch.WordTrace]
  refine ⟨8980618242465311349535643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23948315313240830265428381 8980618242465311349535643)
  ·
    refine ⟨13470927363697967024303465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8980618242465311349535643 13470927363697967024303465)
    ·
      refine ⟨10103195522773475268227599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13470927363697967024303465 10103195522773475268227599)
      ·
        refine ⟨15154793284160212902341399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10103195522773475268227599 15154793284160212902341399)
        ·
          refine ⟨22732189926240319353512099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15154793284160212902341399 22732189926240319353512099)
          ·
            refine ⟨34098284889360479030268149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22732189926240319353512099 34098284889360479030268149)
            ·
              refine ⟨3196714208377544909087639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34098284889360479030268149 3196714208377544909087639)
              ·
                refine ⟨4795071312566317363631459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3196714208377544909087639 4795071312566317363631459)
                ·
                  refine ⟨7192606968849476045447189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4795071312566317363631459 7192606968849476045447189)
                  ·
                    refine ⟨337153451664819189630337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7192606968849476045447189 337153451664819189630337)
                    ·
                      rfl

theorem cell22_984906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_984906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_984906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_984906 prefixEnd_984906 := by exact prefixLift 984906
  have htrace : WordTrace (prefixWord ++ tailWord_984906) baseStart_984906 baseEnd_984906 := by
    simpa [prefixWord, tailWord_984906, baseEnd_984906] using wordTrace_append hprefix tailTrace_984906
  have hstable : (prefixWord ++ tailWord_984906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984906).length < 2 ^ (prefixWord ++ tailWord_984906).sum := by decide
  have hdescent : baseEnd_984906 < baseStart_984906 := by decide
  rcases family_descends (prefixWord ++ tailWord_984906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_984953 : List Nat := [1, 2, 1, 3, 2, 2, 1, 4, 3, 3]
def baseStart_984953 : Nat := 118140960795 + 984953 * 2 ^ 59
def prefixEnd_984953 : Nat := 4983230072969 + 3 ^ 40 * 984953 * 2
def baseEnd_984953 : Nat := 337169540725326733705193

theorem tailTrace_984953 : CollatzResearch.WordTrace tailWord_984953 prefixEnd_984953 337169540725326733705193 := by
  unfold tailWord_984953
  simp only [CollatzResearch.WordTrace]
  refine ⟨35924187200690972425103513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23949458133793981616735675 35924187200690972425103513)
  ·
    refine ⟨26943140400518229318827635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35924187200690972425103513 26943140400518229318827635)
    ·
      refine ⟨40414710600777343978241453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26943140400518229318827635 40414710600777343978241453)
      ·
        refine ⟨15155516475291503991840545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40414710600777343978241453 15155516475291503991840545)
        ·
          refine ⟨11366637356468627993880409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15155516475291503991840545 11366637356468627993880409)
          ·
            refine ⟨8524978017351470995410307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11366637356468627993880409 8524978017351470995410307)
            ·
              refine ⟨12787467026027206493115461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8524978017351470995410307 12787467026027206493115461)
              ·
                refine ⟨2397650067380101217459149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12787467026027206493115461 2397650067380101217459149)
                ·
                  refine ⟨899118775267537956547181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2397650067380101217459149 899118775267537956547181)
                  ·
                    refine ⟨337169540725326733705193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 899118775267537956547181 337169540725326733705193)
                    ·
                      rfl

theorem cell22_984953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 3, 3].length) (baseStart_984953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_984953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_984953 prefixEnd_984953 := by exact prefixLift 984953
  have htrace : WordTrace (prefixWord ++ tailWord_984953) baseStart_984953 baseEnd_984953 := by
    simpa [prefixWord, tailWord_984953, baseEnd_984953] using wordTrace_append hprefix tailTrace_984953
  have hstable : (prefixWord ++ tailWord_984953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_984953).length < 2 ^ (prefixWord ++ tailWord_984953).sum := by decide
  have hdescent : baseEnd_984953 < baseStart_984953 := by decide
  rcases family_descends (prefixWord ++ tailWord_984953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985011 : List Nat := [1, 1, 1, 2, 3, 1, 4, 1, 8]
def baseStart_985011 : Nat := 118140960795 + 985011 * 2 ^ 59
def prefixEnd_985011 : Nat := 4983230072969 + 3 ^ 40 * 985011 * 2
def baseEnd_985011 : Nat := 112396465103544638585005

theorem tailTrace_985011 : CollatzResearch.WordTrace tailWord_985011 prefixEnd_985011 112396465103544638585005 := by
  unfold tailWord_985011
  simp only [CollatzResearch.WordTrace]
  refine ⟨35926302634480848330714887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23950868422987232220476591 35926302634480848330714887)
  ·
    refine ⟨53889453951721272496072331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35926302634480848330714887 53889453951721272496072331)
    ·
      refine ⟨80834180927581908744108497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53889453951721272496072331 80834180927581908744108497)
      ·
        refine ⟨60625635695686431558081373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80834180927581908744108497 60625635695686431558081373)
        ·
          refine ⟨22734613385882411834280515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60625635695686431558081373 22734613385882411834280515)
          ·
            refine ⟨34101920078823617751420773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22734613385882411834280515 34101920078823617751420773)
            ·
              refine ⟨6394110014779428328391395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34101920078823617751420773 6394110014779428328391395)
              ·
                refine ⟨9591165022169142492587093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6394110014779428328391395 9591165022169142492587093)
                ·
                  refine ⟨112396465103544638585005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9591165022169142492587093 112396465103544638585005)
                  ·
                    rfl

theorem cell22_985011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 8].length) (baseStart_985011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_985011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_985011 prefixEnd_985011 := by exact prefixLift 985011
  have htrace : WordTrace (prefixWord ++ tailWord_985011) baseStart_985011 baseEnd_985011 := by
    simpa [prefixWord, tailWord_985011, baseEnd_985011] using wordTrace_append hprefix tailTrace_985011
  have hstable : (prefixWord ++ tailWord_985011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985011).length < 2 ^ (prefixWord ++ tailWord_985011).sum := by decide
  have hdescent : baseEnd_985011 < baseStart_985011 := by decide
  rcases family_descends (prefixWord ++ tailWord_985011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985060 : List Nat := [2, 3, 1, 1, 1, 1, 3, 5, 2, 3]
def baseStart_985060 : Nat := 118140960795 + 985060 * 2 ^ 59
def prefixEnd_985060 : Nat := 4983230072969 + 3 ^ 40 * 985060 * 2
def baseEnd_985060 : Nat := 337206169012014121279865

theorem tailTrace_985060 : CollatzResearch.WordTrace tailWord_985060 prefixEnd_985060 337206169012014121279865 := by
  unfold tailWord_985060
  simp only [CollatzResearch.WordTrace]
  refine ⟨17964044905651664849624317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23952059874202219799499089 17964044905651664849624317)
  ·
    refine ⟨6736516839619374318609119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17964044905651664849624317 6736516839619374318609119)
    ·
      refine ⟨10104775259429061477913679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6736516839619374318609119 10104775259429061477913679)
      ·
        refine ⟨15157162889143592216870519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10104775259429061477913679 15157162889143592216870519)
        ·
          refine ⟨22735744333715388325305779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15157162889143592216870519 22735744333715388325305779)
          ·
            refine ⟨34103616500573082487958669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22735744333715388325305779 34103616500573082487958669)
            ·
              refine ⟨12788856187714905932984501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34103616500573082487958669 12788856187714905932984501)
              ·
                refine ⟨1198955267598272431217297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12788856187714905932984501 1198955267598272431217297)
                ·
                  refine ⟨899216450698704323412973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1198955267598272431217297 899216450698704323412973)
                  ·
                    refine ⟨337206169012014121279865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 899216450698704323412973 337206169012014121279865)
                    ·
                      rfl

theorem cell22_985060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_985060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_985060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_985060 prefixEnd_985060 := by exact prefixLift 985060
  have htrace : WordTrace (prefixWord ++ tailWord_985060) baseStart_985060 baseEnd_985060 := by
    simpa [prefixWord, tailWord_985060, baseEnd_985060] using wordTrace_append hprefix tailTrace_985060
  have hstable : (prefixWord ++ tailWord_985060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985060).length < 2 ^ (prefixWord ++ tailWord_985060).sum := by decide
  have hdescent : baseEnd_985060 < baseStart_985060 := by decide
  rcases family_descends (prefixWord ++ tailWord_985060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985124 : List Nat := [2, 3, 1, 4, 3, 1, 2, 6]
def baseStart_985124 : Nat := 118140960795 + 985124 * 2 ^ 59
def prefixEnd_985124 : Nat := 4983230072969 + 3 ^ 40 * 985124 * 2
def baseEnd_985124 : Nat := 37469786391104365297741

theorem tailTrace_985124 : CollatzResearch.WordTrace tailWord_985124 prefixEnd_985124 37469786391104365297741 := by
  unfold tailWord_985124
  simp only [CollatzResearch.WordTrace]
  refine ⟨17965212041535734314789213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23953616055380979086385617 17965212041535734314789213)
  ·
    refine ⟨6736954515575900368045955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17965212041535734314789213 6736954515575900368045955)
    ·
      refine ⟨10105431773363850552068933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6736954515575900368045955 10105431773363850552068933)
      ·
        refine ⟨1894768457505721978512925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10105431773363850552068933 1894768457505721978512925)
        ·
          refine ⟨710538171564645741942347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1894768457505721978512925 710538171564645741942347)
          ·
            refine ⟨1065807257346968612913521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710538171564645741942347 1065807257346968612913521)
            ·
              refine ⟨799355443010226459685141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1065807257346968612913521 799355443010226459685141)
              ·
                refine ⟨37469786391104365297741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 799355443010226459685141 37469786391104365297741)
                ·
                  rfl

theorem cell22_985124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 6].length) (baseStart_985124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_985124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_985124 prefixEnd_985124 := by exact prefixLift 985124
  have htrace : WordTrace (prefixWord ++ tailWord_985124) baseStart_985124 baseEnd_985124 := by
    simpa [prefixWord, tailWord_985124, baseEnd_985124] using wordTrace_append hprefix tailTrace_985124
  have hstable : (prefixWord ++ tailWord_985124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985124).length < 2 ^ (prefixWord ++ tailWord_985124).sum := by decide
  have hdescent : baseEnd_985124 < baseStart_985124 := by decide
  rcases family_descends (prefixWord ++ tailWord_985124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985197 : List Nat := [1, 5, 1, 1, 2, 1, 2, 5, 4]
def baseStart_985197 : Nat := 118140960795 + 985197 * 2 ^ 59
def prefixEnd_985197 : Nat := 4983230072969 + 3 ^ 40 * 985197 * 2
def baseEnd_985197 : Nat := 112417688970597143534815

theorem tailTrace_985197 : CollatzResearch.WordTrace tailWord_985197 prefixEnd_985197 112417688970597143534815 := by
  unfold tailWord_985197
  simp only [CollatzResearch.WordTrace]
  refine ⟨35933086611807002096985845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23955391074538001397990563 35933086611807002096985845)
  ·
    refine ⟨3368726869856906446592423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35933086611807002096985845 3368726869856906446592423)
    ·
      refine ⟨5053090304785359669888635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3368726869856906446592423 5053090304785359669888635)
      ·
        refine ⟨7579635457178039504832953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5053090304785359669888635 7579635457178039504832953)
        ·
          refine ⟨5684726592883529628624715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7579635457178039504832953 5684726592883529628624715)
          ·
            refine ⟨8527089889325294442937073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5684726592883529628624715 8527089889325294442937073)
            ·
              refine ⟨6395317416993970832202805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8527089889325294442937073 6395317416993970832202805)
              ·
                refine ⟨599561007843184765519013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6395317416993970832202805 599561007843184765519013)
                ·
                  refine ⟨112417688970597143534815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 599561007843184765519013 112417688970597143534815)
                  ·
                    rfl

theorem cell22_985197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_985197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_985197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_985197 prefixEnd_985197 := by exact prefixLift 985197
  have htrace : WordTrace (prefixWord ++ tailWord_985197) baseStart_985197 baseEnd_985197 := by
    simpa [prefixWord, tailWord_985197, baseEnd_985197] using wordTrace_append hprefix tailTrace_985197
  have hstable : (prefixWord ++ tailWord_985197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985197).length < 2 ^ (prefixWord ++ tailWord_985197).sum := by decide
  have hdescent : baseEnd_985197 < baseStart_985197 := by decide
  rcases family_descends (prefixWord ++ tailWord_985197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985212 : List Nat := [2, 2, 2, 1, 1, 4, 1, 4, 2, 3]
def baseStart_985212 : Nat := 118140960795 + 985212 * 2 ^ 59
def prefixEnd_985212 : Nat := 4983230072969 + 3 ^ 40 * 985212 * 2
def baseEnd_985212 : Nat := 337258201718336391479399

theorem tailTrace_985212 : CollatzResearch.WordTrace tailWord_985212 prefixEnd_985212 337258201718336391479399 := by
  unfold tailWord_985212
  simp only [CollatzResearch.WordTrace]
  refine ⟨17966816853376329829390945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23955755804501773105854593 17966816853376329829390945)
  ·
    refine ⟨13475112640032247372043209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17966816853376329829390945 13475112640032247372043209)
    ·
      refine ⟨10106334480024185529032407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13475112640032247372043209 10106334480024185529032407)
      ·
        refine ⟨15159501720036278293548611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10106334480024185529032407 15159501720036278293548611)
        ·
          refine ⟨22739252580054417440322917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15159501720036278293548611 22739252580054417440322917)
          ·
            refine ⟨4263609858760203270060547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22739252580054417440322917 4263609858760203270060547)
            ·
              refine ⟨6395414788140304905090821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4263609858760203270060547 6395414788140304905090821)
              ·
                refine ⟨1199140272776307169704529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6395414788140304905090821 1199140272776307169704529)
                ·
                  refine ⟨899355204582230377278397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1199140272776307169704529 899355204582230377278397)
                  ·
                    refine ⟨337258201718336391479399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 899355204582230377278397 337258201718336391479399)
                    ·
                      rfl

theorem cell22_985212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_985212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_985212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_985212 prefixEnd_985212 := by exact prefixLift 985212
  have htrace : WordTrace (prefixWord ++ tailWord_985212) baseStart_985212 baseEnd_985212 := by
    simpa [prefixWord, tailWord_985212, baseEnd_985212] using wordTrace_append hprefix tailTrace_985212
  have hstable : (prefixWord ++ tailWord_985212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985212).length < 2 ^ (prefixWord ++ tailWord_985212).sum := by decide
  have hdescent : baseEnd_985212 < baseStart_985212 := by decide
  rcases family_descends (prefixWord ++ tailWord_985212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985274 : List Nat := [3, 1, 1, 1, 2, 2, 4, 4, 1, 3]
def baseStart_985274 : Nat := 118140960795 + 985274 * 2 ^ 59
def prefixEnd_985274 : Nat := 4983230072969 + 3 ^ 40 * 985274 * 2
def baseEnd_985274 : Nat := 337279425585388896429209

theorem tailTrace_985274 : CollatzResearch.WordTrace tailWord_985274 prefixEnd_985274 337279425585388896429209 := by
  unfold tailWord_985274
  simp only [CollatzResearch.WordTrace]
  refine ⟨8983973758132011061884719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23957263355018696165025917 8983973758132011061884719)
  ·
    refine ⟨13475960637198016592827079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8983973758132011061884719 13475960637198016592827079)
    ·
      refine ⟨20213940955797024889240619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13475960637198016592827079 20213940955797024889240619)
      ·
        refine ⟨30320911433695537333860929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20213940955797024889240619 30320911433695537333860929)
        ·
          refine ⟨22740683575271653000395697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30320911433695537333860929 22740683575271653000395697)
          ·
            refine ⟨17055512681453739750296773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22740683575271653000395697 17055512681453739750296773)
            ·
              refine ⟨3197908627772576203180645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17055512681453739750296773 3197908627772576203180645)
              ·
                refine ⟨599607867707358038096371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3197908627772576203180645 599607867707358038096371)
                ·
                  refine ⟨899411801561037057144557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 599607867707358038096371 899411801561037057144557)
                  ·
                    refine ⟨337279425585388896429209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 899411801561037057144557 337279425585388896429209)
                    ·
                      rfl

theorem cell22_985274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 4, 1, 3].length) (baseStart_985274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_985274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_985274 prefixEnd_985274 := by exact prefixLift 985274
  have htrace : WordTrace (prefixWord ++ tailWord_985274) baseStart_985274 baseEnd_985274 := by
    simpa [prefixWord, tailWord_985274, baseEnd_985274] using wordTrace_append hprefix tailTrace_985274
  have hstable : (prefixWord ++ tailWord_985274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985274).length < 2 ^ (prefixWord ++ tailWord_985274).sum := by decide
  have hdescent : baseEnd_985274 < baseStart_985274 := by decide
  rcases family_descends (prefixWord ++ tailWord_985274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985285 : List Nat := [1, 3, 1, 1, 1, 1, 6, 1, 2, 5]
def baseStart_985285 : Nat := 118140960795 + 985285 * 2 ^ 59
def prefixEnd_985285 : Nat := 4983230072969 + 3 ^ 40 * 985285 * 2
def baseEnd_985285 : Nat := 337283191110188534404175

theorem tailTrace_985285 : CollatzResearch.WordTrace tailWord_985285 prefixEnd_985285 337283191110188534404175 := by
  unfold tailWord_985285
  simp only [CollatzResearch.WordTrace]
  refine ⟨35936296235488193126189309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23957530823658795417459539 35936296235488193126189309)
  ·
    refine ⟨13476111088308072422320991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35936296235488193126189309 13476111088308072422320991)
    ·
      refine ⟨20214166632462108633481487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13476111088308072422320991 20214166632462108633481487)
      ·
        refine ⟨30321249948693162950222231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20214166632462108633481487 30321249948693162950222231)
        ·
          refine ⟨45481874923039744425333347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30321249948693162950222231 45481874923039744425333347)
          ·
            refine ⟨68222812384559616638000021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45481874923039744425333347 68222812384559616638000021)
            ·
              refine ⟨3197944330526232029906251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68222812384559616638000021 3197944330526232029906251)
              ·
                refine ⟨4796916495789348044859377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3197944330526232029906251 4796916495789348044859377)
                ·
                  refine ⟨3597687371842011033644533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4796916495789348044859377 3597687371842011033644533)
                  ·
                    refine ⟨337283191110188534404175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3597687371842011033644533 337283191110188534404175)
                    ·
                      rfl

theorem cell22_985285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_985285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_985285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_985285 prefixEnd_985285 := by exact prefixLift 985285
  have htrace : WordTrace (prefixWord ++ tailWord_985285) baseStart_985285 baseEnd_985285 := by
    simpa [prefixWord, tailWord_985285, baseEnd_985285] using wordTrace_append hprefix tailTrace_985285
  have hstable : (prefixWord ++ tailWord_985285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985285).length < 2 ^ (prefixWord ++ tailWord_985285).sum := by decide
  have hdescent : baseEnd_985285 < baseStart_985285 := by decide
  rcases family_descends (prefixWord ++ tailWord_985285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985381 : List Nat := [1, 3, 1, 2, 5, 1, 2, 2, 2, 3]
def baseStart_985381 : Nat := 118140960795 + 985381 * 2 ^ 59
def prefixEnd_985381 : Nat := 4983230072969 + 3 ^ 40 * 985381 * 2
def baseEnd_985381 : Nat := 337316053872076284003881

theorem tailTrace_985381 : CollatzResearch.WordTrace tailWord_985381 prefixEnd_985381 337316053872076284003881 := by
  unfold tailWord_985381
  simp only [CollatzResearch.WordTrace]
  refine ⟨35939797643140401521683997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23959865095426934347789331 35939797643140401521683997)
  ·
    refine ⟨13477424116177650570631499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35939797643140401521683997 13477424116177650570631499)
    ·
      refine ⟨20216136174266475855947249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13477424116177650570631499 20216136174266475855947249)
      ·
        refine ⟨15162102130699856891960437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20216136174266475855947249 15162102130699856891960437)
        ·
          refine ⟨1421447074753111583621291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15162102130699856891960437 1421447074753111583621291)
          ·
            refine ⟨2132170612129667375431937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1421447074753111583621291 2132170612129667375431937)
            ·
              refine ⟨1599127959097250531573953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2132170612129667375431937 1599127959097250531573953)
              ·
                refine ⟨1199345969322937898680465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1599127959097250531573953 1199345969322937898680465)
                ·
                  refine ⟨899509476992203424010349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1199345969322937898680465 899509476992203424010349)
                  ·
                    refine ⟨337316053872076284003881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 899509476992203424010349 337316053872076284003881)
                    ·
                      rfl

theorem cell22_985381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 2, 3].length) (baseStart_985381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_985381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_985381 prefixEnd_985381 := by exact prefixLift 985381
  have htrace : WordTrace (prefixWord ++ tailWord_985381) baseStart_985381 baseEnd_985381 := by
    simpa [prefixWord, tailWord_985381, baseEnd_985381] using wordTrace_append hprefix tailTrace_985381
  have hstable : (prefixWord ++ tailWord_985381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985381).length < 2 ^ (prefixWord ++ tailWord_985381).sum := by decide
  have hdescent : baseEnd_985381 < baseStart_985381 := by decide
  rcases family_descends (prefixWord ++ tailWord_985381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985394 : List Nat := [3, 2, 1, 1, 5, 2, 1, 7]
def baseStart_985394 : Nat := 118140960795 + 985394 * 2 ^ 59
def prefixEnd_985394 : Nat := 4983230072969 + 3 ^ 40 * 985394 * 2
def baseEnd_985394 : Nat := 37480056004194287047649

theorem tailTrace_985394 : CollatzResearch.WordTrace tailWord_985394 prefixEnd_985394 37480056004194287047649 := by
  unfold tailWord_985394
  simp only [CollatzResearch.WordTrace]
  refine ⟨8985067948023326185476809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23960181194728869827938157 8985067948023326185476809)
  ·
    refine ⟨6738800961017494639107607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8985067948023326185476809 6738800961017494639107607)
    ·
      refine ⟨10108201441526241958661411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6738800961017494639107607 10108201441526241958661411)
      ·
        refine ⟨15162302162289362937992117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10108201441526241958661411 15162302162289362937992117)
        ·
          refine ⟨1421465827714627775436761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15162302162289362937992117 1421465827714627775436761)
          ·
            refine ⟨1066099370785970831577571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1421465827714627775436761 1066099370785970831577571)
            ·
              refine ⟨1599149056178956247366357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1066099370785970831577571 1599149056178956247366357)
              ·
                refine ⟨37480056004194287047649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1599149056178956247366357 37480056004194287047649)
                ·
                  rfl

theorem cell22_985394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 7].length) (baseStart_985394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_985394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_985394 prefixEnd_985394 := by exact prefixLift 985394
  have htrace : WordTrace (prefixWord ++ tailWord_985394) baseStart_985394 baseEnd_985394 := by
    simpa [prefixWord, tailWord_985394, baseEnd_985394] using wordTrace_append hprefix tailTrace_985394
  have hstable : (prefixWord ++ tailWord_985394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985394).length < 2 ^ (prefixWord ++ tailWord_985394).sum := by decide
  have hdescent : baseEnd_985394 < baseStart_985394 := by decide
  rcases family_descends (prefixWord ++ tailWord_985394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985426 : List Nat := [3, 2, 2, 1, 1, 1, 3, 5, 1, 3]
def baseStart_985426 : Nat := 118140960795 + 985426 * 2 ^ 59
def prefixEnd_985426 : Nat := 4983230072969 + 3 ^ 40 * 985426 * 2
def baseEnd_985426 : Nat := 337331458291711166628743

theorem tailTrace_985426 : CollatzResearch.WordTrace tailWord_985426 prefixEnd_985426 337331458291711166628743 := by
  unfold tailWord_985426
  simp only [CollatzResearch.WordTrace]
  refine ⟨8985359731994343551768033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23960959285318249471381421 8985359731994343551768033)
  ·
    refine ⟨6739019798995757663826025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8985359731994343551768033 6739019798995757663826025)
    ·
      refine ⟨5054264849246818247869519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6739019798995757663826025 5054264849246818247869519)
      ·
        refine ⟨7581397273870227371804279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5054264849246818247869519 7581397273870227371804279)
        ·
          refine ⟨11372095910805341057706419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7581397273870227371804279 11372095910805341057706419)
          ·
            refine ⟨17058143866208011586559629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11372095910805341057706419 17058143866208011586559629)
            ·
              refine ⟨6396803949828004344959861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17058143866208011586559629 6396803949828004344959861)
              ·
                refine ⟨599700370296375407339987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6396803949828004344959861 599700370296375407339987)
                ·
                  refine ⟨899550555444563111009981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 599700370296375407339987 899550555444563111009981)
                  ·
                    refine ⟨337331458291711166628743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 899550555444563111009981 337331458291711166628743)
                    ·
                      rfl

theorem cell22_985426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_985426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_985426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_985426 prefixEnd_985426 := by exact prefixLift 985426
  have htrace : WordTrace (prefixWord ++ tailWord_985426) baseStart_985426 baseEnd_985426 := by
    simpa [prefixWord, tailWord_985426, baseEnd_985426] using wordTrace_append hprefix tailTrace_985426
  have hstable : (prefixWord ++ tailWord_985426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985426).length < 2 ^ (prefixWord ++ tailWord_985426).sum := by decide
  have hdescent : baseEnd_985426 < baseStart_985426 := by decide
  rcases family_descends (prefixWord ++ tailWord_985426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985467 : List Nat := [1, 1, 1, 1, 1, 7, 2, 2, 6]
def baseStart_985467 : Nat := 118140960795 + 985467 * 2 ^ 59
def prefixEnd_985467 : Nat := 4983230072969 + 3 ^ 40 * 985467 * 2
def baseEnd_985467 : Nat := 112448497809866908784539

theorem tailTrace_985467 : CollatzResearch.WordTrace tailWord_985467 prefixEnd_985467 112448497809866908784539 := by
  unfold tailWord_985467
  simp only [CollatzResearch.WordTrace]
  refine ⟨35942934320828838209314655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23961956213885892139543103 35942934320828838209314655)
  ·
    refine ⟨53914401481243257313971983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35942934320828838209314655 53914401481243257313971983)
    ·
      refine ⟨80871602221864885970957975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53914401481243257313971983 80871602221864885970957975)
      ·
        refine ⟨121307403332797328956436963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80871602221864885970957975 121307403332797328956436963)
        ·
          refine ⟨181961104999195993434655445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121307403332797328956436963 181961104999195993434655445)
          ·
            refine ⟨4264713398418656096124737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 181961104999195993434655445 4264713398418656096124737)
            ·
              refine ⟨3198535048813992072093553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4264713398418656096124737 3198535048813992072093553)
              ·
                refine ⟨2398901286610494054070165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3198535048813992072093553 2398901286610494054070165)
                ·
                  refine ⟨112448497809866908784539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2398901286610494054070165 112448497809866908784539)
                  ·
                    rfl

theorem cell22_985467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 6].length) (baseStart_985467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_985467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_985467 prefixEnd_985467 := by exact prefixLift 985467
  have htrace : WordTrace (prefixWord ++ tailWord_985467) baseStart_985467 baseEnd_985467 := by
    simpa [prefixWord, tailWord_985467, baseEnd_985467] using wordTrace_append hprefix tailTrace_985467
  have hstable : (prefixWord ++ tailWord_985467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985467).length < 2 ^ (prefixWord ++ tailWord_985467).sum := by decide
  have hdescent : baseEnd_985467 < baseStart_985467 := by decide
  rcases family_descends (prefixWord ++ tailWord_985467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985469 : List Nat := [1, 4, 1, 1, 2, 3, 1, 4, 1, 4]
def baseStart_985469 : Nat := 118140960795 + 985469 * 2 ^ 59
def prefixEnd_985469 : Nat := 4983230072969 + 3 ^ 40 * 985469 * 2
def baseEnd_985469 : Nat := 337346178070473387803611

theorem tailTrace_985469 : CollatzResearch.WordTrace tailWord_985469 prefixEnd_985469 337346178070473387803611 := by
  unfold tailWord_985469
  simp only [CollatzResearch.WordTrace]
  refine ⟨35943007266821592550887461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23962004844547728367258307 35943007266821592550887461)
  ·
    refine ⟨6739313862529048603291399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35943007266821592550887461 6739313862529048603291399)
    ·
      refine ⟨10108970793793572904937099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6739313862529048603291399 10108970793793572904937099)
      ·
        refine ⟨15163456190690359357405649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10108970793793572904937099 15163456190690359357405649)
        ·
          refine ⟨11372592143017769518054237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15163456190690359357405649 11372592143017769518054237)
          ·
            refine ⟨4264722053631663569270339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11372592143017769518054237 4264722053631663569270339)
            ·
              refine ⟨6397083080447495353905509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4264722053631663569270339 6397083080447495353905509)
              ·
                refine ⟨1199453077583905378857283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6397083080447495353905509 1199453077583905378857283)
                ·
                  refine ⟨1799179616375858068285925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1199453077583905378857283 1799179616375858068285925)
                  ·
                    refine ⟨337346178070473387803611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1799179616375858068285925 337346178070473387803611)
                    ·
                      rfl

theorem cell22_985469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_985469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_985469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_985469 prefixEnd_985469 := by exact prefixLift 985469
  have htrace : WordTrace (prefixWord ++ tailWord_985469) baseStart_985469 baseEnd_985469 := by
    simpa [prefixWord, tailWord_985469, baseEnd_985469] using wordTrace_append hprefix tailTrace_985469
  have hstable : (prefixWord ++ tailWord_985469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985469).length < 2 ^ (prefixWord ++ tailWord_985469).sum := by decide
  have hdescent : baseEnd_985469 < baseStart_985469 := by decide
  rcases family_descends (prefixWord ++ tailWord_985469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985486 : List Nat := [4, 1, 1, 4, 1, 1, 2, 3, 1, 4]
def baseStart_985486 : Nat := 118140960795 + 985486 * 2 ^ 59
def prefixEnd_985486 : Nat := 4983230072969 + 3 ^ 40 * 985486 * 2
def baseEnd_985486 : Nat := 337351997517891010128559

theorem tailTrace_985486 : CollatzResearch.WordTrace tailWord_985486 prefixEnd_985486 337351997517891010128559 := by
  unfold tailWord_985486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4492953413470000556782039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23962418205173336302837541 4492953413470000556782039)
  ·
    refine ⟨6739430120205000835173059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4492953413470000556782039 6739430120205000835173059)
    ·
      refine ⟨10109145180307501252759589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6739430120205000835173059 10109145180307501252759589)
      ·
        refine ⟨1895464721307656484892423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10109145180307501252759589 1895464721307656484892423)
        ·
          refine ⟨2843197081961484727338635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1895464721307656484892423 2843197081961484727338635)
          ·
            refine ⟨4264795622942227091007953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2843197081961484727338635 4264795622942227091007953)
            ·
              refine ⟨3198596717206670318255965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4264795622942227091007953 3198596717206670318255965)
              ·
                refine ⟨1199473768952501369345987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3198596717206670318255965 1199473768952501369345987)
                ·
                  refine ⟨1799210653428752054018981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1199473768952501369345987 1799210653428752054018981)
                  ·
                    refine ⟨337351997517891010128559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1799210653428752054018981 337351997517891010128559)
                    ·
                      rfl

theorem cell22_985486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_985486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_985486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_985486 prefixEnd_985486 := by exact prefixLift 985486
  have htrace : WordTrace (prefixWord ++ tailWord_985486) baseStart_985486 baseEnd_985486 := by
    simpa [prefixWord, tailWord_985486, baseEnd_985486] using wordTrace_append hprefix tailTrace_985486
  have hstable : (prefixWord ++ tailWord_985486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985486).length < 2 ^ (prefixWord ++ tailWord_985486).sum := by decide
  have hdescent : baseEnd_985486 < baseStart_985486 := by decide
  rcases family_descends (prefixWord ++ tailWord_985486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985494 : List Nat := [5, 3, 1, 2, 2, 1, 1, 1, 3, 3]
def baseStart_985494 : Nat := 118140960795 + 985494 * 2 ^ 59
def prefixEnd_985494 : Nat := 4983230072969 + 3 ^ 40 * 985494 * 2
def baseEnd_985494 : Nat := 337354736081381655928535

theorem tailTrace_985494 : CollatzResearch.WordTrace tailWord_985494 prefixEnd_985494 337354736081381655928535 := by
  unfold tailWord_985494
  simp only [CollatzResearch.WordTrace]
  refine ⟨2246494943233188863784221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23962612727820681213698357 2246494943233188863784221)
  ·
    refine ⟨842435603712445823919083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2246494943233188863784221 842435603712445823919083)
    ·
      refine ⟨1263653405568668735878625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 842435603712445823919083 1263653405568668735878625)
      ·
        refine ⟨947740054176501551908969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1263653405568668735878625 947740054176501551908969)
        ·
          refine ⟨710805040632376163931727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 947740054176501551908969 710805040632376163931727)
          ·
            refine ⟨1066207560948564245897591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710805040632376163931727 1066207560948564245897591)
            ·
              refine ⟨1599311341422846368846387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1066207560948564245897591 1599311341422846368846387)
              ·
                refine ⟨2398967012134269553269581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1599311341422846368846387 2398967012134269553269581)
                ·
                  refine ⟨899612629550351082476093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2398967012134269553269581 899612629550351082476093)
                  ·
                    refine ⟨337354736081381655928535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 899612629550351082476093 337354736081381655928535)
                    ·
                      rfl

theorem cell22_985494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_985494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_985494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_985494 prefixEnd_985494 := by exact prefixLift 985494
  have htrace : WordTrace (prefixWord ++ tailWord_985494) baseStart_985494 baseEnd_985494 := by
    simpa [prefixWord, tailWord_985494, baseEnd_985494] using wordTrace_append hprefix tailTrace_985494
  have hstable : (prefixWord ++ tailWord_985494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985494).length < 2 ^ (prefixWord ++ tailWord_985494).sum := by decide
  have hdescent : baseEnd_985494 < baseStart_985494 := by decide
  rcases family_descends (prefixWord ++ tailWord_985494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985501 : List Nat := [1, 4, 2, 1, 4, 2, 1, 1, 6]
def baseStart_985501 : Nat := 118140960795 + 985501 * 2 ^ 59
def prefixEnd_985501 : Nat := 4983230072969 + 3 ^ 40 * 985501 * 2
def baseEnd_985501 : Nat := 112452377441478657001171

theorem tailTrace_985501 : CollatzResearch.WordTrace tailWord_985501 prefixEnd_985501 112452377441478657001171 := by
  unfold tailWord_985501
  simp only [CollatzResearch.WordTrace]
  refine ⟨35944174402705662016052357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23962782935137108010701571 35944174402705662016052357)
  ·
    refine ⟨6739532700507311628009817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35944174402705662016052357 6739532700507311628009817)
    ·
      refine ⟨5054649525380483721007363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6739532700507311628009817 5054649525380483721007363)
      ·
        refine ⟨7581974288070725581511045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5054649525380483721007363 7581974288070725581511045)
        ·
          refine ⟨1421620179013261046533321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7581974288070725581511045 1421620179013261046533321)
          ·
            refine ⟨1066215134259945784899991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1421620179013261046533321 1066215134259945784899991)
            ·
              refine ⟨1599322701389918677349987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1066215134259945784899991 1599322701389918677349987)
              ·
                refine ⟨2398984052084878016024981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1599322701389918677349987 2398984052084878016024981)
                ·
                  refine ⟨112452377441478657001171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2398984052084878016024981 112452377441478657001171)
                  ·
                    rfl

theorem cell22_985501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_985501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_985501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_985501 prefixEnd_985501 := by exact prefixLift 985501
  have htrace : WordTrace (prefixWord ++ tailWord_985501) baseStart_985501 baseEnd_985501 := by
    simpa [prefixWord, tailWord_985501, baseEnd_985501] using wordTrace_append hprefix tailTrace_985501
  have hstable : (prefixWord ++ tailWord_985501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985501).length < 2 ^ (prefixWord ++ tailWord_985501).sum := by decide
  have hdescent : baseEnd_985501 < baseStart_985501 := by decide
  rcases family_descends (prefixWord ++ tailWord_985501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985537 : List Nat := [1, 2, 7, 1, 1, 1, 3, 1, 1, 4]
def baseStart_985537 : Nat := 118140960795 + 985537 * 2 ^ 59
def prefixEnd_985537 : Nat := 4983230072969 + 3 ^ 40 * 985537 * 2
def baseEnd_985537 : Nat := 337369455860143877103403

theorem tailTrace_985537 : CollatzResearch.WordTrace tailWord_985537 prefixEnd_985537 337369455860143877103403 := by
  unfold tailWord_985537
  simp only [CollatzResearch.WordTrace]
  refine ⟨35945487430575240164362865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23963658287050160109575243 35945487430575240164362865)
  ·
    refine ⟨26959115572931430123272149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35945487430575240164362865 26959115572931430123272149)
    ·
      refine ⟨631854271240580393514191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 26959115572931430123272149 631854271240580393514191)
      ·
        refine ⟨947781406860870590271287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631854271240580393514191 947781406860870590271287)
        ·
          refine ⟨1421672110291305885406931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947781406860870590271287 1421672110291305885406931)
          ·
            refine ⟨2132508165436958828110397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1421672110291305885406931 2132508165436958828110397)
            ·
              refine ⟨799690562038859560541399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2132508165436958828110397 799690562038859560541399)
              ·
                refine ⟨1199535843058289340812099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 799690562038859560541399 1199535843058289340812099)
                ·
                  refine ⟨1799303764587434011218149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1199535843058289340812099 1799303764587434011218149)
                  ·
                    refine ⟨337369455860143877103403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1799303764587434011218149 337369455860143877103403)
                    ·
                      rfl

theorem cell22_985537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_985537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_985537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_985537 prefixEnd_985537 := by exact prefixLift 985537
  have htrace : WordTrace (prefixWord ++ tailWord_985537) baseStart_985537 baseEnd_985537 := by
    simpa [prefixWord, tailWord_985537, baseEnd_985537] using wordTrace_append hprefix tailTrace_985537
  have hstable : (prefixWord ++ tailWord_985537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985537).length < 2 ^ (prefixWord ++ tailWord_985537).sum := by decide
  have hdescent : baseEnd_985537 < baseStart_985537 := by decide
  rcases family_descends (prefixWord ++ tailWord_985537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985619 : List Nat := [1, 1, 1, 2, 1, 5, 4, 1, 6]
def baseStart_985619 : Nat := 118140960795 + 985619 * 2 ^ 59
def prefixEnd_985619 : Nat := 4983230072969 + 3 ^ 40 * 985619 * 2
def baseEnd_985619 : Nat := 112465842045307665517717

theorem tailTrace_985619 : CollatzResearch.WordTrace tailWord_985619 prefixEnd_985619 112465842045307665517717 := by
  unfold tailWord_985619
  simp only [CollatzResearch.WordTrace]
  refine ⟨35948478216278168168847911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23965652144185445445898607 35948478216278168168847911)
  ·
    refine ⟨53922717324417252253271867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35948478216278168168847911 53922717324417252253271867)
    ·
      refine ⟨80884075986625878379907801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53922717324417252253271867 80884075986625878379907801)
      ·
        refine ⟨60663056989969408784930851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80884075986625878379907801 60663056989969408784930851)
        ·
          refine ⟨90994585484954113177396277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60663056989969408784930851 90994585484954113177396277)
          ·
            refine ⟨8530742389214448110380901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90994585484954113177396277 8530742389214448110380901)
            ·
              refine ⟨1599514197977709020696419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8530742389214448110380901 1599514197977709020696419)
              ·
                refine ⟨2399271296966563531044629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1599514197977709020696419 2399271296966563531044629)
                ·
                  refine ⟨112465842045307665517717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2399271296966563531044629 112465842045307665517717)
                  ·
                    rfl

theorem cell22_985619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 6].length) (baseStart_985619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_985619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_985619 prefixEnd_985619 := by exact prefixLift 985619
  have htrace : WordTrace (prefixWord ++ tailWord_985619) baseStart_985619 baseEnd_985619 := by
    simpa [prefixWord, tailWord_985619, baseEnd_985619] using wordTrace_append hprefix tailTrace_985619
  have hstable : (prefixWord ++ tailWord_985619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985619).length < 2 ^ (prefixWord ++ tailWord_985619).sum := by decide
  have hdescent : baseEnd_985619 < baseStart_985619 := by decide
  rcases family_descends (prefixWord ++ tailWord_985619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985649 : List Nat := [1, 2, 2, 3, 1, 1, 4, 1, 1, 6]
def baseStart_985649 : Nat := 118140960795 + 985649 * 2 ^ 59
def prefixEnd_985649 : Nat := 4983230072969 + 3 ^ 40 * 985649 * 2
def baseEnd_985649 : Nat := 337407795749012918303059

theorem tailTrace_985649 : CollatzResearch.WordTrace tailWord_985649 prefixEnd_985649 337407795749012918303059 := by
  unfold tailWord_985649
  simp only [CollatzResearch.WordTrace]
  refine ⟨35949572406169483292440001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23966381604112988861626667 35949572406169483292440001)
  ·
    refine ⟨26962179304627112469330001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35949572406169483292440001 26962179304627112469330001)
    ·
      refine ⟨20221634478470334351997501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26962179304627112469330001 20221634478470334351997501)
      ·
        refine ⟨7583112929426375381999063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20221634478470334351997501 7583112929426375381999063)
        ·
          refine ⟨11374669394139563072998595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7583112929426375381999063 11374669394139563072998595)
          ·
            refine ⟨17062004091209344609497893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11374669394139563072998595 17062004091209344609497893)
            ·
              refine ⟨3199125767101752114280855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17062004091209344609497893 3199125767101752114280855)
              ·
                refine ⟨4798688650652628171421283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3199125767101752114280855 4798688650652628171421283)
                ·
                  refine ⟨7198032975978942257131925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4798688650652628171421283 7198032975978942257131925)
                  ·
                    refine ⟨337407795749012918303059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7198032975978942257131925 337407795749012918303059)
                    ·
                      rfl

theorem cell22_985649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_985649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_985649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_985649 prefixEnd_985649 := by exact prefixLift 985649
  have htrace : WordTrace (prefixWord ++ tailWord_985649) baseStart_985649 baseEnd_985649 := by
    simpa [prefixWord, tailWord_985649, baseEnd_985649] using wordTrace_append hprefix tailTrace_985649
  have hstable : (prefixWord ++ tailWord_985649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985649).length < 2 ^ (prefixWord ++ tailWord_985649).sum := by decide
  have hdescent : baseEnd_985649 < baseStart_985649 := by decide
  rcases family_descends (prefixWord ++ tailWord_985649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985670 : List Nat := [6, 1, 1, 1, 2, 3, 1, 1, 6]
def baseStart_985670 : Nat := 118140960795 + 985670 * 2 ^ 59
def prefixEnd_985670 : Nat := 4983230072969 + 3 ^ 40 * 985670 * 2
def baseEnd_985670 : Nat := 112471661492725287842665

theorem tailTrace_985670 : CollatzResearch.WordTrace tailWord_985670 prefixEnd_985670 112471661492725287842665 := by
  unfold tailWord_985670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1123448073096668871217327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23966892226062269252636309 1123448073096668871217327)
  ·
    refine ⟨1685172109645003306825991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1123448073096668871217327 1685172109645003306825991)
    ·
      refine ⟨2527758164467504960238987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1685172109645003306825991 2527758164467504960238987)
      ·
        refine ⟨3791637246701257440358481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2527758164467504960238987 3791637246701257440358481)
        ·
          refine ⟨2843727935025943080268861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3791637246701257440358481 2843727935025943080268861)
          ·
            refine ⟨1066397975634728655100823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2843727935025943080268861 1066397975634728655100823)
            ·
              refine ⟨1599596963452092982651235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1066397975634728655100823 1599596963452092982651235)
              ·
                refine ⟨2399395445178139473976853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1599596963452092982651235 2399395445178139473976853)
                ·
                  refine ⟨112471661492725287842665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2399395445178139473976853 112471661492725287842665)
                  ·
                    rfl

theorem cell22_985670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_985670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_985670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_985670 prefixEnd_985670 := by exact prefixLift 985670
  have htrace : WordTrace (prefixWord ++ tailWord_985670) baseStart_985670 baseEnd_985670 := by
    simpa [prefixWord, tailWord_985670, baseEnd_985670] using wordTrace_append hprefix tailTrace_985670
  have hstable : (prefixWord ++ tailWord_985670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985670).length < 2 ^ (prefixWord ++ tailWord_985670).sum := by decide
  have hdescent : baseEnd_985670 < baseStart_985670 := by decide
  rcases family_descends (prefixWord ++ tailWord_985670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985696 : List Nat := [2, 1, 1, 3, 2, 1, 2, 4, 3, 3]
def baseStart_985696 : Nat := 118140960795 + 985696 * 2 ^ 59
def prefixEnd_985696 : Nat := 4983230072969 + 3 ^ 40 * 985696 * 2
def baseEnd_985696 : Nat := 337423884809520462377915

theorem tailTrace_985696 : CollatzResearch.WordTrace tailWord_985696 prefixEnd_985696 337423884809520462377915 := by
  unfold tailWord_985696
  simp only [CollatzResearch.WordTrace]
  refine ⟨17975643318499605159700471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23967524424666140212933961 17975643318499605159700471)
  ·
    refine ⟨26963464977749407739550707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17975643318499605159700471 26963464977749407739550707)
    ·
      refine ⟨40445197466624111609326061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26963464977749407739550707 40445197466624111609326061)
      ·
        refine ⟨15166949049984041853497273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40445197466624111609326061 15166949049984041853497273)
        ·
          refine ⟨11375211787488031390122955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15166949049984041853497273 11375211787488031390122955)
          ·
            refine ⟨17062817681232047085184433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11375211787488031390122955 17062817681232047085184433)
            ·
              refine ⟨12797113260924035313888325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17062817681232047085184433 12797113260924035313888325)
              ·
                refine ⟨2399458736423256621354061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12797113260924035313888325 2399458736423256621354061)
                ·
                  refine ⟨899797026158721233007773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2399458736423256621354061 899797026158721233007773)
                  ·
                    refine ⟨337423884809520462377915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 899797026158721233007773 337423884809520462377915)
                    ·
                      rfl

theorem cell22_985696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 3, 3].length) (baseStart_985696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_985696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_985696 prefixEnd_985696 := by exact prefixLift 985696
  have htrace : WordTrace (prefixWord ++ tailWord_985696) baseStart_985696 baseEnd_985696 := by
    simpa [prefixWord, tailWord_985696, baseEnd_985696] using wordTrace_append hprefix tailTrace_985696
  have hstable : (prefixWord ++ tailWord_985696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985696).length < 2 ^ (prefixWord ++ tailWord_985696).sum := by decide
  have hdescent : baseEnd_985696 < baseStart_985696 := by decide
  rcases family_descends (prefixWord ++ tailWord_985696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985777 : List Nat := [1, 2, 2, 6, 2, 1, 1, 2, 5]
def baseStart_985777 : Nat := 118140960795 + 985777 * 2 ^ 59
def prefixEnd_985777 : Nat := 4983230072969 + 3 ^ 40 * 985777 * 2
def baseEnd_985777 : Nat := 112483870921621083700889

theorem tailTrace_985777 : CollatzResearch.WordTrace tailWord_985777 prefixEnd_985777 112483870921621083700889 := by
  unfold tailWord_985777
  simp only [CollatzResearch.WordTrace]
  refine ⟨35954240949705761153099585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23969493966470507435399723 35954240949705761153099585)
  ·
    refine ⟨26965680712279320864824689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35954240949705761153099585 26965680712279320864824689)
    ·
      refine ⟨20224260534209490648618517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26965680712279320864824689 20224260534209490648618517)
      ·
        refine ⟨948012212541069874153993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20224260534209490648618517 948012212541069874153993)
        ·
          refine ⟨711009159405802405615495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 948012212541069874153993 711009159405802405615495)
          ·
            refine ⟨1066513739108703608423243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 711009159405802405615495 1066513739108703608423243)
            ·
              refine ⟨1599770608663055412634865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1066513739108703608423243 1599770608663055412634865)
              ·
                refine ⟨1199827956497291559476149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1599770608663055412634865 1199827956497291559476149)
                ·
                  refine ⟨112483870921621083700889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1199827956497291559476149 112483870921621083700889)
                  ·
                    rfl

theorem cell22_985777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 5].length) (baseStart_985777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_985777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_985777 prefixEnd_985777 := by exact prefixLift 985777
  have htrace : WordTrace (prefixWord ++ tailWord_985777) baseStart_985777 baseEnd_985777 := by
    simpa [prefixWord, tailWord_985777, baseEnd_985777] using wordTrace_append hprefix tailTrace_985777
  have hstable : (prefixWord ++ tailWord_985777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985777).length < 2 ^ (prefixWord ++ tailWord_985777).sum := by decide
  have hdescent : baseEnd_985777 < baseStart_985777 := by decide
  rcases family_descends (prefixWord ++ tailWord_985777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985788 : List Nat := [2, 2, 2, 3, 1, 1, 1, 6, 4]
def baseStart_985788 : Nat := 118140960795 + 985788 * 2 ^ 59
def prefixEnd_985788 : Nat := 4983230072969 + 3 ^ 40 * 985788 * 2
def baseEnd_985788 : Nat := 112485126096554296359211

theorem tailTrace_985788 : CollatzResearch.WordTrace tailWord_985788 prefixEnd_985788 112485126096554296359211 := by
  unfold tailWord_985788
  simp only [CollatzResearch.WordTrace]
  refine ⟨17977321076332955015875009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23969761435110606687833345 17977321076332955015875009)
  ·
    refine ⟨13482990807249716261906257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17977321076332955015875009 13482990807249716261906257)
    ·
      refine ⟨10112243105437287196429693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13482990807249716261906257 10112243105437287196429693)
      ·
        refine ⟨3792091164538982698661135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10112243105437287196429693 3792091164538982698661135)
        ·
          refine ⟨5688136746808474047991703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3792091164538982698661135 5688136746808474047991703)
          ·
            refine ⟨8532205120212711071987555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5688136746808474047991703 8532205120212711071987555)
            ·
              refine ⟨12798307680319066607981333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8532205120212711071987555 12798307680319066607981333)
              ·
                refine ⟨599920672514956247249125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12798307680319066607981333 599920672514956247249125)
                ·
                  refine ⟨112485126096554296359211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 599920672514956247249125 112485126096554296359211)
                  ·
                    rfl

theorem cell22_985788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 6, 4].length) (baseStart_985788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_985788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_985788 prefixEnd_985788 := by exact prefixLift 985788
  have htrace : WordTrace (prefixWord ++ tailWord_985788) baseStart_985788 baseEnd_985788 := by
    simpa [prefixWord, tailWord_985788, baseEnd_985788] using wordTrace_append hprefix tailTrace_985788
  have hstable : (prefixWord ++ tailWord_985788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985788).length < 2 ^ (prefixWord ++ tailWord_985788).sum := by decide
  have hdescent : baseEnd_985788 < baseStart_985788 := by decide
  rcases family_descends (prefixWord ++ tailWord_985788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985816 : List Nat := [2, 1, 2, 2, 3, 3, 1, 8]
def baseStart_985816 : Nat := 118140960795 + 985816 * 2 ^ 59
def prefixEnd_985816 : Nat := 4983230072969 + 3 ^ 40 * 985816 * 2
def baseEnd_985816 : Nat := 37496107029097794375283

theorem tailTrace_985816 : CollatzResearch.WordTrace tailWord_985816 prefixEnd_985816 37496107029097794375283 := by
  unfold tailWord_985816
  simp only [CollatzResearch.WordTrace]
  refine ⟨17977831698282235406884651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23970442264376313875846201 17977831698282235406884651)
  ·
    refine ⟨26966747547423353110326977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17977831698282235406884651 26966747547423353110326977)
    ·
      refine ⟨20225060660567514832745233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26966747547423353110326977 20225060660567514832745233)
      ·
        refine ⟨15168795495425636124558925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20225060660567514832745233 15168795495425636124558925)
        ·
          refine ⟨5688298310784613546709597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15168795495425636124558925 5688298310784613546709597)
          ·
            refine ⟨2133111866544230080016099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5688298310784613546709597 2133111866544230080016099)
            ·
              refine ⟨3199667799816345120024149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2133111866544230080016099 3199667799816345120024149)
              ·
                refine ⟨37496107029097794375283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3199667799816345120024149 37496107029097794375283)
                ·
                  rfl

theorem cell22_985816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 8].length) (baseStart_985816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_985816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_985816 prefixEnd_985816 := by exact prefixLift 985816
  have htrace : WordTrace (prefixWord ++ tailWord_985816) baseStart_985816 baseEnd_985816 := by
    simpa [prefixWord, tailWord_985816, baseEnd_985816] using wordTrace_append hprefix tailTrace_985816
  have hstable : (prefixWord ++ tailWord_985816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985816).length < 2 ^ (prefixWord ++ tailWord_985816).sum := by decide
  have hdescent : baseEnd_985816 < baseStart_985816 := by decide
  rcases family_descends (prefixWord ++ tailWord_985816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985820 : List Nat := [2, 2, 5, 1, 1, 1, 1, 2, 4, 3]
def baseStart_985820 : Nat := 118140960795 + 985820 * 2 ^ 59
def prefixEnd_985820 : Nat := 4983230072969 + 3 ^ 40 * 985820 * 2
def baseEnd_985820 : Nat := 337466332543625472277535

theorem tailTrace_985820 : CollatzResearch.WordTrace tailWord_985820 prefixEnd_985820 337466332543625472277535 := by
  unfold tailWord_985820
  simp only [CollatzResearch.WordTrace]
  refine ⟨17977904644274989748457457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23970539525699986331276609 17977904644274989748457457)
  ·
    refine ⟨13483428483206242311343093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17977904644274989748457457 13483428483206242311343093)
    ·
      refine ⟨1264071420300585216688415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13483428483206242311343093 1264071420300585216688415)
      ·
        refine ⟨1896107130450877825032623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1264071420300585216688415 1896107130450877825032623)
        ·
          refine ⟨2844160695676316737548935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1896107130450877825032623 2844160695676316737548935)
          ·
            refine ⟨4266241043514475106323403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2844160695676316737548935 4266241043514475106323403)
            ·
              refine ⟨6399361565271712659485105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4266241043514475106323403 6399361565271712659485105)
              ·
                refine ⟨4799521173953784494613829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6399361565271712659485105 4799521173953784494613829)
                ·
                  refine ⟨899910220116334592740093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4799521173953784494613829 899910220116334592740093)
                  ·
                    refine ⟨337466332543625472277535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 899910220116334592740093 337466332543625472277535)
                    ·
                      rfl

theorem cell22_985820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_985820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_985820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_985820 prefixEnd_985820 := by exact prefixLift 985820
  have htrace : WordTrace (prefixWord ++ tailWord_985820) baseStart_985820 baseEnd_985820 := by
    simpa [prefixWord, tailWord_985820, baseEnd_985820] using wordTrace_append hprefix tailTrace_985820
  have hstable : (prefixWord ++ tailWord_985820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985820).length < 2 ^ (prefixWord ++ tailWord_985820).sum := by decide
  have hdescent : baseEnd_985820 < baseStart_985820 := by decide
  rcases family_descends (prefixWord ++ tailWord_985820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985854 : List Nat := [4, 2, 2, 1, 2, 3, 2, 1, 2, 3]
def baseStart_985854 : Nat := 118140960795 + 985854 * 2 ^ 59
def prefixEnd_985854 : Nat := 4983230072969 + 3 ^ 40 * 985854 * 2
def baseEnd_985854 : Nat := 337477971438460716927431

theorem tailTrace_985854 : CollatzResearch.WordTrace tailWord_985854 prefixEnd_985854 337477971438460716927431 := by
  unfold tailWord_985854
  simp only [CollatzResearch.WordTrace]
  refine ⟨4494631171303350412956577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23971366246951202202435077 4494631171303350412956577)
  ·
    refine ⟨3370973378477512809717433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4494631171303350412956577 3370973378477512809717433)
    ·
      refine ⟨2528230033858134607288075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3370973378477512809717433 2528230033858134607288075)
      ·
        refine ⟨3792345050787201910932113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2528230033858134607288075 3792345050787201910932113)
        ·
          refine ⟨2844258788090401433199085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3792345050787201910932113 2844258788090401433199085)
          ·
            refine ⟨1066597045533900537449657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2844258788090401433199085 1066597045533900537449657)
            ·
              refine ⟨799947784150425403087243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1066597045533900537449657 799947784150425403087243)
              ·
                refine ⟨1199921676225638104630865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 799947784150425403087243 1199921676225638104630865)
                ·
                  refine ⟨899941257169228578473149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1199921676225638104630865 899941257169228578473149)
                  ·
                    refine ⟨337477971438460716927431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 899941257169228578473149 337477971438460716927431)
                    ·
                      rfl

theorem cell22_985854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_985854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_985854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_985854 prefixEnd_985854 := by exact prefixLift 985854
  have htrace : WordTrace (prefixWord ++ tailWord_985854) baseStart_985854 baseEnd_985854 := by
    simpa [prefixWord, tailWord_985854, baseEnd_985854] using wordTrace_append hprefix tailTrace_985854
  have hstable : (prefixWord ++ tailWord_985854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985854).length < 2 ^ (prefixWord ++ tailWord_985854).sum := by decide
  have hdescent : baseEnd_985854 < baseStart_985854 := by decide
  rcases family_descends (prefixWord ++ tailWord_985854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985938 : List Nat := [3, 2, 2, 1, 1, 2, 1, 4, 1, 5]
def baseStart_985938 : Nat := 118140960795 + 985938 * 2 ^ 59
def prefixEnd_985938 : Nat := 4983230072969 + 3 ^ 40 * 985938 * 2
def baseEnd_985938 : Nat := 337506726355112497827173

theorem tailTrace_985938 : CollatzResearch.WordTrace tailWord_985938 prefixEnd_985938 337506726355112497827173 := by
  unfold tailWord_985938
  simp only [CollatzResearch.WordTrace]
  refine ⟨8990028275530621412427617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23973408734748323766473645 8990028275530621412427617)
  ·
    refine ⟨6742521206647966059320713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8990028275530621412427617 6742521206647966059320713)
    ·
      refine ⟨5056890904985974544490535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6742521206647966059320713 5056890904985974544490535)
      ·
        refine ⟨7585336357478961816735803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5056890904985974544490535 7585336357478961816735803)
        ·
          refine ⟨11378004536218442725103705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7585336357478961816735803 11378004536218442725103705)
          ·
            refine ⟨8533503402163832043827779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11378004536218442725103705 8533503402163832043827779)
            ·
              refine ⟨12800255103245748065741669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8533503402163832043827779 12800255103245748065741669)
              ·
                refine ⟨2400047831858577762326563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12800255103245748065741669 2400047831858577762326563)
                ·
                  refine ⟨3600071747787866643489845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2400047831858577762326563 3600071747787866643489845)
                  ·
                    refine ⟨337506726355112497827173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3600071747787866643489845 337506726355112497827173)
                    ·
                      rfl

theorem cell22_985938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_985938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_985938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_985938 prefixEnd_985938 := by exact prefixLift 985938
  have htrace : WordTrace (prefixWord ++ tailWord_985938) baseStart_985938 baseEnd_985938 := by
    simpa [prefixWord, tailWord_985938, baseEnd_985938] using wordTrace_append hprefix tailTrace_985938
  have hstable : (prefixWord ++ tailWord_985938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985938).length < 2 ^ (prefixWord ++ tailWord_985938).sum := by decide
  have hdescent : baseEnd_985938 < baseStart_985938 := by decide
  rcases family_descends (prefixWord ++ tailWord_985938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985951 : List Nat := [1, 1, 2, 3, 1, 3, 11]
def baseStart_985951 : Nat := 118140960795 + 985951 * 2 ^ 59
def prefixEnd_985951 : Nat := 4983230072969 + 3 ^ 40 * 985951 * 2
def baseEnd_985951 : Nat := 12500413945214251750079

theorem tailTrace_985951 : CollatzResearch.WordTrace tailWord_985951 prefixEnd_985951 12500413945214251750079 := by
  unfold tailWord_985951
  simp only [CollatzResearch.WordTrace]
  refine ⟨35960587251075388869933707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23973724834050259246622471 35960587251075388869933707)
  ·
    refine ⟨53940880876613083304900561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35960587251075388869933707 53940880876613083304900561)
    ·
      refine ⟨40455660657459812478675421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53940880876613083304900561 40455660657459812478675421)
      ·
        refine ⟨15170872746547429679503283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40455660657459812478675421 15170872746547429679503283)
        ·
          refine ⟨22756309119821144519254925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15170872746547429679503283 22756309119821144519254925)
          ·
            refine ⟨8533615919932929194720597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22756309119821144519254925 8533615919932929194720597)
            ·
              refine ⟨12500413945214251750079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 8533615919932929194720597 12500413945214251750079)
              ·
                rfl

theorem cell22_985951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 11].length) (baseStart_985951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_985951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_985951 prefixEnd_985951 := by exact prefixLift 985951
  have htrace : WordTrace (prefixWord ++ tailWord_985951) baseStart_985951 baseEnd_985951 := by
    simpa [prefixWord, tailWord_985951, baseEnd_985951] using wordTrace_append hprefix tailTrace_985951
  have hstable : (prefixWord ++ tailWord_985951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985951).length < 2 ^ (prefixWord ++ tailWord_985951).sum := by decide
  have hdescent : baseEnd_985951 < baseStart_985951 := by decide
  rcases family_descends (prefixWord ++ tailWord_985951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_985955 : List Nat := [1, 1, 1, 5, 3, 2, 1, 1, 4, 3]
def baseStart_985955 : Nat := 118140960795 + 985955 * 2 ^ 59
def prefixEnd_985955 : Nat := 4983230072969 + 3 ^ 40 * 985955 * 2
def baseEnd_985955 : Nat := 337512545802530120152121

theorem tailTrace_985955 : CollatzResearch.WordTrace tailWord_985955 prefixEnd_985955 337512545802530120152121 := by
  unfold tailWord_985955
  simp only [CollatzResearch.WordTrace]
  refine ⟨35960733143060897553079319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23973822095373931702052879 35960733143060897553079319)
  ·
    refine ⟨53941099714591346329618979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35960733143060897553079319 53941099714591346329618979)
    ·
      refine ⟨80911649571887019494428469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53941099714591346329618979 80911649571887019494428469)
      ·
        refine ⟨7585467147364408077602669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80911649571887019494428469 7585467147364408077602669)
        ·
          refine ⟨2844550180261653029101001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7585467147364408077602669 2844550180261653029101001)
          ·
            refine ⟨2133412635196239771825751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2844550180261653029101001 2133412635196239771825751)
            ·
              refine ⟨3200118952794359657738627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2133412635196239771825751 3200118952794359657738627)
              ·
                refine ⟨4800178429191539486607941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3200118952794359657738627 4800178429191539486607941)
                ·
                  refine ⟨900033455473413653738989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4800178429191539486607941 900033455473413653738989)
                  ·
                    refine ⟨337512545802530120152121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 900033455473413653738989 337512545802530120152121)
                    ·
                      rfl

theorem cell22_985955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 4, 3].length) (baseStart_985955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_985955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_985955 prefixEnd_985955 := by exact prefixLift 985955
  have htrace : WordTrace (prefixWord ++ tailWord_985955) baseStart_985955 baseEnd_985955 := by
    simpa [prefixWord, tailWord_985955, baseEnd_985955] using wordTrace_append hprefix tailTrace_985955
  have hstable : (prefixWord ++ tailWord_985955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_985955).length < 2 ^ (prefixWord ++ tailWord_985955).sum := by decide
  have hdescent : baseEnd_985955 < baseStart_985955 := by decide
  rcases family_descends (prefixWord ++ tailWord_985955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986002 : List Nat := [3, 2, 3, 2, 3, 1, 8]
def baseStart_986002 : Nat := 118140960795 + 986002 * 2 ^ 59
def prefixEnd_986002 : Nat := 4983230072969 + 3 ^ 40 * 986002 * 2
def baseEnd_986002 : Nat := 12501060550482876452851

theorem tailTrace_986002 : CollatzResearch.WordTrace tailWord_986002 prefixEnd_986002 12501060550482876452851 := by
  unfold tailWord_986002
  simp only [CollatzResearch.WordTrace]
  refine ⟨8990611843472656145010065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23974964915927083053360173 8990611843472656145010065)
  ·
    refine ⟨6742958882604492108757549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8990611843472656145010065 6742958882604492108757549)
    ·
      refine ⟨2528609580976684540784081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6742958882604492108757549 2528609580976684540784081)
      ·
        refine ⟨1896457185732513405588061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2528609580976684540784081 1896457185732513405588061)
        ·
          refine ⟨711171444649692527095523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1896457185732513405588061 711171444649692527095523)
          ·
            refine ⟨1066757166974538790643285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 711171444649692527095523 1066757166974538790643285)
            ·
              refine ⟨12501060550482876452851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1066757166974538790643285 12501060550482876452851)
              ·
                rfl

theorem cell22_986002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 8].length) (baseStart_986002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_986002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_986002 prefixEnd_986002 := by exact prefixLift 986002
  have htrace : WordTrace (prefixWord ++ tailWord_986002) baseStart_986002 baseEnd_986002 := by
    simpa [prefixWord, tailWord_986002, baseEnd_986002] using wordTrace_append hprefix tailTrace_986002
  have hstable : (prefixWord ++ tailWord_986002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986002).length < 2 ^ (prefixWord ++ tailWord_986002).sum := by decide
  have hdescent : baseEnd_986002 < baseStart_986002 := by decide
  rcases family_descends (prefixWord ++ tailWord_986002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986013 : List Nat := [1, 4, 2, 1, 2, 1, 1, 3, 7]
def baseStart_986013 : Nat := 118140960795 + 986013 * 2 ^ 59
def prefixEnd_986013 : Nat := 4983230072969 + 3 ^ 40 * 986013 * 2
def baseEnd_986013 : Nat := 112510800129279100733981

theorem tailTrace_986013 : CollatzResearch.WordTrace tailWord_986013 prefixEnd_986013 112510800129279100733981 := by
  unfold tailWord_986013
  simp only [CollatzResearch.WordTrace]
  refine ⟨35962848576850773458690693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23975232384567182305793795 35962848576850773458690693)
  ·
    refine ⟨6743034108159520023504505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35962848576850773458690693 6743034108159520023504505)
    ·
      refine ⟨5057275581119640017628379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6743034108159520023504505 5057275581119640017628379)
      ·
        refine ⟨7585913371679460026442569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5057275581119640017628379 7585913371679460026442569)
        ·
          refine ⟨5689435028759595019831927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7585913371679460026442569 5689435028759595019831927)
          ·
            refine ⟨8534152543139392529747891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5689435028759595019831927 8534152543139392529747891)
            ·
              refine ⟨12801228814709088794621837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8534152543139392529747891 12801228814709088794621837)
              ·
                refine ⟨4800460805515908297983189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12801228814709088794621837 4800460805515908297983189)
                ·
                  refine ⟨112510800129279100733981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4800460805515908297983189 112510800129279100733981)
                  ·
                    rfl

theorem cell22_986013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_986013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_986013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_986013 prefixEnd_986013 := by exact prefixLift 986013
  have htrace : WordTrace (prefixWord ++ tailWord_986013) baseStart_986013 baseEnd_986013 := by
    simpa [prefixWord, tailWord_986013, baseEnd_986013] using wordTrace_append hprefix tailTrace_986013
  have hstable : (prefixWord ++ tailWord_986013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986013).length < 2 ^ (prefixWord ++ tailWord_986013).sum := by decide
  have hdescent : baseEnd_986013 < baseStart_986013 := by decide
  rcases family_descends (prefixWord ++ tailWord_986013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986017 : List Nat := [1, 2, 3, 4, 1, 1, 3, 1, 3, 3]
def baseStart_986017 : Nat := 118140960795 + 986017 * 2 ^ 59
def prefixEnd_986017 : Nat := 4983230072969 + 3 ^ 40 * 986017 * 2
def baseEnd_986017 : Nat := 337533769669582625101931

theorem tailTrace_986017 : CollatzResearch.WordTrace tailWord_986017 prefixEnd_986017 337533769669582625101931 := by
  unfold tailWord_986017
  simp only [CollatzResearch.WordTrace]
  refine ⟨35962994468836282141836305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23975329645890854761224203 35962994468836282141836305)
  ·
    refine ⟨26972245851627211606377229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35962994468836282141836305 26972245851627211606377229)
    ·
      refine ⟨10114592194360204352391461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26972245851627211606377229 10114592194360204352391461)
      ·
        refine ⟨1896486036442538316073399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10114592194360204352391461 1896486036442538316073399)
        ·
          refine ⟨2844729054663807474110099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1896486036442538316073399 2844729054663807474110099)
          ·
            refine ⟨4267093581995711211165149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2844729054663807474110099 4267093581995711211165149)
            ·
              refine ⟨1600160093248391704186931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4267093581995711211165149 1600160093248391704186931)
              ·
                refine ⟨2400240139872587556280397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1600160093248391704186931 2400240139872587556280397)
                ·
                  refine ⟨900090052452220333605149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2400240139872587556280397 900090052452220333605149)
                  ·
                    refine ⟨337533769669582625101931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 900090052452220333605149 337533769669582625101931)
                    ·
                      rfl

theorem cell22_986017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_986017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_986017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_986017 prefixEnd_986017 := by exact prefixLift 986017
  have htrace : WordTrace (prefixWord ++ tailWord_986017) baseStart_986017 baseEnd_986017 := by
    simpa [prefixWord, tailWord_986017, baseEnd_986017] using wordTrace_append hprefix tailTrace_986017
  have hstable : (prefixWord ++ tailWord_986017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986017).length < 2 ^ (prefixWord ++ tailWord_986017).sum := by decide
  have hdescent : baseEnd_986017 < baseStart_986017 := by decide
  rcases family_descends (prefixWord ++ tailWord_986017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986090 : List Nat := [3, 1, 3, 1, 2, 2, 1, 3, 1, 5]
def baseStart_986090 : Nat := 118140960795 + 986090 * 2 ^ 59
def prefixEnd_986090 : Nat := 4983230072969 + 3 ^ 40 * 986090 * 2
def baseEnd_986090 : Nat := 337558759061434768026707

theorem tailTrace_986090 : CollatzResearch.WordTrace tailWord_986090 prefixEnd_986090 337558759061434768026707 := by
  unfold tailWord_986090
  simp only [CollatzResearch.WordTrace]
  refine ⟨8991414249392953902310931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23977104665047877072829149 8991414249392953902310931)
  ·
    refine ⟨13487121374089430853466397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8991414249392953902310931 13487121374089430853466397)
    ·
      refine ⟨5057670515283536570049899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13487121374089430853466397 5057670515283536570049899)
      ·
        refine ⟨7586505772925304855074849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5057670515283536570049899 7586505772925304855074849)
        ·
          refine ⟨5689879329693978641306137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7586505772925304855074849 5689879329693978641306137)
          ·
            refine ⟨4267409497270483980979603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5689879329693978641306137 4267409497270483980979603)
            ·
              refine ⟨6401114245905725971469405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4267409497270483980979603 6401114245905725971469405)
              ·
                refine ⟨2400417842214647239301027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6401114245905725971469405 2400417842214647239301027)
                ·
                  refine ⟨3600626763321970858951541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2400417842214647239301027 3600626763321970858951541)
                  ·
                    refine ⟨337558759061434768026707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3600626763321970858951541 337558759061434768026707)
                    ·
                      rfl

theorem cell22_986090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_986090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_986090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_986090 prefixEnd_986090 := by exact prefixLift 986090
  have htrace : WordTrace (prefixWord ++ tailWord_986090) baseStart_986090 baseEnd_986090 := by
    simpa [prefixWord, tailWord_986090, baseEnd_986090] using wordTrace_append hprefix tailTrace_986090
  have hstable : (prefixWord ++ tailWord_986090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986090).length < 2 ^ (prefixWord ++ tailWord_986090).sum := by decide
  have hdescent : baseEnd_986090 < baseStart_986090 := by decide
  rcases family_descends (prefixWord ++ tailWord_986090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986124 : List Nat := [2, 2, 1, 2, 3, 4, 1, 2, 2, 3]
def baseStart_986124 : Nat := 118140960795 + 986124 * 2 ^ 59
def prefixEnd_986124 : Nat := 4983230072969 + 3 ^ 40 * 986124 * 2
def baseEnd_986124 : Nat := 337570397956270012676603

theorem tailTrace_986124 : CollatzResearch.WordTrace tailWord_986124 prefixEnd_986124 337570397956270012676603 := by
  unfold tailWord_986124
  simp only [CollatzResearch.WordTrace]
  refine ⟨17983448539724319707990713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23977931386299092943987617 17983448539724319707990713)
  ·
    refine ⟨13487586404793239780993035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17983448539724319707990713 13487586404793239780993035)
    ·
      refine ⟨20231379607189859671489553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13487586404793239780993035 20231379607189859671489553)
      ·
        refine ⟨15173534705392394753617165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20231379607189859671489553 15173534705392394753617165)
        ·
          refine ⟨5690075514522148032606437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15173534705392394753617165 5690075514522148032606437)
          ·
            refine ⟨1066889158972902756113707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5690075514522148032606437 1066889158972902756113707)
            ·
              refine ⟨1600333738459354134170561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1066889158972902756113707 1600333738459354134170561)
              ·
                refine ⟨1200250303844515600627921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1600333738459354134170561 1200250303844515600627921)
                ·
                  refine ⟨900187727883386700470941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1200250303844515600627921 900187727883386700470941)
                  ·
                    refine ⟨337570397956270012676603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 900187727883386700470941 337570397956270012676603)
                    ·
                      rfl

theorem cell22_986124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 2, 3].length) (baseStart_986124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_986124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_986124 prefixEnd_986124 := by exact prefixLift 986124
  have htrace : WordTrace (prefixWord ++ tailWord_986124) baseStart_986124 baseEnd_986124 := by
    simpa [prefixWord, tailWord_986124, baseEnd_986124] using wordTrace_append hprefix tailTrace_986124
  have hstable : (prefixWord ++ tailWord_986124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986124).length < 2 ^ (prefixWord ++ tailWord_986124).sum := by decide
  have hdescent : baseEnd_986124 < baseStart_986124 := by decide
  rcases family_descends (prefixWord ++ tailWord_986124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_986141 : List Nat := [1, 4, 2, 2, 3, 1, 3, 1, 2, 3]
def baseStart_986141 : Nat := 118140960795 + 986141 * 2 ^ 59
def prefixEnd_986141 : Nat := 4983230072969 + 3 ^ 40 * 986141 * 2
def baseEnd_986141 : Nat := 337576217403687635001551

theorem tailTrace_986141 : CollatzResearch.WordTrace tailWord_986141 prefixEnd_986141 337576217403687635001551 := by
  unfold tailWord_986141
  simp only [CollatzResearch.WordTrace]
  refine ⟨35967517120387051319350277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23978344746924700879566851 35967517120387051319350277)
  ·
    refine ⟨6743909460072572122378177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35967517120387051319350277 6743909460072572122378177)
    ·
      refine ⟨5057932095054429091783633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6743909460072572122378177 5057932095054429091783633)
      ·
        refine ⟨3793449071290821818837725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5057932095054429091783633 3793449071290821818837725)
        ·
          refine ⟨1422543401734058182064147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3793449071290821818837725 1422543401734058182064147)
          ·
            refine ⟨2133815102601087273096221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1422543401734058182064147 2133815102601087273096221)
            ·
              refine ⟨800180663475407727411083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2133815102601087273096221 800180663475407727411083)
              ·
                refine ⟨1200270995213111591116625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 800180663475407727411083 1200270995213111591116625)
                ·
                  refine ⟨900203246409833693337469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1200270995213111591116625 900203246409833693337469)
                  ·
                    refine ⟨337576217403687635001551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 900203246409833693337469 337576217403687635001551)
                    ·
                      rfl

theorem cell22_986141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_986141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_986141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_986141 prefixEnd_986141 := by exact prefixLift 986141
  have htrace : WordTrace (prefixWord ++ tailWord_986141) baseStart_986141 baseEnd_986141 := by
    simpa [prefixWord, tailWord_986141, baseEnd_986141] using wordTrace_append hprefix tailTrace_986141
  have hstable : (prefixWord ++ tailWord_986141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_986141).length < 2 ^ (prefixWord ++ tailWord_986141).sum := by decide
  have hdescent : baseEnd_986141 < baseStart_986141 := by decide
  rcases family_descends (prefixWord ++ tailWord_986141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
