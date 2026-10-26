import V185TrunkScan22Chunk083

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_753498 : List Nat := [3, 1, 1, 2, 1, 3, 1, 4, 6]
def baseStart_753498 : Nat := 118140960795 + 753498 * 2 ^ 59
def prefixEnd_753498 : Nat := 4983230072969 + 3 ^ 40 * 753498 * 2
def baseEnd_753498 : Nat := 85979254711466259846607

theorem tailTrace_753498 : CollatzResearch.WordTrace tailWord_753498 prefixEnd_753498 85979254711466259846607 := by
  unfold tailWord_753498
  simp only [CollatzResearch.WordTrace]
  refine ⟨6870582456053227014549287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18321553216141938705464765 6870582456053227014549287)
  ·
    refine ⟨10305873684079840521823931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6870582456053227014549287 10305873684079840521823931)
    ·
      refine ⟨15458810526119760782735897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10305873684079840521823931 15458810526119760782735897)
      ·
        refine ⟨11594107894589820587051923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15458810526119760782735897 11594107894589820587051923)
        ·
          refine ⟨17391161841884730880577885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11594107894589820587051923 17391161841884730880577885)
          ·
            refine ⟨6521685690706774080216707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17391161841884730880577885 6521685690706774080216707)
            ·
              refine ⟨9782528536060161120325061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6521685690706774080216707 9782528536060161120325061)
              ·
                refine ⟨1834224100511280210060949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9782528536060161120325061 1834224100511280210060949)
                ·
                  refine ⟨85979254711466259846607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1834224100511280210060949 85979254711466259846607)
                  ·
                    rfl

theorem cell22_753498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 6].length) (baseStart_753498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753498 prefixEnd_753498 := by exact prefixLift 753498
  have htrace : WordTrace (prefixWord ++ tailWord_753498) baseStart_753498 baseEnd_753498 := by
    simpa [prefixWord, tailWord_753498, baseEnd_753498] using wordTrace_append hprefix tailTrace_753498
  have hstable : (prefixWord ++ tailWord_753498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753498).length < 2 ^ (prefixWord ++ tailWord_753498).sum := by decide
  have hdescent : baseEnd_753498 < baseStart_753498 := by decide
  rcases family_descends (prefixWord ++ tailWord_753498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753513 : List Nat := [1, 2, 1, 1, 1, 3, 1, 6, 1, 5]
def baseStart_753513 : Nat := 118140960795 + 753513 * 2 ^ 59
def prefixEnd_753513 : Nat := 4983230072969 + 3 ^ 40 * 753513 * 2
def baseEnd_753513 : Nat := 257942898940943740414775

theorem tailTrace_753513 : CollatzResearch.WordTrace tailWord_753513 prefixEnd_753513 257942898940943740414775 := by
  unfold tailWord_753513
  simp only [CollatzResearch.WordTrace]
  refine ⟨27482876919158565619993193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18321917946105710413328795 27482876919158565619993193)
  ·
    refine ⟨20612157689368924214994895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27482876919158565619993193 20612157689368924214994895)
    ·
      refine ⟨30918236534053386322492343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20612157689368924214994895 30918236534053386322492343)
      ·
        refine ⟨46377354801080079483738515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30918236534053386322492343 46377354801080079483738515)
        ·
          refine ⟨69566032201620119225607773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46377354801080079483738515 69566032201620119225607773)
          ·
            refine ⟨26087262075607544709602915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69566032201620119225607773 26087262075607544709602915)
            ·
              refine ⟨39130893113411317064404373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26087262075607544709602915 39130893113411317064404373)
              ·
                refine ⟨1834260614691155487393955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39130893113411317064404373 1834260614691155487393955)
                ·
                  refine ⟨2751390922036733231090933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1834260614691155487393955 2751390922036733231090933)
                  ·
                    refine ⟨257942898940943740414775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2751390922036733231090933 257942898940943740414775)
                    ·
                      rfl

theorem cell22_753513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 5].length) (baseStart_753513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753513 prefixEnd_753513 := by exact prefixLift 753513
  have htrace : WordTrace (prefixWord ++ tailWord_753513) baseStart_753513 baseEnd_753513 := by
    simpa [prefixWord, tailWord_753513, baseEnd_753513] using wordTrace_append hprefix tailTrace_753513
  have hstable : (prefixWord ++ tailWord_753513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753513).length < 2 ^ (prefixWord ++ tailWord_753513).sum := by decide
  have hdescent : baseEnd_753513 < baseStart_753513 := by decide
  rcases family_descends (prefixWord ++ tailWord_753513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753530 : List Nat := [3, 1, 1, 1, 1, 1, 6, 1, 4, 3]
def baseStart_753530 : Nat := 118140960795 + 753530 * 2 ^ 59
def prefixEnd_753530 : Nat := 4983230072969 + 3 ^ 40 * 753530 * 2
def baseEnd_753530 : Nat := 257948718388361362739723

theorem tailTrace_753530 : CollatzResearch.WordTrace tailWord_753530 prefixEnd_753530 257948718388361362739723 := by
  unfold tailWord_753530
  simp only [CollatzResearch.WordTrace]
  refine ⟨6870874240024244380840511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18322331306731318348908029 6870874240024244380840511)
  ·
    refine ⟨10306311360036366571260767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6870874240024244380840511 10306311360036366571260767)
    ·
      refine ⟨15459467040054549856891151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10306311360036366571260767 15459467040054549856891151)
      ·
        refine ⟨23189200560081824785336727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15459467040054549856891151 23189200560081824785336727)
        ·
          refine ⟨34783800840122737178005091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23189200560081824785336727 34783800840122737178005091)
          ·
            refine ⟨52175701260184105767007637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34783800840122737178005091 52175701260184105767007637)
            ·
              refine ⟨2445735996571129957828483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52175701260184105767007637 2445735996571129957828483)
              ·
                refine ⟨3668603994856694936742725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2445735996571129957828483 3668603994856694936742725)
                ·
                  refine ⟨687863249035630300639261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3668603994856694936742725 687863249035630300639261)
                  ·
                    refine ⟨257948718388361362739723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 687863249035630300639261 257948718388361362739723)
                    ·
                      rfl

theorem cell22_753530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 4, 3].length) (baseStart_753530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753530 prefixEnd_753530 := by exact prefixLift 753530
  have htrace : WordTrace (prefixWord ++ tailWord_753530) baseStart_753530 baseEnd_753530 := by
    simpa [prefixWord, tailWord_753530, baseEnd_753530] using wordTrace_append hprefix tailTrace_753530
  have hstable : (prefixWord ++ tailWord_753530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753530).length < 2 ^ (prefixWord ++ tailWord_753530).sum := by decide
  have hdescent : baseEnd_753530 < baseStart_753530 := by decide
  rcases family_descends (prefixWord ++ tailWord_753530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753562 : List Nat := [3, 1, 1, 4, 2, 2, 2, 1, 2, 4]
def baseStart_753562 : Nat := 118140960795 + 753562 * 2 ^ 59
def prefixEnd_753562 : Nat := 4983230072969 + 3 ^ 40 * 753562 * 2
def baseEnd_753562 : Nat := 257959672642323945939625

theorem tailTrace_753562 : CollatzResearch.WordTrace tailWord_753562 prefixEnd_753562 257959672642323945939625 := by
  unfold tailWord_753562
  simp only [CollatzResearch.WordTrace]
  refine ⟨6871166023995261747131735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18323109397320697992351293 6871166023995261747131735)
  ·
    refine ⟨10306749035992892620697603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6871166023995261747131735 10306749035992892620697603)
    ·
      refine ⟨15460123553989338931046405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10306749035992892620697603 15460123553989338931046405)
      ·
        refine ⟨2898773166373001049571201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15460123553989338931046405 2898773166373001049571201)
        ·
          refine ⟨2174079874779750787178401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2898773166373001049571201 2174079874779750787178401)
          ·
            refine ⟨1630559906084813090383801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2174079874779750787178401 1630559906084813090383801)
            ·
              refine ⟨1222919929563609817787851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1630559906084813090383801 1222919929563609817787851)
              ·
                refine ⟨1834379894345414726681777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1222919929563609817787851 1834379894345414726681777)
                ·
                  refine ⟨1375784920759061045011333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1834379894345414726681777 1375784920759061045011333)
                  ·
                    refine ⟨257959672642323945939625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1375784920759061045011333 257959672642323945939625)
                    ·
                      rfl

theorem cell22_753562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 2, 4].length) (baseStart_753562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753562 prefixEnd_753562 := by exact prefixLift 753562
  have htrace : WordTrace (prefixWord ++ tailWord_753562) baseStart_753562 baseEnd_753562 := by
    simpa [prefixWord, tailWord_753562, baseEnd_753562] using wordTrace_append hprefix tailTrace_753562
  have hstable : (prefixWord ++ tailWord_753562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753562).length < 2 ^ (prefixWord ++ tailWord_753562).sum := by decide
  have hdescent : baseEnd_753562 < baseStart_753562 := by decide
  rcases family_descends (prefixWord ++ tailWord_753562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753573 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 4, 6]
def baseStart_753573 : Nat := 118140960795 + 753573 * 2 ^ 59
def prefixEnd_753573 : Nat := 4983230072969 + 3 ^ 40 * 753573 * 2
def baseEnd_753573 : Nat := 257963438167123583914591

theorem tailTrace_753573 : CollatzResearch.WordTrace tailWord_753573 prefixEnd_753573 257963438167123583914591 := by
  unfold tailWord_753573
  simp only [CollatzResearch.WordTrace]
  refine ⟨27485065298941195867177373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18323376865960797244784915 27485065298941195867177373)
  ·
    refine ⟨10306899487102948450191515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27485065298941195867177373 10306899487102948450191515)
    ·
      refine ⟨15460349230654422675287273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10306899487102948450191515 15460349230654422675287273)
      ·
        refine ⟨11595261922990817006465455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15460349230654422675287273 11595261922990817006465455)
        ·
          refine ⟨17392892884486225509698183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11595261922990817006465455 17392892884486225509698183)
          ·
            refine ⟨26089339326729338264547275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17392892884486225509698183 26089339326729338264547275)
            ·
              refine ⟨39134008990094007396820913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26089339326729338264547275 39134008990094007396820913)
              ·
                refine ⟨29350506742570505547615685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39134008990094007396820913 29350506742570505547615685)
                ·
                  refine ⟨5503220014231969790177941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29350506742570505547615685 5503220014231969790177941)
                  ·
                    refine ⟨257963438167123583914591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5503220014231969790177941 257963438167123583914591)
                    ·
                      rfl

theorem cell22_753573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_753573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753573 prefixEnd_753573 := by exact prefixLift 753573
  have htrace : WordTrace (prefixWord ++ tailWord_753573) baseStart_753573 baseEnd_753573 := by
    simpa [prefixWord, tailWord_753573, baseEnd_753573] using wordTrace_append hprefix tailTrace_753573
  have hstable : (prefixWord ++ tailWord_753573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753573).length < 2 ^ (prefixWord ++ tailWord_753573).sum := by decide
  have hdescent : baseEnd_753573 < baseStart_753573 := by decide
  rcases family_descends (prefixWord ++ tailWord_753573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753620 : List Nat := [2, 4, 1, 2, 1, 1, 1, 2, 1, 7]
def baseStart_753620 : Nat := 118140960795 + 753620 * 2 ^ 59
def prefixEnd_753620 : Nat := 4983230072969 + 3 ^ 40 * 753620 * 2
def baseEnd_753620 : Nat := 257979527227631127989447

theorem tailTrace_753620 : CollatzResearch.WordTrace tailWord_753620 prefixEnd_753620 257979527227631127989447 := by
  unfold tailWord_753620
  simp only [CollatzResearch.WordTrace]
  refine ⟨13743389764885461447069157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18324519686513948596092209 13743389764885461447069157)
  ·
    refine ⟨2576885580916024021325467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13743389764885461447069157 2576885580916024021325467)
    ·
      refine ⟨3865328371374036031988201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2576885580916024021325467 3865328371374036031988201)
      ·
        refine ⟨2898996278530527023991151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3865328371374036031988201 2898996278530527023991151)
        ·
          refine ⟨4348494417795790535986727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2898996278530527023991151 4348494417795790535986727)
          ·
            refine ⟨6522741626693685803980091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4348494417795790535986727 6522741626693685803980091)
            ·
              refine ⟨9784112440040528705970137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6522741626693685803980091 9784112440040528705970137)
              ·
                refine ⟨7338084330030396529477603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9784112440040528705970137 7338084330030396529477603)
                ·
                  refine ⟨11007126495045594794216405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7338084330030396529477603 11007126495045594794216405)
                  ·
                    refine ⟨257979527227631127989447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11007126495045594794216405 257979527227631127989447)
                    ·
                      rfl

theorem cell22_753620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_753620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753620 prefixEnd_753620 := by exact prefixLift 753620
  have htrace : WordTrace (prefixWord ++ tailWord_753620) baseStart_753620 baseEnd_753620 := by
    simpa [prefixWord, tailWord_753620, baseEnd_753620] using wordTrace_append hprefix tailTrace_753620
  have hstable : (prefixWord ++ tailWord_753620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753620).length < 2 ^ (prefixWord ++ tailWord_753620).sum := by decide
  have hdescent : baseEnd_753620 < baseStart_753620 := by decide
  rcases family_descends (prefixWord ++ tailWord_753620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753626 : List Nat := [3, 1, 1, 2, 5, 1, 2, 3, 1, 3]
def baseStart_753626 : Nat := 118140960795 + 753626 * 2 ^ 59
def prefixEnd_753626 : Nat := 4983230072969 + 3 ^ 40 * 753626 * 2
def baseEnd_753626 : Nat := 257981581150249112339429

theorem tailTrace_753626 : CollatzResearch.WordTrace tailWord_753626 prefixEnd_753626 257981581150249112339429 := by
  unfold tailWord_753626
  simp only [CollatzResearch.WordTrace]
  refine ⟨6871749591937296479714183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18324665578499457279237821 6871749591937296479714183)
  ·
    refine ⟨10307624387905944719571275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6871749591937296479714183 10307624387905944719571275)
    ·
      refine ⟨15461436581858917079356913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10307624387905944719571275 15461436581858917079356913)
      ·
        refine ⟨11596077436394187809517685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15461436581858917079356913 11596077436394187809517685)
        ·
          refine ⟨1087132259661955107142283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11596077436394187809517685 1087132259661955107142283)
          ·
            refine ⟨1630698389492932660713425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1087132259661955107142283 1630698389492932660713425)
            ·
              refine ⟨1223023792119699495535069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1630698389492932660713425 1223023792119699495535069)
              ·
                refine ⟨458633922044887310825651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1223023792119699495535069 458633922044887310825651)
                ·
                  refine ⟨687950883067330966238477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 458633922044887310825651 687950883067330966238477)
                  ·
                    refine ⟨257981581150249112339429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 687950883067330966238477 257981581150249112339429)
                    ·
                      rfl

theorem cell22_753626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 3, 1, 3].length) (baseStart_753626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753626 prefixEnd_753626 := by exact prefixLift 753626
  have htrace : WordTrace (prefixWord ++ tailWord_753626) baseStart_753626 baseEnd_753626 := by
    simpa [prefixWord, tailWord_753626, baseEnd_753626] using wordTrace_append hprefix tailTrace_753626
  have hstable : (prefixWord ++ tailWord_753626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753626).length < 2 ^ (prefixWord ++ tailWord_753626).sum := by decide
  have hdescent : baseEnd_753626 < baseStart_753626 := by decide
  rcases family_descends (prefixWord ++ tailWord_753626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753639 : List Nat := [1, 1, 5, 2, 3, 2, 1, 2, 5]
def baseStart_753639 : Nat := 118140960795 + 753639 * 2 ^ 59
def prefixEnd_753639 : Nat := 4983230072969 + 3 ^ 40 * 753639 * 2
def baseEnd_753639 : Nat := 85995343771973803921463

theorem tailTrace_753639 : CollatzResearch.WordTrace tailWord_753639 prefixEnd_753639 85995343771973803921463 := by
  unfold tailWord_753639
  simp only [CollatzResearch.WordTrace]
  refine ⟨27487472516702089139079971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18324981677801392759386647 27487472516702089139079971)
  ·
    refine ⟨41231208775053133708619957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27487472516702089139079971 41231208775053133708619957)
    ·
      refine ⟨3865425822661231285183121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41231208775053133708619957 3865425822661231285183121)
      ·
        refine ⟨2899069366995923463887341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3865425822661231285183121 2899069366995923463887341)
        ·
          refine ⟨1087151012623471298957753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2899069366995923463887341 1087151012623471298957753)
          ·
            refine ⟨815363259467603474218315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1087151012623471298957753 815363259467603474218315)
            ·
              refine ⟨1223044889201405211327473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 815363259467603474218315 1223044889201405211327473)
              ·
                refine ⟨917283666901053908495605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1223044889201405211327473 917283666901053908495605)
                ·
                  refine ⟨85995343771973803921463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 917283666901053908495605 85995343771973803921463)
                  ·
                    rfl

theorem cell22_753639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 5].length) (baseStart_753639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753639 prefixEnd_753639 := by exact prefixLift 753639
  have htrace : WordTrace (prefixWord ++ tailWord_753639) baseStart_753639 baseEnd_753639 := by
    simpa [prefixWord, tailWord_753639, baseEnd_753639] using wordTrace_append hprefix tailTrace_753639
  have hstable : (prefixWord ++ tailWord_753639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753639).length < 2 ^ (prefixWord ++ tailWord_753639).sum := by decide
  have hdescent : baseEnd_753639 < baseStart_753639 := by decide
  rcases family_descends (prefixWord ++ tailWord_753639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753677 : List Nat := [1, 7, 1, 2, 1, 2, 1, 3, 1, 3]
def baseStart_753677 : Nat := 118140960795 + 753677 * 2 ^ 59
def prefixEnd_753677 : Nat := 4983230072969 + 3 ^ 40 * 753677 * 2
def baseEnd_753677 : Nat := 257999039492501979314273

theorem tailTrace_753677 : CollatzResearch.WordTrace tailWord_753677 prefixEnd_753677 257999039492501979314273 := by
  unfold tailWord_753677
  simp only [CollatzResearch.WordTrace]
  refine ⟨27488858490564421628963285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18325905660376281085975523 27488858490564421628963285)
  ·
    refine ⟨644270120872603631928827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 27488858490564421628963285 644270120872603631928827)
    ·
      refine ⟨966405181308905447893241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 644270120872603631928827 966405181308905447893241)
      ·
        refine ⟨724803885981679085919931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 966405181308905447893241 724803885981679085919931)
        ·
          refine ⟨1087205828972518628879897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 724803885981679085919931 1087205828972518628879897)
          ·
            refine ⟨815404371729388971659923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1087205828972518628879897 815404371729388971659923)
            ·
              refine ⟨1223106557594083457489885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 815404371729388971659923 1223106557594083457489885)
              ·
                refine ⟨458664959097781296558707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1223106557594083457489885 458664959097781296558707)
                ·
                  refine ⟨687997438646671944838061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 458664959097781296558707 687997438646671944838061)
                  ·
                    refine ⟨257999039492501979314273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 687997438646671944838061 257999039492501979314273)
                    ·
                      rfl

theorem cell22_753677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_753677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753677 prefixEnd_753677 := by exact prefixLift 753677
  have htrace : WordTrace (prefixWord ++ tailWord_753677) baseStart_753677 baseEnd_753677 := by
    simpa [prefixWord, tailWord_753677, baseEnd_753677] using wordTrace_append hprefix tailTrace_753677
  have hstable : (prefixWord ++ tailWord_753677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753677).length < 2 ^ (prefixWord ++ tailWord_753677).sum := by decide
  have hdescent : baseEnd_753677 < baseStart_753677 := by decide
  rcases family_descends (prefixWord ++ tailWord_753677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753727 : List Nat := [1, 1, 2, 2, 3, 1, 2, 4, 3, 3]
def baseStart_753727 : Nat := 118140960795 + 753727 * 2 ^ 59
def prefixEnd_753727 : Nat := 4983230072969 + 3 ^ 40 * 753727 * 2
def baseEnd_753727 : Nat := 258016155514318515564119

theorem tailTrace_753727 : CollatzResearch.WordTrace tailWord_753727 prefixEnd_753727 258016155514318515564119 := by
  unfold tailWord_753727
  simp only [CollatzResearch.WordTrace]
  refine ⟨27490682140383280168283435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18327121426922186778855623 27490682140383280168283435)
  ·
    refine ⟨41236023210574920252425153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27490682140383280168283435 41236023210574920252425153)
    ·
      refine ⟨30927017407931190189318865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41236023210574920252425153 30927017407931190189318865)
      ·
        refine ⟨23195263055948392641989149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30927017407931190189318865 23195263055948392641989149)
        ·
          refine ⟨8698223645980647240745931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23195263055948392641989149 8698223645980647240745931)
          ·
            refine ⟨13047335468970970861118897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8698223645980647240745931 13047335468970970861118897)
            ·
              refine ⟨9785501601728228145839173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13047335468970970861118897 9785501601728228145839173)
              ·
                refine ⟨1834781550324042777344845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9785501601728228145839173 1834781550324042777344845)
                ·
                  refine ⟨688043081371516041504317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1834781550324042777344845 688043081371516041504317)
                  ·
                    refine ⟨258016155514318515564119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 688043081371516041504317 258016155514318515564119)
                    ·
                      rfl

theorem cell22_753727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 3, 3].length) (baseStart_753727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753727 prefixEnd_753727 := by exact prefixLift 753727
  have htrace : WordTrace (prefixWord ++ tailWord_753727) baseStart_753727 baseEnd_753727 := by
    simpa [prefixWord, tailWord_753727, baseEnd_753727] using wordTrace_append hprefix tailTrace_753727
  have hstable : (prefixWord ++ tailWord_753727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753727).length < 2 ^ (prefixWord ++ tailWord_753727).sum := by decide
  have hdescent : baseEnd_753727 < baseStart_753727 := by decide
  rcases family_descends (prefixWord ++ tailWord_753727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753740 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 9]
def baseStart_753740 : Nat := 118140960795 + 753740 * 2 ^ 59
def prefixEnd_753740 : Nat := 4983230072969 + 3 ^ 40 * 753740 * 2
def baseEnd_753740 : Nat := 86006868559996938329693

theorem tailTrace_753740 : CollatzResearch.WordTrace tailWord_753740 prefixEnd_753740 86006868559996938329693 := by
  unfold tailWord_753740
  simp only [CollatzResearch.WordTrace]
  refine ⟨13745578144668091694253337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18327437526224122259004449 13745578144668091694253337)
  ·
    refine ⟨10309183608501068770690003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13745578144668091694253337 10309183608501068770690003)
    ·
      refine ⟨15463775412751603156035005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10309183608501068770690003 15463775412751603156035005)
      ·
        refine ⟨5798915779781851183513127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15463775412751603156035005 5798915779781851183513127)
        ·
          refine ⟨8698373669672776775269691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5798915779781851183513127 8698373669672776775269691)
          ·
            refine ⟨13047560504509165162904537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8698373669672776775269691 13047560504509165162904537)
            ·
              refine ⟨9785670378381873872178403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13047560504509165162904537 9785670378381873872178403)
              ·
                refine ⟨14678505567572810808267605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9785670378381873872178403 14678505567572810808267605)
                ·
                  refine ⟨86006868559996938329693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 14678505567572810808267605 86006868559996938329693)
                  ·
                    rfl

theorem cell22_753740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 9].length) (baseStart_753740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753740 prefixEnd_753740 := by exact prefixLift 753740
  have htrace : WordTrace (prefixWord ++ tailWord_753740) baseStart_753740 baseEnd_753740 := by
    simpa [prefixWord, tailWord_753740, baseEnd_753740] using wordTrace_append hprefix tailTrace_753740
  have hstable : (prefixWord ++ tailWord_753740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753740).length < 2 ^ (prefixWord ++ tailWord_753740).sum := by decide
  have hdescent : baseEnd_753740 < baseStart_753740 := by decide
  rcases family_descends (prefixWord ++ tailWord_753740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753772 : List Nat := [2, 2, 1, 1, 3, 4, 1, 1, 2, 5]
def baseStart_753772 : Nat := 118140960795 + 753772 * 2 ^ 59
def prefixEnd_753772 : Nat := 4983230072969 + 3 ^ 40 * 753772 * 2
def baseEnd_753772 : Nat := 258031559933953398188981

theorem tailTrace_753772 : CollatzResearch.WordTrace tailWord_753772 prefixEnd_753772 258031559933953398188981 := by
  unfold tailWord_753772
  simp only [CollatzResearch.WordTrace]
  refine ⟨13746161712610126426835785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18328215616813501902447713 13746161712610126426835785)
  ·
    refine ⟨10309621284457594820126839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13746161712610126426835785 10309621284457594820126839)
    ·
      refine ⟨15464431926686392230190259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10309621284457594820126839 15464431926686392230190259)
      ·
        refine ⟨23196647890029588345285389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15464431926686392230190259 23196647890029588345285389)
        ·
          refine ⟨8698742958761095629482021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23196647890029588345285389 8698742958761095629482021)
          ·
            refine ⟨1631014304767705430527879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8698742958761095629482021 1631014304767705430527879)
            ·
              refine ⟨2446521457151558145791819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1631014304767705430527879 2446521457151558145791819)
              ·
                refine ⟨3669782185727337218687729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2446521457151558145791819 3669782185727337218687729)
                ·
                  refine ⟨2752336639295502914015797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3669782185727337218687729 2752336639295502914015797)
                  ·
                    refine ⟨258031559933953398188981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2752336639295502914015797 258031559933953398188981)
                    ·
                      rfl

theorem cell22_753772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_753772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753772 prefixEnd_753772 := by exact prefixLift 753772
  have htrace : WordTrace (prefixWord ++ tailWord_753772) baseStart_753772 baseEnd_753772 := by
    simpa [prefixWord, tailWord_753772, baseEnd_753772] using wordTrace_append hprefix tailTrace_753772
  have hstable : (prefixWord ++ tailWord_753772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753772).length < 2 ^ (prefixWord ++ tailWord_753772).sum := by decide
  have hdescent : baseEnd_753772 < baseStart_753772 := by decide
  rcases family_descends (prefixWord ++ tailWord_753772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753847 : List Nat := [1, 1, 3, 1, 4, 3, 1, 8]
def baseStart_753847 : Nat := 118140960795 + 753847 * 2 ^ 59
def prefixEnd_753847 : Nat := 4983230072969 + 3 ^ 40 * 753847 * 2
def baseEnd_753847 : Nat := 28673025996297578062639

theorem tailTrace_753847 : CollatzResearch.WordTrace tailWord_753847 prefixEnd_753847 28673025996297578062639 := by
  unfold tailWord_753847
  simp only [CollatzResearch.WordTrace]
  refine ⟨27495058899948540662651795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18330039266632360441767863 27495058899948540662651795)
  ·
    refine ⟨41242588349922810993977693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27495058899948540662651795 41242588349922810993977693)
    ·
      refine ⟨15465970631221054122741635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41242588349922810993977693 15465970631221054122741635)
      ·
        refine ⟨23198955946831581184112453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15465970631221054122741635 23198955946831581184112453)
        ·
          refine ⟨4349804240030921472021085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23198955946831581184112453 4349804240030921472021085)
          ·
            refine ⟨1631176590011595552007907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4349804240030921472021085 1631176590011595552007907)
            ·
              refine ⟨2446764885017393328011861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1631176590011595552007907 2446764885017393328011861)
              ·
                refine ⟨28673025996297578062639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2446764885017393328011861 28673025996297578062639)
                ·
                  rfl

theorem cell22_753847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 8].length) (baseStart_753847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753847 prefixEnd_753847 := by exact prefixLift 753847
  have htrace : WordTrace (prefixWord ++ tailWord_753847) baseStart_753847 baseEnd_753847 := by
    simpa [prefixWord, tailWord_753847, baseEnd_753847] using wordTrace_append hprefix tailTrace_753847
  have hstable : (prefixWord ++ tailWord_753847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753847).length < 2 ^ (prefixWord ++ tailWord_753847).sum := by decide
  have hdescent : baseEnd_753847 < baseStart_753847 := by decide
  rcases family_descends (prefixWord ++ tailWord_753847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753885 : List Nat := [1, 4, 3, 2, 1, 3, 2, 1, 2, 3]
def baseStart_753885 : Nat := 118140960795 + 753885 * 2 ^ 59
def prefixEnd_753885 : Nat := 4983230072969 + 3 ^ 40 * 753885 * 2
def baseEnd_753885 : Nat := 258070242143258770113635

theorem tailTrace_753885 : CollatzResearch.WordTrace tailWord_753885 prefixEnd_753885 258070242143258770113635 := by
  unfold tailWord_753885
  simp only [CollatzResearch.WordTrace]
  refine ⟨27496444873810873152535109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18330963249207248768356739 27496444873810873152535109)
  ·
    refine ⟨5155583413839538716100333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27496444873810873152535109 5155583413839538716100333)
    ·
      refine ⟨1933343780189827018537625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5155583413839538716100333 1933343780189827018537625)
      ·
        refine ⟨1450007835142370263903219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1933343780189827018537625 1450007835142370263903219)
        ·
          refine ⟨2175011752713555395854829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1450007835142370263903219 2175011752713555395854829)
          ·
            refine ⟨815629407267583273445561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2175011752713555395854829 815629407267583273445561)
            ·
              refine ⟨611722055450687455084171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 815629407267583273445561 611722055450687455084171)
              ·
                refine ⟨917583083176031182626257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 611722055450687455084171 917583083176031182626257)
                ·
                  refine ⟨688187312382023386969693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 917583083176031182626257 688187312382023386969693)
                  ·
                    refine ⟨258070242143258770113635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 688187312382023386969693 258070242143258770113635)
                    ·
                      rfl

theorem cell22_753885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_753885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753885 prefixEnd_753885 := by exact prefixLift 753885
  have htrace : WordTrace (prefixWord ++ tailWord_753885) baseStart_753885 baseEnd_753885 := by
    simpa [prefixWord, tailWord_753885, baseEnd_753885] using wordTrace_append hprefix tailTrace_753885
  have hstable : (prefixWord ++ tailWord_753885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753885).length < 2 ^ (prefixWord ++ tailWord_753885).sum := by decide
  have hdescent : baseEnd_753885 < baseStart_753885 := by decide
  rcases family_descends (prefixWord ++ tailWord_753885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753954 : List Nat := [3, 3, 1, 1, 3, 1, 1, 1, 8]
def baseStart_753954 : Nat := 118140960795 + 753954 * 2 ^ 59
def prefixEnd_753954 : Nat := 4983230072969 + 3 ^ 40 * 753954 * 2
def baseEnd_753954 : Nat := 86031287417788530046141

theorem tailTrace_753954 : CollatzResearch.WordTrace tailWord_753954 prefixEnd_753954 86031287417788530046141 := by
  unfold tailWord_753954
  simp only [CollatzResearch.WordTrace]
  refine ⟨6874740377640224484199229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18332641007040598624531277 6874740377640224484199229)
  ·
    refine ⟨2578027641615084181574711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6874740377640224484199229 2578027641615084181574711)
    ·
      refine ⟨3867041462422626272362067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2578027641615084181574711 3867041462422626272362067)
      ·
        refine ⟨5800562193633939408543101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3867041462422626272362067 5800562193633939408543101)
        ·
          refine ⟨2175210822612727278203663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5800562193633939408543101 2175210822612727278203663)
          ·
            refine ⟨3262816233919090917305495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2175210822612727278203663 3262816233919090917305495)
            ·
              refine ⟨4894224350878636375958243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3262816233919090917305495 4894224350878636375958243)
              ·
                refine ⟨7341336526317954563937365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4894224350878636375958243 7341336526317954563937365)
                ·
                  refine ⟨86031287417788530046141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7341336526317954563937365 86031287417788530046141)
                  ·
                    rfl

theorem cell22_753954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_753954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753954 prefixEnd_753954 := by exact prefixLift 753954
  have htrace : WordTrace (prefixWord ++ tailWord_753954) baseStart_753954 baseEnd_753954 := by
    simpa [prefixWord, tailWord_753954, baseEnd_753954] using wordTrace_append hprefix tailTrace_753954
  have hstable : (prefixWord ++ tailWord_753954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753954).length < 2 ^ (prefixWord ++ tailWord_753954).sum := by decide
  have hdescent : baseEnd_753954 < baseStart_753954 := by decide
  rcases family_descends (prefixWord ++ tailWord_753954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753971 : List Nat := [1, 1, 1, 2, 5, 1, 4, 3, 4]
def baseStart_753971 : Nat := 118140960795 + 753971 * 2 ^ 59
def prefixEnd_753971 : Nat := 4983230072969 + 3 ^ 40 * 753971 * 2
def baseEnd_753971 : Nat := 86033227233594404154457

theorem tailTrace_753971 : CollatzResearch.WordTrace tailWord_753971 prefixEnd_753971 86033227233594404154457 := by
  unfold tailWord_753971
  simp only [CollatzResearch.WordTrace]
  refine ⟨27499581551499309840165767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18333054367666206560110511 27499581551499309840165767)
  ·
    refine ⟨41249372327248964760248651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27499581551499309840165767 41249372327248964760248651)
    ·
      refine ⟨61874058490873447140372977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41249372327248964760248651 61874058490873447140372977)
      ·
        refine ⟨46405543868155085355279733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61874058490873447140372977 46405543868155085355279733)
        ·
          refine ⟨4350519737639539252057475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46405543868155085355279733 4350519737639539252057475)
          ·
            refine ⟨6525779606459308878086213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4350519737639539252057475 6525779606459308878086213)
            ·
              refine ⟨1223583676211120414641165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6525779606459308878086213 1223583676211120414641165)
              ·
                refine ⟨458843878579170155490437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1223583676211120414641165 458843878579170155490437)
                ·
                  refine ⟨86033227233594404154457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 458843878579170155490437 86033227233594404154457)
                  ·
                    rfl

theorem cell22_753971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 3, 4].length) (baseStart_753971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753971 prefixEnd_753971 := by exact prefixLift 753971
  have htrace : WordTrace (prefixWord ++ tailWord_753971) baseStart_753971 baseEnd_753971 := by
    simpa [prefixWord, tailWord_753971, baseEnd_753971] using wordTrace_append hprefix tailTrace_753971
  have hstable : (prefixWord ++ tailWord_753971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753971).length < 2 ^ (prefixWord ++ tailWord_753971).sum := by decide
  have hdescent : baseEnd_753971 < baseStart_753971 := by decide
  rcases family_descends (prefixWord ++ tailWord_753971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_753988 : List Nat := [2, 3, 4, 1, 2, 1, 2, 1, 6]
def baseStart_753988 : Nat := 118140960795 + 753988 * 2 ^ 59
def prefixEnd_753988 : Nat := 4983230072969 + 3 ^ 40 * 753988 * 2
def baseEnd_753988 : Nat := 86035167049400278262773

theorem tailTrace_753988 : CollatzResearch.WordTrace tailWord_753988 prefixEnd_753988 86035167049400278262773 := by
  unfold tailWord_753988
  simp only [CollatzResearch.WordTrace]
  refine ⟨13750100796218860871767309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18333467728291814495689745 13750100796218860871767309)
  ·
    refine ⟨5156287798582072826912741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13750100796218860871767309 5156287798582072826912741)
    ·
      refine ⟨966803962234138655046139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5156287798582072826912741 966803962234138655046139)
      ·
        refine ⟨1450205943351207982569209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 966803962234138655046139 1450205943351207982569209)
        ·
          refine ⟨1087654457513405986926907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1450205943351207982569209 1087654457513405986926907)
          ·
            refine ⟨1631481686270108980390361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1087654457513405986926907 1631481686270108980390361)
            ·
              refine ⟨1223611264702581735292771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1631481686270108980390361 1223611264702581735292771)
              ·
                refine ⟨1835416897053872602939157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1223611264702581735292771 1835416897053872602939157)
                ·
                  refine ⟨86035167049400278262773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1835416897053872602939157 86035167049400278262773)
                  ·
                    rfl

theorem cell22_753988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_753988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_753988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_753988 prefixEnd_753988 := by exact prefixLift 753988
  have htrace : WordTrace (prefixWord ++ tailWord_753988) baseStart_753988 baseEnd_753988 := by
    simpa [prefixWord, tailWord_753988, baseEnd_753988] using wordTrace_append hprefix tailTrace_753988
  have hstable : (prefixWord ++ tailWord_753988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_753988).length < 2 ^ (prefixWord ++ tailWord_753988).sum := by decide
  have hdescent : baseEnd_753988 < baseStart_753988 := by decide
  rcases family_descends (prefixWord ++ tailWord_753988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754104 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 5, 5]
def baseStart_754104 : Nat := 118140960795 + 754104 * 2 ^ 59
def prefixEnd_754104 : Nat := 4983230072969 + 3 ^ 40 * 754104 * 2
def baseEnd_754104 : Nat := 258145210318815198887963

theorem tailTrace_754104 : CollatzResearch.WordTrace tailWord_754104 prefixEnd_754104 258145210318815198887963 := by
  unfold tailWord_754104
  simp only [CollatzResearch.WordTrace]
  refine ⟨13752216230008736777378683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18336288306678315703171577 13752216230008736777378683)
  ·
    refine ⟨20628324345013105166068025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13752216230008736777378683 20628324345013105166068025)
    ·
      refine ⟨15471243258759828874551019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20628324345013105166068025 15471243258759828874551019)
      ·
        refine ⟨23206864888139743311826529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15471243258759828874551019 23206864888139743311826529)
        ·
          refine ⟨17405148666104807483869897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23206864888139743311826529 17405148666104807483869897)
          ·
            refine ⟨13053861499578605612902423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17405148666104807483869897 13053861499578605612902423)
            ·
              refine ⟨19580792249367908419353635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13053861499578605612902423 19580792249367908419353635)
              ·
                refine ⟨29371188374051862629030453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19580792249367908419353635 29371188374051862629030453)
                ·
                  refine ⟨2753548910067362121471605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29371188374051862629030453 2753548910067362121471605)
                  ·
                    refine ⟨258145210318815198887963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2753548910067362121471605 258145210318815198887963)
                    ·
                      rfl

theorem cell22_754104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_754104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_754104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_754104 prefixEnd_754104 := by exact prefixLift 754104
  have htrace : WordTrace (prefixWord ++ tailWord_754104) baseStart_754104 baseEnd_754104 := by
    simpa [prefixWord, tailWord_754104, baseEnd_754104] using wordTrace_append hprefix tailTrace_754104
  have hstable : (prefixWord ++ tailWord_754104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754104).length < 2 ^ (prefixWord ++ tailWord_754104).sum := by decide
  have hdescent : baseEnd_754104 < baseStart_754104 := by decide
  rcases family_descends (prefixWord ++ tailWord_754104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754230 : List Nat := [5, 1, 2, 1, 2, 2, 1, 3, 5]
def baseStart_754230 : Nat := 118140960795 + 754230 * 2 ^ 59
def prefixEnd_754230 : Nat := 4983230072969 + 3 ^ 40 * 754230 * 2
def baseEnd_754230 : Nat := 86062780897930956745859

theorem tailTrace_754230 : CollatzResearch.WordTrace tailWord_754230 prefixEnd_754230 86062780897930956745859 := by
  unfold tailWord_754230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1719314253597562317115259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18339352038373998049229429 1719314253597562317115259)
  ·
    refine ⟨2578971380396343475672889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1719314253597562317115259 2578971380396343475672889)
    ·
      refine ⟨1934228535297257606754667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2578971380396343475672889 1934228535297257606754667)
      ·
        refine ⟨2901342802945886410132001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1934228535297257606754667 2901342802945886410132001)
        ·
          refine ⟨2176007102209414807599001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2901342802945886410132001 2176007102209414807599001)
          ·
            refine ⟨1632005326657061105699251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2176007102209414807599001 1632005326657061105699251)
            ·
              refine ⟨2448007989985591658548877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1632005326657061105699251 2448007989985591658548877)
              ·
                refine ⟨918002996244596871955829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2448007989985591658548877 918002996244596871955829)
                ·
                  refine ⟨86062780897930956745859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 918002996244596871955829 86062780897930956745859)
                  ·
                    rfl

theorem cell22_754230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_754230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_754230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_754230 prefixEnd_754230 := by exact prefixLift 754230
  have htrace : WordTrace (prefixWord ++ tailWord_754230) baseStart_754230 baseEnd_754230 := by
    simpa [prefixWord, tailWord_754230, baseEnd_754230] using wordTrace_append hprefix tailTrace_754230
  have hstable : (prefixWord ++ tailWord_754230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754230).length < 2 ^ (prefixWord ++ tailWord_754230).sum := by decide
  have hdescent : baseEnd_754230 < baseStart_754230 := by decide
  rcases family_descends (prefixWord ++ tailWord_754230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754290 : List Nat := [3, 2, 1, 2, 4, 1, 2, 1, 1, 5]
def baseStart_754290 : Nat := 118140960795 + 754290 * 2 ^ 59
def prefixEnd_754290 : Nat := 4983230072969 + 3 ^ 40 * 754290 * 2
def baseEnd_754290 : Nat := 258208881919972713737393

theorem tailTrace_754290 : CollatzResearch.WordTrace tailWord_754290 prefixEnd_754290 258208881919972713737393 := by
  unfold tailWord_754290
  simp only [CollatzResearch.WordTrace]
  refine ⟨6877804109335906830257081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18340810958229084880685549 6877804109335906830257081)
  ·
    refine ⟨5158353082001930122692811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6877804109335906830257081 5158353082001930122692811)
    ·
      refine ⟨7737529623002895184039217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5158353082001930122692811 7737529623002895184039217)
      ·
        refine ⟨5803147217252171388029413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7737529623002895184039217 5803147217252171388029413)
        ·
          refine ⟨1088090103234782135255515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5803147217252171388029413 1088090103234782135255515)
          ·
            refine ⟨1632135154852173202883273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1088090103234782135255515 1632135154852173202883273)
            ·
              refine ⟨1224101366139129902162455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1632135154852173202883273 1224101366139129902162455)
              ·
                refine ⟨1836152049208694853243683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1224101366139129902162455 1836152049208694853243683)
                ·
                  refine ⟨2754228073813042279865525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1836152049208694853243683 2754228073813042279865525)
                  ·
                    refine ⟨258208881919972713737393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2754228073813042279865525 258208881919972713737393)
                    ·
                      rfl

theorem cell22_754290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_754290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_754290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_754290 prefixEnd_754290 := by exact prefixLift 754290
  have htrace : WordTrace (prefixWord ++ tailWord_754290) baseStart_754290 baseEnd_754290 := by
    simpa [prefixWord, tailWord_754290, baseEnd_754290] using wordTrace_append hprefix tailTrace_754290
  have hstable : (prefixWord ++ tailWord_754290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754290).length < 2 ^ (prefixWord ++ tailWord_754290).sum := by decide
  have hdescent : baseEnd_754290 < baseStart_754290 := by decide
  rcases family_descends (prefixWord ++ tailWord_754290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754316 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 1, 8]
def baseStart_754316 : Nat := 118140960795 + 754316 * 2 ^ 59
def prefixEnd_754316 : Nat := 4983230072969 + 3 ^ 40 * 754316 * 2
def baseEnd_754316 : Nat := 258217782251317312587313

theorem tailTrace_754316 : CollatzResearch.WordTrace tailWord_754316 prefixEnd_754316 258217782251317312587313 := by
  unfold tailWord_754316
  simp only [CollatzResearch.WordTrace]
  refine ⟨13756082367624716880737401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18341443156832955840983201 13756082367624716880737401)
  ·
    refine ⟨10317061775718537660553051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13756082367624716880737401 10317061775718537660553051)
    ·
      refine ⟨15475592663577806490829577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10317061775718537660553051 15475592663577806490829577)
      ·
        refine ⟨11606694497683354868122183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15475592663577806490829577 11606694497683354868122183)
        ·
          refine ⟨17410041746525032302183275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11606694497683354868122183 17410041746525032302183275)
          ·
            refine ⟨26115062619787548453274913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17410041746525032302183275 26115062619787548453274913)
            ·
              refine ⟨19586296964840661339956185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26115062619787548453274913 19586296964840661339956185)
              ·
                refine ⟨14689722723630496004967139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19586296964840661339956185 14689722723630496004967139)
                ·
                  refine ⟨22034584085445744007450709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14689722723630496004967139 22034584085445744007450709)
                  ·
                    refine ⟨258217782251317312587313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 22034584085445744007450709 258217782251317312587313)
                    ·
                      rfl

theorem cell22_754316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_754316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_754316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_754316 prefixEnd_754316 := by exact prefixLift 754316
  have htrace : WordTrace (prefixWord ++ tailWord_754316) baseStart_754316 baseEnd_754316 := by
    simpa [prefixWord, tailWord_754316, baseEnd_754316] using wordTrace_append hprefix tailTrace_754316
  have hstable : (prefixWord ++ tailWord_754316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754316).length < 2 ^ (prefixWord ++ tailWord_754316).sum := by decide
  have hdescent : baseEnd_754316 < baseStart_754316 := by decide
  rcases family_descends (prefixWord ++ tailWord_754316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754324 : List Nat := [2, 4, 2, 2, 1, 3, 1, 2, 2, 3]
def baseStart_754324 : Nat := 118140960795 + 754324 * 2 ^ 59
def prefixEnd_754324 : Nat := 4983230072969 + 3 ^ 40 * 754324 * 2
def baseEnd_754324 : Nat := 258220520814807958387289

theorem tailTrace_754324 : CollatzResearch.WordTrace tailWord_754324 prefixEnd_754324 258220520814807958387289 := by
  unfold tailWord_754324
  simp only [CollatzResearch.WordTrace]
  refine ⟨13756228259610225563883013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18341637679480300751844017 13756228259610225563883013)
  ·
    refine ⟨2579292798676917293228065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13756228259610225563883013 2579292798676917293228065)
    ·
      refine ⟨1934469599007687969921049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2579292798676917293228065 1934469599007687969921049)
      ·
        refine ⟨1450852199255765977440787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1934469599007687969921049 1450852199255765977440787)
        ·
          refine ⟨2176278298883648966161181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1450852199255765977440787 2176278298883648966161181)
          ·
            refine ⟨816104362081368362310443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2176278298883648966161181 816104362081368362310443)
            ·
              refine ⟨1224156543122052543465665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 816104362081368362310443 1224156543122052543465665)
              ·
                refine ⟨918117407341539407599249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1224156543122052543465665 918117407341539407599249)
                ·
                  refine ⟨688588055506154555699437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 918117407341539407599249 688588055506154555699437)
                  ·
                    refine ⟨258220520814807958387289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 688588055506154555699437 258220520814807958387289)
                    ·
                      rfl

theorem cell22_754324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_754324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_754324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_754324 prefixEnd_754324 := by exact prefixLift 754324
  have htrace : WordTrace (prefixWord ++ tailWord_754324) baseStart_754324 baseEnd_754324 := by
    simpa [prefixWord, tailWord_754324, baseEnd_754324] using wordTrace_append hprefix tailTrace_754324
  have hstable : (prefixWord ++ tailWord_754324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754324).length < 2 ^ (prefixWord ++ tailWord_754324).sum := by decide
  have hdescent : baseEnd_754324 < baseStart_754324 := by decide
  rcases family_descends (prefixWord ++ tailWord_754324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754386 : List Nat := [3, 2, 2, 2, 3, 1, 3, 2, 1, 3]
def baseStart_754386 : Nat := 118140960795 + 754386 * 2 ^ 59
def prefixEnd_754386 : Nat := 4983230072969 + 3 ^ 40 * 754386 * 2
def baseEnd_754386 : Nat := 258241744681860463337099

theorem tailTrace_754386 : CollatzResearch.WordTrace tailWord_754386 prefixEnd_754386 258241744681860463337099 := by
  unfold tailWord_754386
  simp only [CollatzResearch.WordTrace]
  refine ⟨6878679461248958929130753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18343145229997223811015341 6878679461248958929130753)
  ·
    refine ⟨5159009595936719196848065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6878679461248958929130753 5159009595936719196848065)
    ·
      refine ⟨3869257196952539397636049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5159009595936719196848065 3869257196952539397636049)
      ·
        refine ⟨2901942897714404548227037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3869257196952539397636049 2901942897714404548227037)
        ·
          refine ⟨1088228586642901705585139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2901942897714404548227037 1088228586642901705585139)
          ·
            refine ⟨1632342879964352558377709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1088228586642901705585139 1632342879964352558377709)
            ·
              refine ⟨612128579986632209391641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1632342879964352558377709 612128579986632209391641)
              ·
                refine ⟨459096434989974157043731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 612128579986632209391641 459096434989974157043731)
                ·
                  refine ⟨688644652484961235565597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 459096434989974157043731 688644652484961235565597)
                  ·
                    refine ⟨258241744681860463337099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 688644652484961235565597 258241744681860463337099)
                    ·
                      rfl

theorem cell22_754386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_754386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_754386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_754386 prefixEnd_754386 := by exact prefixLift 754386
  have htrace : WordTrace (prefixWord ++ tailWord_754386) baseStart_754386 baseEnd_754386 := by
    simpa [prefixWord, tailWord_754386, baseEnd_754386] using wordTrace_append hprefix tailTrace_754386
  have hstable : (prefixWord ++ tailWord_754386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754386).length < 2 ^ (prefixWord ++ tailWord_754386).sum := by decide
  have hdescent : baseEnd_754386 < baseStart_754386 := by decide
  rcases family_descends (prefixWord ++ tailWord_754386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754440 : List Nat := [2, 1, 3, 2, 2, 2, 2, 2, 2, 4]
def baseStart_754440 : Nat := 118140960795 + 754440 * 2 ^ 59
def prefixEnd_754440 : Nat := 4983230072969 + 3 ^ 40 * 754440 * 2
def baseEnd_754440 : Nat := 258260229985422322486933

theorem tailTrace_754440 : CollatzResearch.WordTrace tailWord_754440 prefixEnd_754440 258260229985422322486933 := by
  unfold tailWord_754440
  simp only [CollatzResearch.WordTrace]
  refine ⟨13758343693400101469494387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18344458257866801959325849 13758343693400101469494387)
  ·
    refine ⟨20637515540100152204241581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13758343693400101469494387 20637515540100152204241581)
    ·
      refine ⟨7739068327537557076590593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20637515540100152204241581 7739068327537557076590593)
      ·
        refine ⟨5804301245653167807442945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7739068327537557076590593 5804301245653167807442945)
        ·
          refine ⟨4353225934239875855582209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5804301245653167807442945 4353225934239875855582209)
          ·
            refine ⟨3264919450679906891686657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4353225934239875855582209 3264919450679906891686657)
            ·
              refine ⟨2448689588009930168764993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3264919450679906891686657 2448689588009930168764993)
              ·
                refine ⟨1836517191007447626573745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2448689588009930168764993 1836517191007447626573745)
                ·
                  refine ⟨1377387893255585719930309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1836517191007447626573745 1377387893255585719930309)
                  ·
                    refine ⟨258260229985422322486933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1377387893255585719930309 258260229985422322486933)
                    ·
                      rfl

theorem cell22_754440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_754440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_754440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_754440 prefixEnd_754440 := by exact prefixLift 754440
  have htrace : WordTrace (prefixWord ++ tailWord_754440) baseStart_754440 baseEnd_754440 := by
    simpa [prefixWord, tailWord_754440, baseEnd_754440] using wordTrace_append hprefix tailTrace_754440
  have hstable : (prefixWord ++ tailWord_754440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754440).length < 2 ^ (prefixWord ++ tailWord_754440).sum := by decide
  have hdescent : baseEnd_754440 < baseStart_754440 := by decide
  rcases family_descends (prefixWord ++ tailWord_754440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754442 : List Nat := [3, 1, 2, 2, 1, 2, 4, 2, 2, 3]
def baseStart_754442 : Nat := 118140960795 + 754442 * 2 ^ 59
def prefixEnd_754442 : Nat := 4983230072969 + 3 ^ 40 * 754442 * 2
def baseEnd_754442 : Nat := 258260914626294983936927

theorem tailTrace_754442 : CollatzResearch.WordTrace tailWord_754442 prefixEnd_754442 258260914626294983936927 := by
  unfold tailWord_754442
  simp only [CollatzResearch.WordTrace]
  refine ⟨6879190083198239320140395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18344506888528638187041053 6879190083198239320140395)
  ·
    refine ⟨10318785124797358980210593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6879190083198239320140395 10318785124797358980210593)
    ·
      refine ⟨7739088843598019235157945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10318785124797358980210593 7739088843598019235157945)
      ·
        refine ⟨5804316632698514426368459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7739088843598019235157945 5804316632698514426368459)
        ·
          refine ⟨8706474949047771639552689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5804316632698514426368459 8706474949047771639552689)
          ·
            refine ⟨6529856211785828729664517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8706474949047771639552689 6529856211785828729664517)
            ·
              refine ⟨1224348039709842886812097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6529856211785828729664517 1224348039709842886812097)
              ·
                refine ⟨918261029782382165109073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1224348039709842886812097 918261029782382165109073)
                ·
                  refine ⟨688695772336786623831805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 918261029782382165109073 688695772336786623831805)
                  ·
                    refine ⟨258260914626294983936927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 688695772336786623831805 258260914626294983936927)
                    ·
                      rfl

theorem cell22_754442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_754442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_754442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_754442 prefixEnd_754442 := by exact prefixLift 754442
  have htrace : WordTrace (prefixWord ++ tailWord_754442) baseStart_754442 baseEnd_754442 := by
    simpa [prefixWord, tailWord_754442, baseEnd_754442] using wordTrace_append hprefix tailTrace_754442
  have hstable : (prefixWord ++ tailWord_754442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754442).length < 2 ^ (prefixWord ++ tailWord_754442).sum := by decide
  have hdescent : baseEnd_754442 < baseStart_754442 := by decide
  rcases family_descends (prefixWord ++ tailWord_754442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754517 : List Nat := [1, 3, 2, 2, 2, 1, 5, 1, 5]
def baseStart_754517 : Nat := 118140960795 + 754517 * 2 ^ 59
def prefixEnd_754517 : Nat := 4983230072969 + 3 ^ 40 * 754517 * 2
def baseEnd_754517 : Nat := 86095529553006596103899

theorem tailTrace_754517 : CollatzResearch.WordTrace tailWord_754517 prefixEnd_754517 86095529553006596103899 := by
  unfold tailWord_754517
  simp only [CollatzResearch.WordTrace]
  refine ⟨27519495807521245089541805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18346330538347496726361203 27519495807521245089541805)
  ·
    refine ⟨10319810927820466908578177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27519495807521245089541805 10319810927820466908578177)
    ·
      refine ⟨7739858195865350181433633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10319810927820466908578177 7739858195865350181433633)
      ·
        refine ⟨5804893646899012636075225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7739858195865350181433633 5804893646899012636075225)
        ·
          refine ⟨4353670235174259477056419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5804893646899012636075225 4353670235174259477056419)
          ·
            refine ⟨6530505352761389215584629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4353670235174259477056419 6530505352761389215584629)
            ·
              refine ⟨612234876821380238961059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6530505352761389215584629 612234876821380238961059)
              ·
                refine ⟨918352315232070358441589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 612234876821380238961059 918352315232070358441589)
                ·
                  refine ⟨86095529553006596103899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 918352315232070358441589 86095529553006596103899)
                  ·
                    rfl

theorem cell22_754517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 5].length) (baseStart_754517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_754517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_754517 prefixEnd_754517 := by exact prefixLift 754517
  have htrace : WordTrace (prefixWord ++ tailWord_754517) baseStart_754517 baseEnd_754517 := by
    simpa [prefixWord, tailWord_754517, baseEnd_754517] using wordTrace_append hprefix tailTrace_754517
  have hstable : (prefixWord ++ tailWord_754517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754517).length < 2 ^ (prefixWord ++ tailWord_754517).sum := by decide
  have hdescent : baseEnd_754517 < baseStart_754517 := by decide
  rcases family_descends (prefixWord ++ tailWord_754517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754699 : List Nat := [1, 1, 1, 1, 6, 3, 2, 2, 1, 4]
def baseStart_754699 : Nat := 118140960795 + 754699 * 2 ^ 59
def prefixEnd_754699 : Nat := 4983230072969 + 3 ^ 40 * 754699 * 2
def baseEnd_754699 : Nat := 258348890978431980261139

theorem tailTrace_754699 : CollatzResearch.WordTrace tailWord_754699 prefixEnd_754699 258348890978431980261139 := by
  unfold tailWord_754699
  simp only [CollatzResearch.WordTrace]
  refine ⟨27526133892861890172667151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18350755928574593448444767 27526133892861890172667151)
  ·
    refine ⟨41289200839292835259000727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27526133892861890172667151 41289200839292835259000727)
    ·
      refine ⟨61933801258939252888501091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41289200839292835259000727 61933801258939252888501091)
      ·
        refine ⟨92900701888408879332751637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61933801258939252888501091 92900701888408879332751637)
        ·
          refine ⟨4354720401019166218722733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 92900701888408879332751637 4354720401019166218722733)
          ·
            refine ⟨1633020150382187332021025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4354720401019166218722733 1633020150382187332021025)
            ·
              refine ⟨1224765112786640499015769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1633020150382187332021025 1224765112786640499015769)
              ·
                refine ⟨918573834589980374261827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1224765112786640499015769 918573834589980374261827)
                ·
                  refine ⟨1377860751884970561392741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 918573834589980374261827 1377860751884970561392741)
                  ·
                    refine ⟨258348890978431980261139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1377860751884970561392741 258348890978431980261139)
                    ·
                      rfl

theorem cell22_754699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 4].length) (baseStart_754699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_754699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_754699 prefixEnd_754699 := by exact prefixLift 754699
  have htrace : WordTrace (prefixWord ++ tailWord_754699) baseStart_754699 baseEnd_754699 := by
    simpa [prefixWord, tailWord_754699, baseEnd_754699] using wordTrace_append hprefix tailTrace_754699
  have hstable : (prefixWord ++ tailWord_754699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754699).length < 2 ^ (prefixWord ++ tailWord_754699).sum := by decide
  have hdescent : baseEnd_754699 < baseStart_754699 := by decide
  rcases family_descends (prefixWord ++ tailWord_754699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754746 : List Nat := [3, 1, 1, 1, 3, 1, 6, 1, 2, 3]
def baseStart_754746 : Nat := 118140960795 + 754746 * 2 ^ 59
def prefixEnd_754746 : Nat := 4983230072969 + 3 ^ 40 * 754746 * 2
def baseEnd_754746 : Nat := 258364980038939524335995

theorem tailTrace_754746 : CollatzResearch.WordTrace tailWord_754746 prefixEnd_754746 258364980038939524335995 := by
  unfold tailWord_754746
  simp only [CollatzResearch.WordTrace]
  refine ⟨6881962030922904299907023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18351898749127744799752061 6881962030922904299907023)
  ·
    refine ⟨10322943046384356449860535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6881962030922904299907023 10322943046384356449860535)
    ·
      refine ⟨15484414569576534674790803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10322943046384356449860535 15484414569576534674790803)
      ·
        refine ⟨23226621854364802012186205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15484414569576534674790803 23226621854364802012186205)
        ·
          refine ⟨8709983195386800754569827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23226621854364802012186205 8709983195386800754569827)
          ·
            refine ⟨13064974793080201131854741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8709983195386800754569827 13064974793080201131854741)
            ·
              refine ⟨612420693425634428055691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13064974793080201131854741 612420693425634428055691)
              ·
                refine ⟨918631040138451642083537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 612420693425634428055691 918631040138451642083537)
                ·
                  refine ⟨688973280103838731562653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 918631040138451642083537 688973280103838731562653)
                  ·
                    refine ⟨258364980038939524335995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 688973280103838731562653 258364980038939524335995)
                    ·
                      rfl

theorem cell22_754746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 2, 3].length) (baseStart_754746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_754746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_754746 prefixEnd_754746 := by exact prefixLift 754746
  have htrace : WordTrace (prefixWord ++ tailWord_754746) baseStart_754746 baseEnd_754746 := by
    simpa [prefixWord, tailWord_754746, baseEnd_754746] using wordTrace_append hprefix tailTrace_754746
  have hstable : (prefixWord ++ tailWord_754746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754746).length < 2 ^ (prefixWord ++ tailWord_754746).sum := by decide
  have hdescent : baseEnd_754746 < baseStart_754746 := by decide
  rcases family_descends (prefixWord ++ tailWord_754746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754782 : List Nat := [4, 4, 1, 1, 1, 3, 2, 2, 4]
def baseStart_754782 : Nat := 118140960795 + 754782 * 2 ^ 59
def prefixEnd_754782 : Nat := 4983230072969 + 3 ^ 40 * 754782 * 2
def baseEnd_754782 : Nat := 86125767858215810145295

theorem tailTrace_754782 : CollatzResearch.WordTrace tailWord_754782 prefixEnd_754782 86125767858215810145295 := by
  unfold tailWord_754782
  simp only [CollatzResearch.WordTrace]
  refine ⟨3441145143945149418492325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18352774101040796898625733 3441145143945149418492325)
  ·
    refine ⟨645214714489715515967311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3441145143945149418492325 645214714489715515967311)
    ·
      refine ⟨967822071734573273950967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 645214714489715515967311 967822071734573273950967)
      ·
        refine ⟨1451733107601859910926451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 967822071734573273950967 1451733107601859910926451)
        ·
          refine ⟨2177599661402789866389677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1451733107601859910926451 2177599661402789866389677)
          ·
            refine ⟨816599873026046199896129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2177599661402789866389677 816599873026046199896129)
            ·
              refine ⟨612449904769534649922097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 816599873026046199896129 612449904769534649922097)
              ·
                refine ⟨459337428577150987441573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 612449904769534649922097 459337428577150987441573)
                ·
                  refine ⟨86125767858215810145295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 459337428577150987441573 86125767858215810145295)
                  ·
                    rfl

theorem cell22_754782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_754782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_754782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_754782 prefixEnd_754782 := by exact prefixLift 754782
  have htrace : WordTrace (prefixWord ++ tailWord_754782) baseStart_754782 baseEnd_754782 := by
    simpa [prefixWord, tailWord_754782, baseEnd_754782] using wordTrace_append hprefix tailTrace_754782
  have hstable : (prefixWord ++ tailWord_754782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754782).length < 2 ^ (prefixWord ++ tailWord_754782).sum := by decide
  have hdescent : baseEnd_754782 < baseStart_754782 := by decide
  rcases family_descends (prefixWord ++ tailWord_754782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754849 : List Nat := [1, 2, 3, 3, 1, 1, 4, 1, 6]
def baseStart_754849 : Nat := 118140960795 + 754849 * 2 ^ 59
def prefixEnd_754849 : Nat := 4983230072969 + 3 ^ 40 * 754849 * 2
def baseEnd_754849 : Nat := 86133413014627196336893

theorem tailTrace_754849 : CollatzResearch.WordTrace tailWord_754849 prefixEnd_754849 86133413014627196336893 := by
  unfold tailWord_754849
  simp only [CollatzResearch.WordTrace]
  refine ⟨27531604842318465790627601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18354403228212310527085067 27531604842318465790627601)
  ·
    refine ⟨20648703631738849342970701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27531604842318465790627601 20648703631738849342970701)
    ·
      refine ⟨7743263861902068503614013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20648703631738849342970701 7743263861902068503614013)
      ·
        refine ⟨2903723948213275688855255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7743263861902068503614013 2903723948213275688855255)
        ·
          refine ⟨4355585922319913533282883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2903723948213275688855255 4355585922319913533282883)
          ·
            refine ⟨6533378883479870299924325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4355585922319913533282883 6533378883479870299924325)
            ·
              refine ⟨1225008540652475681235811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6533378883479870299924325 1225008540652475681235811)
              ·
                refine ⟨1837512810978713521853717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1225008540652475681235811 1837512810978713521853717)
                ·
                  refine ⟨86133413014627196336893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1837512810978713521853717 86133413014627196336893)
                  ·
                    rfl

theorem cell22_754849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 6].length) (baseStart_754849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_754849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_754849 prefixEnd_754849 := by exact prefixLift 754849
  have htrace : WordTrace (prefixWord ++ tailWord_754849) baseStart_754849 baseEnd_754849 := by
    simpa [prefixWord, tailWord_754849, baseEnd_754849] using wordTrace_append hprefix tailTrace_754849
  have hstable : (prefixWord ++ tailWord_754849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754849).length < 2 ^ (prefixWord ++ tailWord_754849).sum := by decide
  have hdescent : baseEnd_754849 < baseStart_754849 := by decide
  rcases family_descends (prefixWord ++ tailWord_754849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754900 : List Nat := [2, 4, 1, 4, 2, 1, 1, 1, 6]
def baseStart_754900 : Nat := 118140960795 + 754900 * 2 ^ 59
def prefixEnd_754900 : Nat := 4983230072969 + 3 ^ 40 * 754900 * 2
def baseEnd_754900 : Nat := 86139232462044818661841

theorem tailTrace_754900 : CollatzResearch.WordTrace tailWord_754900 prefixEnd_754900 86139232462044818661841 := by
  unfold tailWord_754900
  simp only [CollatzResearch.WordTrace]
  refine ⟨13766732482566850750367077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18355643310089134333822769 13766732482566850750367077)
  ·
    refine ⟨2581262340481284515693827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13766732482566850750367077 2581262340481284515693827)
    ·
      refine ⟨3871893510721926773540741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2581262340481284515693827 3871893510721926773540741)
      ·
        refine ⟨725980033260361270038889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3871893510721926773540741 725980033260361270038889)
        ·
          refine ⟨544485024945270952529167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 725980033260361270038889 544485024945270952529167)
          ·
            refine ⟨816727537417906428793751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544485024945270952529167 816727537417906428793751)
            ·
              refine ⟨1225091306126859643190627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 816727537417906428793751 1225091306126859643190627)
              ·
                refine ⟨1837636959190289464785941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1225091306126859643190627 1837636959190289464785941)
                ·
                  refine ⟨86139232462044818661841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1837636959190289464785941 86139232462044818661841)
                  ·
                    rfl

theorem cell22_754900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_754900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_754900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_754900 prefixEnd_754900 := by exact prefixLift 754900
  have htrace : WordTrace (prefixWord ++ tailWord_754900) baseStart_754900 baseEnd_754900 := by
    simpa [prefixWord, tailWord_754900, baseEnd_754900] using wordTrace_append hprefix tailTrace_754900
  have hstable : (prefixWord ++ tailWord_754900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754900).length < 2 ^ (prefixWord ++ tailWord_754900).sum := by decide
  have hdescent : baseEnd_754900 < baseStart_754900 := by decide
  rcases family_descends (prefixWord ++ tailWord_754900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754926 : List Nat := [4, 1, 2, 1, 1, 1, 2, 4, 3, 3]
def baseStart_754926 : Nat := 118140960795 + 754926 * 2 ^ 59
def prefixEnd_754926 : Nat := 4983230072969 + 3 ^ 40 * 754926 * 2
def baseEnd_754926 : Nat := 258426597717479054835443

theorem tailTrace_754926 : CollatzResearch.WordTrace tailWord_754926 prefixEnd_754926 258426597717479054835443 := by
  unfold tailWord_754926
  simp only [CollatzResearch.WordTrace]
  refine ⟨3441801657879938492647579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18356275508693005294120421 3441801657879938492647579)
  ·
    refine ⟨5162702486819907738971369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3441801657879938492647579 5162702486819907738971369)
    ·
      refine ⟨3872026865114930804228527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5162702486819907738971369 3872026865114930804228527)
      ·
        refine ⟨5808040297672396206342791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3872026865114930804228527 5808040297672396206342791)
        ·
          refine ⟨8712060446508594309514187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5808040297672396206342791 8712060446508594309514187)
          ·
            refine ⟨13068090669762891464271281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8712060446508594309514187 13068090669762891464271281)
            ·
              refine ⟨9801068002322168598203461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13068090669762891464271281 9801068002322168598203461)
              ·
                refine ⟨1837700250435406612163149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9801068002322168598203461 1837700250435406612163149)
                ·
                  refine ⟨689137593913277479561181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1837700250435406612163149 689137593913277479561181)
                  ·
                    refine ⟨258426597717479054835443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 689137593913277479561181 258426597717479054835443)
                    ·
                      rfl

theorem cell22_754926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_754926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_754926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_754926 prefixEnd_754926 := by exact prefixLift 754926
  have htrace : WordTrace (prefixWord ++ tailWord_754926) baseStart_754926 baseEnd_754926 := by
    simpa [prefixWord, tailWord_754926, baseEnd_754926] using wordTrace_append hprefix tailTrace_754926
  have hstable : (prefixWord ++ tailWord_754926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754926).length < 2 ^ (prefixWord ++ tailWord_754926).sum := by decide
  have hdescent : baseEnd_754926 < baseStart_754926 := by decide
  rcases family_descends (prefixWord ++ tailWord_754926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754954 : List Nat := [3, 1, 2, 2, 1, 1, 1, 4, 2, 5]
def baseStart_754954 : Nat := 118140960795 + 754954 * 2 ^ 59
def prefixEnd_754954 : Nat := 4983230072969 + 3 ^ 40 * 754954 * 2
def baseEnd_754954 : Nat := 258436182689696315135357

theorem tailTrace_754954 : CollatzResearch.WordTrace tailWord_754954 prefixEnd_754954 258436182689696315135357 := by
  unfold tailWord_754954
  simp only [CollatzResearch.WordTrace]
  refine ⟨6883858626734517180799979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18356956337958712482133277 6883858626734517180799979)
  ·
    refine ⟨10325787940101775771199969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6883858626734517180799979 10325787940101775771199969)
    ·
      refine ⟨7744340955076331828399977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10325787940101775771199969 7744340955076331828399977)
      ·
        refine ⟨5808255716307248871299983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7744340955076331828399977 5808255716307248871299983)
        ·
          refine ⟨8712383574460873306949975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5808255716307248871299983 8712383574460873306949975)
          ·
            refine ⟨13068575361691309960424963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8712383574460873306949975 13068575361691309960424963)
            ·
              refine ⟨19602863042536964940637445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13068575361691309960424963 19602863042536964940637445)
              ·
                refine ⟨3675536820475680926369521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19602863042536964940637445 3675536820475680926369521)
                ·
                  refine ⟨2756652615356760694777141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3675536820475680926369521 2756652615356760694777141)
                  ·
                    refine ⟨258436182689696315135357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2756652615356760694777141 258436182689696315135357)
                    ·
                      rfl

theorem cell22_754954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_754954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_754954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_754954 prefixEnd_754954 := by exact prefixLift 754954
  have htrace : WordTrace (prefixWord ++ tailWord_754954) baseStart_754954 baseEnd_754954 := by
    simpa [prefixWord, tailWord_754954, baseEnd_754954] using wordTrace_append hprefix tailTrace_754954
  have hstable : (prefixWord ++ tailWord_754954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754954).length < 2 ^ (prefixWord ++ tailWord_754954).sum := by decide
  have hdescent : baseEnd_754954 < baseStart_754954 := by decide
  rcases family_descends (prefixWord ++ tailWord_754954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_754956 : List Nat := [2, 2, 1, 2, 2, 4, 2, 2, 5]
def baseStart_754956 : Nat := 118140960795 + 754956 * 2 ^ 59
def prefixEnd_754956 : Nat := 4983230072969 + 3 ^ 40 * 754956 * 2
def baseEnd_754956 : Nat := 86145622443522992195117

theorem tailTrace_754956 : CollatzResearch.WordTrace tailWord_754956 prefixEnd_754956 86145622443522992195117 := by
  unfold tailWord_754956
  simp only [CollatzResearch.WordTrace]
  refine ⟨13767753726465411532386361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18357004968620548709848481 13767753726465411532386361)
  ·
    refine ⟨10325815294849058649289771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13767753726465411532386361 10325815294849058649289771)
    ·
      refine ⟨15488722942273587973934657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10325815294849058649289771 15488722942273587973934657)
      ·
        refine ⟨11616542206705190980450993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15488722942273587973934657 11616542206705190980450993)
        ·
          refine ⟨8712406655028893235338245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11616542206705190980450993 8712406655028893235338245)
          ·
            refine ⟨1633576247817917481625921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8712406655028893235338245 1633576247817917481625921)
            ·
              refine ⟨1225182185863438111219441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1633576247817917481625921 1225182185863438111219441)
              ·
                refine ⟨918886639397578583414581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1225182185863438111219441 918886639397578583414581)
                ·
                  refine ⟨86145622443522992195117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 918886639397578583414581 86145622443522992195117)
                  ·
                    rfl

theorem cell22_754956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 5].length) (baseStart_754956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_754956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_754956 prefixEnd_754956 := by exact prefixLift 754956
  have htrace : WordTrace (prefixWord ++ tailWord_754956) baseStart_754956 baseEnd_754956 := by
    simpa [prefixWord, tailWord_754956, baseEnd_754956] using wordTrace_append hprefix tailTrace_754956
  have hstable : (prefixWord ++ tailWord_754956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_754956).length < 2 ^ (prefixWord ++ tailWord_754956).sum := by decide
  have hdescent : baseEnd_754956 < baseStart_754956 := by decide
  rcases family_descends (prefixWord ++ tailWord_754956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755129 : List Nat := [1, 2, 1, 4, 4, 2, 2, 2, 1, 3]
def baseStart_755129 : Nat := 118140960795 + 755129 * 2 ^ 59
def prefixEnd_755129 : Nat := 4983230072969 + 3 ^ 40 * 755129 * 2
def baseEnd_755129 : Nat := 258496088766054192009821

theorem tailTrace_755129 : CollatzResearch.WordTrace tailWord_755129 prefixEnd_755129 258496088766054192009821 := by
  unfold tailWord_755129
  simp only [CollatzResearch.WordTrace]
  refine ⟨27541817281304073610820441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18361211520869382407213627 27541817281304073610820441)
  ·
    refine ⟨20656362960978055208115331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27541817281304073610820441 20656362960978055208115331)
    ·
      refine ⟨30984544441467082812172997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20656362960978055208115331 30984544441467082812172997)
      ·
        refine ⟨5809602082775078027282437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30984544441467082812172997 5809602082775078027282437)
        ·
          refine ⟨1089300390520327130115457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5809602082775078027282437 1089300390520327130115457)
          ·
            refine ⟨816975292890245347586593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1089300390520327130115457 816975292890245347586593)
            ·
              refine ⟨612731469667684010689945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 816975292890245347586593 612731469667684010689945)
              ·
                refine ⟨459548602250763008017459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 612731469667684010689945 459548602250763008017459)
                ·
                  refine ⟨689322903376144512026189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 459548602250763008017459 689322903376144512026189)
                  ·
                    refine ⟨258496088766054192009821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 689322903376144512026189 258496088766054192009821)
                    ·
                      rfl

theorem cell22_755129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 2, 1, 3].length) (baseStart_755129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_755129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_755129 prefixEnd_755129 := by exact prefixLift 755129
  have htrace : WordTrace (prefixWord ++ tailWord_755129) baseStart_755129 baseEnd_755129 := by
    simpa [prefixWord, tailWord_755129, baseEnd_755129] using wordTrace_append hprefix tailTrace_755129
  have hstable : (prefixWord ++ tailWord_755129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755129).length < 2 ^ (prefixWord ++ tailWord_755129).sum := by decide
  have hdescent : baseEnd_755129 < baseStart_755129 := by decide
  rcases family_descends (prefixWord ++ tailWord_755129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755151 : List Nat := [1, 1, 2, 1, 1, 4, 3, 3, 1, 5]
def baseStart_755151 : Nat := 118140960795 + 755151 * 2 ^ 59
def prefixEnd_755151 : Nat := 4983230072969 + 3 ^ 40 * 755151 * 2
def baseEnd_755151 : Nat := 258503619815653467959753

theorem tailTrace_755151 : CollatzResearch.WordTrace tailWord_755151 prefixEnd_755151 258503619815653467959753 := by
  unfold tailWord_755151
  simp only [CollatzResearch.WordTrace]
  refine ⟨27542619687224371368121307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18361746458149580912080871 27542619687224371368121307)
  ·
    refine ⟨41313929530836557052181961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27542619687224371368121307 41313929530836557052181961)
    ·
      refine ⟨30985447148127417789136471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41313929530836557052181961 30985447148127417789136471)
      ·
        refine ⟨46478170722191126683704707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30985447148127417789136471 46478170722191126683704707)
        ·
          refine ⟨69717256083286690025557061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46478170722191126683704707 69717256083286690025557061)
          ·
            refine ⟨13071985515616254379791949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69717256083286690025557061 13071985515616254379791949)
            ·
              refine ⟨4901994568356095392421981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13071985515616254379791949 4901994568356095392421981)
              ·
                refine ⟨1838247963133535772158243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4901994568356095392421981 1838247963133535772158243)
                ·
                  refine ⟨2757371944700303658237365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1838247963133535772158243 2757371944700303658237365)
                  ·
                    refine ⟨258503619815653467959753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2757371944700303658237365 258503619815653467959753)
                    ·
                      rfl

theorem cell22_755151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 5].length) (baseStart_755151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_755151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_755151 prefixEnd_755151 := by exact prefixLift 755151
  have htrace : WordTrace (prefixWord ++ tailWord_755151) baseStart_755151 baseEnd_755151 := by
    simpa [prefixWord, tailWord_755151, baseEnd_755151] using wordTrace_append hprefix tailTrace_755151
  have hstable : (prefixWord ++ tailWord_755151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755151).length < 2 ^ (prefixWord ++ tailWord_755151).sum := by decide
  have hdescent : baseEnd_755151 < baseStart_755151 := by decide
  rcases family_descends (prefixWord ++ tailWord_755151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755185 : List Nat := [1, 2, 2, 2, 3, 2, 3, 2, 2, 3]
def baseStart_755185 : Nat := 118140960795 + 755185 * 2 ^ 59
def prefixEnd_755185 : Nat := 4983230072969 + 3 ^ 40 * 755185 * 2
def baseEnd_755185 : Nat := 258515258710488712609649

theorem tailTrace_755185 : CollatzResearch.WordTrace tailWord_755185 prefixEnd_755185 258515258710488712609649 := by
  unfold tailWord_755185
  simp only [CollatzResearch.WordTrace]
  refine ⟨27543859769101195174859009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18362573179400796783239339 27543859769101195174859009)
  ·
    refine ⟨20657894826825896381144257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27543859769101195174859009 20657894826825896381144257)
    ·
      refine ⟨15493421120119422285858193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20657894826825896381144257 15493421120119422285858193)
      ·
        refine ⟨11620065840089566714393645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15493421120119422285858193 11620065840089566714393645)
        ·
          refine ⟨4357524690033587517897617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11620065840089566714393645 4357524690033587517897617)
          ·
            refine ⟨3268143517525190638423213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4357524690033587517897617 3268143517525190638423213)
            ·
              refine ⟨1225553819071946489408705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3268143517525190638423213 1225553819071946489408705)
              ·
                refine ⟨919165364303959867056529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1225553819071946489408705 919165364303959867056529)
                ·
                  refine ⟨689374023227969900292397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 919165364303959867056529 689374023227969900292397)
                  ·
                    refine ⟨258515258710488712609649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 689374023227969900292397 258515258710488712609649)
                    ·
                      rfl

theorem cell22_755185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 2, 3].length) (baseStart_755185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_755185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_755185 prefixEnd_755185 := by exact prefixLift 755185
  have htrace : WordTrace (prefixWord ++ tailWord_755185) baseStart_755185 baseEnd_755185 := by
    simpa [prefixWord, tailWord_755185, baseEnd_755185] using wordTrace_append hprefix tailTrace_755185
  have hstable : (prefixWord ++ tailWord_755185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755185).length < 2 ^ (prefixWord ++ tailWord_755185).sum := by decide
  have hdescent : baseEnd_755185 < baseStart_755185 := by decide
  rcases family_descends (prefixWord ++ tailWord_755185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755202 : List Nat := [3, 4, 1, 2, 1, 3, 1, 1, 1, 5]
def baseStart_755202 : Nat := 118140960795 + 755202 * 2 ^ 59
def prefixEnd_755202 : Nat := 4983230072969 + 3 ^ 40 * 755202 * 2
def baseEnd_755202 : Nat := 258521078157906334934597

theorem tailTrace_755202 : CollatzResearch.WordTrace tailWord_755202 prefixEnd_755202 258521078157906334934597 := by
  unfold tailWord_755202
  simp only [CollatzResearch.WordTrace]
  refine ⟨6886119952509901769556965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18362986540026404718818573 6886119952509901769556965)
  ·
    refine ⟨1291147491095606581791931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6886119952509901769556965 1291147491095606581791931)
    ·
      refine ⟨1936721236643409872687897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1291147491095606581791931 1936721236643409872687897)
      ·
        refine ⟨1452540927482557404515923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1936721236643409872687897 1452540927482557404515923)
        ·
          refine ⟨2178811391223836106773885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1452540927482557404515923 2178811391223836106773885)
          ·
            refine ⟨817054271708938540040207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2178811391223836106773885 817054271708938540040207)
            ·
              refine ⟨1225581407563407810060311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 817054271708938540040207 1225581407563407810060311)
              ·
                refine ⟨1838372111345111715090467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1225581407563407810060311 1838372111345111715090467)
                ·
                  refine ⟨2757558167017667572635701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1838372111345111715090467 2757558167017667572635701)
                  ·
                    refine ⟨258521078157906334934597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2757558167017667572635701 258521078157906334934597)
                    ·
                      rfl

theorem cell22_755202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_755202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_755202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_755202 prefixEnd_755202 := by exact prefixLift 755202
  have htrace : WordTrace (prefixWord ++ tailWord_755202) baseStart_755202 baseEnd_755202 := by
    simpa [prefixWord, tailWord_755202, baseEnd_755202] using wordTrace_append hprefix tailTrace_755202
  have hstable : (prefixWord ++ tailWord_755202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755202).length < 2 ^ (prefixWord ++ tailWord_755202).sum := by decide
  have hdescent : baseEnd_755202 < baseStart_755202 := by decide
  rcases family_descends (prefixWord ++ tailWord_755202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755206 : List Nat := [6, 2, 1, 1, 2, 1, 2, 2, 1, 4]
def baseStart_755206 : Nat := 118140960795 + 755206 * 2 ^ 59
def prefixEnd_755206 : Nat := 4983230072969 + 3 ^ 40 * 755206 * 2
def baseEnd_755206 : Nat := 258522447439651657834585

theorem tailTrace_755206 : CollatzResearch.WordTrace tailWord_755206 prefixEnd_755206 258522447439651657834585 := by
  unfold tailWord_755206
  simp only [CollatzResearch.WordTrace]
  refine ⟨860769553188284867542921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18363083801350077174248981 860769553188284867542921)
  ·
    refine ⟨645577164891213650657191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 860769553188284867542921 645577164891213650657191)
    ·
      refine ⟨968365747336820475985787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 645577164891213650657191 968365747336820475985787)
      ·
        refine ⟨1452548621005230713978681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 968365747336820475985787 1452548621005230713978681)
        ·
          refine ⟨1089411465753923035484011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1452548621005230713978681 1089411465753923035484011)
          ·
            refine ⟨1634117198630884553226017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1089411465753923035484011 1634117198630884553226017)
            ·
              refine ⟨1225587898973163414919513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1634117198630884553226017 1225587898973163414919513)
              ·
                refine ⟨919190924229872561189635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1225587898973163414919513 919190924229872561189635)
                ·
                  refine ⟨1378786386344808841784453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 919190924229872561189635 1378786386344808841784453)
                  ·
                    refine ⟨258522447439651657834585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1378786386344808841784453 258522447439651657834585)
                    ·
                      rfl

theorem cell22_755206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_755206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_755206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_755206 prefixEnd_755206 := by exact prefixLift 755206
  have htrace : WordTrace (prefixWord ++ tailWord_755206) baseStart_755206 baseEnd_755206 := by
    simpa [prefixWord, tailWord_755206, baseEnd_755206] using wordTrace_append hprefix tailTrace_755206
  have hstable : (prefixWord ++ tailWord_755206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755206).length < 2 ^ (prefixWord ++ tailWord_755206).sum := by decide
  have hdescent : baseEnd_755206 < baseStart_755206 := by decide
  rcases family_descends (prefixWord ++ tailWord_755206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755260 : List Nat := [2, 2, 2, 2, 4, 1, 1, 3, 5]
def baseStart_755260 : Nat := 118140960795 + 755260 * 2 ^ 59
def prefixEnd_755260 : Nat := 4983230072969 + 3 ^ 40 * 755260 * 2
def baseEnd_755260 : Nat := 86180310914404505661473

theorem tailTrace_755260 : CollatzResearch.WordTrace tailWord_755260 prefixEnd_755260 86180310914404505661473 := by
  unfold tailWord_755260
  simp only [CollatzResearch.WordTrace]
  refine ⟨13773297621914741491919617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18364396829219655322559489 13773297621914741491919617)
  ·
    refine ⟨10329973216436056118939713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13773297621914741491919617 10329973216436056118939713)
    ·
      refine ⟨7747479912327042089204785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10329973216436056118939713 7747479912327042089204785)
      ·
        refine ⟨5810609934245281566903589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7747479912327042089204785 5810609934245281566903589)
        ·
          refine ⟨1089489362670990293794423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5810609934245281566903589 1089489362670990293794423)
          ·
            refine ⟨1634234044006485440691635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1089489362670990293794423 1634234044006485440691635)
            ·
              refine ⟨2451351066009728161037453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1634234044006485440691635 2451351066009728161037453)
              ·
                refine ⟨919256649753648060389045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2451351066009728161037453 919256649753648060389045)
                ·
                  refine ⟨86180310914404505661473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 919256649753648060389045 86180310914404505661473)
                  ·
                    rfl

theorem cell22_755260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 5].length) (baseStart_755260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_755260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_755260 prefixEnd_755260 := by exact prefixLift 755260
  have htrace : WordTrace (prefixWord ++ tailWord_755260) baseStart_755260 baseEnd_755260 := by
    simpa [prefixWord, tailWord_755260, baseEnd_755260] using wordTrace_append hprefix tailTrace_755260
  have hstable : (prefixWord ++ tailWord_755260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755260).length < 2 ^ (prefixWord ++ tailWord_755260).sum := by decide
  have hdescent : baseEnd_755260 < baseStart_755260 := by decide
  rcases family_descends (prefixWord ++ tailWord_755260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755335 : List Nat := [1, 1, 4, 2, 1, 3, 3, 1, 2, 4]
def baseStart_755335 : Nat := 118140960795 + 755335 * 2 ^ 59
def prefixEnd_755335 : Nat := 4983230072969 + 3 ^ 40 * 755335 * 2
def baseEnd_755335 : Nat := 258566606775938321359189

theorem tailTrace_755335 : CollatzResearch.WordTrace tailWord_755335 prefixEnd_755335 258566606775938321359189 := by
  unfold tailWord_755335
  simp only [CollatzResearch.WordTrace]
  refine ⟨27549330718557770792819459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18366220479038513861879639 27549330718557770792819459)
  ·
    refine ⟨41323996077836656189229189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27549330718557770792819459 41323996077836656189229189)
    ·
      refine ⟨7748249264594373035480473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41323996077836656189229189 7748249264594373035480473)
      ·
        refine ⟨5811186948445779776610355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7748249264594373035480473 5811186948445779776610355)
        ·
          refine ⟨8716780422668669664915533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5811186948445779776610355 8716780422668669664915533)
          ·
            refine ⟨3268792658500751124343325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8716780422668669664915533 3268792658500751124343325)
            ·
              refine ⟨1225797246937781671628747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3268792658500751124343325 1225797246937781671628747)
              ·
                refine ⟨1838695870406672507443121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1225797246937781671628747 1838695870406672507443121)
                ·
                  refine ⟨1379021902805004380582341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1838695870406672507443121 1379021902805004380582341)
                  ·
                    refine ⟨258566606775938321359189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1379021902805004380582341 258566606775938321359189)
                    ·
                      rfl

theorem cell22_755335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_755335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_755335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_755335 prefixEnd_755335 := by exact prefixLift 755335
  have htrace : WordTrace (prefixWord ++ tailWord_755335) baseStart_755335 baseEnd_755335 := by
    simpa [prefixWord, tailWord_755335, baseEnd_755335] using wordTrace_append hprefix tailTrace_755335
  have hstable : (prefixWord ++ tailWord_755335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755335).length < 2 ^ (prefixWord ++ tailWord_755335).sum := by decide
  have hdescent : baseEnd_755335 < baseStart_755335 := by decide
  rcases family_descends (prefixWord ++ tailWord_755335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755365 : List Nat := [1, 3, 1, 2, 1, 2, 3, 3, 3, 3]
def baseStart_755365 : Nat := 118140960795 + 755365 * 2 ^ 59
def prefixEnd_755365 : Nat := 4983230072969 + 3 ^ 40 * 755365 * 2
def baseEnd_755365 : Nat := 258576876389028243109097

theorem tailTrace_755365 : CollatzResearch.WordTrace tailWord_755365 prefixEnd_755365 258576876389028243109097 := by
  unfold tailWord_755365
  simp only [CollatzResearch.WordTrace]
  refine ⟨27550424908449085916411549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18366949938966057277607699 27550424908449085916411549)
  ·
    refine ⟨10331409340668407218654331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27550424908449085916411549 10331409340668407218654331)
    ·
      refine ⟨15497114011002610827981497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10331409340668407218654331 15497114011002610827981497)
      ·
        refine ⟨11622835508251958120986123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15497114011002610827981497 11622835508251958120986123)
        ·
          refine ⟨17434253262377937181479185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11622835508251958120986123 17434253262377937181479185)
          ·
            refine ⟨13075689946783452886109389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17434253262377937181479185 13075689946783452886109389)
            ·
              refine ⟨4903383730043794832291021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13075689946783452886109389 4903383730043794832291021)
              ·
                refine ⟨1838768898766423062109133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4903383730043794832291021 1838768898766423062109133)
                ·
                  refine ⟨689538337037408648290925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1838768898766423062109133 689538337037408648290925)
                  ·
                    refine ⟨258576876389028243109097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 689538337037408648290925 258576876389028243109097)
                    ·
                      rfl

theorem cell22_755365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 3, 3].length) (baseStart_755365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_755365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_755365 prefixEnd_755365 := by exact prefixLift 755365
  have htrace : WordTrace (prefixWord ++ tailWord_755365) baseStart_755365 baseEnd_755365 := by
    simpa [prefixWord, tailWord_755365, baseEnd_755365] using wordTrace_append hprefix tailTrace_755365
  have hstable : (prefixWord ++ tailWord_755365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755365).length < 2 ^ (prefixWord ++ tailWord_755365).sum := by decide
  have hdescent : baseEnd_755365 < baseStart_755365 := by decide
  rcases family_descends (prefixWord ++ tailWord_755365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755455 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 6, 3]
def baseStart_755455 : Nat := 118140960795 + 755455 * 2 ^ 59
def prefixEnd_755455 : Nat := 4983230072969 + 3 ^ 40 * 755455 * 2
def baseEnd_755455 : Nat := 258607685228298008358821

theorem tailTrace_755455 : CollatzResearch.WordTrace tailWord_755455 prefixEnd_755455 258607685228298008358821 := by
  unfold tailWord_755455
  simp only [CollatzResearch.WordTrace]
  refine ⟨27553707478123031287187819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18369138318748687524791879 27553707478123031287187819)
  ·
    refine ⟨41330561217184546930781729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27553707478123031287187819 41330561217184546930781729)
    ·
      refine ⟨30997920912888410198086297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41330561217184546930781729 30997920912888410198086297)
      ·
        refine ⟨23248440684666307648564723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30997920912888410198086297 23248440684666307648564723)
        ·
          refine ⟨34872661026999461472847085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23248440684666307648564723 34872661026999461472847085)
          ·
            refine ⟨13077247885124798052317657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34872661026999461472847085 13077247885124798052317657)
            ·
              refine ⟨9807935913843598539238243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13077247885124798052317657 9807935913843598539238243)
              ·
                refine ⟨14711903870765397808857365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9807935913843598539238243 14711903870765397808857365)
                ·
                  refine ⟨689620493942128022290189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 14711903870765397808857365 689620493942128022290189)
                  ·
                    refine ⟨258607685228298008358821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 689620493942128022290189 258607685228298008358821)
                    ·
                      rfl

theorem cell22_755455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 6, 3].length) (baseStart_755455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_755455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_755455 prefixEnd_755455 := by exact prefixLift 755455
  have htrace : WordTrace (prefixWord ++ tailWord_755455) baseStart_755455 baseEnd_755455 := by
    simpa [prefixWord, tailWord_755455, baseEnd_755455] using wordTrace_append hprefix tailTrace_755455
  have hstable : (prefixWord ++ tailWord_755455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755455).length < 2 ^ (prefixWord ++ tailWord_755455).sum := by decide
  have hdescent : baseEnd_755455 < baseStart_755455 := by decide
  rcases family_descends (prefixWord ++ tailWord_755455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755530 : List Nat := [3, 1, 2, 1, 1, 1, 5, 1, 7]
def baseStart_755530 : Nat := 118140960795 + 755530 * 2 ^ 59
def prefixEnd_755530 : Nat := 4983230072969 + 3 ^ 40 * 755530 * 2
def baseEnd_755530 : Nat := 86211119753674270911197

theorem tailTrace_755530 : CollatzResearch.WordTrace tailWord_755530 prefixEnd_755530 86211119753674270911197 := by
  unfold tailWord_755530
  simp only [CollatzResearch.WordTrace]
  refine ⟨6889110738212829774042011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18370961968567546064112029 6889110738212829774042011)
  ·
    refine ⟨10333666107319244661063017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6889110738212829774042011 10333666107319244661063017)
    ·
      refine ⟨7750249580489433495797263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10333666107319244661063017 7750249580489433495797263)
      ·
        refine ⟨11625374370734150243695895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7750249580489433495797263 11625374370734150243695895)
        ·
          refine ⟨17438061556101225365543843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11625374370734150243695895 17438061556101225365543843)
          ·
            refine ⟨26157092334151838048315765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17438061556101225365543843 26157092334151838048315765)
            ·
              refine ⟨2452227406326734817029603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26157092334151838048315765 2452227406326734817029603)
              ·
                refine ⟨3678341109490102225544405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2452227406326734817029603 3678341109490102225544405)
                ·
                  refine ⟨86211119753674270911197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3678341109490102225544405 86211119753674270911197)
                  ·
                    rfl

theorem cell22_755530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 7].length) (baseStart_755530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_755530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_755530 prefixEnd_755530 := by exact prefixLift 755530
  have htrace : WordTrace (prefixWord ++ tailWord_755530) baseStart_755530 baseEnd_755530 := by
    simpa [prefixWord, tailWord_755530, baseEnd_755530] using wordTrace_append hprefix tailTrace_755530
  have hstable : (prefixWord ++ tailWord_755530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755530).length < 2 ^ (prefixWord ++ tailWord_755530).sum := by decide
  have hdescent : baseEnd_755530 < baseStart_755530 := by decide
  rcases family_descends (prefixWord ++ tailWord_755530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755545 : List Nat := [1, 2, 1, 2, 2, 3, 1, 3, 2, 5]
def baseStart_755545 : Nat := 118140960795 + 755545 * 2 ^ 59
def prefixEnd_755545 : Nat := 4983230072969 + 3 ^ 40 * 755545 * 2
def baseEnd_755545 : Nat := 258638494067567773608545

theorem tailTrace_755545 : CollatzResearch.WordTrace tailWord_755545 prefixEnd_755545 258638494067567773608545 := by
  unfold tailWord_755545
  simp only [CollatzResearch.WordTrace]
  refine ⟨27556990047796976657964089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18371326698531317771976059 27556990047796976657964089)
  ·
    refine ⟨20667742535847732493473067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27556990047796976657964089 20667742535847732493473067)
    ·
      refine ⟨31001613803771598740209601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20667742535847732493473067 31001613803771598740209601)
      ·
        refine ⟨23251210352828699055157201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31001613803771598740209601 23251210352828699055157201)
        ·
          refine ⟨17438407764621524291367901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23251210352828699055157201 17438407764621524291367901)
          ·
            refine ⟨6539402911733071609262963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17438407764621524291367901 6539402911733071609262963)
            ·
              refine ⟨9809104367599607413894445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6539402911733071609262963 9809104367599607413894445)
              ·
                refine ⟨3678414137849852780210417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9809104367599607413894445 3678414137849852780210417)
                ·
                  refine ⟨2758810603387389585157813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3678414137849852780210417 2758810603387389585157813)
                  ·
                    refine ⟨258638494067567773608545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2758810603387389585157813 258638494067567773608545)
                    ·
                      rfl

theorem cell22_755545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 5].length) (baseStart_755545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_755545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_755545 prefixEnd_755545 := by exact prefixLift 755545
  have htrace : WordTrace (prefixWord ++ tailWord_755545) baseStart_755545 baseEnd_755545 := by
    simpa [prefixWord, tailWord_755545, baseEnd_755545] using wordTrace_append hprefix tailTrace_755545
  have hstable : (prefixWord ++ tailWord_755545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755545).length < 2 ^ (prefixWord ++ tailWord_755545).sum := by decide
  have hdescent : baseEnd_755545 < baseStart_755545 := by decide
  rcases family_descends (prefixWord ++ tailWord_755545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755577 : List Nat := [1, 2, 1, 3, 2, 2, 1, 5, 1, 4]
def baseStart_755577 : Nat := 118140960795 + 755577 * 2 ^ 59
def prefixEnd_755577 : Nat := 4983230072969 + 3 ^ 40 * 755577 * 2
def baseEnd_755577 : Nat := 258649448321530356808447

theorem tailTrace_755577 : CollatzResearch.WordTrace tailWord_755577 prefixEnd_755577 258649448321530356808447 := by
  unfold tailWord_755577
  simp only [CollatzResearch.WordTrace]
  refine ⟨27558157183681046123128985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18372104789120697415419323 27558157183681046123128985)
  ·
    refine ⟨20668617887760784592346739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27558157183681046123128985 20668617887760784592346739)
    ·
      refine ⟨31002926831641176888520109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20668617887760784592346739 31002926831641176888520109)
      ·
        refine ⟨11626097561865441333195041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31002926831641176888520109 11626097561865441333195041)
        ·
          refine ⟨8719573171399080999896281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11626097561865441333195041 8719573171399080999896281)
          ·
            refine ⟨6539679878549310749922211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8719573171399080999896281 6539679878549310749922211)
            ·
              refine ⟨9809519817823966124883317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6539679878549310749922211 9809519817823966124883317)
              ·
                refine ⟨919642482920996824207811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9809519817823966124883317 919642482920996824207811)
                ·
                  refine ⟨1379463724381495236311717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 919642482920996824207811 1379463724381495236311717)
                  ·
                    refine ⟨258649448321530356808447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1379463724381495236311717 258649448321530356808447)
                    ·
                      rfl

theorem cell22_755577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 4].length) (baseStart_755577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_755577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_755577 prefixEnd_755577 := by exact prefixLift 755577
  have htrace : WordTrace (prefixWord ++ tailWord_755577) baseStart_755577 baseEnd_755577 := by
    simpa [prefixWord, tailWord_755577, baseEnd_755577] using wordTrace_append hprefix tailTrace_755577
  have hstable : (prefixWord ++ tailWord_755577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755577).length < 2 ^ (prefixWord ++ tailWord_755577).sum := by decide
  have hdescent : baseEnd_755577 < baseStart_755577 := by decide
  rcases family_descends (prefixWord ++ tailWord_755577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755585 : List Nat := [1, 2, 4, 4, 1, 1, 3, 2, 1, 3]
def baseStart_755585 : Nat := 118140960795 + 755585 * 2 ^ 59
def prefixEnd_755585 : Nat := 4983230072969 + 3 ^ 40 * 755585 * 2
def baseEnd_755585 : Nat := 258652186885021002608423

theorem tailTrace_755585 : CollatzResearch.WordTrace tailWord_755585 prefixEnd_755585 258652186885021002608423 := by
  unfold tailWord_755585
  simp only [CollatzResearch.WordTrace]
  refine ⟨27558448967652063489420209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18372299311768042326280139 27558448967652063489420209)
  ·
    refine ⟨20668836725739047617065157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27558448967652063489420209 20668836725739047617065157)
    ·
      refine ⟨3875406886076071428199717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20668836725739047617065157 3875406886076071428199717)
      ·
        refine ⟨726638791139263392787447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3875406886076071428199717 726638791139263392787447)
        ·
          refine ⟨1089958186708895089181171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 726638791139263392787447 1089958186708895089181171)
          ·
            refine ⟨1634937280063342633771757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1089958186708895089181171 1634937280063342633771757)
            ·
              refine ⟨613101480023753487664409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1634937280063342633771757 613101480023753487664409)
              ·
                refine ⟨459826110017815115748307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 613101480023753487664409 459826110017815115748307)
                ·
                  refine ⟨689739165026722673622461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 459826110017815115748307 689739165026722673622461)
                  ·
                    refine ⟨258652186885021002608423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 689739165026722673622461 258652186885021002608423)
                    ·
                      rfl

theorem cell22_755585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_755585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_755585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_755585 prefixEnd_755585 := by exact prefixLift 755585
  have htrace : WordTrace (prefixWord ++ tailWord_755585) baseStart_755585 baseEnd_755585 := by
    simpa [prefixWord, tailWord_755585, baseEnd_755585] using wordTrace_append hprefix tailTrace_755585
  have hstable : (prefixWord ++ tailWord_755585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755585).length < 2 ^ (prefixWord ++ tailWord_755585).sum := by decide
  have hdescent : baseEnd_755585 < baseStart_755585 := by decide
  rcases family_descends (prefixWord ++ tailWord_755585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755598 : List Nat := [4, 1, 1, 5, 1, 2, 2, 1, 5]
def baseStart_755598 : Nat := 118140960795 + 755598 * 2 ^ 59
def prefixEnd_755598 : Nat := 4983230072969 + 3 ^ 40 * 755598 * 2
def baseEnd_755598 : Nat := 86218879016897767344461

theorem tailTrace_755598 : CollatzResearch.WordTrace tailWord_755598 prefixEnd_755598 86218879016897767344461 := by
  unfold tailWord_755598
  simp only [CollatzResearch.WordTrace]
  refine ⟨3444865389575620838705431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18372615411069977806428965 3444865389575620838705431)
  ·
    refine ⟨5167298084363431258058147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3444865389575620838705431 5167298084363431258058147)
    ·
      refine ⟨7750947126545146887087221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5167298084363431258058147 7750947126545146887087221)
      ·
        refine ⟨726651293113607520664427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7750947126545146887087221 726651293113607520664427)
        ·
          refine ⟨1089976939670411280996641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 726651293113607520664427 1089976939670411280996641)
          ·
            refine ⟨817482704752808460747481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1089976939670411280996641 817482704752808460747481)
            ·
              refine ⟨613112028564606345560611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 817482704752808460747481 613112028564606345560611)
              ·
                refine ⟨919668042846909518340917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 613112028564606345560611 919668042846909518340917)
                ·
                  refine ⟨86218879016897767344461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 919668042846909518340917 86218879016897767344461)
                  ·
                    rfl

theorem cell22_755598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_755598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_755598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_755598 prefixEnd_755598 := by exact prefixLift 755598
  have htrace : WordTrace (prefixWord ++ tailWord_755598) baseStart_755598 baseEnd_755598 := by
    simpa [prefixWord, tailWord_755598, baseEnd_755598] using wordTrace_append hprefix tailTrace_755598
  have hstable : (prefixWord ++ tailWord_755598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755598).length < 2 ^ (prefixWord ++ tailWord_755598).sum := by decide
  have hdescent : baseEnd_755598 < baseStart_755598 := by decide
  rcases family_descends (prefixWord ++ tailWord_755598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755669 : List Nat := [1, 3, 2, 3, 2, 1, 1, 1, 5, 3]
def baseStart_755669 : Nat := 118140960795 + 755669 * 2 ^ 59
def prefixEnd_755669 : Nat := 4983230072969 + 3 ^ 40 * 755669 * 2
def baseEnd_755669 : Nat := 258680941801672783508165

theorem tailTrace_755669 : CollatzResearch.WordTrace tailWord_755669 prefixEnd_755669 258680941801672783508165 := by
  unfold tailWord_755669
  simp only [CollatzResearch.WordTrace]
  refine ⟨27561512699347745835478061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18374341799565163890318707 27561512699347745835478061)
  ·
    refine ⟨10335567262255404688304273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27561512699347745835478061 10335567262255404688304273)
    ·
      refine ⟨7751675446691553516228205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10335567262255404688304273 7751675446691553516228205)
      ·
        refine ⟨2906878292509332568585577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7751675446691553516228205 2906878292509332568585577)
        ·
          refine ⟨2180158719381999426439183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2906878292509332568585577 2180158719381999426439183)
          ·
            refine ⟨3270238079072999139658775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2180158719381999426439183 3270238079072999139658775)
            ·
              refine ⟨4905357118609498709488163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3270238079072999139658775 4905357118609498709488163)
              ·
                refine ⟨7358035677914248064232245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4905357118609498709488163 7358035677914248064232245)
                ·
                  refine ⟨689815844804460756021773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7358035677914248064232245 689815844804460756021773)
                  ·
                    refine ⟨258680941801672783508165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 689815844804460756021773 258680941801672783508165)
                    ·
                      rfl

theorem cell22_755669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_755669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_755669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_755669 prefixEnd_755669 := by exact prefixLift 755669
  have htrace : WordTrace (prefixWord ++ tailWord_755669) baseStart_755669 baseEnd_755669 := by
    simpa [prefixWord, tailWord_755669, baseEnd_755669] using wordTrace_append hprefix tailTrace_755669
  have hstable : (prefixWord ++ tailWord_755669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755669).length < 2 ^ (prefixWord ++ tailWord_755669).sum := by decide
  have hdescent : baseEnd_755669 < baseStart_755669 := by decide
  rcases family_descends (prefixWord ++ tailWord_755669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755712 : List Nat := [2, 1, 1, 2, 1, 1, 1, 6, 3, 4]
def baseStart_755712 : Nat := 118140960795 + 755712 * 2 ^ 59
def prefixEnd_755712 : Nat := 4983230072969 + 3 ^ 40 * 755712 * 2
def baseEnd_755712 : Nat := 258695661580435004683033

theorem tailTrace_755712 : CollatzResearch.WordTrace tailWord_755712 prefixEnd_755712 258695661580435004683033 := by
  unfold tailWord_755712
  simp only [CollatzResearch.WordTrace]
  refine ⟨13781540519095982089646695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18375387358794642786195593 13781540519095982089646695)
  ·
    refine ⟨20672310778643973134470043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13781540519095982089646695 20672310778643973134470043)
    ·
      refine ⟨31008466167965959701705065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20672310778643973134470043 31008466167965959701705065)
      ·
        refine ⟨23256349625974469776278799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31008466167965959701705065 23256349625974469776278799)
        ·
          refine ⟨34884524438961704664418199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23256349625974469776278799 34884524438961704664418199)
          ·
            refine ⟨52326786658442556996627299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34884524438961704664418199 52326786658442556996627299)
            ·
              refine ⟨78490179987663835494940949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52326786658442556996627299 78490179987663835494940949)
              ·
                refine ⟨3679227186921742288825357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78490179987663835494940949 3679227186921742288825357)
                ·
                  refine ⟨1379710195095653358309509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3679227186921742288825357 1379710195095653358309509)
                  ·
                    refine ⟨258695661580435004683033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1379710195095653358309509 258695661580435004683033)
                    ·
                      rfl

theorem cell22_755712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 3, 4].length) (baseStart_755712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_755712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_755712 prefixEnd_755712 := by exact prefixLift 755712
  have htrace : WordTrace (prefixWord ++ tailWord_755712) baseStart_755712 baseEnd_755712 := by
    simpa [prefixWord, tailWord_755712, baseEnd_755712] using wordTrace_append hprefix tailTrace_755712
  have hstable : (prefixWord ++ tailWord_755712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755712).length < 2 ^ (prefixWord ++ tailWord_755712).sum := by decide
  have hdescent : baseEnd_755712 < baseStart_755712 := by decide
  rcases family_descends (prefixWord ++ tailWord_755712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755776 : List Nat := [2, 1, 1, 2, 2, 5, 1, 3, 2, 3]
def baseStart_755776 : Nat := 118140960795 + 755776 * 2 ^ 59
def prefixEnd_755776 : Nat := 4983230072969 + 3 ^ 40 * 755776 * 2
def baseEnd_755776 : Nat := 258717570088360171082837

theorem tailTrace_755776 : CollatzResearch.WordTrace tailWord_755776 prefixEnd_755776 258717570088360171082837 := by
  unfold tailWord_755776
  simp only [CollatzResearch.WordTrace]
  refine ⟨13782707654980051554811591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18376943539973402073082121 13782707654980051554811591)
  ·
    refine ⟨20674061482470077332217387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13782707654980051554811591 20674061482470077332217387)
    ·
      refine ⟨31011092223705115998326081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20674061482470077332217387 31011092223705115998326081)
      ·
        refine ⟨23258319167778836998744561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31011092223705115998326081 23258319167778836998744561)
        ·
          refine ⟨17443739375834127749058421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23258319167778836998744561 17443739375834127749058421)
          ·
            refine ⟨1635350566484449476474227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17443739375834127749058421 1635350566484449476474227)
            ·
              refine ⟨2453025849726674214711341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1635350566484449476474227 2453025849726674214711341)
              ·
                refine ⟨919884693647502830516753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2453025849726674214711341 919884693647502830516753)
                ·
                  refine ⟨689913520235627122887565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 919884693647502830516753 689913520235627122887565)
                  ·
                    refine ⟨258717570088360171082837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 689913520235627122887565 258717570088360171082837)
                    ·
                      rfl

theorem cell22_755776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 2, 3].length) (baseStart_755776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_755776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_755776 prefixEnd_755776 := by exact prefixLift 755776
  have htrace : WordTrace (prefixWord ++ tailWord_755776) baseStart_755776 baseEnd_755776 := by
    simpa [prefixWord, tailWord_755776, baseEnd_755776] using wordTrace_append hprefix tailTrace_755776
  have hstable : (prefixWord ++ tailWord_755776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755776).length < 2 ^ (prefixWord ++ tailWord_755776).sum := by decide
  have hdescent : baseEnd_755776 < baseStart_755776 := by decide
  rcases family_descends (prefixWord ++ tailWord_755776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755789 : List Nat := [1, 6, 1, 1, 1, 1, 1, 10]
def baseStart_755789 : Nat := 118140960795 + 755789 * 2 ^ 59
def prefixEnd_755789 : Nat := 4983230072969 + 3 ^ 40 * 755789 * 2
def baseEnd_755789 : Nat := 28746891139336941167533

theorem tailTrace_755789 : CollatzResearch.WordTrace tailWord_755789 prefixEnd_755789 28746891139336941167533 := by
  unfold tailWord_755789
  simp only [CollatzResearch.WordTrace]
  refine ⟨27565889458913006329846421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18377259639275337553230947 27565889458913006329846421)
  ·
    refine ⟨1292151068386547171711551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27565889458913006329846421 1292151068386547171711551)
    ·
      refine ⟨1938226602579820757567327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1292151068386547171711551 1938226602579820757567327)
      ·
        refine ⟨2907339903869731136350991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1938226602579820757567327 2907339903869731136350991)
        ·
          refine ⟨4361009855804596704526487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2907339903869731136350991 4361009855804596704526487)
          ·
            refine ⟨6541514783706895056789731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4361009855804596704526487 6541514783706895056789731)
            ·
              refine ⟨9812272175560342585184597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6541514783706895056789731 9812272175560342585184597)
              ·
                refine ⟨28746891139336941167533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 9812272175560342585184597 28746891139336941167533)
                ·
                  rfl

theorem cell22_755789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 10].length) (baseStart_755789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_755789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_755789 prefixEnd_755789 := by exact prefixLift 755789
  have htrace : WordTrace (prefixWord ++ tailWord_755789) baseStart_755789 baseEnd_755789 := by
    simpa [prefixWord, tailWord_755789, baseEnd_755789] using wordTrace_append hprefix tailTrace_755789
  have hstable : (prefixWord ++ tailWord_755789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755789).length < 2 ^ (prefixWord ++ tailWord_755789).sum := by decide
  have hdescent : baseEnd_755789 < baseStart_755789 := by decide
  rcases family_descends (prefixWord ++ tailWord_755789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755806 : List Nat := [4, 4, 1, 1, 12]
def baseStart_755806 : Nat := 118140960795 + 755806 * 2 ^ 59
def prefixEnd_755806 : Nat := 4983230072969 + 3 ^ 40 * 755806 * 2
def baseEnd_755806 : Nat := 1064723620170576513715

theorem tailTrace_755806 : CollatzResearch.WordTrace tailWord_755806 prefixEnd_755806 1064723620170576513715 := by
  unfold tailWord_755806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3445813687481427279151909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18377672999900945488810181 3445813687481427279151909)
  ·
    refine ⟨646090066402767614840983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3445813687481427279151909 646090066402767614840983)
    ·
      refine ⟨969135099604151422261475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 646090066402767614840983 969135099604151422261475)
      ·
        refine ⟨1453702649406227133392213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 969135099604151422261475 1453702649406227133392213)
        ·
          refine ⟨1064723620170576513715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 1453702649406227133392213 1064723620170576513715)
          ·
            rfl

theorem cell22_755806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 12].length) (baseStart_755806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_755806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_755806 prefixEnd_755806 := by exact prefixLift 755806
  have htrace : WordTrace (prefixWord ++ tailWord_755806) baseStart_755806 baseEnd_755806 := by
    simpa [prefixWord, tailWord_755806, baseEnd_755806] using wordTrace_append hprefix tailTrace_755806
  have hstable : (prefixWord ++ tailWord_755806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755806).length < 2 ^ (prefixWord ++ tailWord_755806).sum := by decide
  have hdescent : baseEnd_755806 < baseStart_755806 := by decide
  rcases family_descends (prefixWord ++ tailWord_755806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755810 : List Nat := [3, 3, 2, 2, 2, 1, 2, 2, 2, 3]
def baseStart_755810 : Nat := 118140960795 + 755810 * 2 ^ 59
def prefixEnd_755810 : Nat := 4983230072969 + 3 ^ 40 * 755810 * 2
def baseEnd_755810 : Nat := 258729208983195415732733

theorem tailTrace_755810 : CollatzResearch.WordTrace tailWord_755810 prefixEnd_755810 258729208983195415732733 := by
  unfold tailWord_755810
  simp only [CollatzResearch.WordTrace]
  refine ⟨6891663847959231729090221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18377770261224617944240589 6891663847959231729090221)
  ·
    refine ⟨2584373942984711898408833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6891663847959231729090221 2584373942984711898408833)
    ·
      refine ⟨1938280457238533923806625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2584373942984711898408833 1938280457238533923806625)
      ·
        refine ⟨1453710342928900442854969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1938280457238533923806625 1453710342928900442854969)
        ·
          refine ⟨1090282757196675332141227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1453710342928900442854969 1090282757196675332141227)
          ·
            refine ⟨1635424135795012998211841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1090282757196675332141227 1635424135795012998211841)
            ·
              refine ⟨1226568101846259748658881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1635424135795012998211841 1226568101846259748658881)
              ·
                refine ⟨919926076384694811494161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1226568101846259748658881 919926076384694811494161)
                ·
                  refine ⟨689944557288521108620621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 919926076384694811494161 689944557288521108620621)
                  ·
                    refine ⟨258729208983195415732733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 689944557288521108620621 258729208983195415732733)
                    ·
                      rfl

theorem cell22_755810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_755810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_755810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_755810 prefixEnd_755810 := by exact prefixLift 755810
  have htrace : WordTrace (prefixWord ++ tailWord_755810) baseStart_755810 baseEnd_755810 := by
    simpa [prefixWord, tailWord_755810, baseEnd_755810] using wordTrace_append hprefix tailTrace_755810
  have hstable : (prefixWord ++ tailWord_755810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755810).length < 2 ^ (prefixWord ++ tailWord_755810).sum := by decide
  have hdescent : baseEnd_755810 < baseStart_755810 := by decide
  rcases family_descends (prefixWord ++ tailWord_755810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755821 : List Nat := [1, 5, 1, 1, 2, 1, 2, 3, 3, 3]
def baseStart_755821 : Nat := 118140960795 + 755821 * 2 ^ 59
def prefixEnd_755821 : Nat := 4983230072969 + 3 ^ 40 * 755821 * 2
def baseEnd_755821 : Nat := 258732974507995053707699

theorem tailTrace_755821 : CollatzResearch.WordTrace tailWord_755821 prefixEnd_755821 258732974507995053707699 := by
  unfold tailWord_755821
  simp only [CollatzResearch.WordTrace]
  refine ⟨27567056594797075795011317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18378037729864717196674211 27567056594797075795011317)
  ·
    refine ⟨2584411555762225855782311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27567056594797075795011317 2584411555762225855782311)
    ·
      refine ⟨3876617333643338783673467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2584411555762225855782311 3876617333643338783673467)
      ·
        refine ⟨5814926000465008175510201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3876617333643338783673467 5814926000465008175510201)
        ·
          refine ⟨4361194500348756131632651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5814926000465008175510201 4361194500348756131632651)
          ·
            refine ⟨6541791750523134197448977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4361194500348756131632651 6541791750523134197448977)
            ·
              refine ⟨4906343812892350648086733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6541791750523134197448977 4906343812892350648086733)
              ·
                refine ⟨1839878929834631493032525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4906343812892350648086733 1839878929834631493032525)
                ·
                  refine ⟨689954598687986809887197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1839878929834631493032525 689954598687986809887197)
                  ·
                    refine ⟨258732974507995053707699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 689954598687986809887197 258732974507995053707699)
                    ·
                      rfl

theorem cell22_755821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_755821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_755821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_755821 prefixEnd_755821 := by exact prefixLift 755821
  have htrace : WordTrace (prefixWord ++ tailWord_755821) baseStart_755821 baseEnd_755821 := by
    simpa [prefixWord, tailWord_755821, baseEnd_755821] using wordTrace_append hprefix tailTrace_755821
  have hstable : (prefixWord ++ tailWord_755821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755821).length < 2 ^ (prefixWord ++ tailWord_755821).sum := by decide
  have hdescent : baseEnd_755821 < baseStart_755821 := by decide
  rcases family_descends (prefixWord ++ tailWord_755821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755909 : List Nat := [1, 3, 1, 1, 1, 1, 6, 1, 1, 6]
def baseStart_755909 : Nat := 118140960795 + 755909 * 2 ^ 59
def prefixEnd_755909 : Nat := 4983230072969 + 3 ^ 40 * 755909 * 2
def baseEnd_755909 : Nat := 258763098706392157507429

theorem tailTrace_755909 : CollatzResearch.WordTrace tailWord_755909 prefixEnd_755909 258763098706392157507429 := by
  unfold tailWord_755909
  simp only [CollatzResearch.WordTrace]
  refine ⟨27570266218478266824214781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18380177478985511216143187 27570266218478266824214781)
  ·
    refine ⟨10338849831929350059080543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27570266218478266824214781 10338849831929350059080543)
    ·
      refine ⟨15508274747894025088620815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10338849831929350059080543 15508274747894025088620815)
      ·
        refine ⟨23262412121841037632931223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15508274747894025088620815 23262412121841037632931223)
        ·
          refine ⟨34893618182761556449396835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23262412121841037632931223 34893618182761556449396835)
          ·
            refine ⟨52340427274142334674095253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34893618182761556449396835 52340427274142334674095253)
            ·
              refine ⟨2453457528475421937848215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52340427274142334674095253 2453457528475421937848215)
              ·
                refine ⟨3680186292713132906772323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2453457528475421937848215 3680186292713132906772323)
                ·
                  refine ⟨5520279439069699360158485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3680186292713132906772323 5520279439069699360158485)
                  ·
                    refine ⟨258763098706392157507429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5520279439069699360158485 258763098706392157507429)
                    ·
                      rfl

theorem cell22_755909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_755909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_755909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_755909 prefixEnd_755909 := by exact prefixLift 755909
  have htrace : WordTrace (prefixWord ++ tailWord_755909) baseStart_755909 baseEnd_755909 := by
    simpa [prefixWord, tailWord_755909, baseEnd_755909] using wordTrace_append hprefix tailTrace_755909
  have hstable : (prefixWord ++ tailWord_755909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755909).length < 2 ^ (prefixWord ++ tailWord_755909).sum := by decide
  have hdescent : baseEnd_755909 < baseStart_755909 := by decide
  rcases family_descends (prefixWord ++ tailWord_755909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_755941 : List Nat := [1, 3, 1, 4, 2, 2, 2, 7]
def baseStart_755941 : Nat := 118140960795 + 755941 * 2 ^ 59
def prefixEnd_755941 : Nat := 4983230072969 + 3 ^ 40 * 755941 * 2
def baseEnd_755941 : Nat := 28752672551150526745259

theorem tailTrace_755941 : CollatzResearch.WordTrace tailWord_755941 prefixEnd_755941 28752672551150526745259 := by
  unfold tailWord_755941
  simp only [CollatzResearch.WordTrace]
  refine ⟨27571433354362336289379677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18380955569574890859586451 27571433354362336289379677)
  ·
    refine ⟨10339287507885876108517379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27571433354362336289379677 10339287507885876108517379)
    ·
      refine ⟨15508931261828814162776069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10339287507885876108517379 15508931261828814162776069)
      ·
        refine ⟨2907924611592902655520513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15508931261828814162776069 2907924611592902655520513)
        ·
          refine ⟨2180943458694676991640385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2907924611592902655520513 2180943458694676991640385)
          ·
            refine ⟨1635707594021007743730289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2180943458694676991640385 1635707594021007743730289)
            ·
              refine ⟨1226780695515755807797717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1635707594021007743730289 1226780695515755807797717)
              ·
                refine ⟨28752672551150526745259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1226780695515755807797717 28752672551150526745259)
                ·
                  rfl

theorem cell22_755941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 7].length) (baseStart_755941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_755941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_755941 prefixEnd_755941 := by exact prefixLift 755941
  have htrace : WordTrace (prefixWord ++ tailWord_755941) baseStart_755941 baseEnd_755941 := by
    simpa [prefixWord, tailWord_755941, baseEnd_755941] using wordTrace_append hprefix tailTrace_755941
  have hstable : (prefixWord ++ tailWord_755941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_755941).length < 2 ^ (prefixWord ++ tailWord_755941).sum := by decide
  have hdescent : baseEnd_755941 < baseStart_755941 := by decide
  rcases family_descends (prefixWord ++ tailWord_755941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756048 : List Nat := [2, 1, 1, 1, 1, 6, 2, 4, 4]
def baseStart_756048 : Nat := 118140960795 + 756048 * 2 ^ 59
def prefixEnd_756048 : Nat := 4983230072969 + 3 ^ 40 * 756048 * 2
def baseEnd_756048 : Nat := 86270227082347376094001

theorem tailTrace_756048 : CollatzResearch.WordTrace tailWord_756048 prefixEnd_756048 86270227082347376094001 := by
  unfold tailWord_756048
  simp only [CollatzResearch.WordTrace]
  refine ⟨13787667982487346781762399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18383557309983129042349865 13787667982487346781762399)
  ·
    refine ⟨20681501973731020172643599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13787667982487346781762399 20681501973731020172643599)
    ·
      refine ⟨31022252960596530258965399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20681501973731020172643599 31022252960596530258965399)
      ·
        refine ⟨46533379440894795388448099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31022252960596530258965399 46533379440894795388448099)
        ·
          refine ⟨69800069161342193082672149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46533379440894795388448099 69800069161342193082672149)
          ·
            refine ⟨3271878241937915300750257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 69800069161342193082672149 3271878241937915300750257)
            ·
              refine ⟨2453908681453436475562693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3271878241937915300750257 2453908681453436475562693)
              ·
                refine ⟨460107877772519339168005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2453908681453436475562693 460107877772519339168005)
                ·
                  refine ⟨86270227082347376094001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 460107877772519339168005 86270227082347376094001)
                  ·
                    rfl

theorem cell22_756048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 4, 4].length) (baseStart_756048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_756048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_756048 prefixEnd_756048 := by exact prefixLift 756048
  have htrace : WordTrace (prefixWord ++ tailWord_756048) baseStart_756048 baseEnd_756048 := by
    simpa [prefixWord, tailWord_756048, baseEnd_756048] using wordTrace_append hprefix tailTrace_756048
  have hstable : (prefixWord ++ tailWord_756048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756048).length < 2 ^ (prefixWord ++ tailWord_756048).sum := by decide
  have hdescent : baseEnd_756048 < baseStart_756048 := by decide
  rcases family_descends (prefixWord ++ tailWord_756048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756063 : List Nat := [1, 1, 2, 3, 1, 2, 2, 5, 2, 3]
def baseStart_756063 : Nat := 118140960795 + 756063 * 2 ^ 59
def prefixEnd_756063 : Nat := 4983230072969 + 3 ^ 40 * 756063 * 2
def baseEnd_756063 : Nat := 258815816053587089156957

theorem tailTrace_756063 : CollatzResearch.WordTrace tailWord_756063 prefixEnd_756063 258815816053587089156957 := by
  unfold tailWord_756063
  simp only [CollatzResearch.WordTrace]
  refine ⟨27575883059920351125320843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18383922039946900750213895 27575883059920351125320843)
  ·
    refine ⟨41363824589880526687981265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27575883059920351125320843 41363824589880526687981265)
    ·
      refine ⟨31022868442410395015985949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41363824589880526687981265 31022868442410395015985949)
      ·
        refine ⟨11633575665903898130994731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31022868442410395015985949 11633575665903898130994731)
        ·
          refine ⟨17450363498855847196492097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11633575665903898130994731 17450363498855847196492097)
          ·
            refine ⟨13087772624141885397369073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17450363498855847196492097 13087772624141885397369073)
            ·
              refine ⟨9815829468106414048026805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13087772624141885397369073 9815829468106414048026805)
              ·
                refine ⟨920234012634976317002513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9815829468106414048026805 920234012634976317002513)
                ·
                  refine ⟨690175509476232237751885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 920234012634976317002513 690175509476232237751885)
                  ·
                    refine ⟨258815816053587089156957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 690175509476232237751885 258815816053587089156957)
                    ·
                      rfl

theorem cell22_756063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 2, 3].length) (baseStart_756063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_756063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_756063 prefixEnd_756063 := by exact prefixLift 756063
  have htrace : WordTrace (prefixWord ++ tailWord_756063) baseStart_756063 baseEnd_756063 := by
    simpa [prefixWord, tailWord_756063, baseEnd_756063] using wordTrace_append hprefix tailTrace_756063
  have hstable : (prefixWord ++ tailWord_756063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756063).length < 2 ^ (prefixWord ++ tailWord_756063).sum := by decide
  have hdescent : baseEnd_756063 < baseStart_756063 := by decide
  rcases family_descends (prefixWord ++ tailWord_756063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756118 : List Nat := [5, 3, 1, 2, 2, 1, 1, 2, 1, 4]
def baseStart_756118 : Nat := 118140960795 + 756118 * 2 ^ 59
def prefixEnd_756118 : Nat := 4983230072969 + 3 ^ 40 * 756118 * 2
def baseEnd_756118 : Nat := 258834643677585279031789

theorem tailTrace_756118 : CollatzResearch.WordTrace tailWord_756118 prefixEnd_756118 258834643677585279031789 := by
  unfold tailWord_756118
  simp only [CollatzResearch.WordTrace]
  refine ⟨1723618067170068469910813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18385259383147397012382005 1723618067170068469910813)
  ·
    refine ⟨646356775188775676216555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1723618067170068469910813 646356775188775676216555)
    ·
      refine ⟨969535162783163514324833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 646356775188775676216555 969535162783163514324833)
      ·
        refine ⟨727151372087372635743625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 969535162783163514324833 727151372087372635743625)
        ·
          refine ⟨545363529065529476807719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 727151372087372635743625 545363529065529476807719)
          ·
            refine ⟨818045293598294215211579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545363529065529476807719 818045293598294215211579)
            ·
              refine ⟨1227067940397441322817369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 818045293598294215211579 1227067940397441322817369)
              ·
                refine ⟨920300955298080992113027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1227067940397441322817369 920300955298080992113027)
                ·
                  refine ⟨1380451432947121488169541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 920300955298080992113027 1380451432947121488169541)
                  ·
                    refine ⟨258834643677585279031789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1380451432947121488169541 258834643677585279031789)
                    ·
                      rfl

theorem cell22_756118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_756118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_756118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_756118 prefixEnd_756118 := by exact prefixLift 756118
  have htrace : WordTrace (prefixWord ++ tailWord_756118) baseStart_756118 baseEnd_756118 := by
    simpa [prefixWord, tailWord_756118, baseEnd_756118] using wordTrace_append hprefix tailTrace_756118
  have hstable : (prefixWord ++ tailWord_756118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756118).length < 2 ^ (prefixWord ++ tailWord_756118).sum := by decide
  have hdescent : baseEnd_756118 < baseStart_756118 := by decide
  rcases family_descends (prefixWord ++ tailWord_756118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756168 : List Nat := [2, 1, 3, 1, 3, 2, 1, 2, 3, 4]
def baseStart_756168 : Nat := 118140960795 + 756168 * 2 ^ 59
def prefixEnd_756168 : Nat := 4983230072969 + 3 ^ 40 * 756168 * 2
def baseEnd_756168 : Nat := 258851759699401815281635

theorem tailTrace_756168 : CollatzResearch.WordTrace tailWord_756168 prefixEnd_756168 258851759699401815281635 := by
  unfold tailWord_756168
  simp only [CollatzResearch.WordTrace]
  refine ⟨13789856362269977028946579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18386475149693302705262105 13789856362269977028946579)
  ·
    refine ⟨20684784543404965543419869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13789856362269977028946579 20684784543404965543419869)
    ·
      refine ⟨7756794203776862078782451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20684784543404965543419869 7756794203776862078782451)
      ·
        refine ⟨11635191305665293118173677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7756794203776862078782451 11635191305665293118173677)
        ·
          refine ⟨4363196739624484919315129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11635191305665293118173677 4363196739624484919315129)
          ·
            refine ⟨3272397554718363689486347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4363196739624484919315129 3272397554718363689486347)
            ·
              refine ⟨4908596332077545534229521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3272397554718363689486347 4908596332077545534229521)
              ·
                refine ⟨3681447249058159150672141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4908596332077545534229521 3681447249058159150672141)
                ·
                  refine ⟨1380542718396809681502053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3681447249058159150672141 1380542718396809681502053)
                  ·
                    refine ⟨258851759699401815281635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1380542718396809681502053 258851759699401815281635)
                    ·
                      rfl

theorem cell22_756168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_756168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_756168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_756168 prefixEnd_756168 := by exact prefixLift 756168
  have htrace : WordTrace (prefixWord ++ tailWord_756168) baseStart_756168 baseEnd_756168 := by
    simpa [prefixWord, tailWord_756168, baseEnd_756168] using wordTrace_append hprefix tailTrace_756168
  have hstable : (prefixWord ++ tailWord_756168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756168).length < 2 ^ (prefixWord ++ tailWord_756168).sum := by decide
  have hdescent : baseEnd_756168 < baseStart_756168 := by decide
  rcases family_descends (prefixWord ++ tailWord_756168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756200 : List Nat := [2, 1, 4, 1, 1, 3, 1, 5, 4]
def baseStart_756200 : Nat := 118140960795 + 756200 * 2 ^ 59
def prefixEnd_756200 : Nat := 4983230072969 + 3 ^ 40 * 756200 * 2
def baseEnd_756200 : Nat := 86287571317788132827179

theorem tailTrace_756200 : CollatzResearch.WordTrace tailWord_756200 prefixEnd_756200 86287571317788132827179 := by
  unfold tailWord_756200
  simp only [CollatzResearch.WordTrace]
  refine ⟨13790439930212011761529027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18387253240282682348705369 13790439930212011761529027)
  ·
    refine ⟨20685659895318017642293541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13790439930212011761529027 20685659895318017642293541)
    ·
      refine ⟨3878561230372128307930039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20685659895318017642293541 3878561230372128307930039)
      ·
        refine ⟨5817841845558192461895059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3878561230372128307930039 5817841845558192461895059)
        ·
          refine ⟨8726762768337288692842589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5817841845558192461895059 8726762768337288692842589)
          ·
            refine ⟨3272536038126483259815971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8726762768337288692842589 3272536038126483259815971)
            ·
              refine ⟨4908804057189724889723957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3272536038126483259815971 4908804057189724889723957)
              ·
                refine ⟨460200380361536708411621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4908804057189724889723957 460200380361536708411621)
                ·
                  refine ⟨86287571317788132827179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 460200380361536708411621 86287571317788132827179)
                  ·
                    rfl

theorem cell22_756200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 5, 4].length) (baseStart_756200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_756200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_756200 prefixEnd_756200 := by exact prefixLift 756200
  have htrace : WordTrace (prefixWord ++ tailWord_756200) baseStart_756200 baseEnd_756200 := by
    simpa [prefixWord, tailWord_756200, baseEnd_756200] using wordTrace_append hprefix tailTrace_756200
  have hstable : (prefixWord ++ tailWord_756200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756200).length < 2 ^ (prefixWord ++ tailWord_756200).sum := by decide
  have hdescent : baseEnd_756200 < baseStart_756200 := by decide
  rcases family_descends (prefixWord ++ tailWord_756200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756202 : List Nat := [3, 1, 3, 1, 3, 1, 4, 1, 1, 4]
def baseStart_756202 : Nat := 118140960795 + 756202 * 2 ^ 59
def prefixEnd_756202 : Nat := 4983230072969 + 3 ^ 40 * 756202 * 2
def baseEnd_756202 : Nat := 258863398594237059931531

theorem tailTrace_756202 : CollatzResearch.WordTrace tailWord_756202 prefixEnd_756202 258863398594237059931531 := by
  unfold tailWord_756202
  simp only [CollatzResearch.WordTrace]
  refine ⟨6895238201604194466157715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18387301870944518576420573 6895238201604194466157715)
  ·
    refine ⟨10342857302406291699236573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6895238201604194466157715 10342857302406291699236573)
    ·
      refine ⟨3878571488402359387213715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10342857302406291699236573 3878571488402359387213715)
      ·
        refine ⟨5817857232603539080820573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3878571488402359387213715 5817857232603539080820573)
        ·
          refine ⟨2181696462226327155307715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5817857232603539080820573 2181696462226327155307715)
          ·
            refine ⟨3272544693339490732961573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2181696462226327155307715 3272544693339490732961573)
            ·
              refine ⟨613602130001154512430295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3272544693339490732961573 613602130001154512430295)
              ·
                refine ⟨920403195001731768645443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 613602130001154512430295 920403195001731768645443)
                ·
                  refine ⟨1380604792502597652968165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 920403195001731768645443 1380604792502597652968165)
                  ·
                    refine ⟨258863398594237059931531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1380604792502597652968165 258863398594237059931531)
                    ·
                      rfl

theorem cell22_756202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_756202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_756202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_756202 prefixEnd_756202 := by exact prefixLift 756202
  have htrace : WordTrace (prefixWord ++ tailWord_756202) baseStart_756202 baseEnd_756202 := by
    simpa [prefixWord, tailWord_756202, baseEnd_756202] using wordTrace_append hprefix tailTrace_756202
  have hstable : (prefixWord ++ tailWord_756202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756202).length < 2 ^ (prefixWord ++ tailWord_756202).sum := by decide
  have hdescent : baseEnd_756202 < baseStart_756202 := by decide
  rcases family_descends (prefixWord ++ tailWord_756202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756211 : List Nat := [1, 1, 1, 2, 2, 2, 13]
def baseStart_756211 : Nat := 118140960795 + 756211 * 2 ^ 59
def prefixEnd_756211 : Nat := 4983230072969 + 3 ^ 40 * 756211 * 2
def baseEnd_756211 : Nat := 9587647388080149498389

theorem tailTrace_756211 : CollatzResearch.WordTrace tailWord_756211 prefixEnd_756211 9587647388080149498389 := by
  unfold tailWord_756211
  simp only [CollatzResearch.WordTrace]
  refine ⟨27581281063384172401708487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18387520708922781601138991 27581281063384172401708487)
  ·
    refine ⟨41371921595076258602562731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27581281063384172401708487 41371921595076258602562731)
    ·
      refine ⟨62057882392614387903844097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41371921595076258602562731 62057882392614387903844097)
      ·
        refine ⟨46543411794460790927883073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62057882392614387903844097 46543411794460790927883073)
        ·
          refine ⟨34907558845845593195912305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46543411794460790927883073 34907558845845593195912305)
          ·
            refine ⟨26180669134384194896934229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34907558845845593195912305 26180669134384194896934229)
            ·
              refine ⟨9587647388080149498389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 26180669134384194896934229 9587647388080149498389)
              ·
                rfl

theorem cell22_756211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 13].length) (baseStart_756211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_756211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_756211 prefixEnd_756211 := by exact prefixLift 756211
  have htrace : WordTrace (prefixWord ++ tailWord_756211) baseStart_756211 baseEnd_756211 := by
    simpa [prefixWord, tailWord_756211, baseEnd_756211] using wordTrace_append hprefix tailTrace_756211
  have hstable : (prefixWord ++ tailWord_756211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756211).length < 2 ^ (prefixWord ++ tailWord_756211).sum := by decide
  have hdescent : baseEnd_756211 < baseStart_756211 := by decide
  rcases family_descends (prefixWord ++ tailWord_756211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756258 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 1, 8]
def baseStart_756258 : Nat := 118140960795 + 756258 * 2 ^ 59
def prefixEnd_756258 : Nat := 4983230072969 + 3 ^ 40 * 756258 * 2
def baseEnd_756258 : Nat := 258882568538671580531359

theorem tailTrace_756258 : CollatzResearch.WordTrace tailWord_756258 prefixEnd_756258 258882568538671580531359 := by
  unfold tailWord_756258
  simp only [CollatzResearch.WordTrace]
  refine ⟨6895748823553474857167357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18388663529475932952446285 6895748823553474857167357)
  ·
    refine ⟨2585905808832553071437759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6895748823553474857167357 2585905808832553071437759)
    ·
      refine ⟨3878858713248829607156639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2585905808832553071437759 3878858713248829607156639)
      ·
        refine ⟨5818288069873244410734959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3878858713248829607156639 5818288069873244410734959)
        ·
          refine ⟨8727432104809866616102439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5818288069873244410734959 8727432104809866616102439)
          ·
            refine ⟨13091148157214799924153659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8727432104809866616102439 13091148157214799924153659)
            ·
              refine ⟨19636722235822199886230489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13091148157214799924153659 19636722235822199886230489)
              ·
                refine ⟨14727541676866649914672867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19636722235822199886230489 14727541676866649914672867)
                ·
                  refine ⟨22091312515299974872009301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14727541676866649914672867 22091312515299974872009301)
                  ·
                    refine ⟨258882568538671580531359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 22091312515299974872009301 258882568538671580531359)
                    ·
                      rfl

theorem cell22_756258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_756258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_756258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_756258 prefixEnd_756258 := by exact prefixLift 756258
  have htrace : WordTrace (prefixWord ++ tailWord_756258) baseStart_756258 baseEnd_756258 := by
    simpa [prefixWord, tailWord_756258, baseEnd_756258] using wordTrace_append hprefix tailTrace_756258
  have hstable : (prefixWord ++ tailWord_756258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756258).length < 2 ^ (prefixWord ++ tailWord_756258).sum := by decide
  have hdescent : baseEnd_756258 < baseStart_756258 := by decide
  rcases family_descends (prefixWord ++ tailWord_756258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756273 : List Nat := [1, 2, 2, 3, 1, 1, 4, 1, 7]
def baseStart_756273 : Nat := 118140960795 + 756273 * 2 ^ 59
def prefixEnd_756273 : Nat := 4983230072969 + 3 ^ 40 * 756273 * 2
def baseEnd_756273 : Nat := 86295901115072180468771

theorem tailTrace_756273 : CollatzResearch.WordTrace tailWord_756273 prefixEnd_756273 86295901115072180468771 := by
  unfold tailWord_756273
  simp only [CollatzResearch.WordTrace]
  refine ⟨27583542389159556990465473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18389028259439704660310315 27583542389159556990465473)
  ·
    refine ⟨20687656791869667742849105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27583542389159556990465473 20687656791869667742849105)
    ·
      refine ⟨15515742593902250807136829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20687656791869667742849105 15515742593902250807136829)
      ·
        refine ⟨5818403472713344052676311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15515742593902250807136829 5818403472713344052676311)
        ·
          refine ⟨8727605209070016079014467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5818403472713344052676311 8727605209070016079014467)
          ·
            refine ⟨13091407813605024118521701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8727605209070016079014467 13091407813605024118521701)
            ·
              refine ⟨2454638965050942022222819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13091407813605024118521701 2454638965050942022222819)
              ·
                refine ⟨3681958447576413033334229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2454638965050942022222819 3681958447576413033334229)
                ·
                  refine ⟨86295901115072180468771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3681958447576413033334229 86295901115072180468771)
                  ·
                    rfl

theorem cell22_756273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 7].length) (baseStart_756273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_756273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_756273 prefixEnd_756273 := by exact prefixLift 756273
  have htrace : WordTrace (prefixWord ++ tailWord_756273) baseStart_756273 baseEnd_756273 := by
    simpa [prefixWord, tailWord_756273, baseEnd_756273] using wordTrace_append hprefix tailTrace_756273
  have hstable : (prefixWord ++ tailWord_756273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756273).length < 2 ^ (prefixWord ++ tailWord_756273).sum := by decide
  have hdescent : baseEnd_756273 < baseStart_756273 := by decide
  rcases family_descends (prefixWord ++ tailWord_756273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756288 : List Nat := [2, 1, 1, 2, 2, 2, 2, 3, 2, 5]
def baseStart_756288 : Nat := 118140960795 + 756288 * 2 ^ 59
def prefixEnd_756288 : Nat := 4983230072969 + 3 ^ 40 * 756288 * 2
def baseEnd_756288 : Nat := 258892838151761502281267

theorem tailTrace_756288 : CollatzResearch.WordTrace tailWord_756288 prefixEnd_756288 258892838151761502281267 := by
  unfold tailWord_756288
  simp only [CollatzResearch.WordTrace]
  refine ⟨13792044742052607276130759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18389392989403476368174345 13792044742052607276130759)
  ·
    refine ⟨20688067113078910914196139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13792044742052607276130759 20688067113078910914196139)
    ·
      refine ⟨31032100669618366371294209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20688067113078910914196139 31032100669618366371294209)
      ·
        refine ⟨23274075502213774778470657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31032100669618366371294209 23274075502213774778470657)
        ·
          refine ⟨17455556626660331083852993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23274075502213774778470657 17455556626660331083852993)
          ·
            refine ⟨13091667469995248312889745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17455556626660331083852993 13091667469995248312889745)
            ·
              refine ⟨9818750602496436234667309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13091667469995248312889745 9818750602496436234667309)
              ·
                refine ⟨3682031475936163588000241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9818750602496436234667309 3682031475936163588000241)
                ·
                  refine ⟨2761523606952122691000181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3682031475936163588000241 2761523606952122691000181)
                  ·
                    refine ⟨258892838151761502281267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2761523606952122691000181 258892838151761502281267)
                    ·
                      rfl

theorem cell22_756288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 2, 5].length) (baseStart_756288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_756288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_756288 prefixEnd_756288 := by exact prefixLift 756288
  have htrace : WordTrace (prefixWord ++ tailWord_756288) baseStart_756288 baseEnd_756288 := by
    simpa [prefixWord, tailWord_756288, baseEnd_756288] using wordTrace_append hprefix tailTrace_756288
  have hstable : (prefixWord ++ tailWord_756288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756288).length < 2 ^ (prefixWord ++ tailWord_756288).sum := by decide
  have hdescent : baseEnd_756288 < baseStart_756288 := by decide
  rcases family_descends (prefixWord ++ tailWord_756288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756320 : List Nat := [2, 1, 1, 3, 2, 1, 2, 5, 1, 4]
def baseStart_756320 : Nat := 118140960795 + 756320 * 2 ^ 59
def prefixEnd_756320 : Nat := 4983230072969 + 3 ^ 40 * 756320 * 2
def baseEnd_756320 : Nat := 258903792405724085481169

theorem tailTrace_756320 : CollatzResearch.WordTrace tailWord_756320 prefixEnd_756320 258903792405724085481169 := by
  unfold tailWord_756320
  simp only [CollatzResearch.WordTrace]
  refine ⟨13792628309994642008713207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18390171079992856011617609 13792628309994642008713207)
  ·
    refine ⟨20688942464991963013069811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13792628309994642008713207 20688942464991963013069811)
    ·
      refine ⟨31033413697487944519604717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20688942464991963013069811 31033413697487944519604717)
      ·
        refine ⟨11637530136557979194851769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31033413697487944519604717 11637530136557979194851769)
        ·
          refine ⟨8728147602418484396138827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11637530136557979194851769 8728147602418484396138827)
          ·
            refine ⟨13092221403627726594208241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8728147602418484396138827 13092221403627726594208241)
            ·
              refine ⟨9819166052720794945656181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13092221403627726594208241 9819166052720794945656181)
              ·
                refine ⟨920546817442574526155267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9819166052720794945656181 920546817442574526155267)
                ·
                  refine ⟨1380820226163861789232901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 920546817442574526155267 1380820226163861789232901)
                  ·
                    refine ⟨258903792405724085481169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1380820226163861789232901 258903792405724085481169)
                    ·
                      rfl

theorem cell22_756320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 1, 4].length) (baseStart_756320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_756320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_756320 prefixEnd_756320 := by exact prefixLift 756320
  have htrace : WordTrace (prefixWord ++ tailWord_756320) baseStart_756320 baseEnd_756320 := by
    simpa [prefixWord, tailWord_756320, baseEnd_756320] using wordTrace_append hprefix tailTrace_756320
  have hstable : (prefixWord ++ tailWord_756320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756320).length < 2 ^ (prefixWord ++ tailWord_756320).sum := by decide
  have hdescent : baseEnd_756320 < baseStart_756320 := by decide
  rcases family_descends (prefixWord ++ tailWord_756320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756328 : List Nat := [2, 1, 4, 3, 2, 2, 2, 2, 1, 3]
def baseStart_756328 : Nat := 118140960795 + 756328 * 2 ^ 59
def prefixEnd_756328 : Nat := 4983230072969 + 3 ^ 40 * 756328 * 2
def baseEnd_756328 : Nat := 258906530969214731281145

theorem tailTrace_756328 : CollatzResearch.WordTrace tailWord_756328 prefixEnd_756328 258906530969214731281145 := by
  unfold tailWord_756328
  simp only [CollatzResearch.WordTrace]
  refine ⟨13792774201980150691858819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18390365602640200922478425 13792774201980150691858819)
  ·
    refine ⟨20689161302970226037788229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13792774201980150691858819 20689161302970226037788229)
    ·
      refine ⟨3879217744306917382085293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20689161302970226037788229 3879217744306917382085293)
      ·
        refine ⟨1454706654115094018281985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3879217744306917382085293 1454706654115094018281985)
        ·
          refine ⟨1091029990586320513711489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1454706654115094018281985 1091029990586320513711489)
          ·
            refine ⟨818272492939740385283617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1091029990586320513711489 818272492939740385283617)
            ·
              refine ⟨613704369704805288962713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 818272492939740385283617 613704369704805288962713)
              ·
                refine ⟨460278277278603966722035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 613704369704805288962713 460278277278603966722035)
                ·
                  refine ⟨690417415917905950083053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 460278277278603966722035 690417415917905950083053)
                  ·
                    refine ⟨258906530969214731281145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 690417415917905950083053 258906530969214731281145)
                    ·
                      rfl

theorem cell22_756328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_756328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_756328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_756328 prefixEnd_756328 := by exact prefixLift 756328
  have htrace : WordTrace (prefixWord ++ tailWord_756328) baseStart_756328 baseEnd_756328 := by
    simpa [prefixWord, tailWord_756328, baseEnd_756328] using wordTrace_append hprefix tailTrace_756328
  have hstable : (prefixWord ++ tailWord_756328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756328).length < 2 ^ (prefixWord ++ tailWord_756328).sum := by decide
  have hdescent : baseEnd_756328 < baseStart_756328 := by decide
  rcases family_descends (prefixWord ++ tailWord_756328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756380 : List Nat := [2, 2, 3, 2, 2, 2, 9]
def baseStart_756380 : Nat := 118140960795 + 756380 * 2 ^ 59
def prefixEnd_756380 : Nat := 4983230072969 + 3 ^ 40 * 756380 * 2
def baseEnd_756380 : Nat := 9589790060440886258555

theorem tailTrace_756380 : CollatzResearch.WordTrace tailWord_756380 prefixEnd_756380 9589790060440886258555 := by
  unfold tailWord_756380
  simp only [CollatzResearch.WordTrace]
  refine ⟨13793722499885957132305297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18391629999847942843073729 13793722499885957132305297)
  ·
    refine ⟨10345291874914467849228973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13793722499885957132305297 10345291874914467849228973)
    ·
      refine ⟨3879484453092925443460865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10345291874914467849228973 3879484453092925443460865)
      ·
        refine ⟨2909613339819694082595649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3879484453092925443460865 2909613339819694082595649)
        ·
          refine ⟨2182210004864770561946737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2909613339819694082595649 2182210004864770561946737)
          ·
            refine ⟨1636657503648577921460053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2182210004864770561946737 1636657503648577921460053)
            ·
              refine ⟨9589790060440886258555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1636657503648577921460053 9589790060440886258555)
              ·
                rfl

theorem cell22_756380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 9].length) (baseStart_756380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_756380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_756380 prefixEnd_756380 := by exact prefixLift 756380
  have htrace : WordTrace (prefixWord ++ tailWord_756380) baseStart_756380 baseEnd_756380 := by
    simpa [prefixWord, tailWord_756380, baseEnd_756380] using wordTrace_append hprefix tailTrace_756380
  have hstable : (prefixWord ++ tailWord_756380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756380).length < 2 ^ (prefixWord ++ tailWord_756380).sum := by decide
  have hdescent : baseEnd_756380 < baseStart_756380 := by decide
  rcases family_descends (prefixWord ++ tailWord_756380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756382 : List Nat := [4, 3, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_756382 : Nat := 118140960795 + 756382 * 2 ^ 59
def prefixEnd_756382 : Nat := 4983230072969 + 3 ^ 40 * 756382 * 2
def baseEnd_756382 : Nat := 258925016272776590430979

theorem tailTrace_756382 : CollatzResearch.WordTrace tailWord_756382 prefixEnd_756382 258925016272776590430979 := by
  unfold tailWord_756382
  simp only [CollatzResearch.WordTrace]
  refine ⟨3448439743220583575772925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18391678630509779070788933 3448439743220583575772925)
  ·
    refine ⟨1293164903707718840914847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3448439743220583575772925 1293164903707718840914847)
    ·
      refine ⟨1939747355561578261372271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1293164903707718840914847 1939747355561578261372271)
      ·
        refine ⟨2909621033342367392058407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1939747355561578261372271 2909621033342367392058407)
        ·
          refine ⟨4364431550013551088087611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2909621033342367392058407 4364431550013551088087611)
          ·
            refine ⟨6546647325020326632131417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4364431550013551088087611 6546647325020326632131417)
            ·
              refine ⟨4909985493765244974098563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6546647325020326632131417 4909985493765244974098563)
              ·
                refine ⟨7364978240647867461147845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4909985493765244974098563 7364978240647867461147845)
                ·
                  refine ⟨1380933420121475148965221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7364978240647867461147845 1380933420121475148965221)
                  ·
                    refine ⟨258925016272776590430979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1380933420121475148965221 258925016272776590430979)
                    ·
                      rfl

theorem cell22_756382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_756382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_756382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_756382 prefixEnd_756382 := by exact prefixLift 756382
  have htrace : WordTrace (prefixWord ++ tailWord_756382) baseStart_756382 baseEnd_756382 := by
    simpa [prefixWord, tailWord_756382, baseEnd_756382] using wordTrace_append hprefix tailTrace_756382
  have hstable : (prefixWord ++ tailWord_756382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756382).length < 2 ^ (prefixWord ++ tailWord_756382).sum := by decide
  have hdescent : baseEnd_756382 < baseStart_756382 := by decide
  rcases family_descends (prefixWord ++ tailWord_756382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756401 : List Nat := [1, 2, 2, 6, 2, 1, 1, 1, 1, 5]
def baseStart_756401 : Nat := 118140960795 + 756401 * 2 ^ 59
def prefixEnd_756401 : Nat := 4983230072969 + 3 ^ 40 * 756401 * 2
def baseEnd_756401 : Nat := 258931520361066874205921

theorem tailTrace_756401 : CollatzResearch.WordTrace tailWord_756401 prefixEnd_756401 258931520361066874205921 := by
  unfold tailWord_756401
  simp only [CollatzResearch.WordTrace]
  refine ⟨27588210932695834851125057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18392140621797223234083371 27588210932695834851125057)
  ·
    refine ⟨20691158199521876138343793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27588210932695834851125057 20691158199521876138343793)
    ·
      refine ⟨15518368649641407103757845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20691158199521876138343793 15518368649641407103757845)
      ·
        refine ⟨727423530451940957988649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15518368649641407103757845 727423530451940957988649)
        ·
          refine ⟨545567647838955718491487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 727423530451940957988649 545567647838955718491487)
          ·
            refine ⟨818351471758433577737231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545567647838955718491487 818351471758433577737231)
            ·
              refine ⟨1227527207637650366605847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 818351471758433577737231 1227527207637650366605847)
              ·
                refine ⟨1841290811456475549908771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1227527207637650366605847 1841290811456475549908771)
                ·
                  refine ⟨2761936217184713324863157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1841290811456475549908771 2761936217184713324863157)
                  ·
                    refine ⟨258931520361066874205921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2761936217184713324863157 258931520361066874205921)
                    ·
                      rfl

theorem cell22_756401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 1, 5].length) (baseStart_756401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_756401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_756401 prefixEnd_756401 := by exact prefixLift 756401
  have htrace : WordTrace (prefixWord ++ tailWord_756401) baseStart_756401 baseEnd_756401 := by
    simpa [prefixWord, tailWord_756401, baseEnd_756401] using wordTrace_append hprefix tailTrace_756401
  have hstable : (prefixWord ++ tailWord_756401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756401).length < 2 ^ (prefixWord ++ tailWord_756401).sum := by decide
  have hdescent : baseEnd_756401 < baseStart_756401 := by decide
  rcases family_descends (prefixWord ++ tailWord_756401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756412 : List Nat := [2, 2, 2, 3, 1, 1, 1, 4, 3, 3]
def baseStart_756412 : Nat := 118140960795 + 756412 * 2 ^ 59
def prefixEnd_756412 : Nat := 4983230072969 + 3 ^ 40 * 756412 * 2
def baseEnd_756412 : Nat := 258935285885866512180887

theorem tailTrace_756412 : CollatzResearch.WordTrace tailWord_756412 prefixEnd_756412 258935285885866512180887 := by
  unfold tailWord_756412
  simp only [CollatzResearch.WordTrace]
  refine ⟨13794306067827991864887745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18392408090437322486516993 13794306067827991864887745)
  ·
    refine ⟨10345729550870993898665809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13794306067827991864887745 10345729550870993898665809)
    ·
      refine ⟨7759297163153245423999357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10345729550870993898665809 7759297163153245423999357)
      ·
        refine ⟨2909736436182467033999759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7759297163153245423999357 2909736436182467033999759)
        ·
          refine ⟨4364604654273700550999639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2909736436182467033999759 4364604654273700550999639)
          ·
            refine ⟨6546906981410550826499459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4364604654273700550999639 6546906981410550826499459)
            ·
              refine ⟨9820360472115826239749189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6546906981410550826499459 9820360472115826239749189)
              ·
                refine ⟨1841317588521717419952973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9820360472115826239749189 1841317588521717419952973)
                ·
                  refine ⟨690494095695644032482365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1841317588521717419952973 690494095695644032482365)
                  ·
                    refine ⟨258935285885866512180887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 690494095695644032482365 258935285885866512180887)
                    ·
                      rfl

theorem cell22_756412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_756412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_756412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_756412 prefixEnd_756412 := by exact prefixLift 756412
  have htrace : WordTrace (prefixWord ++ tailWord_756412) baseStart_756412 baseEnd_756412 := by
    simpa [prefixWord, tailWord_756412, baseEnd_756412] using wordTrace_append hprefix tailTrace_756412
  have hstable : (prefixWord ++ tailWord_756412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756412).length < 2 ^ (prefixWord ++ tailWord_756412).sum := by decide
  have hdescent : baseEnd_756412 < baseStart_756412 := by decide
  rcases family_descends (prefixWord ++ tailWord_756412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756547 : List Nat := [1, 1, 1, 3, 1, 4, 1, 2, 5, 3]
def baseStart_756547 : Nat := 118140960795 + 756547 * 2 ^ 59
def prefixEnd_756547 : Nat := 4983230072969 + 3 ^ 40 * 756547 * 2
def baseEnd_756547 : Nat := 258981499144771160055473

theorem tailTrace_756547 : CollatzResearch.WordTrace tailWord_756547 prefixEnd_756547 258981499144771160055473 := by
  unfold tailWord_756547
  simp only [CollatzResearch.WordTrace]
  refine ⟨27593535990166901785939895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18395690660111267857293263 27593535990166901785939895)
  ·
    refine ⟨41390303985250352678909843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27593535990166901785939895 41390303985250352678909843)
    ·
      refine ⟨62085455977875529018364765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41390303985250352678909843 62085455977875529018364765)
      ·
        refine ⟨23282045991703323381886787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62085455977875529018364765 23282045991703323381886787)
        ·
          refine ⟨34923068987554985072830181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23282045991703323381886787 34923068987554985072830181)
          ·
            refine ⟨6548075435166559701155659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34923068987554985072830181 6548075435166559701155659)
            ·
              refine ⟨9822113152749839551733489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6548075435166559701155659 9822113152749839551733489)
              ·
                refine ⟨7366584864562379663800117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9822113152749839551733489 7366584864562379663800117)
                ·
                  refine ⟨690617331052723093481261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7366584864562379663800117 690617331052723093481261)
                  ·
                    refine ⟨258981499144771160055473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 690617331052723093481261 258981499144771160055473)
                    ·
                      rfl

theorem cell22_756547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 5, 3].length) (baseStart_756547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_756547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_756547 prefixEnd_756547 := by exact prefixLift 756547
  have htrace : WordTrace (prefixWord ++ tailWord_756547) baseStart_756547 baseEnd_756547 := by
    simpa [prefixWord, tailWord_756547, baseEnd_756547] using wordTrace_append hprefix tailTrace_756547
  have hstable : (prefixWord ++ tailWord_756547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756547).length < 2 ^ (prefixWord ++ tailWord_756547).sum := by decide
  have hdescent : baseEnd_756547 < baseStart_756547 := by decide
  rcases family_descends (prefixWord ++ tailWord_756547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756641 : List Nat := [1, 2, 3, 4, 1, 1, 3, 2, 1, 4]
def baseStart_756641 : Nat := 118140960795 + 756641 * 2 ^ 59
def prefixEnd_756641 : Nat := 4983230072969 + 3 ^ 40 * 756641 * 2
def baseEnd_756641 : Nat := 259013677265786248205185

theorem tailTrace_756641 : CollatzResearch.WordTrace tailWord_756641 prefixEnd_756641 259013677265786248205185 := by
  unfold tailWord_756641
  simp only [CollatzResearch.WordTrace]
  refine ⟨27596964451826355839861777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18397976301217570559907851 27596964451826355839861777)
  ·
    refine ⟨20697723338869766879896333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27596964451826355839861777 20697723338869766879896333)
    ·
      refine ⟨7761646252076162579961125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20697723338869766879896333 7761646252076162579961125)
      ·
        refine ⟨1455308672264280483742711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7761646252076162579961125 1455308672264280483742711)
        ·
          refine ⟨2182963008396420725614067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1455308672264280483742711 2182963008396420725614067)
          ·
            refine ⟨3274444512594631088421101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2182963008396420725614067 3274444512594631088421101)
            ·
              refine ⟨1227916692222986658157913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3274444512594631088421101 1227916692222986658157913)
              ·
                refine ⟨920937519167239993618435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1227916692222986658157913 920937519167239993618435)
                ·
                  refine ⟨1381406278750859990427653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 920937519167239993618435 1381406278750859990427653)
                  ·
                    refine ⟨259013677265786248205185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1381406278750859990427653 259013677265786248205185)
                    ·
                      rfl

theorem cell22_756641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_756641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_756641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_756641 prefixEnd_756641 := by exact prefixLift 756641
  have htrace : WordTrace (prefixWord ++ tailWord_756641) baseStart_756641 baseEnd_756641 := by
    simpa [prefixWord, tailWord_756641, baseEnd_756641] using wordTrace_append hprefix tailTrace_756641
  have hstable : (prefixWord ++ tailWord_756641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756641).length < 2 ^ (prefixWord ++ tailWord_756641).sum := by decide
  have hdescent : baseEnd_756641 < baseStart_756641 := by decide
  rcases family_descends (prefixWord ++ tailWord_756641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756652 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 6, 4]
def baseStart_756652 : Nat := 118140960795 + 756652 * 2 ^ 59
def prefixEnd_756652 : Nat := 4983230072969 + 3 ^ 40 * 756652 * 2
def baseEnd_756652 : Nat := 259017442790585886180151

theorem tailTrace_756652 : CollatzResearch.WordTrace tailWord_756652 prefixEnd_756652 259017442790585886180151 := by
  unfold tailWord_756652
  simp only [CollatzResearch.WordTrace]
  refine ⟨13798682827393252359256105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18398243769857669812341473 13798682827393252359256105)
  ·
    refine ⟨10349012120544939269442079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13798682827393252359256105 10349012120544939269442079)
    ·
      refine ⟨15523518180817408904163119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10349012120544939269442079 15523518180817408904163119)
      ·
        refine ⟨23285277271226113356244679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15523518180817408904163119 23285277271226113356244679)
        ·
          refine ⟨34927915906839170034367019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23285277271226113356244679 34927915906839170034367019)
          ·
            refine ⟨52391873860258755051550529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34927915906839170034367019 52391873860258755051550529)
            ·
              refine ⟨39293905395194066288662897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52391873860258755051550529 39293905395194066288662897)
              ·
                refine ⟨29470429046395549716497173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39293905395194066288662897 29470429046395549716497173)
                ·
                  refine ⟨1381426361549791392960805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29470429046395549716497173 1381426361549791392960805)
                  ·
                    refine ⟨259017442790585886180151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1381426361549791392960805 259017442790585886180151)
                    ·
                      rfl

theorem cell22_756652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_756652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_756652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_756652 prefixEnd_756652 := by exact prefixLift 756652
  have htrace : WordTrace (prefixWord ++ tailWord_756652) baseStart_756652 baseEnd_756652 := by
    simpa [prefixWord, tailWord_756652, baseEnd_756652] using wordTrace_append hprefix tailTrace_756652
  have hstable : (prefixWord ++ tailWord_756652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756652).length < 2 ^ (prefixWord ++ tailWord_756652).sum := by decide
  have hdescent : baseEnd_756652 < baseStart_756652 := by decide
  rcases family_descends (prefixWord ++ tailWord_756652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756682 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 2, 7]
def baseStart_756682 : Nat := 118140960795 + 756682 * 2 ^ 59
def prefixEnd_756682 : Nat := 4983230072969 + 3 ^ 40 * 756682 * 2
def baseEnd_756682 : Nat := 259027712403675807930059

theorem tailTrace_756682 : CollatzResearch.WordTrace tailWord_756682 prefixEnd_756682 259027712403675807930059 := by
  unfold tailWord_756682
  simp only [CollatzResearch.WordTrace]
  refine ⟨6899614961169454960526075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18398973229785213228069533 6899614961169454960526075)
  ·
    refine ⟨10349422441754182440789113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6899614961169454960526075 10349422441754182440789113)
    ·
      refine ⟨7762066831315636830591835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10349422441754182440789113 7762066831315636830591835)
      ·
        refine ⟨11643100246973455245887753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7762066831315636830591835 11643100246973455245887753)
        ·
          refine ⟨8732325185230091434415815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11643100246973455245887753 8732325185230091434415815)
          ·
            refine ⟨13098487777845137151623723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8732325185230091434415815 13098487777845137151623723)
            ·
              refine ⟨19647731666767705727435585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13098487777845137151623723 19647731666767705727435585)
              ·
                refine ⟨14735798750075779295576689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19647731666767705727435585 14735798750075779295576689)
                ·
                  refine ⟨11051849062556834471682517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14735798750075779295576689 11051849062556834471682517)
                  ·
                    refine ⟨259027712403675807930059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11051849062556834471682517 259027712403675807930059)
                    ·
                      rfl

theorem cell22_756682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_756682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_756682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_756682 prefixEnd_756682 := by exact prefixLift 756682
  have htrace : WordTrace (prefixWord ++ tailWord_756682) baseStart_756682 baseEnd_756682 := by
    simpa [prefixWord, tailWord_756682, baseEnd_756682] using wordTrace_append hprefix tailTrace_756682
  have hstable : (prefixWord ++ tailWord_756682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756682).length < 2 ^ (prefixWord ++ tailWord_756682).sum := by decide
  have hdescent : baseEnd_756682 < baseStart_756682 := by decide
  rcases family_descends (prefixWord ++ tailWord_756682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756701 : List Nat := [1, 4, 3, 1, 2, 2, 3, 6]
def baseStart_756701 : Nat := 118140960795 + 756701 * 2 ^ 59
def prefixEnd_756701 : Nat := 4983230072969 + 3 ^ 40 * 756701 * 2
def baseEnd_756701 : Nat := 28781579610218454633889

theorem tailTrace_756701 : CollatzResearch.WordTrace tailWord_756701 prefixEnd_756701 28781579610218454633889 := by
  unfold tailWord_756701
  simp only [CollatzResearch.WordTrace]
  refine ⟨27599152831608986087045957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18399435221072657391363971 27599152831608986087045957)
  ·
    refine ⟨5174841155926684891321117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27599152831608986087045957 5174841155926684891321117)
    ·
      refine ⟨1940565433472506834245419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5174841155926684891321117 1940565433472506834245419)
      ·
        refine ⟨2910848150208760251368129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1940565433472506834245419 2910848150208760251368129)
        ·
          refine ⟨2183136112656570188526097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2910848150208760251368129 2183136112656570188526097)
          ·
            refine ⟨1637352084492427641394573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2183136112656570188526097 1637352084492427641394573)
            ·
              refine ⟨614007031684660365522965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1637352084492427641394573 614007031684660365522965)
              ·
                refine ⟨28781579610218454633889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 614007031684660365522965 28781579610218454633889)
                ·
                  rfl

theorem cell22_756701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 6].length) (baseStart_756701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_756701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_756701 prefixEnd_756701 := by exact prefixLift 756701
  have htrace : WordTrace (prefixWord ++ tailWord_756701) baseStart_756701 baseEnd_756701 := by
    simpa [prefixWord, tailWord_756701, baseEnd_756701] using wordTrace_append hprefix tailTrace_756701
  have hstable : (prefixWord ++ tailWord_756701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756701).length < 2 ^ (prefixWord ++ tailWord_756701).sum := by decide
  have hdescent : baseEnd_756701 < baseStart_756701 := by decide
  rcases family_descends (prefixWord ++ tailWord_756701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756703 : List Nat := [1, 1, 2, 3, 6, 1, 1, 1, 2, 4]
def baseStart_756703 : Nat := 118140960795 + 756703 * 2 ^ 59
def prefixEnd_756703 : Nat := 4983230072969 + 3 ^ 40 * 756703 * 2
def baseEnd_756703 : Nat := 259034901132838753154995

theorem tailTrace_756703 : CollatzResearch.WordTrace tailWord_756703 prefixEnd_756703 259034901132838753154995 := by
  unfold tailWord_756703
  simp only [CollatzResearch.WordTrace]
  refine ⟨27599225777601740428618763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18399483851734493619079175 27599225777601740428618763)
  ·
    refine ⟨41398838666402610642928145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27599225777601740428618763 41398838666402610642928145)
    ·
      refine ⟨31049128999801957982196109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41398838666402610642928145 31049128999801957982196109)
      ·
        refine ⟨11643423374925734243323541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31049128999801957982196109 11643423374925734243323541)
        ·
          refine ⟨545785470699643792655791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11643423374925734243323541 545785470699643792655791)
          ·
            refine ⟨818678206049465688983687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545785470699643792655791 818678206049465688983687)
            ·
              refine ⟨1228017309074198533475531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 818678206049465688983687 1228017309074198533475531)
              ·
                refine ⟨1842025963611297800213297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1228017309074198533475531 1842025963611297800213297)
                ·
                  refine ⟨1381519472708473350159973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1842025963611297800213297 1381519472708473350159973)
                  ·
                    refine ⟨259034901132838753154995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1381519472708473350159973 259034901132838753154995)
                    ·
                      rfl

theorem cell22_756703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 2, 4].length) (baseStart_756703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_756703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_756703 prefixEnd_756703 := by exact prefixLift 756703
  have htrace : WordTrace (prefixWord ++ tailWord_756703) baseStart_756703 baseEnd_756703 := by
    simpa [prefixWord, tailWord_756703, baseEnd_756703] using wordTrace_append hprefix tailTrace_756703
  have hstable : (prefixWord ++ tailWord_756703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756703).length < 2 ^ (prefixWord ++ tailWord_756703).sum := by decide
  have hdescent : baseEnd_756703 < baseStart_756703 := by decide
  rcases family_descends (prefixWord ++ tailWord_756703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756722 : List Nat := [3, 2, 1, 5, 2, 1, 1, 2, 2, 3]
def baseStart_756722 : Nat := 118140960795 + 756722 * 2 ^ 59
def prefixEnd_756722 : Nat := 4983230072969 + 3 ^ 40 * 756722 * 2
def baseEnd_756722 : Nat := 259041405221129036929937

theorem tailTrace_756722 : CollatzResearch.WordTrace tailWord_756722 prefixEnd_756722 259041405221129036929937 := by
  unfold tailWord_756722
  simp only [CollatzResearch.WordTrace]
  refine ⟨6899979691133226668390105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18399945843021937782373613 6899979691133226668390105)
  ·
    refine ⟨5174984768349920001292579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6899979691133226668390105 5174984768349920001292579)
    ·
      refine ⟨7762477152524880001938869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5174984768349920001292579 7762477152524880001938869)
      ·
        refine ⟨727732233049207500181769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7762477152524880001938869 727732233049207500181769)
        ·
          refine ⟨545799174786905625136327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 727732233049207500181769 545799174786905625136327)
          ·
            refine ⟨818698762180358437704491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545799174786905625136327 818698762180358437704491)
            ·
              refine ⟨1228048143270537656556737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 818698762180358437704491 1228048143270537656556737)
              ·
                refine ⟨921036107452903242417553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1228048143270537656556737 921036107452903242417553)
                ·
                  refine ⟨690777080589677431813165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 921036107452903242417553 690777080589677431813165)
                  ·
                    refine ⟨259041405221129036929937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 690777080589677431813165 259041405221129036929937)
                    ·
                      rfl

theorem cell22_756722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 2, 3].length) (baseStart_756722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_756722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_756722 prefixEnd_756722 := by exact prefixLift 756722
  have htrace : WordTrace (prefixWord ++ tailWord_756722) baseStart_756722 baseEnd_756722 := by
    simpa [prefixWord, tailWord_756722, baseEnd_756722] using wordTrace_append hprefix tailTrace_756722
  have hstable : (prefixWord ++ tailWord_756722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756722).length < 2 ^ (prefixWord ++ tailWord_756722).sum := by decide
  have hdescent : baseEnd_756722 < baseStart_756722 := by decide
  rcases family_descends (prefixWord ++ tailWord_756722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756744 : List Nat := [2, 1, 3, 2, 1, 3, 2, 1, 2, 5]
def baseStart_756744 : Nat := 118140960795 + 756744 * 2 ^ 59
def prefixEnd_756744 : Nat := 4983230072969 + 3 ^ 40 * 756744 * 2
def baseEnd_756744 : Nat := 259048936270728312879869

theorem tailTrace_756744 : CollatzResearch.WordTrace tailWord_756744 prefixEnd_756744 259048936270728312879869 := by
  unfold tailWord_756744
  simp only [CollatzResearch.WordTrace]
  refine ⟨13800360585226602215430643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18400480780302136287240857 13800360585226602215430643)
  ·
    refine ⟨20700540877839903323145965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13800360585226602215430643 20700540877839903323145965)
    ·
      refine ⟨7762702829189963746179737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20700540877839903323145965 7762702829189963746179737)
      ·
        refine ⟨5822027121892472809634803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7762702829189963746179737 5822027121892472809634803)
        ·
          refine ⟨8733040682838709214452205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5822027121892472809634803 8733040682838709214452205)
          ·
            refine ⟨3274890256064515955419577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8733040682838709214452205 3274890256064515955419577)
            ·
              refine ⟨2456167692048386966564683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3274890256064515955419577 2456167692048386966564683)
              ·
                refine ⟨3684251538072580449847025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2456167692048386966564683 3684251538072580449847025)
                ·
                  refine ⟨2763188653554435337385269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3684251538072580449847025 2763188653554435337385269)
                  ·
                    refine ⟨259048936270728312879869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2763188653554435337385269 259048936270728312879869)
                    ·
                      rfl

theorem cell22_756744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_756744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_756744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_756744 prefixEnd_756744 := by exact prefixLift 756744
  have htrace : WordTrace (prefixWord ++ tailWord_756744) baseStart_756744 baseEnd_756744 := by
    simpa [prefixWord, tailWord_756744, baseEnd_756744] using wordTrace_append hprefix tailTrace_756744
  have hstable : (prefixWord ++ tailWord_756744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756744).length < 2 ^ (prefixWord ++ tailWord_756744).sum := by decide
  have hdescent : baseEnd_756744 < baseStart_756744 := by decide
  rcases family_descends (prefixWord ++ tailWord_756744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756821 : List Nat := [1, 3, 2, 2, 1, 2, 4, 1, 2, 4]
def baseStart_756821 : Nat := 118140960795 + 756821 * 2 ^ 59
def prefixEnd_756821 : Nat := 4983230072969 + 3 ^ 40 * 756821 * 2
def baseEnd_756821 : Nat := 259075294944325778704633

theorem tailTrace_756821 : CollatzResearch.WordTrace tailWord_756821 prefixEnd_756821 259075294944325778704633 := by
  unfold tailWord_756821
  simp only [CollatzResearch.WordTrace]
  refine ⟨27603529591174246581414317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18402353060782831054276211 27603529591174246581414317)
  ·
    refine ⟨10351323596690342468030369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27603529591174246581414317 10351323596690342468030369)
    ·
      refine ⟨7763492697517756851022777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10351323596690342468030369 7763492697517756851022777)
      ·
        refine ⟨5822619523138317638267083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7763492697517756851022777 5822619523138317638267083)
        ·
          refine ⟨8733929284707476457400625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5822619523138317638267083 8733929284707476457400625)
          ·
            refine ⟨6550446963530607343050469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8733929284707476457400625 6550446963530607343050469)
            ·
              refine ⟨1228208805661988876821963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6550446963530607343050469 1228208805661988876821963)
              ·
                refine ⟨1842313208492983315232945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1228208805661988876821963 1842313208492983315232945)
                ·
                  refine ⟨1381734906369737486424709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1842313208492983315232945 1381734906369737486424709)
                  ·
                    refine ⟨259075294944325778704633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1381734906369737486424709 259075294944325778704633)
                    ·
                      rfl

theorem cell22_756821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_756821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_756821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_756821 prefixEnd_756821 := by exact prefixLift 756821
  have htrace : WordTrace (prefixWord ++ tailWord_756821) baseStart_756821 baseEnd_756821 := by
    simpa [prefixWord, tailWord_756821, baseEnd_756821] using wordTrace_append hprefix tailTrace_756821
  have hstable : (prefixWord ++ tailWord_756821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756821).length < 2 ^ (prefixWord ++ tailWord_756821).sum := by decide
  have hdescent : baseEnd_756821 < baseStart_756821 := by decide
  rcases family_descends (prefixWord ++ tailWord_756821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756868 : List Nat := [2, 3, 2, 1, 2, 3, 1, 2, 3, 3]
def baseStart_756868 : Nat := 118140960795 + 756868 * 2 ^ 59
def prefixEnd_756868 : Nat := 4983230072969 + 3 ^ 40 * 756868 * 2
def baseEnd_756868 : Nat := 259091384004833322779489

theorem tailTrace_756868 : CollatzResearch.WordTrace tailWord_756868 prefixEnd_756868 259091384004833322779489 := by
  unfold tailWord_756868
  simp only [CollatzResearch.WordTrace]
  refine ⟨13802621911001986804187629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18403495881335982405583505 13802621911001986804187629)
  ·
    refine ⟨5175983216625745051570361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13802621911001986804187629 5175983216625745051570361)
    ·
      refine ⟨3881987412469308788677771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5175983216625745051570361 3881987412469308788677771)
      ·
        refine ⟨5822981118703963183016657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3881987412469308788677771 5822981118703963183016657)
        ·
          refine ⟨4367235839027972387262493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5822981118703963183016657 4367235839027972387262493)
          ·
            refine ⟨1637713439635489645223435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4367235839027972387262493 1637713439635489645223435)
            ·
              refine ⟨2456570159453234467835153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1637713439635489645223435 2456570159453234467835153)
              ·
                refine ⟨1842427619589925850876365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2456570159453234467835153 1842427619589925850876365)
                ·
                  refine ⟨690910357346222194078637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1842427619589925850876365 690910357346222194078637)
                  ·
                    refine ⟨259091384004833322779489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 690910357346222194078637 259091384004833322779489)
                    ·
                      rfl

theorem cell22_756868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_756868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_756868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_756868 prefixEnd_756868 := by exact prefixLift 756868
  have htrace : WordTrace (prefixWord ++ tailWord_756868) baseStart_756868 baseEnd_756868 := by
    simpa [prefixWord, tailWord_756868, baseEnd_756868] using wordTrace_append hprefix tailTrace_756868
  have hstable : (prefixWord ++ tailWord_756868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756868).length < 2 ^ (prefixWord ++ tailWord_756868).sum := by decide
  have hdescent : baseEnd_756868 < baseStart_756868 := by decide
  rcases family_descends (prefixWord ++ tailWord_756868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756898 : List Nat := [3, 3, 1, 3, 2, 1, 1, 1, 7]
def baseStart_756898 : Nat := 118140960795 + 756898 * 2 ^ 59
def prefixEnd_756898 : Nat := 4983230072969 + 3 ^ 40 * 756898 * 2
def baseEnd_756898 : Nat := 86367217872641081509799

theorem tailTrace_756898 : CollatzResearch.WordTrace tailWord_756898 prefixEnd_756898 86367217872641081509799 := by
  unfold tailWord_756898
  simp only [CollatzResearch.WordTrace]
  refine ⟨6901584502973822182991837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18404225341263525821311565 6901584502973822182991837)
  ·
    refine ⟨2588094188615183318621939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6901584502973822182991837 2588094188615183318621939)
    ·
      refine ⟨3882141282922774977932909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2588094188615183318621939 3882141282922774977932909)
      ·
        refine ⟨1455802981096040616724841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3882141282922774977932909 1455802981096040616724841)
        ·
          refine ⟨1091852235822030462543631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1455802981096040616724841 1091852235822030462543631)
          ·
            refine ⟨1637778353733045693815447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1091852235822030462543631 1637778353733045693815447)
            ·
              refine ⟨2456667530599568540723171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1637778353733045693815447 2456667530599568540723171)
              ·
                refine ⟨3685001295899352811084757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2456667530599568540723171 3685001295899352811084757)
                ·
                  refine ⟨86367217872641081509799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3685001295899352811084757 86367217872641081509799)
                  ·
                    rfl

theorem cell22_756898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_756898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_756898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_756898 prefixEnd_756898 := by exact prefixLift 756898
  have htrace : WordTrace (prefixWord ++ tailWord_756898) baseStart_756898 baseEnd_756898 := by
    simpa [prefixWord, tailWord_756898, baseEnd_756898] using wordTrace_append hprefix tailTrace_756898
  have hstable : (prefixWord ++ tailWord_756898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756898).length < 2 ^ (prefixWord ++ tailWord_756898).sum := by decide
  have hdescent : baseEnd_756898 < baseStart_756898 := by decide
  rcases family_descends (prefixWord ++ tailWord_756898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756960 : List Nat := [2, 1, 1, 3, 1, 5, 3, 2, 4]
def baseStart_756960 : Nat := 118140960795 + 756960 * 2 ^ 59
def prefixEnd_756960 : Nat := 4983230072969 + 3 ^ 40 * 756960 * 2
def baseEnd_756960 : Nat := 86374292494991916493069

theorem tailTrace_756960 : CollatzResearch.WordTrace tailWord_756960 prefixEnd_756960 86374292494991916493069 := by
  unfold tailWord_756960
  simp only [CollatzResearch.WordTrace]
  refine ⟨13804299668835336660362167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18405732891780448880482889 13804299668835336660362167)
  ·
    refine ⟨20706449503253004990543251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13804299668835336660362167 20706449503253004990543251)
    ·
      refine ⟨31059674254879507485814877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20706449503253004990543251 31059674254879507485814877)
      ·
        refine ⟨11647377845579815307180579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31059674254879507485814877 11647377845579815307180579)
        ·
          refine ⟨17471066768369722960770869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11647377845579815307180579 17471066768369722960770869)
          ·
            refine ⟨1637912509534661527572269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17471066768369722960770869 1637912509534661527572269)
            ·
              refine ⟨614217191075498072839601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1637912509534661527572269 614217191075498072839601)
              ·
                refine ⟨460662893306623554629701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 614217191075498072839601 460662893306623554629701)
                ·
                  refine ⟨86374292494991916493069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 460662893306623554629701 86374292494991916493069)
                  ·
                    rfl

theorem cell22_756960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 2, 4].length) (baseStart_756960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_756960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_756960 prefixEnd_756960 := by exact prefixLift 756960
  have htrace : WordTrace (prefixWord ++ tailWord_756960) baseStart_756960 baseEnd_756960 := by
    simpa [prefixWord, tailWord_756960, baseEnd_756960] using wordTrace_append hprefix tailTrace_756960
  have hstable : (prefixWord ++ tailWord_756960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756960).length < 2 ^ (prefixWord ++ tailWord_756960).sum := by decide
  have hdescent : baseEnd_756960 < baseStart_756960 := by decide
  rcases family_descends (prefixWord ++ tailWord_756960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756971 : List Nat := [1, 1, 1, 1, 2, 7, 2, 7]
def baseStart_756971 : Nat := 118140960795 + 756971 * 2 ^ 59
def prefixEnd_756971 : Nat := 4983230072969 + 3 ^ 40 * 756971 * 2
def baseEnd_756971 : Nat := 28791849223308376383797

theorem tailTrace_756971 : CollatzResearch.WordTrace tailWord_756971 prefixEnd_756971 28791849223308376383797 := by
  unfold tailWord_756971
  simp only [CollatzResearch.WordTrace]
  refine ⟨27609000540630822199374767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18406000360420548132916511 27609000540630822199374767)
  ·
    refine ⟨41413500810946233299062151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27609000540630822199374767 41413500810946233299062151)
    ·
      refine ⟨62120251216419349948593227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41413500810946233299062151 62120251216419349948593227)
      ·
        refine ⟨93180376824629024922889841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62120251216419349948593227 93180376824629024922889841)
        ·
          refine ⟨69885282618471768692167381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93180376824629024922889841 69885282618471768692167381)
          ·
            refine ⟨1637936311370432078722673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 69885282618471768692167381 1637936311370432078722673)
            ·
              refine ⟨1228452233527824059042005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1637936311370432078722673 1228452233527824059042005)
              ·
                refine ⟨28791849223308376383797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1228452233527824059042005 28791849223308376383797)
                ·
                  rfl

theorem cell22_756971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 7].length) (baseStart_756971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_756971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_756971 prefixEnd_756971 := by exact prefixLift 756971
  have htrace : WordTrace (prefixWord ++ tailWord_756971) baseStart_756971 baseEnd_756971 := by
    simpa [prefixWord, tailWord_756971, baseEnd_756971] using wordTrace_append hprefix tailTrace_756971
  have hstable : (prefixWord ++ tailWord_756971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756971).length < 2 ^ (prefixWord ++ tailWord_756971).sum := by decide
  have hdescent : baseEnd_756971 < baseStart_756971 := by decide
  rcases family_descends (prefixWord ++ tailWord_756971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756975 : List Nat := [1, 1, 2, 1, 7, 1, 1, 3, 2, 3]
def baseStart_756975 : Nat := 118140960795 + 756975 * 2 ^ 59
def prefixEnd_756975 : Nat := 4983230072969 + 3 ^ 40 * 756975 * 2
def baseEnd_756975 : Nat := 259128012291520710354161

theorem tailTrace_756975 : CollatzResearch.WordTrace tailWord_756975 prefixEnd_756975 259128012291520710354161 := by
  unfold tailWord_756975
  simp only [CollatzResearch.WordTrace]
  refine ⟨27609146432616330882520379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18406097621744220588346919 27609146432616330882520379)
  ·
    refine ⟨41413719648924496323780569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27609146432616330882520379 41413719648924496323780569)
    ·
      refine ⟨31060289736693372242835427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41413719648924496323780569 31060289736693372242835427)
      ·
        refine ⟨46590434605040058364253141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31060289736693372242835427 46590434605040058364253141)
        ·
          refine ⟨1091963311055626367912183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 46590434605040058364253141 1091963311055626367912183)
          ·
            refine ⟨1637944966583439551868275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1091963311055626367912183 1637944966583439551868275)
            ·
              refine ⟨2456917449875159327802413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1637944966583439551868275 2456917449875159327802413)
              ·
                refine ⟨921344043703184747925905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2456917449875159327802413 921344043703184747925905)
                ·
                  refine ⟨691008032777388560944429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 921344043703184747925905 691008032777388560944429)
                  ·
                    refine ⟨259128012291520710354161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 691008032777388560944429 259128012291520710354161)
                    ·
                      rfl

theorem cell22_756975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 2, 3].length) (baseStart_756975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_756975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_756975 prefixEnd_756975 := by exact prefixLift 756975
  have htrace : WordTrace (prefixWord ++ tailWord_756975) baseStart_756975 baseEnd_756975 := by
    simpa [prefixWord, tailWord_756975, baseEnd_756975] using wordTrace_append hprefix tailTrace_756975
  have hstable : (prefixWord ++ tailWord_756975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756975).length < 2 ^ (prefixWord ++ tailWord_756975).sum := by decide
  have hdescent : baseEnd_756975 < baseStart_756975 := by decide
  rcases family_descends (prefixWord ++ tailWord_756975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_756990 : List Nat := [4, 2, 2, 1, 1, 3, 2, 1, 2, 4]
def baseStart_756990 : Nat := 118140960795 + 756990 * 2 ^ 59
def prefixEnd_756990 : Nat := 4983230072969 + 3 ^ 40 * 756990 * 2
def baseEnd_756990 : Nat := 259133147098065671229115

theorem tailTrace_756990 : CollatzResearch.WordTrace tailWord_756990 prefixEnd_756990 259133147098065671229115 := by
  unfold tailWord_756990
  simp only [CollatzResearch.WordTrace]
  refine ⟨3451211690945248555539553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18406462351707992296210949 3451211690945248555539553)
  ·
    refine ⟨2588408768208936416654665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3451211690945248555539553 2588408768208936416654665)
    ·
      refine ⟨1941306576156702312490999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2588408768208936416654665 1941306576156702312490999)
      ·
        refine ⟨2911959864235053468736499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1941306576156702312490999 2911959864235053468736499)
        ·
          refine ⟨4367939796352580203104749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2911959864235053468736499 4367939796352580203104749)
          ·
            refine ⟨1637977423632217576164281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4367939796352580203104749 1637977423632217576164281)
            ·
              refine ⟨1228483067724163182123211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1637977423632217576164281 1228483067724163182123211)
              ·
                refine ⟨1842724601586244773184817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1228483067724163182123211 1842724601586244773184817)
                ·
                  refine ⟨1382043451189683579888613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1842724601586244773184817 1382043451189683579888613)
                  ·
                    refine ⟨259133147098065671229115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1382043451189683579888613 259133147098065671229115)
                    ·
                      rfl

theorem cell22_756990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_756990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_756990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_756990 prefixEnd_756990 := by exact prefixLift 756990
  have htrace : WordTrace (prefixWord ++ tailWord_756990) baseStart_756990 baseEnd_756990 := by
    simpa [prefixWord, tailWord_756990, baseEnd_756990] using wordTrace_append hprefix tailTrace_756990
  have hstable : (prefixWord ++ tailWord_756990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_756990).length < 2 ^ (prefixWord ++ tailWord_756990).sum := by decide
  have hdescent : baseEnd_756990 < baseStart_756990 := by decide
  rcases family_descends (prefixWord ++ tailWord_756990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757022 : List Nat := [4, 3, 2, 1, 2, 2, 1, 7]
def baseStart_757022 : Nat := 118140960795 + 757022 * 2 ^ 59
def prefixEnd_757022 : Nat := 4983230072969 + 3 ^ 40 * 757022 * 2
def baseEnd_757022 : Nat := 28793789039114250492113

theorem tailTrace_757022 : CollatzResearch.WordTrace tailWord_757022 prefixEnd_757022 28793789039114250492113 := by
  unfold tailWord_757022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3451357582930757238685165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18407240442297371939654213 3451357582930757238685165)
  ·
    refine ⟨1294259093599033964506937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3451357582930757238685165 1294259093599033964506937)
    ·
      refine ⟨970694320199275473380203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1294259093599033964506937 970694320199275473380203)
      ·
        refine ⟨1456041480298913210070305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 970694320199275473380203 1456041480298913210070305)
        ·
          refine ⟨1092031110224184907552729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1456041480298913210070305 1092031110224184907552729)
          ·
            refine ⟨819023332668138680664547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1092031110224184907552729 819023332668138680664547)
            ·
              refine ⟨1228534999002208020996821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 819023332668138680664547 1228534999002208020996821)
              ·
                refine ⟨28793789039114250492113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1228534999002208020996821 28793789039114250492113)
                ·
                  rfl

theorem cell22_757022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 7].length) (baseStart_757022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_757022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_757022 prefixEnd_757022 := by exact prefixLift 757022
  have htrace : WordTrace (prefixWord ++ tailWord_757022) baseStart_757022 baseEnd_757022 := by
    simpa [prefixWord, tailWord_757022, baseEnd_757022] using wordTrace_append hprefix tailTrace_757022
  have hstable : (prefixWord ++ tailWord_757022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757022).length < 2 ^ (prefixWord ++ tailWord_757022).sum := by decide
  have hdescent : baseEnd_757022 < baseStart_757022 := by decide
  rcases family_descends (prefixWord ++ tailWord_757022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757037 : List Nat := [1, 5, 3, 1, 1, 2, 1, 2, 3, 3]
def baseStart_757037 : Nat := 118140960795 + 757037 * 2 ^ 59
def prefixEnd_757037 : Nat := 4983230072969 + 3 ^ 40 * 757037 * 2
def baseEnd_757037 : Nat := 259149236158573215303971

theorem tailTrace_757037 : CollatzResearch.WordTrace tailWord_757037 prefixEnd_757037 259149236158573215303971 := by
  unfold tailWord_757037
  simp only [CollatzResearch.WordTrace]
  refine ⟨27611407758391715471277365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18407605172261143647518243 27611407758391715471277365)
  ·
    refine ⟨2588569477349223325432253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27611407758391715471277365 2588569477349223325432253)
    ·
      refine ⟨970713554005958747037095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2588569477349223325432253 970713554005958747037095)
      ·
        refine ⟨1456070331008938120555643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 970713554005958747037095 1456070331008938120555643)
        ·
          refine ⟨2184105496513407180833465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1456070331008938120555643 2184105496513407180833465)
          ·
            refine ⟨1638079122385055385625099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2184105496513407180833465 1638079122385055385625099)
            ·
              refine ⟨2457118683577583078437649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1638079122385055385625099 2457118683577583078437649)
              ·
                refine ⟨1842839012683187308828237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2457118683577583078437649 1842839012683187308828237)
                ·
                  refine ⟨691064629756195240810589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1842839012683187308828237 691064629756195240810589)
                  ·
                    refine ⟨259149236158573215303971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 691064629756195240810589 259149236158573215303971)
                    ·
                      rfl

theorem cell22_757037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_757037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_757037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_757037 prefixEnd_757037 := by exact prefixLift 757037
  have htrace : WordTrace (prefixWord ++ tailWord_757037) baseStart_757037 baseEnd_757037 := by
    simpa [prefixWord, tailWord_757037, baseEnd_757037] using wordTrace_append hprefix tailTrace_757037
  have hstable : (prefixWord ++ tailWord_757037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757037).length < 2 ^ (prefixWord ++ tailWord_757037).sum := by decide
  have hdescent : baseEnd_757037 < baseStart_757037 := by decide
  rcases family_descends (prefixWord ++ tailWord_757037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757123 : List Nat := [1, 1, 1, 3, 5, 3, 8]
def baseStart_757123 : Nat := 118140960795 + 757123 * 2 ^ 59
def prefixEnd_757123 : Nat := 4983230072969 + 3 ^ 40 * 757123 * 2
def baseEnd_757123 : Nat := 9599210211707320653841

theorem tailTrace_757123 : CollatzResearch.WordTrace tailWord_757123 prefixEnd_757123 9599210211707320653841 := by
  unfold tailWord_757123
  simp only [CollatzResearch.WordTrace]
  refine ⟨27614544436080152158908023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18409696290720101439272015 27614544436080152158908023)
  ·
    refine ⟨41421816654120228238362035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27614544436080152158908023 41421816654120228238362035)
    ·
      refine ⟨62132724981180342357543053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41421816654120228238362035 62132724981180342357543053)
      ·
        refine ⟨23299771867942628384078645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62132724981180342357543053 23299771867942628384078645)
        ·
          refine ⟨2184353612619621411007373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23299771867942628384078645 2184353612619621411007373)
          ·
            refine ⟨819132604732358029127765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2184353612619621411007373 819132604732358029127765)
            ·
              refine ⟨9599210211707320653841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 819132604732358029127765 9599210211707320653841)
              ·
                rfl

theorem cell22_757123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 8].length) (baseStart_757123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_757123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_757123 prefixEnd_757123 := by exact prefixLift 757123
  have htrace : WordTrace (prefixWord ++ tailWord_757123) baseStart_757123 baseEnd_757123 := by
    simpa [prefixWord, tailWord_757123, baseEnd_757123] using wordTrace_append hprefix tailTrace_757123
  have hstable : (prefixWord ++ tailWord_757123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757123).length < 2 ^ (prefixWord ++ tailWord_757123).sum := by decide
  have hdescent : baseEnd_757123 < baseStart_757123 := by decide
  rcases family_descends (prefixWord ++ tailWord_757123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757140 : List Nat := [2, 4, 2, 1, 2, 2, 2, 7]
def baseStart_757140 : Nat := 118140960795 + 757140 * 2 ^ 59
def prefixEnd_757140 : Nat := 4983230072969 + 3 ^ 40 * 757140 * 2
def baseEnd_757140 : Nat := 28798277240390586664295

theorem tailTrace_757140 : CollatzResearch.WordTrace tailWord_757140 prefixEnd_757140 28798277240390586664295 := by
  unfold tailWord_757140
  simp only [CollatzResearch.WordTrace]
  refine ⟨13807582238509282031138437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18410109651345709374851249 13807582238509282031138437)
  ·
    refine ⟨2588921669720490380838457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13807582238509282031138437 2588921669720490380838457)
    ·
      refine ⟨1941691252290367785628843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2588921669720490380838457 1941691252290367785628843)
      ·
        refine ⟨2912536878435551678443265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1941691252290367785628843 2912536878435551678443265)
        ·
          refine ⟨2184402658826663758832449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2912536878435551678443265 2184402658826663758832449)
          ·
            refine ⟨1638301994119997819124337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2184402658826663758832449 1638301994119997819124337)
            ·
              refine ⟨1228726495589998364343253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1638301994119997819124337 1228726495589998364343253)
              ·
                refine ⟨28798277240390586664295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1228726495589998364343253 28798277240390586664295)
                ·
                  rfl

theorem cell22_757140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 7].length) (baseStart_757140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_757140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_757140 prefixEnd_757140 := by exact prefixLift 757140
  have htrace : WordTrace (prefixWord ++ tailWord_757140) baseStart_757140 baseEnd_757140 := by
    simpa [prefixWord, tailWord_757140, baseEnd_757140] using wordTrace_append hprefix tailTrace_757140
  have hstable : (prefixWord ++ tailWord_757140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757140).length < 2 ^ (prefixWord ++ tailWord_757140).sum := by decide
  have hdescent : baseEnd_757140 < baseStart_757140 := by decide
  rcases family_descends (prefixWord ++ tailWord_757140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757215 : List Nat := [1, 1, 2, 3, 3, 1, 2, 4, 1, 4]
def baseStart_757215 : Nat := 118140960795 + 757215 * 2 ^ 59
def prefixEnd_757215 : Nat := 4983230072969 + 3 ^ 40 * 757215 * 2
def baseEnd_757215 : Nat := 259210169196240084353425

theorem tailTrace_757215 : CollatzResearch.WordTrace tailWord_757215 prefixEnd_757215 259210169196240084353425 := by
  unfold tailWord_757215
  simp only [CollatzResearch.WordTrace]
  refine ⟨27617899951746851871257099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18411933301164567914171399 27617899951746851871257099)
  ·
    refine ⟨41426849927620277806885649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27617899951746851871257099 41426849927620277806885649)
    ·
      refine ⟨31070137445715208355164237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41426849927620277806885649 31070137445715208355164237)
      ·
        refine ⟨11651301542143203133186589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31070137445715208355164237 11651301542143203133186589)
        ·
          refine ⟨4369238078303701174944971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11651301542143203133186589 4369238078303701174944971)
          ·
            refine ⟨6553857117455551762417457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4369238078303701174944971 6553857117455551762417457)
            ·
              refine ⟨4915392838091663821813093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6553857117455551762417457 4915392838091663821813093)
              ·
                refine ⟨921636157142186966589955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4915392838091663821813093 921636157142186966589955)
                ·
                  refine ⟨1382454235713280449884933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 921636157142186966589955 1382454235713280449884933)
                  ·
                    refine ⟨259210169196240084353425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1382454235713280449884933 259210169196240084353425)
                    ·
                      rfl

theorem cell22_757215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 4].length) (baseStart_757215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_757215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_757215 prefixEnd_757215 := by exact prefixLift 757215
  have htrace : WordTrace (prefixWord ++ tailWord_757215) baseStart_757215 baseEnd_757215 := by
    simpa [prefixWord, tailWord_757215, baseEnd_757215] using wordTrace_append hprefix tailTrace_757215
  have hstable : (prefixWord ++ tailWord_757215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757215).length < 2 ^ (prefixWord ++ tailWord_757215).sum := by decide
  have hdescent : baseEnd_757215 < baseStart_757215 := by decide
  rcases family_descends (prefixWord ++ tailWord_757215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757228 : List Nat := [2, 2, 1, 1, 2, 1, 2, 3, 3, 5]
def baseStart_757228 : Nat := 118140960795 + 757228 * 2 ^ 59
def prefixEnd_757228 : Nat := 4983230072969 + 3 ^ 40 * 757228 * 2
def baseEnd_757228 : Nat := 259214619361912383778385

theorem tailTrace_757228 : CollatzResearch.WordTrace tailWord_757228 prefixEnd_757228 259214619361912383778385 := by
  unfold tailWord_757228
  simp only [CollatzResearch.WordTrace]
  refine ⟨13809187050349877545740169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18412249400466503394320225 13809187050349877545740169)
  ·
    refine ⟨10356890287762408159305127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13809187050349877545740169 10356890287762408159305127)
    ·
      refine ⟨15535335431643612238957691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10356890287762408159305127 15535335431643612238957691)
      ·
        refine ⟨23303003147465418358436537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15535335431643612238957691 23303003147465418358436537)
        ·
          refine ⟨17477252360599063768827403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23303003147465418358436537 17477252360599063768827403)
          ·
            refine ⟨26215878540898595653241105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17477252360599063768827403 26215878540898595653241105)
            ·
              refine ⟨19661908905673946739930829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26215878540898595653241105 19661908905673946739930829)
              ·
                refine ⟨7373215839627730027474061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19661908905673946739930829 7373215839627730027474061)
                ·
                  refine ⟨2764955939860398760302773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7373215839627730027474061 2764955939860398760302773)
                  ·
                    refine ⟨259214619361912383778385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2764955939860398760302773 259214619361912383778385)
                    ·
                      rfl

theorem cell22_757228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_757228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_757228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_757228 prefixEnd_757228 := by exact prefixLift 757228
  have htrace : WordTrace (prefixWord ++ tailWord_757228) baseStart_757228 baseEnd_757228 := by
    simpa [prefixWord, tailWord_757228, baseEnd_757228] using wordTrace_append hprefix tailTrace_757228
  have hstable : (prefixWord ++ tailWord_757228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757228).length < 2 ^ (prefixWord ++ tailWord_757228).sum := by decide
  have hdescent : baseEnd_757228 < baseStart_757228 := by decide
  rcases family_descends (prefixWord ++ tailWord_757228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757232 : List Nat := [2, 1, 1, 1, 3, 4, 4, 1, 1, 4]
def baseStart_757232 : Nat := 118140960795 + 757232 * 2 ^ 59
def prefixEnd_757232 : Nat := 4983230072969 + 3 ^ 40 * 757232 * 2
def baseEnd_757232 : Nat := 259215988643657706678373

theorem tailTrace_757232 : CollatzResearch.WordTrace tailWord_757232 prefixEnd_757232 259215988643657706678373 := by
  unfold tailWord_757232
  simp only [CollatzResearch.WordTrace]
  refine ⟨13809259996342631887312975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18412346661790175849750633 13809259996342631887312975)
  ·
    refine ⟨20713889994513947830969463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13809259996342631887312975 20713889994513947830969463)
    ·
      refine ⟨31070834991770921746454195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20713889994513947830969463 31070834991770921746454195)
      ·
        refine ⟨46606252487656382619681293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31070834991770921746454195 46606252487656382619681293)
        ·
          refine ⟨17477344682871143482380485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46606252487656382619681293 17477344682871143482380485)
          ·
            refine ⟨3277002128038339402946341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17477344682871143482380485 3277002128038339402946341)
            ·
              refine ⟨614437899007188638052439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3277002128038339402946341 614437899007188638052439)
              ·
                refine ⟨921656848510782957078659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 614437899007188638052439 921656848510782957078659)
                ·
                  refine ⟨1382485272766174435617989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 921656848510782957078659 1382485272766174435617989)
                  ·
                    refine ⟨259215988643657706678373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1382485272766174435617989 259215988643657706678373)
                    ·
                      rfl

theorem cell22_757232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 1, 4].length) (baseStart_757232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_757232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_757232 prefixEnd_757232 := by exact prefixLift 757232
  have htrace : WordTrace (prefixWord ++ tailWord_757232) baseStart_757232 baseEnd_757232 := by
    simpa [prefixWord, tailWord_757232, baseEnd_757232] using wordTrace_append hprefix tailTrace_757232
  have hstable : (prefixWord ++ tailWord_757232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757232).length < 2 ^ (prefixWord ++ tailWord_757232).sum := by decide
  have hdescent : baseEnd_757232 < baseStart_757232 := by decide
  rcases family_descends (prefixWord ++ tailWord_757232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757399 : List Nat := [1, 1, 3, 3, 2, 3, 2, 3, 4]
def baseStart_757399 : Nat := 118140960795 + 757399 * 2 ^ 59
def prefixEnd_757399 : Nat := 4983230072969 + 3 ^ 40 * 757399 * 2
def baseEnd_757399 : Nat := 86424385385508312584287

theorem tailTrace_757399 : CollatzResearch.WordTrace tailWord_757399 prefixEnd_757399 86424385385508312584287 := by
  unfold tailWord_757399
  simp only [CollatzResearch.WordTrace]
  refine ⟨27624610983080251295955251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18416407322053500863970167 27624610983080251295955251)
  ·
    refine ⟨41436916474620376943932877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27624610983080251295955251 41436916474620376943932877)
    ·
      refine ⟨15538843677982641353974829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41436916474620376943932877 15538843677982641353974829)
      ·
        refine ⟨5827066379243490507740561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15538843677982641353974829 5827066379243490507740561)
        ·
          refine ⟨4370299784432617880805421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5827066379243490507740561 4370299784432617880805421)
          ·
            refine ⟨1638862419162231705302033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4370299784432617880805421 1638862419162231705302033)
            ·
              refine ⟨1229146814371673778976525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1638862419162231705302033 1229146814371673778976525)
              ·
                refine ⟨460930055389377667116197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1229146814371673778976525 460930055389377667116197)
                ·
                  refine ⟨86424385385508312584287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 460930055389377667116197 86424385385508312584287)
                  ·
                    rfl

theorem cell22_757399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 3, 4].length) (baseStart_757399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_757399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_757399 prefixEnd_757399 := by exact prefixLift 757399
  have htrace : WordTrace (prefixWord ++ tailWord_757399) baseStart_757399 baseEnd_757399 := by
    simpa [prefixWord, tailWord_757399, baseEnd_757399] using wordTrace_append hprefix tailTrace_757399
  have hstable : (prefixWord ++ tailWord_757399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757399).length < 2 ^ (prefixWord ++ tailWord_757399).sum := by decide
  have hdescent : baseEnd_757399 < baseStart_757399 := by decide
  rcases family_descends (prefixWord ++ tailWord_757399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757431 : List Nat := [1, 1, 3, 1, 5, 2, 3, 1, 2, 3]
def baseStart_757431 : Nat := 118140960795 + 757431 * 2 ^ 59
def prefixEnd_757431 : Nat := 4983230072969 + 3 ^ 40 * 757431 * 2
def baseEnd_757431 : Nat := 259284110410487520952763

theorem tailTrace_757431 : CollatzResearch.WordTrace tailWord_757431 prefixEnd_757431 259284110410487520952763 := by
  unfold tailWord_757431
  simp only [CollatzResearch.WordTrace]
  refine ⟨27625778118964320761120147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18417185412642880507413431 27625778118964320761120147)
  ·
    refine ⟨41438667178446481141680221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27625778118964320761120147 41438667178446481141680221)
    ·
      refine ⟨15539500191917430428130083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41438667178446481141680221 15539500191917430428130083)
      ·
        refine ⟨23309250287876145642195125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15539500191917430428130083 23309250287876145642195125)
        ·
          refine ⟨2185242214488388653955793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23309250287876145642195125 2185242214488388653955793)
          ·
            refine ⟨1638931660866291490466845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2185242214488388653955793 1638931660866291490466845)
            ·
              refine ⟨614599372824859308925067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1638931660866291490466845 614599372824859308925067)
              ·
                refine ⟨921899059237288963387601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 614599372824859308925067 921899059237288963387601)
                ·
                  refine ⟨691424294427966722540701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 921899059237288963387601 691424294427966722540701)
                  ·
                    refine ⟨259284110410487520952763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 691424294427966722540701 259284110410487520952763)
                    ·
                      rfl

theorem cell22_757431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 2, 3].length) (baseStart_757431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_757431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_757431 prefixEnd_757431 := by exact prefixLift 757431
  have htrace : WordTrace (prefixWord ++ tailWord_757431) baseStart_757431 baseEnd_757431 := by
    simpa [prefixWord, tailWord_757431, baseEnd_757431] using wordTrace_append hprefix tailTrace_757431
  have hstable : (prefixWord ++ tailWord_757431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757431).length < 2 ^ (prefixWord ++ tailWord_757431).sum := by decide
  have hdescent : baseEnd_757431 < baseStart_757431 := by decide
  rcases family_descends (prefixWord ++ tailWord_757431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757446 : List Nat := [6, 1, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_757446 : Nat := 118140960795 + 757446 * 2 ^ 59
def prefixEnd_757446 : Nat := 4983230072969 + 3 ^ 40 * 757446 * 2
def baseEnd_757446 : Nat := 259289245217032481827717

theorem tailTrace_757446 : CollatzResearch.WordTrace tailWord_757446 prefixEnd_757446 259289245217032481827717 := by
  unfold tailWord_757446
  simp only [CollatzResearch.WordTrace]
  refine ⟨863322662934686822591131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18417550142606652215277461 863322662934686822591131)
  ·
    refine ⟨1294983994402030233886697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 863322662934686822591131 1294983994402030233886697)
    ·
      refine ⟨971237995801522675415023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1294983994402030233886697 971237995801522675415023)
      ·
        refine ⟨1456856993702284013122535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 971237995801522675415023 1456856993702284013122535)
        ·
          refine ⟨2185285490553426019683803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1456856993702284013122535 2185285490553426019683803)
          ·
            refine ⟨3277928235830139029525705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2185285490553426019683803 3277928235830139029525705)
            ·
              refine ⟨2458446176872604272144279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3277928235830139029525705 2458446176872604272144279)
              ·
                refine ⟨3687669265308906408216419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2458446176872604272144279 3687669265308906408216419)
                ·
                  refine ⟨5531503897963359612324629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3687669265308906408216419 5531503897963359612324629)
                  ·
                    refine ⟨259289245217032481827717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5531503897963359612324629 259289245217032481827717)
                    ·
                      rfl

theorem cell22_757446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_757446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_757446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_757446 prefixEnd_757446 := by exact prefixLift 757446
  have htrace : WordTrace (prefixWord ++ tailWord_757446) baseStart_757446 baseEnd_757446 := by
    simpa [prefixWord, tailWord_757446, baseEnd_757446] using wordTrace_append hprefix tailTrace_757446
  have hstable : (prefixWord ++ tailWord_757446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757446).length < 2 ^ (prefixWord ++ tailWord_757446).sum := by decide
  have hdescent : baseEnd_757446 < baseStart_757446 := by decide
  rcases family_descends (prefixWord ++ tailWord_757446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757489 : List Nat := [1, 2, 2, 2, 2, 3, 4, 1, 5]
def baseStart_757489 : Nat := 118140960795 + 757489 * 2 ^ 59
def prefixEnd_757489 : Nat := 4983230072969 + 3 ^ 40 * 757489 * 2
def baseEnd_757489 : Nat := 86434654998598234334195

theorem tailTrace_757489 : CollatzResearch.WordTrace tailWord_757489 prefixEnd_757489 86434654998598234334195 := by
  unfold tailWord_757489
  simp only [CollatzResearch.WordTrace]
  refine ⟨27627893552754196666731521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18418595701836131111154347 27627893552754196666731521)
  ·
    refine ⟨20720920164565647500048641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27627893552754196666731521 20720920164565647500048641)
    ·
      refine ⟨15540690123424235625036481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20720920164565647500048641 15540690123424235625036481)
      ·
        refine ⟨11655517592568176718777361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15540690123424235625036481 11655517592568176718777361)
        ·
          refine ⟨8741638194426132539083021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11655517592568176718777361 8741638194426132539083021)
          ·
            refine ⟨3278114322909799702156133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8741638194426132539083021 3278114322909799702156133)
            ·
              refine ⟨614646435545587444154275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3278114322909799702156133 614646435545587444154275)
              ·
                refine ⟨921969653318381166231413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 614646435545587444154275 921969653318381166231413)
                ·
                  refine ⟨86434654998598234334195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 921969653318381166231413 86434654998598234334195)
                  ·
                    rfl

theorem cell22_757489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 5].length) (baseStart_757489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_757489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_757489 prefixEnd_757489 := by exact prefixLift 757489
  have htrace : WordTrace (prefixWord ++ tailWord_757489) baseStart_757489 baseEnd_757489 := by
    simpa [prefixWord, tailWord_757489, baseEnd_757489] using wordTrace_append hprefix tailTrace_757489
  have hstable : (prefixWord ++ tailWord_757489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757489).length < 2 ^ (prefixWord ++ tailWord_757489).sum := by decide
  have hdescent : baseEnd_757489 < baseStart_757489 := by decide
  rcases family_descends (prefixWord ++ tailWord_757489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757532 : List Nat := [2, 2, 3, 1, 1, 2, 1, 2, 3, 5]
def baseStart_757532 : Nat := 118140960795 + 757532 * 2 ^ 59
def prefixEnd_757532 : Nat := 4983230072969 + 3 ^ 40 * 757532 * 2
def baseEnd_757532 : Nat := 259318684774556924177453

theorem tailTrace_757532 : CollatzResearch.WordTrace tailWord_757532 prefixEnd_757532 259318684774556924177453 := by
  unfold tailWord_757532
  simp only [CollatzResearch.WordTrace]
  refine ⟨13814730945799207505273425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18419641261065610007031233 13814730945799207505273425)
  ·
    refine ⟨10361048209349405628955069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13814730945799207505273425 10361048209349405628955069)
    ·
      refine ⟨3885393078506027110858151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10361048209349405628955069 3885393078506027110858151)
      ·
        refine ⟨5828089617759040666287227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3885393078506027110858151 5828089617759040666287227)
        ·
          refine ⟨8742134426638560999430841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5828089617759040666287227 8742134426638560999430841)
          ·
            refine ⟨6556600819978920749573131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8742134426638560999430841 6556600819978920749573131)
            ·
              refine ⟨9834901229968381124359697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6556600819978920749573131 9834901229968381124359697)
              ·
                refine ⟨7376175922476285843269773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9834901229968381124359697 7376175922476285843269773)
                ·
                  refine ⟨2766065970928607191226165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7376175922476285843269773 2766065970928607191226165)
                  ·
                    refine ⟨259318684774556924177453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2766065970928607191226165 259318684774556924177453)
                    ·
                      rfl

theorem cell22_757532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_757532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_757532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_757532 prefixEnd_757532 := by exact prefixLift 757532
  have htrace : WordTrace (prefixWord ++ tailWord_757532) baseStart_757532 baseEnd_757532 := by
    simpa [prefixWord, tailWord_757532, baseEnd_757532] using wordTrace_append hprefix tailTrace_757532
  have hstable : (prefixWord ++ tailWord_757532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757532).length < 2 ^ (prefixWord ++ tailWord_757532).sum := by decide
  have hdescent : baseEnd_757532 < baseStart_757532 := by decide
  rcases family_descends (prefixWord ++ tailWord_757532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757564 : List Nat := [2, 2, 2, 2, 1, 1, 5, 1, 2, 4]
def baseStart_757564 : Nat := 118140960795 + 757564 * 2 ^ 59
def prefixEnd_757564 : Nat := 4983230072969 + 3 ^ 40 * 757564 * 2
def baseEnd_757564 : Nat := 259329639028519507377355

theorem tailTrace_757564 : CollatzResearch.WordTrace tailWord_757564 prefixEnd_757564 259329639028519507377355 := by
  unfold tailWord_757564
  simp only [CollatzResearch.WordTrace]
  refine ⟨13815314513741242237855873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18420419351654989650474497 13815314513741242237855873)
  ·
    refine ⟨10361485885305931678391905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13815314513741242237855873 10361485885305931678391905)
    ·
      refine ⟨7771114413979448758793929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10361485885305931678391905 7771114413979448758793929)
      ·
        refine ⟨5828335810484586569095447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7771114413979448758793929 5828335810484586569095447)
        ·
          refine ⟨8742503715726879853643171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5828335810484586569095447 8742503715726879853643171)
          ·
            refine ⟨13113755573590319780464757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8742503715726879853643171 13113755573590319780464757)
            ·
              refine ⟨1229414585024092479418571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13113755573590319780464757 1229414585024092479418571)
              ·
                refine ⟨1844121877536138719127857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1229414585024092479418571 1844121877536138719127857)
                ·
                  refine ⟨1383091408152104039345893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1844121877536138719127857 1383091408152104039345893)
                  ·
                    refine ⟨259329639028519507377355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1383091408152104039345893 259329639028519507377355)
                    ·
                      rfl

theorem cell22_757564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_757564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_757564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_757564 prefixEnd_757564 := by exact prefixLift 757564
  have htrace : WordTrace (prefixWord ++ tailWord_757564) baseStart_757564 baseEnd_757564 := by
    simpa [prefixWord, tailWord_757564, baseEnd_757564] using wordTrace_append hprefix tailTrace_757564
  have hstable : (prefixWord ++ tailWord_757564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757564).length < 2 ^ (prefixWord ++ tailWord_757564).sum := by decide
  have hdescent : baseEnd_757564 < baseStart_757564 := by decide
  rcases family_descends (prefixWord ++ tailWord_757564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757658 : List Nat := [3, 1, 1, 4, 2, 3, 2, 1, 5]
def baseStart_757658 : Nat := 118140960795 + 757658 * 2 ^ 59
def prefixEnd_757658 : Nat := 4983230072969 + 3 ^ 40 * 757658 * 2
def baseEnd_757658 : Nat := 86453939049844865175689

theorem tailTrace_757658 : CollatzResearch.WordTrace tailWord_757658 prefixEnd_757658 86453939049844865175689 := by
  unfold tailWord_757658
  simp only [CollatzResearch.WordTrace]
  refine ⟨6908514372285484632408407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18422704992761292353089085 6908514372285484632408407)
  ·
    refine ⟨10362771558428226948612611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6908514372285484632408407 10362771558428226948612611)
    ·
      refine ⟨15544157337642340422918917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10362771558428226948612611 15544157337642340422918917)
      ·
        refine ⟨2914529500807938829297297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15544157337642340422918917 2914529500807938829297297)
        ·
          refine ⟨2185897125605954121972973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2914529500807938829297297 2185897125605954121972973)
          ·
            refine ⟨819711422102232795739865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2185897125605954121972973 819711422102232795739865)
            ·
              refine ⟨614783566576674596804899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 819711422102232795739865 614783566576674596804899)
              ·
                refine ⟨922175349865011895207349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 614783566576674596804899 922175349865011895207349)
                ·
                  refine ⟨86453939049844865175689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 922175349865011895207349 86453939049844865175689)
                  ·
                    rfl

theorem cell22_757658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 5].length) (baseStart_757658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_757658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_757658 prefixEnd_757658 := by exact prefixLift 757658
  have htrace : WordTrace (prefixWord ++ tailWord_757658) baseStart_757658 baseEnd_757658 := by
    simpa [prefixWord, tailWord_757658, baseEnd_757658] using wordTrace_append hprefix tailTrace_757658
  have hstable : (prefixWord ++ tailWord_757658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757658).length < 2 ^ (prefixWord ++ tailWord_757658).sum := by decide
  have hdescent : baseEnd_757658 < baseStart_757658 := by decide
  rcases family_descends (prefixWord ++ tailWord_757658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757671 : List Nat := [1, 1, 6, 1, 2, 2, 1, 1, 3, 4]
def baseStart_757671 : Nat := 118140960795 + 757671 * 2 ^ 59
def prefixEnd_757671 : Nat := 4983230072969 + 3 ^ 40 * 757671 * 2
def baseEnd_757671 : Nat := 259366267315206894952027

theorem tailTrace_757671 : CollatzResearch.WordTrace tailWord_757671 prefixEnd_757671 259366267315206894952027 := by
  unfold tailWord_757671
  simp only [CollatzResearch.WordTrace]
  refine ⟨27634531638094841749856867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18423021092063227833237911 27634531638094841749856867)
  ·
    refine ⟨41451797457142262624785301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27634531638094841749856867 41451797457142262624785301)
    ·
      refine ⟨1943053005803543560536811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 41451797457142262624785301 1943053005803543560536811)
      ·
        refine ⟨2914579508705315340805217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1943053005803543560536811 2914579508705315340805217)
        ·
          refine ⟨2185934631528986505603913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2914579508705315340805217 2185934631528986505603913)
          ·
            refine ⟨1639450973646739879202935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2185934631528986505603913 1639450973646739879202935)
            ·
              refine ⟨2459176460470109818804403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1639450973646739879202935 2459176460470109818804403)
              ·
                refine ⟨3688764690705164728206605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2459176460470109818804403 3688764690705164728206605)
                ·
                  refine ⟨1383286759014436773077477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3688764690705164728206605 1383286759014436773077477)
                  ·
                    refine ⟨259366267315206894952027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1383286759014436773077477 259366267315206894952027)
                    ·
                      rfl

theorem cell22_757671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_757671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_757671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_757671 prefixEnd_757671 := by exact prefixLift 757671
  have htrace : WordTrace (prefixWord ++ tailWord_757671) baseStart_757671 baseEnd_757671 := by
    simpa [prefixWord, tailWord_757671, baseEnd_757671] using wordTrace_append hprefix tailTrace_757671
  have hstable : (prefixWord ++ tailWord_757671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757671).length < 2 ^ (prefixWord ++ tailWord_757671).sum := by decide
  have hdescent : baseEnd_757671 < baseStart_757671 := by decide
  rcases family_descends (prefixWord ++ tailWord_757671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757697 : List Nat := [1, 2, 19]
def baseStart_757697 : Nat := 118140960795 + 757697 * 2 ^ 59
def prefixEnd_757697 : Nat := 4983230072969 + 3 ^ 40 * 757697 * 2
def baseEnd_757697 : Nat := 118598613464358250481

theorem tailTrace_757697 : CollatzResearch.WordTrace tailWord_757697 prefixEnd_757697 118598613464358250481 := by
  unfold tailWord_757697
  simp only [CollatzResearch.WordTrace]
  refine ⟨27635479936000648190303345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18423653290667098793535563 27635479936000648190303345)
  ·
    refine ⟨20726609952000486142727509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27635479936000648190303345 20726609952000486142727509)
    ·
      refine ⟨118598613464358250481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 19 20726609952000486142727509 118598613464358250481)
      ·
        rfl

theorem cell22_757697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 19].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 19].length) (baseStart_757697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_757697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_757697 prefixEnd_757697 := by exact prefixLift 757697
  have htrace : WordTrace (prefixWord ++ tailWord_757697) baseStart_757697 baseEnd_757697 := by
    simpa [prefixWord, tailWord_757697, baseEnd_757697] using wordTrace_append hprefix tailTrace_757697
  have hstable : (prefixWord ++ tailWord_757697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757697).length < 2 ^ (prefixWord ++ tailWord_757697).sum := by decide
  have hdescent : baseEnd_757697 < baseStart_757697 := by decide
  rcases family_descends (prefixWord ++ tailWord_757697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757731 : List Nat := [1, 1, 1, 6, 1, 3, 3, 6]
def baseStart_757731 : Nat := 118140960795 + 757731 * 2 ^ 59
def prefixEnd_757731 : Nat := 4983230072969 + 3 ^ 40 * 757731 * 2
def baseEnd_757731 : Nat := 28820756282376304272427

theorem tailTrace_757731 : CollatzResearch.WordTrace tailWord_757731 prefixEnd_757731 28820756282376304272427 := by
  unfold tailWord_757731
  simp only [CollatzResearch.WordTrace]
  refine ⟨27636720017877471997041047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18424480011918314664694031 27636720017877471997041047)
  ·
    refine ⟨41455080026816207995561571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27636720017877471997041047 41455080026816207995561571)
    ·
      refine ⟨62182620040224311993342357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41455080026816207995561571 62182620040224311993342357)
      ·
        refine ⟨2914810314385514624687923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 62182620040224311993342357 2914810314385514624687923)
        ·
          refine ⟨4372215471578271937031885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2914810314385514624687923 4372215471578271937031885)
          ·
            refine ⟨1639580801841851976386957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4372215471578271937031885 1639580801841851976386957)
            ·
              refine ⟨614842800690694491145109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1639580801841851976386957 614842800690694491145109)
              ·
                refine ⟨28820756282376304272427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 614842800690694491145109 28820756282376304272427)
                ·
                  rfl

theorem cell22_757731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 6].length) (baseStart_757731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_757731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_757731 prefixEnd_757731 := by exact prefixLift 757731
  have htrace : WordTrace (prefixWord ++ tailWord_757731) baseStart_757731 baseEnd_757731 := by
    simpa [prefixWord, tailWord_757731, baseEnd_757731] using wordTrace_append hprefix tailTrace_757731
  have hstable : (prefixWord ++ tailWord_757731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757731).length < 2 ^ (prefixWord ++ tailWord_757731).sum := by decide
  have hdescent : baseEnd_757731 < baseStart_757731 := by decide
  rcases family_descends (prefixWord ++ tailWord_757731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757819 : List Nat := [1, 1, 1, 1, 1, 2, 1, 6, 3, 5]
def baseStart_757819 : Nat := 118140960795 + 757819 * 2 ^ 59
def prefixEnd_757819 : Nat := 4983230072969 + 3 ^ 40 * 757819 * 2
def baseEnd_757819 : Nat := 259416930739783842251573

theorem tailTrace_757819 : CollatzResearch.WordTrace tailWord_757819 prefixEnd_757819 259416930739783842251573 := by
  unfold tailWord_757819
  simp only [CollatzResearch.WordTrace]
  refine ⟨27639929641558663026244511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18426619761039108684163007 27639929641558663026244511)
  ·
    refine ⟨41459894462337994539366767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27639929641558663026244511 41459894462337994539366767)
    ·
      refine ⟨62189841693506991809050151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41459894462337994539366767 62189841693506991809050151)
      ·
        refine ⟨93284762540260487713575227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62189841693506991809050151 93284762540260487713575227)
        ·
          refine ⟨139927143810390731570362841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93284762540260487713575227 139927143810390731570362841)
          ·
            refine ⟨104945357857793048677772131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139927143810390731570362841 104945357857793048677772131)
            ·
              refine ⟨157418036786689573016658197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104945357857793048677772131 157418036786689573016658197)
              ·
                refine ⟨7378970474376073735155853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 157418036786689573016658197 7378970474376073735155853)
                ·
                  refine ⟨2767113927891027650683445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7378970474376073735155853 2767113927891027650683445)
                  ·
                    refine ⟨259416930739783842251573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2767113927891027650683445 259416930739783842251573)
                    ·
                      rfl

theorem cell22_757819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 5].length) (baseStart_757819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_757819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_757819 prefixEnd_757819 := by exact prefixLift 757819
  have htrace : WordTrace (prefixWord ++ tailWord_757819) baseStart_757819 baseEnd_757819 := by
    simpa [prefixWord, tailWord_757819, baseEnd_757819] using wordTrace_append hprefix tailTrace_757819
  have hstable : (prefixWord ++ tailWord_757819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757819).length < 2 ^ (prefixWord ++ tailWord_757819).sum := by decide
  have hdescent : baseEnd_757819 < baseStart_757819 := by decide
  rcases family_descends (prefixWord ++ tailWord_757819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757849 : List Nat := [1, 2, 1, 2, 2, 1, 3, 10]
def baseStart_757849 : Nat := 118140960795 + 757849 * 2 ^ 59
def prefixEnd_757849 : Nat := 4983230072969 + 3 ^ 40 * 757849 * 2
def baseEnd_757849 : Nat := 28825244483652640444609

theorem tailTrace_757849 : CollatzResearch.WordTrace tailWord_757849 prefixEnd_757849 28825244483652640444609 := by
  unfold tailWord_757849
  simp only [CollatzResearch.WordTrace]
  refine ⟨27641023831449978149836601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18427349220966652099891067 27641023831449978149836601)
  ·
    refine ⟨20730767873587483612377451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27641023831449978149836601 20730767873587483612377451)
    ·
      refine ⟨31096151810381225418566177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20730767873587483612377451 31096151810381225418566177)
      ·
        refine ⟨23322113857785919063924633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31096151810381225418566177 23322113857785919063924633)
        ·
          refine ⟨17491585393339439297943475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23322113857785919063924633 17491585393339439297943475)
          ·
            refine ⟨26237378090009158946915213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17491585393339439297943475 26237378090009158946915213)
            ·
              refine ⟨9839016783753434605093205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26237378090009158946915213 9839016783753434605093205)
              ·
                refine ⟨28825244483652640444609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 9839016783753434605093205 28825244483652640444609)
                ·
                  rfl

theorem cell22_757849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 10].length) (baseStart_757849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_757849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_757849 prefixEnd_757849 := by exact prefixLift 757849
  have htrace : WordTrace (prefixWord ++ tailWord_757849) baseStart_757849 baseEnd_757849 := by
    simpa [prefixWord, tailWord_757849, baseEnd_757849] using wordTrace_append hprefix tailTrace_757849
  have hstable : (prefixWord ++ tailWord_757849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757849).length < 2 ^ (prefixWord ++ tailWord_757849).sum := by decide
  have hdescent : baseEnd_757849 < baseStart_757849 := by decide
  rcases family_descends (prefixWord ++ tailWord_757849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757853 : List Nat := [1, 4, 4, 1, 1, 1, 1, 1, 3, 5]
def baseStart_757853 : Nat := 118140960795 + 757853 * 2 ^ 59
def prefixEnd_757853 : Nat := 4983230072969 + 3 ^ 40 * 757853 * 2
def baseEnd_757853 : Nat := 259428569634619086901469

theorem tailTrace_757853 : CollatzResearch.WordTrace tailWord_757853 prefixEnd_757853 259428569634619086901469 := by
  unfold tailWord_757853
  simp only [CollatzResearch.WordTrace]
  refine ⟨27641169723435486832982213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18427446482290324555321475 27641169723435486832982213)
  ·
    refine ⟨5182719323144153781184165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27641169723435486832982213 5182719323144153781184165)
    ·
      refine ⟨971759873089528833972031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5182719323144153781184165 971759873089528833972031)
      ·
        refine ⟨1457639809634293250958047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 971759873089528833972031 1457639809634293250958047)
        ·
          refine ⟨2186459714451439876437071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1457639809634293250958047 2186459714451439876437071)
          ·
            refine ⟨3279689571677159814655607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2186459714451439876437071 3279689571677159814655607)
            ·
              refine ⟨4919534357515739721983411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3279689571677159814655607 4919534357515739721983411)
              ·
                refine ⟨7379301536273609582975117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4919534357515739721983411 7379301536273609582975117)
                ·
                  refine ⟨2767238076102603593615669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7379301536273609582975117 2767238076102603593615669)
                  ·
                    refine ⟨259428569634619086901469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2767238076102603593615669 259428569634619086901469)
                    ·
                      rfl

theorem cell22_757853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_757853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_757853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_757853 prefixEnd_757853 := by exact prefixLift 757853
  have htrace : WordTrace (prefixWord ++ tailWord_757853) baseStart_757853 baseEnd_757853 := by
    simpa [prefixWord, tailWord_757853, baseEnd_757853] using wordTrace_append hprefix tailTrace_757853
  have hstable : (prefixWord ++ tailWord_757853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757853).length < 2 ^ (prefixWord ++ tailWord_757853).sum := by decide
  have hdescent : baseEnd_757853 < baseStart_757853 := by decide
  rcases family_descends (prefixWord ++ tailWord_757853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757866 : List Nat := [3, 1, 3, 2, 3, 10]
def baseStart_757866 : Nat := 118140960795 + 757866 * 2 ^ 59
def prefixEnd_757866 : Nat := 4983230072969 + 3 ^ 40 * 757866 * 2
def baseEnd_757866 : Nat := 3202876787657918349709

theorem tailTrace_757866 : CollatzResearch.WordTrace tailWord_757866 prefixEnd_757866 3202876787657918349709 := by
  unfold tailWord_757866
  simp only [CollatzResearch.WordTrace]
  refine ⟨6910410968097097513301363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18427762581592260035470301 6910410968097097513301363)
  ·
    refine ⟨10365616452145646269952045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6910410968097097513301363 10365616452145646269952045)
    ·
      refine ⟨3887106169554617351232017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10365616452145646269952045 3887106169554617351232017)
      ·
        refine ⟨2915329627165963013424013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3887106169554617351232017 2915329627165963013424013)
        ·
          refine ⟨1093248610187236130034005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2915329627165963013424013 1093248610187236130034005)
          ·
            refine ⟨3202876787657918349709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1093248610187236130034005 3202876787657918349709)
            ·
              rfl

theorem cell22_757866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 10].length) (baseStart_757866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_757866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_757866 prefixEnd_757866 := by exact prefixLift 757866
  have htrace : WordTrace (prefixWord ++ tailWord_757866) baseStart_757866 baseEnd_757866 := by
    simpa [prefixWord, tailWord_757866, baseEnd_757866] using wordTrace_append hprefix tailTrace_757866
  have hstable : (prefixWord ++ tailWord_757866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757866).length < 2 ^ (prefixWord ++ tailWord_757866).sum := by decide
  have hdescent : baseEnd_757866 < baseStart_757866 := by decide
  rcases family_descends (prefixWord ++ tailWord_757866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757870 : List Nat := [4, 1, 2, 2, 1, 1, 4, 2, 2, 3]
def baseStart_757870 : Nat := 118140960795 + 757870 * 2 ^ 59
def prefixEnd_757870 : Nat := 4983230072969 + 3 ^ 40 * 757870 * 2
def baseEnd_757870 : Nat := 259434389082036709226417

theorem tailTrace_757870 : CollatzResearch.WordTrace tailWord_757870 prefixEnd_757870 259434389082036709226417 := by
  unfold tailWord_757870
  simp only [CollatzResearch.WordTrace]
  refine ⟨3455223720546737342043883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18427859842915932490900709 3455223720546737342043883)
  ·
    refine ⟨5182835580820106013065825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3455223720546737342043883 5182835580820106013065825)
    ·
      refine ⟨3887126685615079509799369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5182835580820106013065825 3887126685615079509799369)
      ·
        refine ⟨2915345014211309632349527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3887126685615079509799369 2915345014211309632349527)
        ·
          refine ⟨4373017521316964448524291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2915345014211309632349527 4373017521316964448524291)
          ·
            refine ⟨6559526281975446672786437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4373017521316964448524291 6559526281975446672786437)
            ·
              refine ⟨1229911177870396251147457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6559526281975446672786437 1229911177870396251147457)
              ·
                refine ⟨922433383402797188360593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1229911177870396251147457 922433383402797188360593)
                ·
                  refine ⟨691825037552097891270445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 922433383402797188360593 691825037552097891270445)
                  ·
                    refine ⟨259434389082036709226417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 691825037552097891270445 259434389082036709226417)
                    ·
                      rfl

theorem cell22_757870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_757870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_757870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_757870 prefixEnd_757870 := by exact prefixLift 757870
  have htrace : WordTrace (prefixWord ++ tailWord_757870) baseStart_757870 baseEnd_757870 := by
    simpa [prefixWord, tailWord_757870, baseEnd_757870] using wordTrace_append hprefix tailTrace_757870
  have hstable : (prefixWord ++ tailWord_757870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757870).length < 2 ^ (prefixWord ++ tailWord_757870).sum := by decide
  have hdescent : baseEnd_757870 < baseStart_757870 := by decide
  rcases family_descends (prefixWord ++ tailWord_757870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757898 : List Nat := [3, 1, 2, 3, 1, 2, 1, 1, 5, 3]
def baseStart_757898 : Nat := 118140960795 + 757898 * 2 ^ 59
def prefixEnd_757898 : Nat := 4983230072969 + 3 ^ 40 * 757898 * 2
def baseEnd_757898 : Nat := 259443974054253969526331

theorem tailTrace_757898 : CollatzResearch.WordTrace tailWord_757898 prefixEnd_757898 259443974054253969526331 := by
  unfold tailWord_757898
  simp only [CollatzResearch.WordTrace]
  refine ⟨6910702752068114879592587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18428540672181639678913565 6910702752068114879592587)
  ·
    refine ⟨10366054128102172319388881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6910702752068114879592587 10366054128102172319388881)
    ·
      refine ⟨7774540596076629239541661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10366054128102172319388881 7774540596076629239541661)
      ·
        refine ⟨2915452723528735964828123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7774540596076629239541661 2915452723528735964828123)
        ·
          refine ⟨4373179085293103947242185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2915452723528735964828123 4373179085293103947242185)
          ·
            refine ⟨3279884313969827960431639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4373179085293103947242185 3279884313969827960431639)
            ·
              refine ⟨4919826470954741940647459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3279884313969827960431639 4919826470954741940647459)
              ·
                refine ⟨7379739706432112910971189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4919826470954741940647459 7379739706432112910971189)
                ·
                  refine ⟨691850597478010585403549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7379739706432112910971189 691850597478010585403549)
                  ·
                    refine ⟨259443974054253969526331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 691850597478010585403549 259443974054253969526331)
                    ·
                      rfl

theorem cell22_757898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_757898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_757898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_757898 prefixEnd_757898 := by exact prefixLift 757898
  have htrace : WordTrace (prefixWord ++ tailWord_757898) baseStart_757898 baseEnd_757898 := by
    simpa [prefixWord, tailWord_757898, baseEnd_757898] using wordTrace_append hprefix tailTrace_757898
  have hstable : (prefixWord ++ tailWord_757898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757898).length < 2 ^ (prefixWord ++ tailWord_757898).sum := by decide
  have hdescent : baseEnd_757898 < baseStart_757898 := by decide
  rcases family_descends (prefixWord ++ tailWord_757898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_757902 : List Nat := [4, 1, 1, 3, 4, 1, 1, 1, 2, 4]
def baseStart_757902 : Nat := 118140960795 + 757902 * 2 ^ 59
def prefixEnd_757902 : Nat := 4983230072969 + 3 ^ 40 * 757902 * 2
def baseEnd_757902 : Nat := 259445343335999292426319

theorem tailTrace_757902 : CollatzResearch.WordTrace tailWord_757902 prefixEnd_757902 259445343335999292426319 := by
  unfold tailWord_757902
  simp only [CollatzResearch.WordTrace]
  refine ⟨3455369612532246025189495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18428637933505312134343973 3455369612532246025189495)
  ·
    refine ⟨5183054418798369037784243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3455369612532246025189495 5183054418798369037784243)
    ·
      refine ⟨7774581628197553556676365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5183054418798369037784243 7774581628197553556676365)
      ·
        refine ⟨2915468110574082583753637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7774581628197553556676365 2915468110574082583753637)
        ·
          refine ⟨546650270732640484453807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2915468110574082583753637 546650270732640484453807)
          ·
            refine ⟨819975406098960726680711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546650270732640484453807 819975406098960726680711)
            ·
              refine ⟨1229963109148441090021067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 819975406098960726680711 1229963109148441090021067)
              ·
                refine ⟨1844944663722661635031601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1229963109148441090021067 1844944663722661635031601)
                ·
                  refine ⟨1383708497791996226273701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1844944663722661635031601 1383708497791996226273701)
                  ·
                    refine ⟨259445343335999292426319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1383708497791996226273701 259445343335999292426319)
                    ·
                      rfl

theorem cell22_757902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 2, 4].length) (baseStart_757902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_757902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_757902 prefixEnd_757902 := by exact prefixLift 757902
  have htrace : WordTrace (prefixWord ++ tailWord_757902) baseStart_757902 baseEnd_757902 := by
    simpa [prefixWord, tailWord_757902, baseEnd_757902] using wordTrace_append hprefix tailTrace_757902
  have hstable : (prefixWord ++ tailWord_757902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_757902).length < 2 ^ (prefixWord ++ tailWord_757902).sum := by decide
  have hdescent : baseEnd_757902 < baseStart_757902 := by decide
  rcases family_descends (prefixWord ++ tailWord_757902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758001 : List Nat := [1, 2, 2, 2, 2, 1, 3, 9]
def baseStart_758001 : Nat := 118140960795 + 758001 * 2 ^ 59
def prefixEnd_758001 : Nat := 4983230072969 + 3 ^ 40 * 758001 * 2
def baseEnd_758001 : Nat := 28831025895466226022335

theorem tailTrace_758001 : CollatzResearch.WordTrace tailWord_758001 prefixEnd_758001 28831025895466226022335 := by
  unfold tailWord_758001
  simp only [CollatzResearch.WordTrace]
  refine ⟨27646567726899308109369857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18431045151266205406246571 27646567726899308109369857)
  ·
    refine ⟨20734925795174481082027393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27646567726899308109369857 20734925795174481082027393)
    ·
      refine ⟨15551194346380860811520545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20734925795174481082027393 15551194346380860811520545)
      ·
        refine ⟨11663395759785645608640409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15551194346380860811520545 11663395759785645608640409)
        ·
          refine ⟨8747546819839234206480307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11663395759785645608640409 8747546819839234206480307)
          ·
            refine ⟨13121320229758851309720461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8747546819839234206480307 13121320229758851309720461)
            ·
              refine ⟨4920495086159569241145173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13121320229758851309720461 4920495086159569241145173)
              ·
                refine ⟨28831025895466226022335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4920495086159569241145173 28831025895466226022335)
                ·
                  rfl

theorem cell22_758001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 9].length) (baseStart_758001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_758001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_758001 prefixEnd_758001 := by exact prefixLift 758001
  have htrace : WordTrace (prefixWord ++ tailWord_758001) baseStart_758001 baseEnd_758001 := by
    simpa [prefixWord, tailWord_758001, baseEnd_758001] using wordTrace_append hprefix tailTrace_758001
  have hstable : (prefixWord ++ tailWord_758001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758001).length < 2 ^ (prefixWord ++ tailWord_758001).sum := by decide
  have hdescent : baseEnd_758001 < baseStart_758001 := by decide
  rcases family_descends (prefixWord ++ tailWord_758001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758016 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 2, 7]
def baseStart_758016 : Nat := 118140960795 + 758016 * 2 ^ 59
def prefixEnd_758016 : Nat := 4983230072969 + 3 ^ 40 * 758016 * 2
def baseEnd_758016 : Nat := 259484367865740995075969

theorem tailTrace_758016 : CollatzResearch.WordTrace tailWord_758016 prefixEnd_758016 259484367865740995075969 := by
  unfold tailWord_758016
  simp only [CollatzResearch.WordTrace]
  refine ⟨13823557410922482835582951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18431409881229977114110601 13823557410922482835582951)
  ·
    refine ⟨20735336116383724253374427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13823557410922482835582951 20735336116383724253374427)
    ·
      refine ⟨31103004174575586380061641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20735336116383724253374427 31103004174575586380061641)
      ·
        refine ⟨23327253130931689785046231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31103004174575586380061641 23327253130931689785046231)
        ·
          refine ⟨34990879696397534677569347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23327253130931689785046231 34990879696397534677569347)
          ·
            refine ⟨52486319544596302016354021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34990879696397534677569347 52486319544596302016354021)
            ·
              refine ⟨9841184914611806628066379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52486319544596302016354021 9841184914611806628066379)
              ·
                refine ⟨14761777371917709942099569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9841184914611806628066379 14761777371917709942099569)
                ·
                  refine ⟨11071333028938282456574677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14761777371917709942099569 11071333028938282456574677)
                  ·
                    refine ⟨259484367865740995075969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11071333028938282456574677 259484367865740995075969)
                    ·
                      rfl

theorem cell22_758016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 2, 7].length) (baseStart_758016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_758016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_758016 prefixEnd_758016 := by exact prefixLift 758016
  have htrace : WordTrace (prefixWord ++ tailWord_758016) baseStart_758016 baseEnd_758016 := by
    simpa [prefixWord, tailWord_758016, baseEnd_758016] using wordTrace_append hprefix tailTrace_758016
  have hstable : (prefixWord ++ tailWord_758016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758016).length < 2 ^ (prefixWord ++ tailWord_758016).sum := by decide
  have hdescent : baseEnd_758016 < baseStart_758016 := by decide
  rcases family_descends (prefixWord ++ tailWord_758016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758031 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 4, 6]
def baseStart_758031 : Nat := 118140960795 + 758031 * 2 ^ 59
def prefixEnd_758031 : Nat := 4983230072969 + 3 ^ 40 * 758031 * 2
def baseEnd_758031 : Nat := 259489502672285955950923

theorem tailTrace_758031 : CollatzResearch.WordTrace tailWord_758031 prefixEnd_758031 259489502672285955950923 := by
  unfold tailWord_758031
  simp only [CollatzResearch.WordTrace]
  refine ⟨27647661916790623232961947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18431774611193748821974631 27647661916790623232961947)
  ·
    refine ⟨41471492875185934849442921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27647661916790623232961947 41471492875185934849442921)
    ·
      refine ⟨31103619656389451137082191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41471492875185934849442921 31103619656389451137082191)
      ·
        refine ⟨46655429484584176705623287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31103619656389451137082191 46655429484584176705623287)
        ·
          refine ⟨69983144226876265058434931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46655429484584176705623287 69983144226876265058434931)
          ·
            refine ⟨104974716340314397587652397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69983144226876265058434931 104974716340314397587652397)
            ·
              refine ⟨39365518627617899095369649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104974716340314397587652397 39365518627617899095369649)
              ·
                refine ⟨29524138970713424321527237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39365518627617899095369649 29524138970713424321527237)
                ·
                  refine ⟨5535776057008767060286357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29524138970713424321527237 5535776057008767060286357)
                  ·
                    refine ⟨259489502672285955950923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5535776057008767060286357 259489502672285955950923)
                    ·
                      rfl

theorem cell22_758031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 6].length) (baseStart_758031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_758031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_758031 prefixEnd_758031 := by exact prefixLift 758031
  have htrace : WordTrace (prefixWord ++ tailWord_758031) baseStart_758031 baseEnd_758031 := by
    simpa [prefixWord, tailWord_758031, baseEnd_758031] using wordTrace_append hprefix tailTrace_758031
  have hstable : (prefixWord ++ tailWord_758031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758031).length < 2 ^ (prefixWord ++ tailWord_758031).sum := by decide
  have hdescent : baseEnd_758031 < baseStart_758031 := by decide
  rcases family_descends (prefixWord ++ tailWord_758031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758048 : List Nat := [2, 1, 1, 5, 2, 1, 1, 1, 2, 6]
def baseStart_758048 : Nat := 118140960795 + 758048 * 2 ^ 59
def prefixEnd_758048 : Nat := 4983230072969 + 3 ^ 40 * 758048 * 2
def baseEnd_758048 : Nat := 259495322119703578275871

theorem tailTrace_758048 : CollatzResearch.WordTrace tailWord_758048 prefixEnd_758048 259495322119703578275871 := by
  unfold tailWord_758048
  simp only [CollatzResearch.WordTrace]
  refine ⟨13824140978864517568165399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18432187971819356757553865 13824140978864517568165399)
  ·
    refine ⟨20736211468296776352248099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13824140978864517568165399 20736211468296776352248099)
    ·
      refine ⟨31104317202445164528372149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20736211468296776352248099 31104317202445164528372149)
      ·
        refine ⟨2916029737729234174534889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31104317202445164528372149 2916029737729234174534889)
        ·
          refine ⟨2187022303296925630901167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2916029737729234174534889 2187022303296925630901167)
          ·
            refine ⟨3280533454945388446351751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2187022303296925630901167 3280533454945388446351751)
            ·
              refine ⟨4920800182418082669527627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3280533454945388446351751 4920800182418082669527627)
              ·
                refine ⟨7381200273627124004291441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4920800182418082669527627 7381200273627124004291441)
                ·
                  refine ⟨5535900205220343003218581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7381200273627124004291441 5535900205220343003218581)
                  ·
                    refine ⟨259495322119703578275871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5535900205220343003218581 259495322119703578275871)
                    ·
                      rfl

theorem cell22_758048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 2, 6].length) (baseStart_758048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_758048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_758048 prefixEnd_758048 := by exact prefixLift 758048
  have htrace : WordTrace (prefixWord ++ tailWord_758048) baseStart_758048 baseEnd_758048 := by
    simpa [prefixWord, tailWord_758048, baseEnd_758048] using wordTrace_append hprefix tailTrace_758048
  have hstable : (prefixWord ++ tailWord_758048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758048).length < 2 ^ (prefixWord ++ tailWord_758048).sum := by decide
  have hdescent : baseEnd_758048 < baseStart_758048 := by decide
  rcases family_descends (prefixWord ++ tailWord_758048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758063 : List Nat := [1, 1, 2, 1, 2, 1, 6, 3, 5]
def baseStart_758063 : Nat := 118140960795 + 758063 * 2 ^ 59
def prefixEnd_758063 : Nat := 4983230072969 + 3 ^ 40 * 758063 * 2
def baseEnd_758063 : Nat := 86500152308749513050275

theorem tailTrace_758063 : CollatzResearch.WordTrace tailWord_758063 prefixEnd_758063 86500152308749513050275 := by
  unfold tailWord_758063
  simp only [CollatzResearch.WordTrace]
  refine ⟨27648829052674692698126843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18432552701783128465417895 27648829052674692698126843)
  ·
    refine ⟨41473243579012039047190265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27648829052674692698126843 41473243579012039047190265)
    ·
      refine ⟨31104932684259029285392699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41473243579012039047190265 31104932684259029285392699)
      ·
        refine ⟨46657399026388543928089049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31104932684259029285392699 46657399026388543928089049)
        ·
          refine ⟨34993049269791407946066787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46657399026388543928089049 34993049269791407946066787)
          ·
            refine ⟨52489573904687111919100181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34993049269791407946066787 52489573904687111919100181)
            ·
              refine ⟨2460448776782208371207821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52489573904687111919100181 2460448776782208371207821)
              ·
                refine ⟨922668291293328139202933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2460448776782208371207821 922668291293328139202933)
                ·
                  refine ⟨86500152308749513050275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 922668291293328139202933 86500152308749513050275)
                  ·
                    rfl

theorem cell22_758063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 5].length) (baseStart_758063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_758063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_758063 prefixEnd_758063 := by exact prefixLift 758063
  have htrace : WordTrace (prefixWord ++ tailWord_758063) baseStart_758063 baseEnd_758063 := by
    simpa [prefixWord, tailWord_758063, baseEnd_758063] using wordTrace_append hprefix tailTrace_758063
  have hstable : (prefixWord ++ tailWord_758063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758063).length < 2 ^ (prefixWord ++ tailWord_758063).sum := by decide
  have hdescent : baseEnd_758063 < baseStart_758063 := by decide
  rcases family_descends (prefixWord ++ tailWord_758063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758153 : List Nat := [1, 2, 1, 1, 6, 1, 10]
def baseStart_758153 : Nat := 118140960795 + 758153 * 2 ^ 59
def prefixEnd_758153 : Nat := 4983230072969 + 3 ^ 40 * 758153 * 2
def baseEnd_758153 : Nat := 9612269102426603866687

theorem tailTrace_758153 : CollatzResearch.WordTrace tailWord_758153 prefixEnd_758153 9612269102426603866687 := by
  unfold tailWord_758153
  simp only [CollatzResearch.WordTrace]
  refine ⟨27652111622348638068903113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18434741081565758712602075 27652111622348638068903113)
  ·
    refine ⟨20739083716761478551677335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27652111622348638068903113 20739083716761478551677335)
    ·
      refine ⟨31108625575142217827516003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20739083716761478551677335 31108625575142217827516003)
      ·
        refine ⟨46662938362713326741274005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31108625575142217827516003 46662938362713326741274005)
        ·
          refine ⟨2187325235752187190997219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46662938362713326741274005 2187325235752187190997219)
          ·
            refine ⟨3280987853628280786495829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2187325235752187190997219 3280987853628280786495829)
            ·
              refine ⟨9612269102426603866687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3280987853628280786495829 9612269102426603866687)
              ·
                rfl

theorem cell22_758153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 10].length) (baseStart_758153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_758153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_758153 prefixEnd_758153 := by exact prefixLift 758153
  have htrace : WordTrace (prefixWord ++ tailWord_758153) baseStart_758153 baseEnd_758153 := by
    simpa [prefixWord, tailWord_758153, baseEnd_758153] using wordTrace_append hprefix tailTrace_758153
  have hstable : (prefixWord ++ tailWord_758153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758153).length < 2 ^ (prefixWord ++ tailWord_758153).sum := by decide
  have hdescent : baseEnd_758153 < baseStart_758153 := by decide
  rcases family_descends (prefixWord ++ tailWord_758153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758155 : List Nat := [1, 1, 1, 1, 4, 5, 1, 2, 2, 4]
def baseStart_758155 : Nat := 118140960795 + 758155 * 2 ^ 59
def prefixEnd_758155 : Nat := 4983230072969 + 3 ^ 40 * 758155 * 2
def baseEnd_758155 : Nat := 259531950406390965850543

theorem tailTrace_758155 : CollatzResearch.WordTrace tailWord_758155 prefixEnd_758155 259531950406390965850543 := by
  unfold tailWord_758155
  simp only [CollatzResearch.WordTrace]
  refine ⟨27652184568341392410475919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18434789712227594940317279 27652184568341392410475919)
  ·
    refine ⟨41478276852512088615713879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27652184568341392410475919 41478276852512088615713879)
    ·
      refine ⟨62217415278768132923570819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41478276852512088615713879 62217415278768132923570819)
      ·
        refine ⟨93326122918152199385356229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62217415278768132923570819 93326122918152199385356229)
        ·
          refine ⟨17498648047153537384754293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93326122918152199385356229 17498648047153537384754293)
          ·
            refine ⟨1640498254420644129820715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17498648047153537384754293 1640498254420644129820715)
            ·
              refine ⟨2460747381630966194731073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1640498254420644129820715 2460747381630966194731073)
              ·
                refine ⟨1845560536223224646048305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2460747381630966194731073 1845560536223224646048305)
                ·
                  refine ⟨1384170402167418484536229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1845560536223224646048305 1384170402167418484536229)
                  ·
                    refine ⟨259531950406390965850543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1384170402167418484536229 259531950406390965850543)
                    ·
                      rfl

theorem cell22_758155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 4].length) (baseStart_758155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_758155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_758155 prefixEnd_758155 := by exact prefixLift 758155
  have htrace : WordTrace (prefixWord ++ tailWord_758155) baseStart_758155 baseEnd_758155 := by
    simpa [prefixWord, tailWord_758155, baseEnd_758155] using wordTrace_append hprefix tailTrace_758155
  have hstable : (prefixWord ++ tailWord_758155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758155).length < 2 ^ (prefixWord ++ tailWord_758155).sum := by decide
  have hdescent : baseEnd_758155 < baseStart_758155 := by decide
  rcases family_descends (prefixWord ++ tailWord_758155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758170 : List Nat := [3, 1, 1, 4, 1, 3, 2, 7]
def baseStart_758170 : Nat := 118140960795 + 758170 * 2 ^ 59
def prefixEnd_758170 : Nat := 4983230072969 + 3 ^ 40 * 758170 * 2
def baseEnd_758170 : Nat := 28837453912548436302833

theorem tailTrace_758170 : CollatzResearch.WordTrace tailWord_758170 prefixEnd_758170 28837453912548436302833 := by
  unfold tailWord_758170
  simp only [CollatzResearch.WordTrace]
  refine ⟨6913182915821762493067991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18435154442191366648181309 6913182915821762493067991)
  ·
    refine ⟨10369774373732643739601987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6913182915821762493067991 10369774373732643739601987)
    ·
      refine ⟨15554661560598965609402981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10369774373732643739601987 15554661560598965609402981)
      ·
        refine ⟨2916499042612306051763059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15554661560598965609402981 2916499042612306051763059)
        ·
          refine ⟨4374748563918459077644589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2916499042612306051763059 4374748563918459077644589)
          ·
            refine ⟨1640530711469422154116721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4374748563918459077644589 1640530711469422154116721)
            ·
              refine ⟨1230398033602066615587541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1640530711469422154116721 1230398033602066615587541)
              ·
                refine ⟨28837453912548436302833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1230398033602066615587541 28837453912548436302833)
                ·
                  rfl

theorem cell22_758170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 7].length) (baseStart_758170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_758170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_758170 prefixEnd_758170 := by exact prefixLift 758170
  have htrace : WordTrace (prefixWord ++ tailWord_758170) baseStart_758170 baseEnd_758170 := by
    simpa [prefixWord, tailWord_758170, baseEnd_758170] using wordTrace_append hprefix tailTrace_758170
  have hstable : (prefixWord ++ tailWord_758170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758170).length < 2 ^ (prefixWord ++ tailWord_758170).sum := by decide
  have hdescent : baseEnd_758170 < baseStart_758170 := by decide
  rcases family_descends (prefixWord ++ tailWord_758170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758185 : List Nat := [1, 2, 1, 1, 1, 1, 3, 6, 3, 3]
def baseStart_758185 : Nat := 118140960795 + 758185 * 2 ^ 59
def prefixEnd_758185 : Nat := 4983230072969 + 3 ^ 40 * 758185 * 2
def baseEnd_758185 : Nat := 259542220019480887600451

theorem tailTrace_758185 : CollatzResearch.WordTrace tailWord_758185 prefixEnd_758185 259542220019480887600451 := by
  unfold tailWord_758185
  simp only [CollatzResearch.WordTrace]
  refine ⟨27653278758232707534068009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18435519172155138356045339 27653278758232707534068009)
  ·
    refine ⟨20739959068674530650551007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27653278758232707534068009 20739959068674530650551007)
    ·
      refine ⟨31109938603011795975826511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20739959068674530650551007 31109938603011795975826511)
      ·
        refine ⟨46664907904517693963739767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31109938603011795975826511 46664907904517693963739767)
        ·
          refine ⟨69997361856776540945609651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46664907904517693963739767 69997361856776540945609651)
          ·
            refine ⟨104996042785164811418414477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69997361856776540945609651 104996042785164811418414477)
            ·
              refine ⟨39373516044436804281905429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104996042785164811418414477 39373516044436804281905429)
              ·
                refine ⟨1845633564582975200714317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39373516044436804281905429 1845633564582975200714317)
                ·
                  refine ⟨692112586718615700267869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1845633564582975200714317 692112586718615700267869)
                  ·
                    refine ⟨259542220019480887600451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 692112586718615700267869 259542220019480887600451)
                    ·
                      rfl

theorem cell22_758185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 3, 3].length) (baseStart_758185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_758185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_758185 prefixEnd_758185 := by exact prefixLift 758185
  have htrace : WordTrace (prefixWord ++ tailWord_758185) baseStart_758185 baseEnd_758185 := by
    simpa [prefixWord, tailWord_758185, baseEnd_758185] using wordTrace_append hprefix tailTrace_758185
  have hstable : (prefixWord ++ tailWord_758185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758185).length < 2 ^ (prefixWord ++ tailWord_758185).sum := by decide
  have hdescent : baseEnd_758185 < baseStart_758185 := by decide
  rcases family_descends (prefixWord ++ tailWord_758185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758189 : List Nat := [1, 5, 2, 2, 2, 1, 2, 1, 2, 4]
def baseStart_758189 : Nat := 118140960795 + 758189 * 2 ^ 59
def prefixEnd_758189 : Nat := 4983230072969 + 3 ^ 40 * 758189 * 2
def baseEnd_758189 : Nat := 259543589301226210500439

theorem tailTrace_758189 : CollatzResearch.WordTrace tailWord_758189 prefixEnd_758189 259543589301226210500439 := by
  unfold tailWord_758189
  simp only [CollatzResearch.WordTrace]
  refine ⟨27653424650218216217213621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18435616433478810811475747 27653424650218216217213621)
  ·
    refine ⟨2592508560957957770363777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27653424650218216217213621 2592508560957957770363777)
    ·
      refine ⟨1944381420718468327772833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2592508560957957770363777 1944381420718468327772833)
      ·
        refine ⟨1458286065538851245829625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1944381420718468327772833 1458286065538851245829625)
        ·
          refine ⟨1093714549154138434372219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1458286065538851245829625 1093714549154138434372219)
          ·
            refine ⟨1640571823731207651558329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1093714549154138434372219 1640571823731207651558329)
            ·
              refine ⟨1230428867798405738668747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1640571823731207651558329 1230428867798405738668747)
              ·
                refine ⟨1845643301697608608003121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1230428867798405738668747 1845643301697608608003121)
                ·
                  refine ⟨1384232476273206456002341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1845643301697608608003121 1384232476273206456002341)
                  ·
                    refine ⟨259543589301226210500439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1384232476273206456002341 259543589301226210500439)
                    ·
                      rfl

theorem cell22_758189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_758189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_758189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_758189 prefixEnd_758189 := by exact prefixLift 758189
  have htrace : WordTrace (prefixWord ++ tailWord_758189) baseStart_758189 baseEnd_758189 := by
    simpa [prefixWord, tailWord_758189, baseEnd_758189] using wordTrace_append hprefix tailTrace_758189
  have hstable : (prefixWord ++ tailWord_758189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758189).length < 2 ^ (prefixWord ++ tailWord_758189).sum := by decide
  have hdescent : baseEnd_758189 < baseStart_758189 := by decide
  rcases family_descends (prefixWord ++ tailWord_758189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758213 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 5, 7]
def baseStart_758213 : Nat := 118140960795 + 758213 * 2 ^ 59
def prefixEnd_758213 : Nat := 4983230072969 + 3 ^ 40 * 758213 * 2
def baseEnd_758213 : Nat := 259551804991698147900365

theorem tailTrace_758213 : CollatzResearch.WordTrace tailWord_758213 prefixEnd_758213 259551804991698147900365 := by
  unfold tailWord_758213
  simp only [CollatzResearch.WordTrace]
  refine ⟨27654300002131268316087293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18436200001420845544058195 27654300002131268316087293)
  ·
    refine ⟨10370362500799225618532735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27654300002131268316087293 10370362500799225618532735)
    ·
      refine ⟨15555543751198838427799103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10370362500799225618532735 15555543751198838427799103)
      ·
        refine ⟨23333315626798257641698655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15555543751198838427799103 23333315626798257641698655)
        ·
          refine ⟨34999973440197386462547983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23333315626798257641698655 34999973440197386462547983)
          ·
            refine ⟨52499960160296079693821975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34999973440197386462547983 52499960160296079693821975)
            ·
              refine ⟨78749940240444119540732963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52499960160296079693821975 78749940240444119540732963)
              ·
                refine ⟨118124910360666179311099445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78749940240444119540732963 118124910360666179311099445)
                ·
                  refine ⟨11074210346312454310415573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 118124910360666179311099445 11074210346312454310415573)
                  ·
                    refine ⟨259551804991698147900365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11074210346312454310415573 259551804991698147900365)
                    ·
                      rfl

theorem cell22_758213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_758213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_758213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_758213 prefixEnd_758213 := by exact prefixLift 758213
  have htrace : WordTrace (prefixWord ++ tailWord_758213) baseStart_758213 baseEnd_758213 := by
    simpa [prefixWord, tailWord_758213, baseEnd_758213] using wordTrace_append hprefix tailTrace_758213
  have hstable : (prefixWord ++ tailWord_758213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758213).length < 2 ^ (prefixWord ++ tailWord_758213).sum := by decide
  have hdescent : baseEnd_758213 < baseStart_758213 := by decide
  rcases family_descends (prefixWord ++ tailWord_758213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758215 : List Nat := [1, 1, 4, 1, 1, 4, 1, 4, 5]
def baseStart_758215 : Nat := 118140960795 + 758215 * 2 ^ 59
def prefixEnd_758215 : Nat := 4983230072969 + 3 ^ 40 * 758215 * 2
def baseEnd_758215 : Nat := 86517496544190269783453

theorem tailTrace_758215 : CollatzResearch.WordTrace tailWord_758215 prefixEnd_758215 86517496544190269783453 := by
  unfold tailWord_758215
  simp only [CollatzResearch.WordTrace]
  refine ⟨27654372948124022657660099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18436248632082681771773399 27654372948124022657660099)
  ·
    refine ⟨41481559422186033986490149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27654372948124022657660099 41481559422186033986490149)
    ·
      refine ⟨7777792391659881372466903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41481559422186033986490149 7777792391659881372466903)
      ·
        refine ⟨11666688587489822058700355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7777792391659881372466903 11666688587489822058700355)
        ·
          refine ⟨17500032881234733088050533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11666688587489822058700355 17500032881234733088050533)
          ·
            refine ⟨3281256165231512454009475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17500032881234733088050533 3281256165231512454009475)
            ·
              refine ⟨4921884247847268681014213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3281256165231512454009475 4921884247847268681014213)
              ·
                refine ⟨922853296471362877690165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4921884247847268681014213 922853296471362877690165)
                ·
                  refine ⟨86517496544190269783453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 922853296471362877690165 86517496544190269783453)
                  ·
                    rfl

theorem cell22_758215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 5].length) (baseStart_758215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_758215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_758215 prefixEnd_758215 := by exact prefixLift 758215
  have htrace : WordTrace (prefixWord ++ tailWord_758215) baseStart_758215 baseEnd_758215 := by
    simpa [prefixWord, tailWord_758215, baseEnd_758215] using wordTrace_append hprefix tailTrace_758215
  have hstable : (prefixWord ++ tailWord_758215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758215).length < 2 ^ (prefixWord ++ tailWord_758215).sum := by decide
  have hdescent : baseEnd_758215 < baseStart_758215 := by decide
  rcases family_descends (prefixWord ++ tailWord_758215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758277 : List Nat := [1, 3, 1, 1, 2, 2, 4, 4, 4]
def baseStart_758277 : Nat := 118140960795 + 758277 * 2 ^ 59
def prefixEnd_758277 : Nat := 4983230072969 + 3 ^ 40 * 758277 * 2
def baseEnd_758277 : Nat := 86524571166541104766723

theorem tailTrace_758277 : CollatzResearch.WordTrace tailWord_758277 prefixEnd_758277 86524571166541104766723 := by
  unfold tailWord_758277
  simp only [CollatzResearch.WordTrace]
  refine ⟨27656634273899407246417085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18437756182599604830944723 27656634273899407246417085)
  ·
    refine ⟨10371237852712277717406407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27656634273899407246417085 10371237852712277717406407)
    ·
      refine ⟨15556856779068416576109611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10371237852712277717406407 15556856779068416576109611)
      ·
        refine ⟨23335285168602624864164417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15556856779068416576109611 23335285168602624864164417)
        ·
          refine ⟨17501463876451968648123313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23335285168602624864164417 17501463876451968648123313)
          ·
            refine ⟨13126097907338976486092485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17501463876451968648123313 13126097907338976486092485)
            ·
              refine ⟨2461143357626058091142341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13126097907338976486092485 2461143357626058091142341)
              ·
                refine ⟨461464379554885892089189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2461143357626058091142341 461464379554885892089189)
                ·
                  refine ⟨86524571166541104766723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 461464379554885892089189 86524571166541104766723)
                  ·
                    rfl

theorem cell22_758277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 4, 4].length) (baseStart_758277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_758277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_758277 prefixEnd_758277 := by exact prefixLift 758277
  have htrace : WordTrace (prefixWord ++ tailWord_758277) baseStart_758277 baseEnd_758277 := by
    simpa [prefixWord, tailWord_758277, baseEnd_758277] using wordTrace_append hprefix tailTrace_758277
  have hstable : (prefixWord ++ tailWord_758277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758277).length < 2 ^ (prefixWord ++ tailWord_758277).sum := by decide
  have hdescent : baseEnd_758277 < baseStart_758277 := by decide
  rcases family_descends (prefixWord ++ tailWord_758277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758305 : List Nat := [1, 2, 3, 2, 2, 1, 3, 8]
def baseStart_758305 : Nat := 118140960795 + 758305 * 2 ^ 59
def prefixEnd_758305 : Nat := 4983230072969 + 3 ^ 40 * 758305 * 2
def baseEnd_758305 : Nat := 28842588719093397177787

theorem tailTrace_758305 : CollatzResearch.WordTrace tailWord_758305 prefixEnd_758305 28842588719093397177787 := by
  unfold tailWord_758305
  simp only [CollatzResearch.WordTrace]
  refine ⟨27657655517797968028436369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18438437011865312018957579 27657655517797968028436369)
  ·
    refine ⟨20743241638348476021327277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27657655517797968028436369 20743241638348476021327277)
    ·
      refine ⟨7778715614380678507997729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20743241638348476021327277 7778715614380678507997729)
      ·
        refine ⟨5834036710785508880998297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7778715614380678507997729 5834036710785508880998297)
        ·
          refine ⟨4375527533089131660748723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5834036710785508880998297 4375527533089131660748723)
          ·
            refine ⟨6563291299633697491123085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4375527533089131660748723 6563291299633697491123085)
            ·
              refine ⟨2461234237362636559171157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6563291299633697491123085 2461234237362636559171157)
              ·
                refine ⟨28842588719093397177787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2461234237362636559171157 28842588719093397177787)
                ·
                  rfl

theorem cell22_758305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 8].length) (baseStart_758305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_758305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_758305 prefixEnd_758305 := by exact prefixLift 758305
  have htrace : WordTrace (prefixWord ++ tailWord_758305) baseStart_758305 baseEnd_758305 := by
    simpa [prefixWord, tailWord_758305, baseEnd_758305] using wordTrace_append hprefix tailTrace_758305
  have hstable : (prefixWord ++ tailWord_758305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758305).length < 2 ^ (prefixWord ++ tailWord_758305).sum := by decide
  have hdescent : baseEnd_758305 < baseStart_758305 := by decide
  rcases family_descends (prefixWord ++ tailWord_758305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758335 : List Nat := [1, 1, 2, 2, 3, 2, 2, 1, 2, 6]
def baseStart_758335 : Nat := 118140960795 + 758335 * 2 ^ 59
def prefixEnd_758335 : Nat := 4983230072969 + 3 ^ 40 * 758335 * 2
def baseEnd_758335 : Nat := 259593568084930496349991

theorem tailTrace_758335 : CollatzResearch.WordTrace tailWord_758335 prefixEnd_758335 259593568084930496349991 := by
  unfold tailWord_758335
  simp only [CollatzResearch.WordTrace]
  refine ⟨27658749707689283152028459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18439166471792855434685639 27658749707689283152028459)
  ·
    refine ⟨41488124561533924728042689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27658749707689283152028459 41488124561533924728042689)
    ·
      refine ⟨31116093421150443546032017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41488124561533924728042689 31116093421150443546032017)
      ·
        refine ⟨23337070065862832659524013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31116093421150443546032017 23337070065862832659524013)
        ·
          refine ⟨8751401274698562247321505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23337070065862832659524013 8751401274698562247321505)
          ·
            refine ⟨6563550956023921685491129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8751401274698562247321505 6563550956023921685491129)
            ·
              refine ⟨4922663217017941264118347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6563550956023921685491129 4922663217017941264118347)
              ·
                refine ⟨7383994825526911896177521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4922663217017941264118347 7383994825526911896177521)
                ·
                  refine ⟨5537996119145183922133141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7383994825526911896177521 5537996119145183922133141)
                  ·
                    refine ⟨259593568084930496349991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5537996119145183922133141 259593568084930496349991)
                    ·
                      rfl

theorem cell22_758335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 6].length) (baseStart_758335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_758335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_758335 prefixEnd_758335 := by exact prefixLift 758335
  have htrace : WordTrace (prefixWord ++ tailWord_758335) baseStart_758335 baseEnd_758335 := by
    simpa [prefixWord, tailWord_758335, baseEnd_758335] using wordTrace_append hprefix tailTrace_758335
  have hstable : (prefixWord ++ tailWord_758335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758335).length < 2 ^ (prefixWord ++ tailWord_758335).sum := by decide
  have hdescent : baseEnd_758335 < baseStart_758335 := by decide
  rcases family_descends (prefixWord ++ tailWord_758335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758384 : List Nat := [2, 1, 1, 1, 7, 1, 2, 2, 5]
def baseStart_758384 : Nat := 118140960795 + 758384 * 2 ^ 59
def prefixEnd_758384 : Nat := 4983230072969 + 3 ^ 40 * 758384 * 2
def baseEnd_758384 : Nat := 86536780595436900624947

theorem tailTrace_758384 : CollatzResearch.WordTrace tailWord_758384 prefixEnd_758384 86536780595436900624947 := by
  unfold tailWord_758384
  simp only [CollatzResearch.WordTrace]
  refine ⟨13830268442255882260281103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18440357923007843013708137 13830268442255882260281103)
  ·
    refine ⟨20745402663383823390421655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13830268442255882260281103 20745402663383823390421655)
    ·
      refine ⟨31118103995075735085632483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20745402663383823390421655 31118103995075735085632483)
      ·
        refine ⟨46677155992613602628448725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31118103995075735085632483 46677155992613602628448725)
        ·
          refine ⟨1093995843576881311604267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 46677155992613602628448725 1093995843576881311604267)
          ·
            refine ⟨1640993765365321967406401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1093995843576881311604267 1640993765365321967406401)
            ·
              refine ⟨1230745324023991475554801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1640993765365321967406401 1230745324023991475554801)
              ·
                refine ⟨923058993017993606666101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1230745324023991475554801 923058993017993606666101)
                ·
                  refine ⟨86536780595436900624947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 923058993017993606666101 86536780595436900624947)
                  ·
                    rfl

theorem cell22_758384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 5].length) (baseStart_758384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_758384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_758384 prefixEnd_758384 := by exact prefixLift 758384
  have htrace : WordTrace (prefixWord ++ tailWord_758384) baseStart_758384 baseEnd_758384 := by
    simpa [prefixWord, tailWord_758384, baseEnd_758384] using wordTrace_append hprefix tailTrace_758384
  have hstable : (prefixWord ++ tailWord_758384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758384).length < 2 ^ (prefixWord ++ tailWord_758384).sum := by decide
  have hdescent : baseEnd_758384 < baseStart_758384 := by decide
  rcases family_descends (prefixWord ++ tailWord_758384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758414 : List Nat := [4, 1, 1, 3, 1, 1, 2, 4, 1, 4]
def baseStart_758414 : Nat := 118140960795 + 758414 * 2 ^ 59
def prefixEnd_758414 : Nat := 4983230072969 + 3 ^ 40 * 758414 * 2
def baseEnd_758414 : Nat := 259620611399400623624749

theorem tailTrace_758414 : CollatzResearch.WordTrace tailWord_758414 prefixEnd_758414 259620611399400623624749 := by
  unfold tailWord_758414
  simp only [CollatzResearch.WordTrace]
  refine ⟨3457703884300384955519287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18441087382935386429436197 3457703884300384955519287)
  ·
    refine ⟨5186555826450577433278931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3457703884300384955519287 5186555826450577433278931)
    ·
      refine ⟨7779833739675866149918397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5186555826450577433278931 7779833739675866149918397)
      ·
        refine ⟨2917437652378449806219399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7779833739675866149918397 2917437652378449806219399)
        ·
          refine ⟨4376156478567674709329099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2917437652378449806219399 4376156478567674709329099)
          ·
            refine ⟨6564234717851512063993649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4376156478567674709329099 6564234717851512063993649)
            ·
              refine ⟨4923176038388634047995237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6564234717851512063993649 4923176038388634047995237)
              ·
                refine ⟨923095507197868883999107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4923176038388634047995237 923095507197868883999107)
                ·
                  refine ⟨1384643260796803325998661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 923095507197868883999107 1384643260796803325998661)
                  ·
                    refine ⟨259620611399400623624749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1384643260796803325998661 259620611399400623624749)
                    ·
                      rfl

theorem cell22_758414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_758414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_758414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_758414 prefixEnd_758414 := by exact prefixLift 758414
  have htrace : WordTrace (prefixWord ++ tailWord_758414) baseStart_758414 baseEnd_758414 := by
    simpa [prefixWord, tailWord_758414, baseEnd_758414] using wordTrace_append hprefix tailTrace_758414
  have hstable : (prefixWord ++ tailWord_758414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758414).length < 2 ^ (prefixWord ++ tailWord_758414).sum := by decide
  have hdescent : baseEnd_758414 < baseStart_758414 := by decide
  rcases family_descends (prefixWord ++ tailWord_758414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758429 : List Nat := [1, 4, 2, 1, 1, 1, 3, 5, 4]
def baseStart_758429 : Nat := 118140960795 + 758429 * 2 ^ 59
def prefixEnd_758429 : Nat := 4983230072969 + 3 ^ 40 * 758429 * 2
def baseEnd_758429 : Nat := 86541915401981861499901

theorem tailTrace_758429 : CollatzResearch.WordTrace tailWord_758429 prefixEnd_758429 86541915401981861499901 := by
  unfold tailWord_758429
  simp only [CollatzResearch.WordTrace]
  refine ⟨27662178169348737205950341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18441452112899158137300227 27662178169348737205950341)
  ·
    refine ⟨5186658406752888226115689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27662178169348737205950341 5186658406752888226115689)
    ·
      refine ⟨3889993805064666169586767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5186658406752888226115689 3889993805064666169586767)
      ·
        refine ⟨5834990707596999254380151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3889993805064666169586767 5834990707596999254380151)
        ·
          refine ⟨8752486061395498881570227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5834990707596999254380151 8752486061395498881570227)
          ·
            refine ⟨13128729092093248322355341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8752486061395498881570227 13128729092093248322355341)
            ·
              refine ⟨4923273409534968120883253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13128729092093248322355341 4923273409534968120883253)
              ·
                refine ⟨461556882143903261332805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4923273409534968120883253 461556882143903261332805)
                ·
                  refine ⟨86541915401981861499901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 461556882143903261332805 86541915401981861499901)
                  ·
                    rfl

theorem cell22_758429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_758429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_758429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_758429 prefixEnd_758429 := by exact prefixLift 758429
  have htrace : WordTrace (prefixWord ++ tailWord_758429) baseStart_758429 baseEnd_758429 := by
    simpa [prefixWord, tailWord_758429, baseEnd_758429] using wordTrace_append hprefix tailTrace_758429
  have hstable : (prefixWord ++ tailWord_758429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758429).length < 2 ^ (prefixWord ++ tailWord_758429).sum := by decide
  have hdescent : baseEnd_758429 < baseStart_758429 := by decide
  rcases family_descends (prefixWord ++ tailWord_758429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758446 : List Nat := [4, 1, 4, 1, 1, 2, 2, 1, 6]
def baseStart_758446 : Nat := 118140960795 + 758446 * 2 ^ 59
def prefixEnd_758446 : Nat := 4983230072969 + 3 ^ 40 * 758446 * 2
def baseEnd_758446 : Nat := 86543855217787735608217

theorem tailTrace_758446 : CollatzResearch.WordTrace tailWord_758446 prefixEnd_758446 86543855217787735608217 := by
  unfold tailWord_758446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3457849776285893638664899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18441865473524766072879461 3457849776285893638664899)
  ·
    refine ⟨5186774664428840457997349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3457849776285893638664899 5186774664428840457997349)
    ·
      refine ⟨972520249580407585874503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5186774664428840457997349 972520249580407585874503)
      ·
        refine ⟨1458780374370611378811755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 972520249580407585874503 1458780374370611378811755)
        ·
          refine ⟨2188170561555917068217633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1458780374370611378811755 2188170561555917068217633)
          ·
            refine ⟨1641127921166937801163225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2188170561555917068217633 1641127921166937801163225)
            ·
              refine ⟨1230845940875203350872419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1641127921166937801163225 1230845940875203350872419)
              ·
                refine ⟨1846268911312805026308629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1230845940875203350872419 1846268911312805026308629)
                ·
                  refine ⟨86543855217787735608217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1846268911312805026308629 86543855217787735608217)
                  ·
                    rfl

theorem cell22_758446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_758446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_758446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_758446 prefixEnd_758446 := by exact prefixLift 758446
  have htrace : WordTrace (prefixWord ++ tailWord_758446) baseStart_758446 baseEnd_758446 := by
    simpa [prefixWord, tailWord_758446, baseEnd_758446] using wordTrace_append hprefix tailTrace_758446
  have hstable : (prefixWord ++ tailWord_758446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758446).length < 2 ^ (prefixWord ++ tailWord_758446).sum := by decide
  have hdescent : baseEnd_758446 < baseStart_758446 := by decide
  rcases family_descends (prefixWord ++ tailWord_758446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758474 : List Nat := [3, 1, 2, 1, 4, 1, 4, 6]
def baseStart_758474 : Nat := 118140960795 + 758474 * 2 ^ 59
def prefixEnd_758474 : Nat := 4983230072969 + 3 ^ 40 * 758474 * 2
def baseEnd_758474 : Nat := 28849016736175607458285

theorem tailTrace_758474 : CollatzResearch.WordTrace tailWord_758474 prefixEnd_758474 28849016736175607458285 := by
  unfold tailWord_758474
  simp only [CollatzResearch.WordTrace]
  refine ⟨6915954863546427472834619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18442546302790473260892317 6915954863546427472834619)
  ·
    refine ⟨10373932295319641209251929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6915954863546427472834619 10373932295319641209251929)
    ·
      refine ⟨7780449221489730906938947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10373932295319641209251929 7780449221489730906938947)
      ·
        refine ⟨11670673832234596360408421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7780449221489730906938947 11670673832234596360408421)
        ·
          refine ⟨2188251343543986817576579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11670673832234596360408421 2188251343543986817576579)
          ·
            refine ⟨3282377015315980226364869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2188251343543986817576579 3282377015315980226364869)
            ·
              refine ⟨615445690371746292443413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3282377015315980226364869 615445690371746292443413)
              ·
                refine ⟨28849016736175607458285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 615445690371746292443413 28849016736175607458285)
                ·
                  rfl

theorem cell22_758474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 6].length) (baseStart_758474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_758474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_758474 prefixEnd_758474 := by exact prefixLift 758474
  have htrace : WordTrace (prefixWord ++ tailWord_758474) baseStart_758474 baseEnd_758474 := by
    simpa [prefixWord, tailWord_758474, baseEnd_758474] using wordTrace_append hprefix tailTrace_758474
  have hstable : (prefixWord ++ tailWord_758474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758474).length < 2 ^ (prefixWord ++ tailWord_758474).sum := by decide
  have hdescent : baseEnd_758474 < baseStart_758474 := by decide
  rcases family_descends (prefixWord ++ tailWord_758474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758579 : List Nat := [1, 1, 1, 2, 6, 1, 1, 3, 1, 5]
def baseStart_758579 : Nat := 118140960795 + 758579 * 2 ^ 59
def prefixEnd_758579 : Nat := 4983230072969 + 3 ^ 40 * 758579 * 2
def baseEnd_758579 : Nat := 259677094271395193249243

theorem tailTrace_758579 : CollatzResearch.WordTrace tailWord_758579 prefixEnd_758579 259677094271395193249243 := by
  unfold tailWord_758579
  simp only [CollatzResearch.WordTrace]
  refine ⟨27667649118805312823910791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18445099412536875215940527 27667649118805312823910791)
  ·
    refine ⟨41501473678207969235866187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27667649118805312823910791 41501473678207969235866187)
    ·
      refine ⟨62252210517311953853799281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41501473678207969235866187 62252210517311953853799281)
      ·
        refine ⟨46689157887983965390349461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62252210517311953853799281 46689157887983965390349461)
        ·
          refine ⟨2188554275999248377672631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46689157887983965390349461 2188554275999248377672631)
          ·
            refine ⟨3282831413998872566508947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2188554275999248377672631 3282831413998872566508947)
            ·
              refine ⟨4924247120998308849763421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3282831413998872566508947 4924247120998308849763421)
              ·
                refine ⟨1846592670374365818661283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4924247120998308849763421 1846592670374365818661283)
                ·
                  refine ⟨2769889005561548727991925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1846592670374365818661283 2769889005561548727991925)
                  ·
                    refine ⟨259677094271395193249243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2769889005561548727991925 259677094271395193249243)
                    ·
                      rfl

theorem cell22_758579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 5].length) (baseStart_758579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_758579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_758579 prefixEnd_758579 := by exact prefixLift 758579
  have htrace : WordTrace (prefixWord ++ tailWord_758579) baseStart_758579 baseEnd_758579 := by
    simpa [prefixWord, tailWord_758579, baseEnd_758579] using wordTrace_append hprefix tailTrace_758579
  have hstable : (prefixWord ++ tailWord_758579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758579).length < 2 ^ (prefixWord ++ tailWord_758579).sum := by decide
  have hdescent : baseEnd_758579 < baseStart_758579 := by decide
  rcases family_descends (prefixWord ++ tailWord_758579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758592 : List Nat := [2, 1, 1, 2, 2, 1, 1, 12]
def baseStart_758592 : Nat := 118140960795 + 758592 * 2 ^ 59
def prefixEnd_758592 : Nat := 4983230072969 + 3 ^ 40 * 758592 * 2
def baseEnd_758592 : Nat := 28853504937451943630467

theorem tailTrace_758592 : CollatzResearch.WordTrace tailWord_758592 prefixEnd_758592 28853504937451943630467 := by
  unfold tailWord_758592
  simp only [CollatzResearch.WordTrace]
  refine ⟨13834061633879108022067015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18445415511838810696089353 13834061633879108022067015)
  ·
    refine ⟨20751092450818662033100523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13834061633879108022067015 20751092450818662033100523)
    ·
      refine ⟨31126638676227993049650785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20751092450818662033100523 31126638676227993049650785)
      ·
        refine ⟨23344979007170994787238089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31126638676227993049650785 23344979007170994787238089)
        ·
          refine ⟨17508734255378246090428567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23344979007170994787238089 17508734255378246090428567)
          ·
            refine ⟨26263101383067369135642851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17508734255378246090428567 26263101383067369135642851)
            ·
              refine ⟨39394652074601053703464277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26263101383067369135642851 39394652074601053703464277)
              ·
                refine ⟨28853504937451943630467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 39394652074601053703464277 28853504937451943630467)
                ·
                  rfl

theorem cell22_758592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 12].length) (baseStart_758592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_758592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_758592 prefixEnd_758592 := by exact prefixLift 758592
  have htrace : WordTrace (prefixWord ++ tailWord_758592) baseStart_758592 baseEnd_758592 := by
    simpa [prefixWord, tailWord_758592, baseEnd_758592] using wordTrace_append hprefix tailTrace_758592
  have hstable : (prefixWord ++ tailWord_758592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758592).length < 2 ^ (prefixWord ++ tailWord_758592).sum := by decide
  have hdescent : baseEnd_758592 < baseStart_758592 := by decide
  rcases family_descends (prefixWord ++ tailWord_758592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758607 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 3, 9]
def baseStart_758607 : Nat := 118140960795 + 758607 * 2 ^ 59
def prefixEnd_758607 : Nat := 4983230072969 + 3 ^ 40 * 758607 * 2
def baseEnd_758607 : Nat := 259686679243612453549157

theorem tailTrace_758607 : CollatzResearch.WordTrace tailWord_758607 prefixEnd_758607 259686679243612453549157 := by
  unfold tailWord_758607
  simp only [CollatzResearch.WordTrace]
  refine ⟨27668670362703873605930075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18445780241802582403953383 27668670362703873605930075)
  ·
    refine ⟨41503005544055810408895113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27668670362703873605930075 41503005544055810408895113)
    ·
      refine ⟨31127254158041857806671335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41503005544055810408895113 31127254158041857806671335)
      ·
        refine ⟨46690881237062786710007003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31127254158041857806671335 46690881237062786710007003)
        ·
          refine ⟨70036321855594180065010505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46690881237062786710007003 70036321855594180065010505)
          ·
            refine ⟨52527241391695635048757879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70036321855594180065010505 52527241391695635048757879)
            ·
              refine ⟨78790862087543452573136819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52527241391695635048757879 78790862087543452573136819)
              ·
                refine ⟨118186293131315178859705229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78790862087543452573136819 118186293131315178859705229)
                ·
                  refine ⟨44319859924243192072389461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118186293131315178859705229 44319859924243192072389461)
                  ·
                    refine ⟨259686679243612453549157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 44319859924243192072389461 259686679243612453549157)
                    ·
                      rfl

theorem cell22_758607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 9].length) (baseStart_758607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_758607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_758607 prefixEnd_758607 := by exact prefixLift 758607
  have htrace : WordTrace (prefixWord ++ tailWord_758607) baseStart_758607 baseEnd_758607 := by
    simpa [prefixWord, tailWord_758607, baseEnd_758607] using wordTrace_append hprefix tailTrace_758607
  have hstable : (prefixWord ++ tailWord_758607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758607).length < 2 ^ (prefixWord ++ tailWord_758607).sum := by decide
  have hdescent : baseEnd_758607 < baseStart_758607 := by decide
  rcases family_descends (prefixWord ++ tailWord_758607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758609 : List Nat := [1, 2, 2, 1, 6, 1, 9]
def baseStart_758609 : Nat := 118140960795 + 758609 * 2 ^ 59
def prefixEnd_758609 : Nat := 4983230072969 + 3 ^ 40 * 758609 * 2
def baseEnd_758609 : Nat := 9618050514240189444413

theorem tailTrace_758609 : CollatzResearch.WordTrace tailWord_758609 prefixEnd_758609 9618050514240189444413 := by
  unfold tailWord_758609
  simp only [CollatzResearch.WordTrace]
  refine ⟨27668743308696627947502881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18445828872464418631668587 27668743308696627947502881)
  ·
    refine ⟨20751557481522470960627161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27668743308696627947502881 20751557481522470960627161)
    ·
      refine ⟨15563668111141853220470371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20751557481522470960627161 15563668111141853220470371)
      ·
        refine ⟨23345502166712779830705557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15563668111141853220470371 23345502166712779830705557)
        ·
          refine ⟨1094320414064661554564323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23345502166712779830705557 1094320414064661554564323)
          ·
            refine ⟨1641480621096992331846485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1094320414064661554564323 1641480621096992331846485)
            ·
              refine ⟨9618050514240189444413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1641480621096992331846485 9618050514240189444413)
              ·
                rfl

theorem cell22_758609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 9].length) (baseStart_758609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_758609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_758609 prefixEnd_758609 := by exact prefixLift 758609
  have htrace : WordTrace (prefixWord ++ tailWord_758609) baseStart_758609 baseEnd_758609 := by
    simpa [prefixWord, tailWord_758609, baseEnd_758609] using wordTrace_append hprefix tailTrace_758609
  have hstable : (prefixWord ++ tailWord_758609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758609).length < 2 ^ (prefixWord ++ tailWord_758609).sum := by decide
  have hdescent : baseEnd_758609 < baseStart_758609 := by decide
  rcases family_descends (prefixWord ++ tailWord_758609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758641 : List Nat := [1, 2, 2, 2, 1, 4, 2, 2, 3, 3]
def baseStart_758641 : Nat := 118140960795 + 758641 * 2 ^ 59
def prefixEnd_758641 : Nat := 4983230072969 + 3 ^ 40 * 758641 * 2
def baseEnd_758641 : Nat := 259698318138447698199053

theorem tailTrace_758641 : CollatzResearch.WordTrace tailWord_758641 prefixEnd_758641 259698318138447698199053 := by
  unfold tailWord_758641
  simp only [CollatzResearch.WordTrace]
  refine ⟨27669910444580697412667777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18446606963053798275111851 27669910444580697412667777)
  ·
    refine ⟨20752432833435523059500833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27669910444580697412667777 20752432833435523059500833)
    ·
      refine ⟨15564324625076642294625625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20752432833435523059500833 15564324625076642294625625)
      ·
        refine ⟨11673243468807481720969219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15564324625076642294625625 11673243468807481720969219)
        ·
          refine ⟨17509865203211222581453829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11673243468807481720969219 17509865203211222581453829)
          ·
            refine ⟨3283099725602104234022593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17509865203211222581453829 3283099725602104234022593)
            ·
              refine ⟨2462324794201578175516945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3283099725602104234022593 2462324794201578175516945)
              ·
                refine ⟨1846743595651183631637709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2462324794201578175516945 1846743595651183631637709)
                ·
                  refine ⟨692528848369193861864141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1846743595651183631637709 692528848369193861864141)
                  ·
                    refine ⟨259698318138447698199053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 692528848369193861864141 259698318138447698199053)
                    ·
                      rfl

theorem cell22_758641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 3, 3].length) (baseStart_758641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_758641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_758641 prefixEnd_758641 := by exact prefixLift 758641
  have htrace : WordTrace (prefixWord ++ tailWord_758641) baseStart_758641 baseEnd_758641 := by
    simpa [prefixWord, tailWord_758641, baseEnd_758641] using wordTrace_append hprefix tailTrace_758641
  have hstable : (prefixWord ++ tailWord_758641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758641).length < 2 ^ (prefixWord ++ tailWord_758641).sum := by decide
  have hdescent : baseEnd_758641 < baseStart_758641 := by decide
  rcases family_descends (prefixWord ++ tailWord_758641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758776 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 7, 3]
def baseStart_758776 : Nat := 118140960795 + 758776 * 2 ^ 59
def prefixEnd_758776 : Nat := 4983230072969 + 3 ^ 40 * 758776 * 2
def baseEnd_758776 : Nat := 259744531397352346073639

theorem tailTrace_758776 : CollatzResearch.WordTrace tailWord_758776 prefixEnd_758776 259744531397352346073639 := by
  unfold tailWord_758776
  simp only [CollatzResearch.WordTrace]
  refine ⟨13837417149545807734416091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18449889532727743645888121 13837417149545807734416091)
  ·
    refine ⟨20756125724318711601624137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13837417149545807734416091 20756125724318711601624137)
    ·
      refine ⟨15567094293239033701218103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20756125724318711601624137 15567094293239033701218103)
      ·
        refine ⟨23350641439858550551827155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15567094293239033701218103 23350641439858550551827155)
        ·
          refine ⟨35025962159787825827740733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23350641439858550551827155 35025962159787825827740733)
          ·
            refine ⟨13134735809920434685402775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35025962159787825827740733 13134735809920434685402775)
            ·
              refine ⟨19702103714880652028104163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13134735809920434685402775 19702103714880652028104163)
              ·
                refine ⟨29553155572320978042156245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19702103714880652028104163 29553155572320978042156245)
                ·
                  refine ⟨692652083726272922863037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 29553155572320978042156245 692652083726272922863037)
                  ·
                    refine ⟨259744531397352346073639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 692652083726272922863037 259744531397352346073639)
                    ·
                      rfl

theorem cell22_758776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 7, 3].length) (baseStart_758776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_758776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_758776 prefixEnd_758776 := by exact prefixLift 758776
  have htrace : WordTrace (prefixWord ++ tailWord_758776) baseStart_758776 baseEnd_758776 := by
    simpa [prefixWord, tailWord_758776, baseEnd_758776] using wordTrace_append hprefix tailTrace_758776
  have hstable : (prefixWord ++ tailWord_758776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758776).length < 2 ^ (prefixWord ++ tailWord_758776).sum := by decide
  have hdescent : baseEnd_758776 < baseStart_758776 := by decide
  rcases family_descends (prefixWord ++ tailWord_758776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758823 : List Nat := [1, 1, 7, 1, 1, 1, 1, 2, 7]
def baseStart_758823 : Nat := 118140960795 + 758823 * 2 ^ 59
def prefixEnd_758823 : Nat := 4983230072969 + 3 ^ 40 * 758823 * 2
def baseEnd_758823 : Nat := 86586873485953296716165

theorem tailTrace_758823 : CollatzResearch.WordTrace tailWord_758823 prefixEnd_758823 86586873485953296716165 := by
  unfold tailWord_758823
  simp only [CollatzResearch.WordTrace]
  refine ⟨27676548529921342495793123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18451032353280894997195415 27676548529921342495793123)
  ·
    refine ⟨41514822794882013743689685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27676548529921342495793123 41514822794882013743689685)
    ·
      refine ⟨973003659255047197117727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 41514822794882013743689685 973003659255047197117727)
      ·
        refine ⟨1459505488882570795676591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 973003659255047197117727 1459505488882570795676591)
        ·
          refine ⟨2189258233323856193514887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1459505488882570795676591 2189258233323856193514887)
          ·
            refine ⟨3283887349985784290272331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2189258233323856193514887 3283887349985784290272331)
            ·
              refine ⟨4925831024978676435408497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3283887349985784290272331 4925831024978676435408497)
              ·
                refine ⟨3694373268734007326556373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4925831024978676435408497 3694373268734007326556373)
                ·
                  refine ⟨86586873485953296716165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3694373268734007326556373 86586873485953296716165)
                  ·
                    rfl

theorem cell22_758823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 7].length) (baseStart_758823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_758823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_758823 prefixEnd_758823 := by exact prefixLift 758823
  have htrace : WordTrace (prefixWord ++ tailWord_758823) baseStart_758823 baseEnd_758823 := by
    simpa [prefixWord, tailWord_758823, baseEnd_758823] using wordTrace_append hprefix tailTrace_758823
  have hstable : (prefixWord ++ tailWord_758823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758823).length < 2 ^ (prefixWord ++ tailWord_758823).sum := by decide
  have hdescent : baseEnd_758823 < baseStart_758823 := by decide
  rcases family_descends (prefixWord ++ tailWord_758823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758881 : List Nat := [1, 2, 3, 1, 1, 2, 2, 3, 1, 6]
def baseStart_758881 : Nat := 118140960795 + 758881 * 2 ^ 59
def prefixEnd_758881 : Nat := 4983230072969 + 3 ^ 40 * 758881 * 2
def baseEnd_758881 : Nat := 259780475043167072198317

theorem tailTrace_758881 : CollatzResearch.WordTrace tailWord_758881 prefixEnd_758881 259780475043167072198317 := by
  unfold tailWord_758881
  simp only [CollatzResearch.WordTrace]
  refine ⟨27678663963711218401404497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18452442642474145600936331 27678663963711218401404497)
  ·
    refine ⟨20758997972783413801053373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27678663963711218401404497 20758997972783413801053373)
    ·
      refine ⟨7784624239793780175395015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20758997972783413801053373 7784624239793780175395015)
      ·
        refine ⟨11676936359690670263092523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7784624239793780175395015 11676936359690670263092523)
        ·
          refine ⟨17515404539536005394638785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11676936359690670263092523 17515404539536005394638785)
          ·
            refine ⟨13136553404652004045979089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17515404539536005394638785 13136553404652004045979089)
            ·
              refine ⟨9852415053489003034484317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13136553404652004045979089 9852415053489003034484317)
              ·
                refine ⟨3694655645058376137931619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9852415053489003034484317 3694655645058376137931619)
                ·
                  refine ⟨5541983467587564206897429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3694655645058376137931619 5541983467587564206897429)
                  ·
                    refine ⟨259780475043167072198317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5541983467587564206897429 259780475043167072198317)
                    ·
                      rfl

theorem cell22_758881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_758881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_758881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_758881 prefixEnd_758881 := by exact prefixLift 758881
  have htrace : WordTrace (prefixWord ++ tailWord_758881) baseStart_758881 baseEnd_758881 := by
    simpa [prefixWord, tailWord_758881, baseEnd_758881] using wordTrace_append hprefix tailTrace_758881
  have hstable : (prefixWord ++ tailWord_758881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758881).length < 2 ^ (prefixWord ++ tailWord_758881).sum := by decide
  have hdescent : baseEnd_758881 < baseStart_758881 := by decide
  rcases family_descends (prefixWord ++ tailWord_758881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758898 : List Nat := [3, 2, 1, 2, 2, 1, 1, 4, 2, 4]
def baseStart_758898 : Nat := 118140960795 + 758898 * 2 ^ 59
def prefixEnd_758898 : Nat := 4983230072969 + 3 ^ 40 * 758898 * 2
def baseEnd_758898 : Nat := 259786294490584694523265

theorem tailTrace_758898 : CollatzResearch.WordTrace tailWord_758898 prefixEnd_758898 259786294490584694523265 := by
  unfold tailWord_758898
  simp only [CollatzResearch.WordTrace]
  refine ⟨6919821001162407576193337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18452856003099753536515565 6919821001162407576193337)
  ·
    refine ⟨5189865750871805682145003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6919821001162407576193337 5189865750871805682145003)
    ·
      refine ⟨7784798626307708523217505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5189865750871805682145003 7784798626307708523217505)
      ·
        refine ⟨5838598969730781392413129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7784798626307708523217505 5838598969730781392413129)
        ·
          refine ⟨4378949227298086044309847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5838598969730781392413129 4378949227298086044309847)
          ·
            refine ⟨6568423840947129066464771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4378949227298086044309847 6568423840947129066464771)
            ·
              refine ⟨9852635761420693599697157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6568423840947129066464771 9852635761420693599697157)
              ·
                refine ⟨1847369205266380049943217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9852635761420693599697157 1847369205266380049943217)
                ·
                  refine ⟨1385526903949785037457413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1847369205266380049943217 1385526903949785037457413)
                  ·
                    refine ⟨259786294490584694523265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1385526903949785037457413 259786294490584694523265)
                    ·
                      rfl

theorem cell22_758898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_758898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_758898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_758898 prefixEnd_758898 := by exact prefixLift 758898
  have htrace : WordTrace (prefixWord ++ tailWord_758898) baseStart_758898 baseEnd_758898 := by
    simpa [prefixWord, tailWord_758898, baseEnd_758898] using wordTrace_append hprefix tailTrace_758898
  have hstable : (prefixWord ++ tailWord_758898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758898).length < 2 ^ (prefixWord ++ tailWord_758898).sum := by decide
  have hdescent : baseEnd_758898 < baseStart_758898 := by decide
  rcases family_descends (prefixWord ++ tailWord_758898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758913 : List Nat := [1, 2, 4, 2, 2, 1, 3, 7]
def baseStart_758913 : Nat := 118140960795 + 758913 * 2 ^ 59
def prefixEnd_758913 : Nat := 4983230072969 + 3 ^ 40 * 758913 * 2
def baseEnd_758913 : Nat := 28865714366347739488691

theorem tailTrace_758913 : CollatzResearch.WordTrace tailWord_758913 prefixEnd_758913 28865714366347739488691 := by
  unfold tailWord_758913
  simp only [CollatzResearch.WordTrace]
  refine ⟨27679831099595287866569393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18453220733063525244379595 27679831099595287866569393)
  ·
    refine ⟨20759873324696465899927045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27679831099595287866569393 20759873324696465899927045)
    ·
      refine ⟨3892476248380587356236321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20759873324696465899927045 3892476248380587356236321)
      ·
        refine ⟨2919357186285440517177241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3892476248380587356236321 2919357186285440517177241)
        ·
          refine ⟨2189517889714080387882931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2919357186285440517177241 2189517889714080387882931)
          ·
            refine ⟨3284276834571120581824397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2189517889714080387882931 3284276834571120581824397)
            ·
              refine ⟨1231603812964170218184149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3284276834571120581824397 1231603812964170218184149)
              ·
                refine ⟨28865714366347739488691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1231603812964170218184149 28865714366347739488691)
                ·
                  rfl

theorem cell22_758913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 7].length) (baseStart_758913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_758913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_758913 prefixEnd_758913 := by exact prefixLift 758913
  have htrace : WordTrace (prefixWord ++ tailWord_758913) baseStart_758913 baseEnd_758913 := by
    simpa [prefixWord, tailWord_758913, baseEnd_758913] using wordTrace_append hprefix tailTrace_758913
  have hstable : (prefixWord ++ tailWord_758913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758913).length < 2 ^ (prefixWord ++ tailWord_758913).sum := by decide
  have hdescent : baseEnd_758913 < baseStart_758913 := by decide
  rcases family_descends (prefixWord ++ tailWord_758913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758930 : List Nat := [3, 2, 3, 1, 1, 3, 3, 6]
def baseStart_758930 : Nat := 118140960795 + 758930 * 2 ^ 59
def prefixEnd_758930 : Nat := 4983230072969 + 3 ^ 40 * 758930 * 2
def baseEnd_758930 : Nat := 28866360971616364191463

theorem tailTrace_758930 : CollatzResearch.WordTrace tailWord_758930 prefixEnd_758930 28866360971616364191463 := by
  unfold tailWord_758930
  simp only [CollatzResearch.WordTrace]
  refine ⟨6920112785133424942484561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18453634093689133179958829 6920112785133424942484561)
  ·
    refine ⟨5190084588850068706863421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6920112785133424942484561 5190084588850068706863421)
    ·
      refine ⟨1946281720818775765073783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5190084588850068706863421 1946281720818775765073783)
      ·
        refine ⟨2919422581228163647610675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1946281720818775765073783 2919422581228163647610675)
        ·
          refine ⟨4379133871842245471416013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2919422581228163647610675 4379133871842245471416013)
          ·
            refine ⟨1642175201940842051781005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4379133871842245471416013 1642175201940842051781005)
            ·
              refine ⟨615815700727815769417877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1642175201940842051781005 615815700727815769417877)
              ·
                refine ⟨28866360971616364191463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 615815700727815769417877 28866360971616364191463)
                ·
                  rfl

theorem cell22_758930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 6].length) (baseStart_758930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_758930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_758930 prefixEnd_758930 := by exact prefixLift 758930
  have htrace : WordTrace (prefixWord ++ tailWord_758930) baseStart_758930 baseEnd_758930 := by
    simpa [prefixWord, tailWord_758930, baseEnd_758930] using wordTrace_append hprefix tailTrace_758930
  have hstable : (prefixWord ++ tailWord_758930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758930).length < 2 ^ (prefixWord ++ tailWord_758930).sum := by decide
  have hdescent : baseEnd_758930 < baseStart_758930 := by decide
  rcases family_descends (prefixWord ++ tailWord_758930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758962 : List Nat := [3, 2, 1, 1, 1, 4, 2, 4, 1, 3]
def baseStart_758962 : Nat := 118140960795 + 758962 * 2 ^ 59
def prefixEnd_758962 : Nat := 4983230072969 + 3 ^ 40 * 758962 * 2
def baseEnd_758962 : Nat := 259808202998509860923069

theorem tailTrace_758962 : CollatzResearch.WordTrace tailWord_758962 prefixEnd_758962 259808202998509860923069 := by
  unfold tailWord_758962
  simp only [CollatzResearch.WordTrace]
  refine ⟨6920404569104442308775785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18454412184278512823402093 6920404569104442308775785)
  ·
    refine ⟨5190303426828331731581839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6920404569104442308775785 5190303426828331731581839)
    ·
      refine ⟨7785455140242497597372759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5190303426828331731581839 7785455140242497597372759)
      ·
        refine ⟨11678182710363746396059139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7785455140242497597372759 11678182710363746396059139)
        ·
          refine ⟨17517274065545619594088709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11678182710363746396059139 17517274065545619594088709)
          ·
            refine ⟨3284488887289803673891633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17517274065545619594088709 3284488887289803673891633)
            ·
              refine ⟨2463366665467352755418725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3284488887289803673891633 2463366665467352755418725)
              ·
                refine ⟨461881249775128641641011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2463366665467352755418725 461881249775128641641011)
                ·
                  refine ⟨692821874662692962461517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 461881249775128641641011 692821874662692962461517)
                  ·
                    refine ⟨259808202998509860923069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 692821874662692962461517 259808202998509860923069)
                    ·
                      rfl

theorem cell22_758962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 4, 1, 3].length) (baseStart_758962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_758962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_758962 prefixEnd_758962 := by exact prefixLift 758962
  have htrace : WordTrace (prefixWord ++ tailWord_758962) baseStart_758962 baseEnd_758962 := by
    simpa [prefixWord, tailWord_758962, baseEnd_758962] using wordTrace_append hprefix tailTrace_758962
  have hstable : (prefixWord ++ tailWord_758962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758962).length < 2 ^ (prefixWord ++ tailWord_758962).sum := by decide
  have hdescent : baseEnd_758962 < baseStart_758962 := by decide
  rcases family_descends (prefixWord ++ tailWord_758962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758971 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 2, 8]
def baseStart_758971 : Nat := 118140960795 + 758971 * 2 ^ 59
def prefixEnd_758971 : Nat := 4983230072969 + 3 ^ 40 * 758971 * 2
def baseEnd_758971 : Nat := 259811283882436837448041

theorem tailTrace_758971 : CollatzResearch.WordTrace tailWord_758971 prefixEnd_758971 259811283882436837448041 := by
  unfold tailWord_758971
  simp only [CollatzResearch.WordTrace]
  refine ⟨27681946533385163772180767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18454631022256775848120511 27681946533385163772180767)
  ·
    refine ⟨41522919800077745658271151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27681946533385163772180767 41522919800077745658271151)
    ·
      refine ⟨62284379700116618487406727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41522919800077745658271151 62284379700116618487406727)
      ·
        refine ⟨93426569550174927731110091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62284379700116618487406727 93426569550174927731110091)
        ·
          refine ⟨140139854325262391596665137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93426569550174927731110091 140139854325262391596665137)
          ·
            refine ⟨105104890743946793697498853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140139854325262391596665137 105104890743946793697498853)
            ·
              refine ⟨19707167014490023818281035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105104890743946793697498853 19707167014490023818281035)
              ·
                refine ⟨29560750521735035727421553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19707167014490023818281035 29560750521735035727421553)
                ·
                  refine ⟨22170562891301276795566165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29560750521735035727421553 22170562891301276795566165)
                  ·
                    refine ⟨259811283882436837448041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 22170562891301276795566165 259811283882436837448041)
                    ·
                      rfl

theorem cell22_758971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 8].length) (baseStart_758971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_758971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_758971 prefixEnd_758971 := by exact prefixLift 758971
  have htrace : WordTrace (prefixWord ++ tailWord_758971) baseStart_758971 baseEnd_758971 := by
    simpa [prefixWord, tailWord_758971, baseEnd_758971] using wordTrace_append hprefix tailTrace_758971
  have hstable : (prefixWord ++ tailWord_758971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758971).length < 2 ^ (prefixWord ++ tailWord_758971).sum := by decide
  have hdescent : baseEnd_758971 < baseStart_758971 := by decide
  rcases family_descends (prefixWord ++ tailWord_758971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_758973 : List Nat := [1, 4, 1, 2, 1, 1, 4, 1, 2, 5]
def baseStart_758973 : Nat := 118140960795 + 758973 * 2 ^ 59
def prefixEnd_758973 : Nat := 4983230072969 + 3 ^ 40 * 758973 * 2
def baseEnd_758973 : Nat := 259811968523309498898035

theorem tailTrace_758973 : CollatzResearch.WordTrace tailWord_758973 prefixEnd_758973 259811968523309498898035 := by
  unfold tailWord_758973
  simp only [CollatzResearch.WordTrace]
  refine ⟨27682019479377918113753573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18454679652918612075835715 27682019479377918113753573)
  ·
    refine ⟨5190378652383359646328795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27682019479377918113753573 5190378652383359646328795)
    ·
      refine ⟨7785567978575039469493193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5190378652383359646328795 7785567978575039469493193)
      ·
        refine ⟨5839175983931279602119895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7785567978575039469493193 5839175983931279602119895)
        ·
          refine ⟨8758763975896919403179843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5839175983931279602119895 8758763975896919403179843)
          ·
            refine ⟨13138145963845379104769765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8758763975896919403179843 13138145963845379104769765)
            ·
              refine ⟨2463402368221008582144331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13138145963845379104769765 2463402368221008582144331)
              ·
                refine ⟨3695103552331512873216497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2463402368221008582144331 3695103552331512873216497)
                ·
                  refine ⟨2771327664248634654912373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3695103552331512873216497 2771327664248634654912373)
                  ·
                    refine ⟨259811968523309498898035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2771327664248634654912373 259811968523309498898035)
                    ·
                      rfl

theorem cell22_758973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_758973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_758973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_758973 prefixEnd_758973 := by exact prefixLift 758973
  have htrace : WordTrace (prefixWord ++ tailWord_758973) baseStart_758973 baseEnd_758973 := by
    simpa [prefixWord, tailWord_758973, baseEnd_758973] using wordTrace_append hprefix tailTrace_758973
  have hstable : (prefixWord ++ tailWord_758973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_758973).length < 2 ^ (prefixWord ++ tailWord_758973).sum := by decide
  have hdescent : baseEnd_758973 < baseStart_758973 := by decide
  rcases family_descends (prefixWord ++ tailWord_758973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759020 : List Nat := [2, 2, 1, 1, 2, 6, 1, 1, 6]
def baseStart_759020 : Nat := 118140960795 + 759020 * 2 ^ 59
def prefixEnd_759020 : Nat := 4983230072969 + 3 ^ 40 * 759020 * 2
def baseEnd_759020 : Nat := 86609352527939014324297

theorem tailTrace_759020 : CollatzResearch.WordTrace tailWord_759020 prefixEnd_759020 86609352527939014324297 := by
  unfold tailWord_759020
  simp only [CollatzResearch.WordTrace]
  refine ⟨13841866855103822570357257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18455822473471763427143009 13841866855103822570357257)
  ·
    refine ⟨10381400141327866927767943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13841866855103822570357257 10381400141327866927767943)
    ·
      refine ⟨15572100211991800391651915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10381400141327866927767943 15572100211991800391651915)
      ·
        refine ⟨23358150317987700587477873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15572100211991800391651915 23358150317987700587477873)
        ·
          refine ⟨17518612738490775440608405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23358150317987700587477873 17518612738490775440608405)
          ·
            refine ⟨821184972116755098778519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17518612738490775440608405 821184972116755098778519)
            ·
              refine ⟨1231777458175132648167779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 821184972116755098778519 1231777458175132648167779)
              ·
                refine ⟨1847666187262698972251669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1231777458175132648167779 1847666187262698972251669)
                ·
                  refine ⟨86609352527939014324297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1847666187262698972251669 86609352527939014324297)
                  ·
                    rfl

theorem cell22_759020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 6].length) (baseStart_759020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759020 prefixEnd_759020 := by exact prefixLift 759020
  have htrace : WordTrace (prefixWord ++ tailWord_759020) baseStart_759020 baseEnd_759020 := by
    simpa [prefixWord, tailWord_759020, baseEnd_759020] using wordTrace_append hprefix tailTrace_759020
  have hstable : (prefixWord ++ tailWord_759020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759020).length < 2 ^ (prefixWord ++ tailWord_759020).sum := by decide
  have hdescent : baseEnd_759020 < baseStart_759020 := by decide
  rcases family_descends (prefixWord ++ tailWord_759020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759033 : List Nat := [1, 2, 1, 3, 1, 1, 3, 2, 4, 4]
def baseStart_759033 : Nat := 118140960795 + 759033 * 2 ^ 59
def prefixEnd_759033 : Nat := 4983230072969 + 3 ^ 40 * 759033 * 2
def baseEnd_759033 : Nat := 259832507749489342397851

theorem tailTrace_759033 : CollatzResearch.WordTrace tailWord_759033 prefixEnd_759033 259832507749489342397851 := by
  unfold tailWord_759033
  simp only [CollatzResearch.WordTrace]
  refine ⟨27684207859160548360937753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18456138572773698907291835 27684207859160548360937753)
  ·
    refine ⟨20763155894370411270703315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27684207859160548360937753 20763155894370411270703315)
    ·
      refine ⟨31144733841555616906054973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20763155894370411270703315 31144733841555616906054973)
      ·
        refine ⟨11679275190583356339770615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31144733841555616906054973 11679275190583356339770615)
        ·
          refine ⟨17518912785875034509655923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11679275190583356339770615 17518912785875034509655923)
          ·
            refine ⟨26278369178812551764483885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17518912785875034509655923 26278369178812551764483885)
            ·
              refine ⟨9854388442054706911681457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26278369178812551764483885 9854388442054706911681457)
              ·
                refine ⟨7390791331541030183761093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9854388442054706911681457 7390791331541030183761093)
                ·
                  refine ⟨1385773374663943159455205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7390791331541030183761093 1385773374663943159455205)
                  ·
                    refine ⟨259832507749489342397851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1385773374663943159455205 259832507749489342397851)
                    ·
                      rfl

theorem cell22_759033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 4].length) (baseStart_759033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759033 prefixEnd_759033 := by exact prefixLift 759033
  have htrace : WordTrace (prefixWord ++ tailWord_759033) baseStart_759033 baseEnd_759033 := by
    simpa [prefixWord, tailWord_759033, baseEnd_759033] using wordTrace_append hprefix tailTrace_759033
  have hstable : (prefixWord ++ tailWord_759033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759033).length < 2 ^ (prefixWord ++ tailWord_759033).sum := by decide
  have hdescent : baseEnd_759033 < baseStart_759033 := by decide
  rcases family_descends (prefixWord ++ tailWord_759033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759069 : List Nat := [1, 4, 2, 3, 1, 2, 2, 2, 2, 3]
def baseStart_759069 : Nat := 118140960795 + 759069 * 2 ^ 59
def prefixEnd_759069 : Nat := 4983230072969 + 3 ^ 40 * 759069 * 2
def baseEnd_759069 : Nat := 259844831285197248497741

theorem tailTrace_759069 : CollatzResearch.WordTrace tailWord_759069 prefixEnd_759069 259844831285197248497741 := by
  unfold tailWord_759069
  simp only [CollatzResearch.WordTrace]
  refine ⟨27685520887030126509248261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18457013924686751006165507 27685520887030126509248261)
  ·
    refine ⟨5191035166318148720484049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27685520887030126509248261 5191035166318148720484049)
    ·
      refine ⟨3893276374738611540363037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5191035166318148720484049 3893276374738611540363037)
      ·
        refine ⟨1459978640526979327636139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3893276374738611540363037 1459978640526979327636139)
        ·
          refine ⟨2189967960790468991454209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1459978640526979327636139 2189967960790468991454209)
          ·
            refine ⟨1642475970592851743590657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2189967960790468991454209 1642475970592851743590657)
            ·
              refine ⟨1231856977944638807692993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1642475970592851743590657 1231856977944638807692993)
              ·
                refine ⟨923892733458479105769745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1231856977944638807692993 923892733458479105769745)
                ·
                  refine ⟨692919550093859329327309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 923892733458479105769745 692919550093859329327309)
                  ·
                    refine ⟨259844831285197248497741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 692919550093859329327309 259844831285197248497741)
                    ·
                      rfl

theorem cell22_759069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_759069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759069 prefixEnd_759069 := by exact prefixLift 759069
  have htrace : WordTrace (prefixWord ++ tailWord_759069) baseStart_759069 baseEnd_759069 := by
    simpa [prefixWord, tailWord_759069, baseEnd_759069] using wordTrace_append hprefix tailTrace_759069
  have hstable : (prefixWord ++ tailWord_759069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759069).length < 2 ^ (prefixWord ++ tailWord_759069).sum := by decide
  have hdescent : baseEnd_759069 < baseStart_759069 := by decide
  rcases family_descends (prefixWord ++ tailWord_759069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759071 : List Nat := [1, 1, 2, 4, 5, 1, 2, 2, 4]
def baseStart_759071 : Nat := 118140960795 + 759071 * 2 ^ 59
def prefixEnd_759071 : Nat := 4983230072969 + 3 ^ 40 * 759071 * 2
def baseEnd_759071 : Nat := 86615171975356636649245

theorem tailTrace_759071 : CollatzResearch.WordTrace tailWord_759071 prefixEnd_759071 86615171975356636649245 := by
  unfold tailWord_759071
  simp only [CollatzResearch.WordTrace]
  refine ⟨27685593833022880850821067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18457062555348587233880711 27685593833022880850821067)
  ·
    refine ⟨41528390749534321276231601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27685593833022880850821067 41528390749534321276231601)
    ·
      refine ⟨31146293062150740957173701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41528390749534321276231601 31146293062150740957173701)
      ·
        refine ⟨5839929949153263929470069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31146293062150740957173701 5839929949153263929470069)
        ·
          refine ⟨547493432733118493387819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5839929949153263929470069 547493432733118493387819)
          ·
            refine ⟨821240149099677740081729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547493432733118493387819 821240149099677740081729)
            ·
              refine ⟨615930111824758305061297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 821240149099677740081729 615930111824758305061297)
              ·
                refine ⟨461947583868568728795973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 615930111824758305061297 461947583868568728795973)
                ·
                  refine ⟨86615171975356636649245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 461947583868568728795973 86615171975356636649245)
                  ·
                    rfl

theorem cell22_759071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 2, 4].length) (baseStart_759071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759071 prefixEnd_759071 := by exact prefixLift 759071
  have htrace : WordTrace (prefixWord ++ tailWord_759071) baseStart_759071 baseEnd_759071 := by
    simpa [prefixWord, tailWord_759071, baseEnd_759071] using wordTrace_append hprefix tailTrace_759071
  have hstable : (prefixWord ++ tailWord_759071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759071).length < 2 ^ (prefixWord ++ tailWord_759071).sum := by decide
  have hdescent : baseEnd_759071 < baseStart_759071 := by decide
  rcases family_descends (prefixWord ++ tailWord_759071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759082 : List Nat := [3, 1, 4, 2, 1, 3, 1, 7]
def baseStart_759082 : Nat := 118140960795 + 759082 * 2 ^ 59
def prefixEnd_759082 : Nat := 4983230072969 + 3 ^ 40 * 759082 * 2
def baseEnd_759082 : Nat := 28872142383429949769189

theorem tailTrace_759082 : CollatzResearch.WordTrace tailWord_759082 prefixEnd_759082 28872142383429949769189 := by
  unfold tailWord_759082
  simp only [CollatzResearch.WordTrace]
  refine ⟨6921498758995757432367875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18457330023988686486314333 6921498758995757432367875)
  ·
    refine ⟨10382248138493636148551813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6921498758995757432367875 10382248138493636148551813)
    ·
      refine ⟨1946671525967556777853465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10382248138493636148551813 1946671525967556777853465)
      ·
        refine ⟨1460003644475667583390099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1946671525967556777853465 1460003644475667583390099)
        ·
          refine ⟨2190005466713501375085149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1460003644475667583390099 2190005466713501375085149)
          ·
            refine ⟨821252050017563015656931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2190005466713501375085149 821252050017563015656931)
            ·
              refine ⟨1231878075026344523485397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 821252050017563015656931 1231878075026344523485397)
              ·
                refine ⟨28872142383429949769189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1231878075026344523485397 28872142383429949769189)
                ·
                  rfl

theorem cell22_759082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 7].length) (baseStart_759082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759082 prefixEnd_759082 := by exact prefixLift 759082
  have htrace : WordTrace (prefixWord ++ tailWord_759082) baseStart_759082 baseEnd_759082 := by
    simpa [prefixWord, tailWord_759082, baseEnd_759082] using wordTrace_append hprefix tailTrace_759082
  have hstable : (prefixWord ++ tailWord_759082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759082).length < 2 ^ (prefixWord ++ tailWord_759082).sum := by decide
  have hdescent : baseEnd_759082 < baseStart_759082 := by decide
  rcases family_descends (prefixWord ++ tailWord_759082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759101 : List Nat := [1, 4, 1, 5, 2, 1, 1, 1, 2, 4]
def baseStart_759101 : Nat := 118140960795 + 759101 * 2 ^ 59
def prefixEnd_759101 : Nat := 4983230072969 + 3 ^ 40 * 759101 * 2
def baseEnd_759101 : Nat := 259855785539159831697643

theorem tailTrace_759101 : CollatzResearch.WordTrace tailWord_759101 prefixEnd_759101 259855785539159831697643 := by
  unfold tailWord_759101
  simp only [CollatzResearch.WordTrace]
  refine ⟨27686688022914195974413157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18457792015276130649608771 27686688022914195974413157)
  ·
    refine ⟨5191254004296411745202467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27686688022914195974413157 5191254004296411745202467)
    ·
      refine ⟨7786881006444617617803701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5191254004296411745202467 7786881006444617617803701)
      ·
        refine ⟨730020094354182901669097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7786881006444617617803701 730020094354182901669097)
        ·
          refine ⟨547515070765637176251823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 730020094354182901669097 547515070765637176251823)
          ·
            refine ⟨821272606148455764377735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547515070765637176251823 821272606148455764377735)
            ·
              refine ⟨1231908909222683646566603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 821272606148455764377735 1231908909222683646566603)
              ·
                refine ⟨1847863363834025469849905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1231908909222683646566603 1847863363834025469849905)
                ·
                  refine ⟨1385897522875519102387429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1847863363834025469849905 1385897522875519102387429)
                  ·
                    refine ⟨259855785539159831697643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1385897522875519102387429 259855785539159831697643)
                    ·
                      rfl

theorem cell22_759101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 2, 4].length) (baseStart_759101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759101 prefixEnd_759101 := by exact prefixLift 759101
  have htrace : WordTrace (prefixWord ++ tailWord_759101) baseStart_759101 baseEnd_759101 := by
    simpa [prefixWord, tailWord_759101, baseEnd_759101] using wordTrace_append hprefix tailTrace_759101
  have hstable : (prefixWord ++ tailWord_759101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759101).length < 2 ^ (prefixWord ++ tailWord_759101).sum := by decide
  have hdescent : baseEnd_759101 < baseStart_759101 := by decide
  rcases family_descends (prefixWord ++ tailWord_759101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759125 : List Nat := [1, 3, 2, 2, 3, 1, 1, 2, 2, 5]
def baseStart_759125 : Nat := 118140960795 + 759125 * 2 ^ 59
def prefixEnd_759125 : Nat := 4983230072969 + 3 ^ 40 * 759125 * 2
def baseEnd_759125 : Nat := 259864001229631769097569

theorem tailTrace_759125 : CollatzResearch.WordTrace tailWord_759125 prefixEnd_759125 259864001229631769097569 := by
  unfold tailWord_759125
  simp only [CollatzResearch.WordTrace]
  refine ⟨27687563374827248073286829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18458375583218165382191219 27687563374827248073286829)
  ·
    refine ⟨10382836265560218027482561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27687563374827248073286829 10382836265560218027482561)
    ·
      refine ⟨7787127199170163520611921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10382836265560218027482561 7787127199170163520611921)
      ·
        refine ⟨5840345399377622640458941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7787127199170163520611921 5840345399377622640458941)
        ·
          refine ⟨2190129524766608490172103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5840345399377622640458941 2190129524766608490172103)
          ·
            refine ⟨3285194287149912735258155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2190129524766608490172103 3285194287149912735258155)
            ·
              refine ⟨4927791430724869102887233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3285194287149912735258155 4927791430724869102887233)
              ·
                refine ⟨3695843573043651827165425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4927791430724869102887233 3695843573043651827165425)
                ·
                  refine ⟨2771882679782738870374069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3695843573043651827165425 2771882679782738870374069)
                  ·
                    refine ⟨259864001229631769097569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2771882679782738870374069 259864001229631769097569)
                    ·
                      rfl

theorem cell22_759125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_759125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759125 prefixEnd_759125 := by exact prefixLift 759125
  have htrace : WordTrace (prefixWord ++ tailWord_759125) baseStart_759125 baseEnd_759125 := by
    simpa [prefixWord, tailWord_759125, baseEnd_759125] using wordTrace_append hprefix tailTrace_759125
  have hstable : (prefixWord ++ tailWord_759125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759125).length < 2 ^ (prefixWord ++ tailWord_759125).sum := by decide
  have hdescent : baseEnd_759125 < baseStart_759125 := by decide
  rcases family_descends (prefixWord ++ tailWord_759125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759127 : List Nat := [1, 1, 3, 2, 3, 4, 1, 2, 5]
def baseStart_759127 : Nat := 118140960795 + 759127 * 2 ^ 59
def prefixEnd_759127 : Nat := 4983230072969 + 3 ^ 40 * 759127 * 2
def baseEnd_759127 : Nat := 86621561956834810182521

theorem tailTrace_759127 : CollatzResearch.WordTrace tailWord_759127 prefixEnd_759127 86621561956834810182521 := by
  unfold tailWord_759127
  simp only [CollatzResearch.WordTrace]
  refine ⟨27687636320820002414859635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18458424213880001609906423 27687636320820002414859635)
  ·
    refine ⟨41531454481230003622289453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27687636320820002414859635 41531454481230003622289453)
    ·
      refine ⟨15574295430461251358358545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41531454481230003622289453 15574295430461251358358545)
      ·
        refine ⟨11680721572845938518768909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15574295430461251358358545 11680721572845938518768909)
        ·
          refine ⟨4380270589817226944538341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11680721572845938518768909 4380270589817226944538341)
          ·
            refine ⟨821300735590730052100939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4380270589817226944538341 821300735590730052100939)
            ·
              refine ⟨1231951103386095078151409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 821300735590730052100939 1231951103386095078151409)
              ·
                refine ⟨923963327539571308613557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1231951103386095078151409 923963327539571308613557)
                ·
                  refine ⟨86621561956834810182521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 923963327539571308613557 86621561956834810182521)
                  ·
                    rfl

theorem cell22_759127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 5].length) (baseStart_759127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759127 prefixEnd_759127 := by exact prefixLift 759127
  have htrace : WordTrace (prefixWord ++ tailWord_759127) baseStart_759127 baseEnd_759127 := by
    simpa [prefixWord, tailWord_759127, baseEnd_759127] using wordTrace_append hprefix tailTrace_759127
  have hstable : (prefixWord ++ tailWord_759127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759127).length < 2 ^ (prefixWord ++ tailWord_759127).sum := by decide
  have hdescent : baseEnd_759127 < baseStart_759127 := by decide
  rcases family_descends (prefixWord ++ tailWord_759127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759144 : List Nat := [2, 1, 4, 2, 3, 1, 3, 1, 5]
def baseStart_759144 : Nat := 118140960795 + 759144 * 2 ^ 59
def prefixEnd_759144 : Nat := 4983230072969 + 3 ^ 40 * 759144 * 2
def baseEnd_759144 : Nat := 86623501772640684290837

theorem tailTrace_759144 : CollatzResearch.WordTrace tailWord_759144 prefixEnd_759144 86623501772640684290837 := by
  unfold tailWord_759144
  simp only [CollatzResearch.WordTrace]
  refine ⟨13844128180879207159114243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18458837574505609545485657 13844128180879207159114243)
  ·
    refine ⟨20766192271318810738671365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13844128180879207159114243 20766192271318810738671365)
    ·
      refine ⟨3893661050872277013500881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20766192271318810738671365 3893661050872277013500881)
      ·
        refine ⟨2920245788154207760125661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3893661050872277013500881 2920245788154207760125661)
        ·
          refine ⟨1095092170557827910047123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2920245788154207760125661 1095092170557827910047123)
          ·
            refine ⟨1642638255836741865070685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1095092170557827910047123 1642638255836741865070685)
            ·
              refine ⟨615989345938778199401507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1642638255836741865070685 615989345938778199401507)
              ·
                refine ⟨923984018908167299102261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 615989345938778199401507 923984018908167299102261)
                ·
                  refine ⟨86623501772640684290837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 923984018908167299102261 86623501772640684290837)
                  ·
                    rfl

theorem cell22_759144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 5].length) (baseStart_759144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759144 prefixEnd_759144 := by exact prefixLift 759144
  have htrace : WordTrace (prefixWord ++ tailWord_759144) baseStart_759144 baseEnd_759144 := by
    simpa [prefixWord, tailWord_759144, baseEnd_759144] using wordTrace_append hprefix tailTrace_759144
  have hstable : (prefixWord ++ tailWord_759144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759144).length < 2 ^ (prefixWord ++ tailWord_759144).sum := by decide
  have hdescent : baseEnd_759144 < baseStart_759144 := by decide
  rcases family_descends (prefixWord ++ tailWord_759144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759185 : List Nat := [1, 2, 2, 1, 1, 1, 2, 6, 2, 4]
def baseStart_759185 : Nat := 118140960795 + 759185 * 2 ^ 59
def prefixEnd_759185 : Nat := 4983230072969 + 3 ^ 40 * 759185 * 2
def baseEnd_759185 : Nat := 259884540455811612597385

theorem tailTrace_759185 : CollatzResearch.WordTrace tailWord_759185 prefixEnd_759185 259884540455811612597385 := by
  unfold tailWord_759185
  simp only [CollatzResearch.WordTrace]
  refine ⟨27689751754609878320471009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18459834503073252213647339 27689751754609878320471009)
  ·
    refine ⟨20767313815957408740353257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27689751754609878320471009 20767313815957408740353257)
    ·
      refine ⟨15575485361968056555264943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20767313815957408740353257 15575485361968056555264943)
      ·
        refine ⟨23363228042952084832897415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15575485361968056555264943 23363228042952084832897415)
        ·
          refine ⟨35044842064428127249346123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23363228042952084832897415 35044842064428127249346123)
          ·
            refine ⟨52567263096642190874019185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35044842064428127249346123 52567263096642190874019185)
            ·
              refine ⟨39425447322481643155514389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52567263096642190874019185 39425447322481643155514389)
              ·
                refine ⟨1848067843241327022914737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39425447322481643155514389 1848067843241327022914737)
                ·
                  refine ⟨1386050882430995267186053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1848067843241327022914737 1386050882430995267186053)
                  ·
                    refine ⟨259884540455811612597385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1386050882430995267186053 259884540455811612597385)
                    ·
                      rfl

theorem cell22_759185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_759185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759185 prefixEnd_759185 := by exact prefixLift 759185
  have htrace : WordTrace (prefixWord ++ tailWord_759185) baseStart_759185 baseEnd_759185 := by
    simpa [prefixWord, tailWord_759185, baseEnd_759185] using wordTrace_append hprefix tailTrace_759185
  have hstable : (prefixWord ++ tailWord_759185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759185).length < 2 ^ (prefixWord ++ tailWord_759185).sum := by decide
  have hdescent : baseEnd_759185 < baseStart_759185 := by decide
  rcases family_descends (prefixWord ++ tailWord_759185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759200 : List Nat := [2, 1, 1, 4, 1, 2, 4, 7]
def baseStart_759200 : Nat := 118140960795 + 759200 * 2 ^ 59
def prefixEnd_759200 : Nat := 4983230072969 + 3 ^ 40 * 759200 * 2
def baseEnd_759200 : Nat := 28876630584706285941371

theorem tailTrace_759200 : CollatzResearch.WordTrace tailWord_759200 prefixEnd_759200 28876630584706285941371 := by
  unfold tailWord_759200
  simp only [CollatzResearch.WordTrace]
  refine ⟨13845149424777767941133527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18460199233037023921511369 13845149424777767941133527)
  ·
    refine ⟨20767724137166651911700291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13845149424777767941133527 20767724137166651911700291)
    ·
      refine ⟨31151586205749977867550437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20767724137166651911700291 31151586205749977867550437)
      ·
        refine ⟨5840922413578120850165707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31151586205749977867550437 5840922413578120850165707)
        ·
          refine ⟨8761383620367181275248561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5840922413578120850165707 8761383620367181275248561)
          ·
            refine ⟨6571037715275385956436421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8761383620367181275248561 6571037715275385956436421)
            ·
              refine ⟨1232069571614134866831829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6571037715275385956436421 1232069571614134866831829)
              ·
                refine ⟨28876630584706285941371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1232069571614134866831829 28876630584706285941371)
                ·
                  rfl

theorem cell22_759200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 7].length) (baseStart_759200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759200 prefixEnd_759200 := by exact prefixLift 759200
  have htrace : WordTrace (prefixWord ++ tailWord_759200) baseStart_759200 baseEnd_759200 := by
    simpa [prefixWord, tailWord_759200, baseEnd_759200] using wordTrace_append hprefix tailTrace_759200
  have hstable : (prefixWord ++ tailWord_759200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759200).length < 2 ^ (prefixWord ++ tailWord_759200).sum := by decide
  have hdescent : baseEnd_759200 < baseStart_759200 := by decide
  rcases family_descends (prefixWord ++ tailWord_759200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759208 : List Nat := [2, 1, 6, 1, 3, 1, 1, 2, 1, 4]
def baseStart_759208 : Nat := 118140960795 + 759208 * 2 ^ 59
def prefixEnd_759208 : Nat := 4983230072969 + 3 ^ 40 * 759208 * 2
def baseEnd_759208 : Nat := 259892413825847219272315

theorem tailTrace_759208 : CollatzResearch.WordTrace tailWord_759208 prefixEnd_759208 259892413825847219272315 := by
  unfold tailWord_759208
  simp only [CollatzResearch.WordTrace]
  refine ⟨13845295316763276624279139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18460393755684368832372185 13845295316763276624279139)
  ·
    refine ⟨20767942975144914936418709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13845295316763276624279139 20767942975144914936418709)
    ·
      refine ⟨973497326959917887644627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20767942975144914936418709 973497326959917887644627)
      ·
        refine ⟨1460245990439876831466941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 973497326959917887644627 1460245990439876831466941)
        ·
          refine ⟨547592246414953811800103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1460245990439876831466941 547592246414953811800103)
          ·
            refine ⟨821388369622430717700155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547592246414953811800103 821388369622430717700155)
            ·
              refine ⟨1232082554433646076550233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 821388369622430717700155 1232082554433646076550233)
              ·
                refine ⟨924061915825234557412675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1232082554433646076550233 924061915825234557412675)
                ·
                  refine ⟨1386092873737851836119013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 924061915825234557412675 1386092873737851836119013)
                  ·
                    refine ⟨259892413825847219272315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1386092873737851836119013 259892413825847219272315)
                    ·
                      rfl

theorem cell22_759208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_759208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759208 prefixEnd_759208 := by exact prefixLift 759208
  have htrace : WordTrace (prefixWord ++ tailWord_759208) baseStart_759208 baseEnd_759208 := by
    simpa [prefixWord, tailWord_759208, baseEnd_759208] using wordTrace_append hprefix tailTrace_759208
  have hstable : (prefixWord ++ tailWord_759208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759208).length < 2 ^ (prefixWord ++ tailWord_759208).sum := by decide
  have hdescent : baseEnd_759208 < baseStart_759208 := by decide
  rcases family_descends (prefixWord ++ tailWord_759208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759290 : List Nat := [3, 1, 1, 1, 1, 2, 3, 2, 8]
def baseStart_759290 : Nat := 118140960795 + 759290 * 2 ^ 59
def prefixEnd_759290 : Nat := 4983230072969 + 3 ^ 40 * 759290 * 2
def baseEnd_759290 : Nat := 86640161367208779574021

theorem tailTrace_759290 : CollatzResearch.WordTrace tailWord_759290 prefixEnd_759290 86640161367208779574021 := by
  unfold tailWord_759290
  simp only [CollatzResearch.WordTrace]
  refine ⟨6923395354807370313260831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18462387612819654168695549 6923395354807370313260831)
  ·
    refine ⟨10385093032211055469891247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6923395354807370313260831 10385093032211055469891247)
    ·
      refine ⟨15577639548316583204836871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10385093032211055469891247 15577639548316583204836871)
      ·
        refine ⟨23366459322474874807255307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15577639548316583204836871 23366459322474874807255307)
        ·
          refine ⟨35049688983712312210882961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23366459322474874807255307 35049688983712312210882961)
          ·
            refine ⟨26287266737784234158162221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35049688983712312210882961 26287266737784234158162221)
            ·
              refine ⟨9857725026669087809310833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26287266737784234158162221 9857725026669087809310833)
              ·
                refine ⟨7393293770001815856983125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9857725026669087809310833 7393293770001815856983125)
                ·
                  refine ⟨86640161367208779574021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7393293770001815856983125 86640161367208779574021)
                  ·
                    rfl

theorem cell22_759290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 8].length) (baseStart_759290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759290 prefixEnd_759290 := by exact prefixLift 759290
  have htrace : WordTrace (prefixWord ++ tailWord_759290) baseStart_759290 baseEnd_759290 := by
    simpa [prefixWord, tailWord_759290, baseEnd_759290] using wordTrace_append hprefix tailTrace_759290
  have hstable : (prefixWord ++ tailWord_759290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759290).length < 2 ^ (prefixWord ++ tailWord_759290).sum := by decide
  have hdescent : baseEnd_759290 < baseStart_759290 := by decide
  rcases family_descends (prefixWord ++ tailWord_759290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759352 : List Nat := [2, 1, 2, 1, 4, 4, 8]
def baseStart_759352 : Nat := 118140960795 + 759352 * 2 ^ 59
def prefixEnd_759352 : Nat := 4983230072969 + 3 ^ 40 * 759352 * 2
def baseEnd_759352 : Nat := 9627470665506623839699

theorem tailTrace_759352 : CollatzResearch.WordTrace tailWord_759352 prefixEnd_759352 9627470665506623839699 := by
  unfold tailWord_759352
  simp only [CollatzResearch.WordTrace]
  refine ⟨13847921372502432920900155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18463895163336577227866873 13847921372502432920900155)
  ·
    refine ⟨20771882058753649381350233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13847921372502432920900155 20771882058753649381350233)
    ·
      refine ⟨15578911544065237036012675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20771882058753649381350233 15578911544065237036012675)
      ·
        refine ⟨23368367316097855554019013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15578911544065237036012675 23368367316097855554019013)
        ·
          refine ⟨4381568871768347916378565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23368367316097855554019013 4381568871768347916378565)
          ·
            refine ⟨821544163456565234320981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4381568871768347916378565 821544163456565234320981)
            ·
              refine ⟨9627470665506623839699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 821544163456565234320981 9627470665506623839699)
              ·
                rfl

theorem cell22_759352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 8].length) (baseStart_759352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759352 prefixEnd_759352 := by exact prefixLift 759352
  have htrace : WordTrace (prefixWord ++ tailWord_759352) baseStart_759352 baseEnd_759352 := by
    simpa [prefixWord, tailWord_759352, baseEnd_759352] using wordTrace_append hprefix tailTrace_759352
  have hstable : (prefixWord ++ tailWord_759352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759352).length < 2 ^ (prefixWord ++ tailWord_759352).sum := by decide
  have hdescent : baseEnd_759352 < baseStart_759352 := by decide
  rcases family_descends (prefixWord ++ tailWord_759352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759373 : List Nat := [1, 6, 1, 1, 3, 1, 1, 3, 2, 3]
def baseStart_759373 : Nat := 118140960795 + 759373 * 2 ^ 59
def prefixEnd_759373 : Nat := 4983230072969 + 3 ^ 40 * 759373 * 2
def baseEnd_759373 : Nat := 259948896697841788896809

theorem tailTrace_759373 : CollatzResearch.WordTrace tailWord_759373 prefixEnd_759373 259948896697841788896809 := by
  unfold tailWord_759373
  simp only [CollatzResearch.WordTrace]
  refine ⟨27696608677928786428314773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18464405785285857618876515 27696608677928786428314773)
  ·
    refine ⟨1298278531777911863827255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27696608677928786428314773 1298278531777911863827255)
    ·
      refine ⟨1947417797666867795740883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1298278531777911863827255 1947417797666867795740883)
      ·
        refine ⟨2921126696500301693611325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1947417797666867795740883 2921126696500301693611325)
        ·
          refine ⟨1095422511187613135104247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2921126696500301693611325 1095422511187613135104247)
          ·
            refine ⟨1643133766781419702656371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1095422511187613135104247 1643133766781419702656371)
            ·
              refine ⟨2464700650172129553984557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1643133766781419702656371 2464700650172129553984557)
              ·
                refine ⟨924262743814548582744209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2464700650172129553984557 924262743814548582744209)
                ·
                  refine ⟨693197057860911437058157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 924262743814548582744209 693197057860911437058157)
                  ·
                    refine ⟨259948896697841788896809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 693197057860911437058157 259948896697841788896809)
                    ·
                      rfl

theorem cell22_759373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_759373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759373 prefixEnd_759373 := by exact prefixLift 759373
  have htrace : WordTrace (prefixWord ++ tailWord_759373) baseStart_759373 baseEnd_759373 := by
    simpa [prefixWord, tailWord_759373, baseEnd_759373] using wordTrace_append hprefix tailTrace_759373
  have hstable : (prefixWord ++ tailWord_759373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759373).length < 2 ^ (prefixWord ++ tailWord_759373).sum := by decide
  have hdescent : baseEnd_759373 < baseStart_759373 := by decide
  rcases family_descends (prefixWord ++ tailWord_759373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759461 : List Nat := [1, 3, 1, 2, 1, 2, 6, 1, 1, 4]
def baseStart_759461 : Nat := 118140960795 + 759461 * 2 ^ 59
def prefixEnd_759461 : Nat := 4983230072969 + 3 ^ 40 * 759461 * 2
def baseEnd_759461 : Nat := 259979020896238892696539

theorem tailTrace_759461 : CollatzResearch.WordTrace tailWord_759461 prefixEnd_759461 259979020896238892696539 := by
  unfold tailWord_759461
  simp only [CollatzResearch.WordTrace]
  refine ⟨27699818301609977457518237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18466545534406651638345491 27699818301609977457518237)
  ·
    refine ⟨10387431863103741546569339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27699818301609977457518237 10387431863103741546569339)
    ·
      refine ⟨15581147794655612319854009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10387431863103741546569339 15581147794655612319854009)
      ·
        refine ⟨11685860845991709239890507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15581147794655612319854009 11685860845991709239890507)
        ·
          refine ⟨17528791268987563859835761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11685860845991709239890507 17528791268987563859835761)
          ·
            refine ⟨13146593451740672894876821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17528791268987563859835761 13146593451740672894876821)
            ·
              refine ⟨616246568050344041947351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13146593451740672894876821 616246568050344041947351)
              ·
                refine ⟨924369852075516062921027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 616246568050344041947351 924369852075516062921027)
                ·
                  refine ⟨1386554778113274094381541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 924369852075516062921027 1386554778113274094381541)
                  ·
                    refine ⟨259979020896238892696539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1386554778113274094381541 259979020896238892696539)
                    ·
                      rfl

theorem cell22_759461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 1, 4].length) (baseStart_759461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759461 prefixEnd_759461 := by exact prefixLift 759461
  have htrace : WordTrace (prefixWord ++ tailWord_759461) baseStart_759461 baseEnd_759461 := by
    simpa [prefixWord, tailWord_759461, baseEnd_759461] using wordTrace_append hprefix tailTrace_759461
  have hstable : (prefixWord ++ tailWord_759461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759461).length < 2 ^ (prefixWord ++ tailWord_759461).sum := by decide
  have hdescent : baseEnd_759461 < baseStart_759461 := by decide
  rcases family_descends (prefixWord ++ tailWord_759461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759487 : List Nat := [1, 1, 2, 2, 2, 3, 2, 9]
def baseStart_759487 : Nat := 118140960795 + 759487 * 2 ^ 59
def prefixEnd_759487 : Nat := 4983230072969 + 3 ^ 40 * 759487 * 2
def baseEnd_759487 : Nat := 28887546803064832394051

theorem tailTrace_759487 : CollatzResearch.WordTrace tailWord_759487 prefixEnd_759487 28887546803064832394051 := by
  unfold tailWord_759487
  simp only [CollatzResearch.WordTrace]
  refine ⟨27700766599515783897964715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18467177733010522598643143 27700766599515783897964715)
  ·
    refine ⟨41551149899273675846947073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27700766599515783897964715 41551149899273675846947073)
    ·
      refine ⟨31163362424455256885210305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41551149899273675846947073 31163362424455256885210305)
      ·
        refine ⟨23372521818341442663907729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31163362424455256885210305 23372521818341442663907729)
        ·
          refine ⟨17529391363756081997930797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23372521818341442663907729 17529391363756081997930797)
          ·
            refine ⟨6573521761408530749224049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17529391363756081997930797 6573521761408530749224049)
            ·
              refine ⟨4930141321056398061918037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6573521761408530749224049 4930141321056398061918037)
              ·
                refine ⟨28887546803064832394051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4930141321056398061918037 28887546803064832394051)
                ·
                  rfl

theorem cell22_759487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 9].length) (baseStart_759487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759487 prefixEnd_759487 := by exact prefixLift 759487
  have htrace : WordTrace (prefixWord ++ tailWord_759487) baseStart_759487 baseEnd_759487 := by
    simpa [prefixWord, tailWord_759487, baseEnd_759487] using wordTrace_append hprefix tailTrace_759487
  have hstable : (prefixWord ++ tailWord_759487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759487).length < 2 ^ (prefixWord ++ tailWord_759487).sum := by decide
  have hdescent : baseEnd_759487 < baseStart_759487 := by decide
  rcases family_descends (prefixWord ++ tailWord_759487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759521 : List Nat := [1, 2, 3, 1, 6, 1, 8]
def baseStart_759521 : Nat := 118140960795 + 759521 * 2 ^ 59
def prefixEnd_759521 : Nat := 4983230072969 + 3 ^ 40 * 759521 * 2
def baseEnd_759521 : Nat := 9629613337867360599865

theorem tailTrace_759521 : CollatzResearch.WordTrace tailWord_759521 prefixEnd_759521 9629613337867360599865 := by
  unfold tailWord_759521
  simp only [CollatzResearch.WordTrace]
  refine ⟨27702006681392607704702417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18468004454261738469801611 27702006681392607704702417)
  ·
    refine ⟨20776505011044455778526813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27702006681392607704702417 20776505011044455778526813)
    ·
      refine ⟨7791189379141670916947555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20776505011044455778526813 7791189379141670916947555)
      ·
        refine ⟨11686784068712506375421333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7791189379141670916947555 11686784068712506375421333)
        ·
          refine ⟨547818003220898736347875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11686784068712506375421333 547818003220898736347875)
          ·
            refine ⟨821727004831348104521813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547818003220898736347875 821727004831348104521813)
            ·
              refine ⟨9629613337867360599865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 821727004831348104521813 9629613337867360599865)
              ·
                rfl

theorem cell22_759521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 8].length) (baseStart_759521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759521 prefixEnd_759521 := by exact prefixLift 759521
  have htrace : WordTrace (prefixWord ++ tailWord_759521) baseStart_759521 baseEnd_759521 := by
    simpa [prefixWord, tailWord_759521, baseEnd_759521] using wordTrace_append hprefix tailTrace_759521
  have hstable : (prefixWord ++ tailWord_759521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759521).length < 2 ^ (prefixWord ++ tailWord_759521).sum := by decide
  have hdescent : baseEnd_759521 < baseStart_759521 := by decide
  rcases family_descends (prefixWord ++ tailWord_759521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759534 : List Nat := [4, 1, 2, 1, 1, 2, 2, 1, 2, 6]
def baseStart_759534 : Nat := 118140960795 + 759534 * 2 ^ 59
def prefixEnd_759534 : Nat := 4983230072969 + 3 ^ 40 * 759534 * 2
def baseEnd_759534 : Nat := 260004010288091035621315

theorem tailTrace_759534 : CollatzResearch.WordTrace tailWord_759534 prefixEnd_759534 260004010288091035621315 := by
  unfold tailWord_759534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3462810103793188865615707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18468320553563673949950437 3462810103793188865615707)
  ·
    refine ⟨5194215155689783298423561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3462810103793188865615707 5194215155689783298423561)
    ·
      refine ⟨3895661366767337473817671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5194215155689783298423561 3895661366767337473817671)
      ·
        refine ⟨5843492050151006210726507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3895661366767337473817671 5843492050151006210726507)
        ·
          refine ⟨8765238075226509316089761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5843492050151006210726507 8765238075226509316089761)
          ·
            refine ⟨6573928556419881987067321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8765238075226509316089761 6573928556419881987067321)
            ·
              refine ⟨4930446417314911490300491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6573928556419881987067321 4930446417314911490300491)
              ·
                refine ⟨7395669625972367235450737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4930446417314911490300491 7395669625972367235450737)
                ·
                  refine ⟨5546752219479275426588053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7395669625972367235450737 5546752219479275426588053)
                  ·
                    refine ⟨260004010288091035621315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5546752219479275426588053 260004010288091035621315)
                    ·
                      rfl

theorem cell22_759534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_759534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759534 prefixEnd_759534 := by exact prefixLift 759534
  have htrace : WordTrace (prefixWord ++ tailWord_759534) baseStart_759534 baseEnd_759534 := by
    simpa [prefixWord, tailWord_759534, baseEnd_759534] using wordTrace_append hprefix tailTrace_759534
  have hstable : (prefixWord ++ tailWord_759534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759534).length < 2 ^ (prefixWord ++ tailWord_759534).sum := by decide
  have hdescent : baseEnd_759534 < baseStart_759534 := by decide
  rcases family_descends (prefixWord ++ tailWord_759534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759598 : List Nat := [4, 1, 3, 2, 2, 1, 1, 1, 2, 5]
def baseStart_759598 : Nat := 118140960795 + 759598 * 2 ^ 59
def prefixEnd_759598 : Nat := 4983230072969 + 3 ^ 40 * 759598 * 2
def baseEnd_759598 : Nat := 260025918796016202021119

theorem tailTrace_759598 : CollatzResearch.WordTrace tailWord_759598 prefixEnd_759598 260025918796016202021119 := by
  unfold tailWord_759598
  simp only [CollatzResearch.WordTrace]
  refine ⟨3463101887764206231906931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18469876734742433236836965 3463101887764206231906931)
  ·
    refine ⟨5194652831646309347860397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3463101887764206231906931 5194652831646309347860397)
    ·
      refine ⟨1947994811867366005447649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5194652831646309347860397 1947994811867366005447649)
      ·
        refine ⟨1460996108900524504085737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1947994811867366005447649 1460996108900524504085737)
        ·
          refine ⟨1095747081675393378064303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1460996108900524504085737 1095747081675393378064303)
          ·
            refine ⟨1643620622513090067096455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1095747081675393378064303 1643620622513090067096455)
            ·
              refine ⟨2465430933769635100644683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1643620622513090067096455 2465430933769635100644683)
              ·
                refine ⟨3698146400654452650967025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2465430933769635100644683 3698146400654452650967025)
                ·
                  refine ⟨2773609800490839488225269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3698146400654452650967025 2773609800490839488225269)
                  ·
                    refine ⟨260025918796016202021119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2773609800490839488225269 260025918796016202021119)
                    ·
                      rfl

theorem cell22_759598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_759598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759598 prefixEnd_759598 := by exact prefixLift 759598
  have htrace : WordTrace (prefixWord ++ tailWord_759598) baseStart_759598 baseEnd_759598 := by
    simpa [prefixWord, tailWord_759598, baseEnd_759598] using wordTrace_append hprefix tailTrace_759598
  have hstable : (prefixWord ++ tailWord_759598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759598).length < 2 ^ (prefixWord ++ tailWord_759598).sum := by decide
  have hdescent : baseEnd_759598 < baseStart_759598 := by decide
  rcases family_descends (prefixWord ++ tailWord_759598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759626 : List Nat := [3, 1, 2, 1, 1, 1, 4, 2, 4, 3]
def baseStart_759626 : Nat := 118140960795 + 759626 * 2 ^ 59
def prefixEnd_759626 : Nat := 4983230072969 + 3 ^ 40 * 759626 * 2
def baseEnd_759626 : Nat := 260035503768233462321033

theorem tailTrace_759626 : CollatzResearch.WordTrace tailWord_759626 prefixEnd_759626 260035503768233462321033 := by
  unfold tailWord_759626
  simp only [CollatzResearch.WordTrace]
  refine ⟨6926459086503052659318683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18470557564008140424849821 6926459086503052659318683)
  ·
    refine ⟨10389688629754578988978025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6926459086503052659318683 10389688629754578988978025)
    ·
      refine ⟨7792266472315934241733519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10389688629754578988978025 7792266472315934241733519)
      ·
        refine ⟨11688399708473901362600279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7792266472315934241733519 11688399708473901362600279)
        ·
          refine ⟨17532599562710852043900419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11688399708473901362600279 17532599562710852043900419)
          ·
            refine ⟨26298899344066278065850629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17532599562710852043900419 26298899344066278065850629)
            ·
              refine ⟨4931043627012427137346993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26298899344066278065850629 4931043627012427137346993)
              ·
                refine ⟨3698282720259320353010245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4931043627012427137346993 3698282720259320353010245)
                ·
                  refine ⟨693428010048622566189421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3698282720259320353010245 693428010048622566189421)
                  ·
                    refine ⟨260035503768233462321033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 693428010048622566189421 260035503768233462321033)
                    ·
                      rfl

theorem cell22_759626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_759626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759626 prefixEnd_759626 := by exact prefixLift 759626
  have htrace : WordTrace (prefixWord ++ tailWord_759626) baseStart_759626 baseEnd_759626 := by
    simpa [prefixWord, tailWord_759626, baseEnd_759626] using wordTrace_append hprefix tailTrace_759626
  have hstable : (prefixWord ++ tailWord_759626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759626).length < 2 ^ (prefixWord ++ tailWord_759626).sum := by decide
  have hdescent : baseEnd_759626 < baseStart_759626 := by decide
  rcases family_descends (prefixWord ++ tailWord_759626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759660 : List Nat := [2, 2, 1, 1, 4, 3, 3, 1, 2, 3]
def baseStart_759660 : Nat := 118140960795 + 759660 * 2 ^ 59
def prefixEnd_759660 : Nat := 4983230072969 + 3 ^ 40 * 759660 * 2
def baseEnd_759660 : Nat := 260047142663068706970929

theorem tailTrace_759660 : CollatzResearch.WordTrace tailWord_759660 prefixEnd_759660 260047142663068706970929 := by
  unfold tailWord_759660
  simp only [CollatzResearch.WordTrace]
  refine ⟨13853538213944517222006217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18471384285259356296008289 13853538213944517222006217)
  ·
    refine ⟨10390153660458387916504663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13853538213944517222006217 10390153660458387916504663)
    ·
      refine ⟨15585230490687581874756995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10390153660458387916504663 15585230490687581874756995)
      ·
        refine ⟨23377845736031372812135493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15585230490687581874756995 23377845736031372812135493)
        ·
          refine ⟨4383346075505882402275405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23377845736031372812135493 4383346075505882402275405)
          ·
            refine ⟨1643754778314705900853277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4383346075505882402275405 1643754778314705900853277)
            ·
              refine ⟨616408041868014712819979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1643754778314705900853277 616408041868014712819979)
              ·
                refine ⟨924612062802022069229969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 616408041868014712819979 924612062802022069229969)
                ·
                  refine ⟨693459047101516551922477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 924612062802022069229969 693459047101516551922477)
                  ·
                    refine ⟨260047142663068706970929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 693459047101516551922477 260047142663068706970929)
                    ·
                      rfl

theorem cell22_759660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 3].length) (baseStart_759660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759660 prefixEnd_759660 := by exact prefixLift 759660
  have htrace : WordTrace (prefixWord ++ tailWord_759660) baseStart_759660 baseEnd_759660 := by
    simpa [prefixWord, tailWord_759660, baseEnd_759660] using wordTrace_append hprefix tailTrace_759660
  have hstable : (prefixWord ++ tailWord_759660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759660).length < 2 ^ (prefixWord ++ tailWord_759660).sum := by decide
  have hdescent : baseEnd_759660 < baseStart_759660 := by decide
  rcases family_descends (prefixWord ++ tailWord_759660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759701 : List Nat := [1, 3, 2, 1, 1, 3, 2, 4, 5]
def baseStart_759701 : Nat := 118140960795 + 759701 * 2 ^ 59
def prefixEnd_759701 : Nat := 4983230072969 + 3 ^ 40 * 759701 * 2
def baseEnd_759701 : Nat := 86687059266986088898601

theorem tailTrace_759701 : CollatzResearch.WordTrace tailWord_759701 prefixEnd_759701 86687059266986088898601 := by
  unfold tailWord_759701
  simp only [CollatzResearch.WordTrace]
  refine ⟨27708571820740498446254957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18472381213826998964169971 27708571820740498446254957)
  ·
    refine ⟨10390714432777686917345609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27708571820740498446254957 10390714432777686917345609)
    ·
      refine ⟨7793035824583265188009207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10390714432777686917345609 7793035824583265188009207)
      ·
        refine ⟨11689553736874897782013811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7793035824583265188009207 11689553736874897782013811)
        ·
          refine ⟨17534330605312346673020717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11689553736874897782013811 17534330605312346673020717)
          ·
            refine ⟨6575373976992130002382769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17534330605312346673020717 6575373976992130002382769)
            ·
              refine ⟨4931530482744097501787077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6575373976992130002382769 4931530482744097501787077)
              ·
                refine ⟨924661965514518281585077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4931530482744097501787077 924661965514518281585077)
                ·
                  refine ⟨86687059266986088898601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 924661965514518281585077 86687059266986088898601)
                  ·
                    rfl

theorem cell22_759701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 5].length) (baseStart_759701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759701 prefixEnd_759701 := by exact prefixLift 759701
  have htrace : WordTrace (prefixWord ++ tailWord_759701) baseStart_759701 baseEnd_759701 := by
    simpa [prefixWord, tailWord_759701, baseEnd_759701] using wordTrace_append hprefix tailTrace_759701
  have hstable : (prefixWord ++ tailWord_759701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759701).length < 2 ^ (prefixWord ++ tailWord_759701).sum := by decide
  have hdescent : baseEnd_759701 < baseStart_759701 := by decide
  rcases family_descends (prefixWord ++ tailWord_759701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759731 : List Nat := [1, 1, 1, 2, 3, 1, 5, 1, 3, 4]
def baseStart_759731 : Nat := 118140960795 + 759731 * 2 ^ 59
def prefixEnd_759731 : Nat := 4983230072969 + 3 ^ 40 * 759731 * 2
def baseEnd_759731 : Nat := 260071447414048188445711

theorem tailTrace_759731 : CollatzResearch.WordTrace tailWord_759731 prefixEnd_759731 260071447414048188445711 := by
  unfold tailWord_759731
  simp only [CollatzResearch.WordTrace]
  refine ⟨27709666010631813569847047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18473110673754542379898031 27709666010631813569847047)
  ·
    refine ⟨41564499015947720354770571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27709666010631813569847047 41564499015947720354770571)
    ·
      refine ⟨62346748523921580532155857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41564499015947720354770571 62346748523921580532155857)
      ·
        refine ⟨46760061392941185399116893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62346748523921580532155857 46760061392941185399116893)
        ·
          refine ⟨17535023022352944524668835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46760061392941185399116893 17535023022352944524668835)
          ·
            refine ⟨26302534533529416787003253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17535023022352944524668835 26302534533529416787003253)
            ·
              refine ⟨2465862612518382823781555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26302534533529416787003253 2465862612518382823781555)
              ·
                refine ⟨3698793918777574235672333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2465862612518382823781555 3698793918777574235672333)
                ·
                  refine ⟨1387047719541590338377125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3698793918777574235672333 1387047719541590338377125)
                  ·
                    refine ⟨260071447414048188445711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1387047719541590338377125 260071447414048188445711)
                    ·
                      rfl

theorem cell22_759731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 4].length) (baseStart_759731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759731 prefixEnd_759731 := by exact prefixLift 759731
  have htrace : WordTrace (prefixWord ++ tailWord_759731) baseStart_759731 baseEnd_759731 := by
    simpa [prefixWord, tailWord_759731, baseEnd_759731] using wordTrace_append hprefix tailTrace_759731
  have hstable : (prefixWord ++ tailWord_759731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759731).length < 2 ^ (prefixWord ++ tailWord_759731).sum := by decide
  have hdescent : baseEnd_759731 < baseStart_759731 := by decide
  rcases family_descends (prefixWord ++ tailWord_759731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759776 : List Nat := [2, 1, 1, 3, 1, 1, 1, 4, 4, 4]
def baseStart_759776 : Nat := 118140960795 + 759776 * 2 ^ 59
def prefixEnd_759776 : Nat := 4983230072969 + 3 ^ 40 * 759776 * 2
def baseEnd_759776 : Nat := 260086851833683071070573

theorem tailTrace_759776 : CollatzResearch.WordTrace tailWord_759776 prefixEnd_759776 260086851833683071070573 := by
  unfold tailWord_759776
  simp only [CollatzResearch.WordTrace]
  refine ⟨13855653647734393127617591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18474204863645857503490121 13855653647734393127617591)
  ·
    refine ⟨20783480471601589691426387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13855653647734393127617591 20783480471601589691426387)
    ·
      refine ⟨31175220707402384537139581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20783480471601589691426387 31175220707402384537139581)
      ·
        refine ⟨11690707765275894201427343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31175220707402384537139581 11690707765275894201427343)
        ·
          refine ⟨17536061647913841302141015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11690707765275894201427343 17536061647913841302141015)
          ·
            refine ⟨26304092471870761953211523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17536061647913841302141015 26304092471870761953211523)
            ·
              refine ⟨39456138707806142929817285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26304092471870761953211523 39456138707806142929817285)
              ·
                refine ⟨7398026007713651799340741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39456138707806142929817285 7398026007713651799340741)
                ·
                  refine ⟨1387129876446309712376389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7398026007713651799340741 1387129876446309712376389)
                  ·
                    refine ⟨260086851833683071070573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1387129876446309712376389 260086851833683071070573)
                    ·
                      rfl

theorem cell22_759776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 4, 4].length) (baseStart_759776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759776 prefixEnd_759776 := by exact prefixLift 759776
  have htrace : WordTrace (prefixWord ++ tailWord_759776) baseStart_759776 baseEnd_759776 := by
    simpa [prefixWord, tailWord_759776, baseEnd_759776] using wordTrace_append hprefix tailTrace_759776
  have hstable : (prefixWord ++ tailWord_759776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759776).length < 2 ^ (prefixWord ++ tailWord_759776).sum := by decide
  have hdescent : baseEnd_759776 < baseStart_759776 := by decide
  rcases family_descends (prefixWord ++ tailWord_759776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759793 : List Nat := [1, 2, 2, 2, 5, 1, 1, 1, 1, 6]
def baseStart_759793 : Nat := 118140960795 + 759793 * 2 ^ 59
def prefixEnd_759793 : Nat := 4983230072969 + 3 ^ 40 * 759793 * 2
def baseEnd_759793 : Nat := 260092671281100693395521

theorem tailTrace_759793 : CollatzResearch.WordTrace tailWord_759793 prefixEnd_759793 260092671281100693395521 := by
  unfold tailWord_759793
  simp only [CollatzResearch.WordTrace]
  refine ⟨27711927336407198158604033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18474618224271465439069355 27711927336407198158604033)
  ·
    refine ⟨20783945502305398618953025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27711927336407198158604033 20783945502305398618953025)
    ·
      refine ⟨15587959126729048964214769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20783945502305398618953025 15587959126729048964214769)
      ·
        refine ⟨11690969345046786723161077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15587959126729048964214769 11690969345046786723161077)
        ·
          refine ⟨1096028376098136255296351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11690969345046786723161077 1096028376098136255296351)
          ·
            refine ⟨1644042564147204382944527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1096028376098136255296351 1644042564147204382944527)
            ·
              refine ⟨2466063846220806574416791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1644042564147204382944527 2466063846220806574416791)
              ·
                refine ⟨3699095769331209861625187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2466063846220806574416791 3699095769331209861625187)
                ·
                  refine ⟨5548643653996814792437781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3699095769331209861625187 5548643653996814792437781)
                  ·
                    refine ⟨260092671281100693395521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5548643653996814792437781 260092671281100693395521)
                    ·
                      rfl

theorem cell22_759793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 6].length) (baseStart_759793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759793 prefixEnd_759793 := by exact prefixLift 759793
  have htrace : WordTrace (prefixWord ++ tailWord_759793) baseStart_759793 baseEnd_759793 := by
    simpa [prefixWord, tailWord_759793, baseEnd_759793] using wordTrace_append hprefix tailTrace_759793
  have hstable : (prefixWord ++ tailWord_759793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759793).length < 2 ^ (prefixWord ++ tailWord_759793).sum := by decide
  have hdescent : baseEnd_759793 < baseStart_759793 := by decide
  rcases family_descends (prefixWord ++ tailWord_759793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759812 : List Nat := [2, 3, 2, 4, 1, 1, 1, 1, 4, 3]
def baseStart_759812 : Nat := 118140960795 + 759812 * 2 ^ 59
def prefixEnd_759812 : Nat := 4983230072969 + 3 ^ 40 * 759812 * 2
def baseEnd_759812 : Nat := 260099175369390977170463

theorem tailTrace_759812 : CollatzResearch.WordTrace tailWord_759812 prefixEnd_759812 260099175369390977170463 := by
  unfold tailWord_759812
  simp only [CollatzResearch.WordTrace]
  refine ⟨13856310161669182201772845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18475080215558909602363793 13856310161669182201772845)
  ·
    refine ⟨5196116310625943325664817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13856310161669182201772845 5196116310625943325664817)
    ·
      refine ⟨3897087232969457494248613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5196116310625943325664817 3897087232969457494248613)
      ·
        refine ⟨730703856181773280171615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3897087232969457494248613 730703856181773280171615)
        ·
          refine ⟨1096055784272659920257423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 730703856181773280171615 1096055784272659920257423)
          ·
            refine ⟨1644083676408989880386135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1096055784272659920257423 1644083676408989880386135)
            ·
              refine ⟨2466125514613484820579203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1644083676408989880386135 2466125514613484820579203)
              ·
                refine ⟨3699188271920227230868805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2466125514613484820579203 3699188271920227230868805)
                ·
                  refine ⟨693597800985042605787901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3699188271920227230868805 693597800985042605787901)
                  ·
                    refine ⟨260099175369390977170463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 693597800985042605787901 260099175369390977170463)
                    ·
                      rfl

theorem cell22_759812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_759812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759812 prefixEnd_759812 := by exact prefixLift 759812
  have htrace : WordTrace (prefixWord ++ tailWord_759812) baseStart_759812 baseEnd_759812 := by
    simpa [prefixWord, tailWord_759812, baseEnd_759812] using wordTrace_append hprefix tailTrace_759812
  have hstable : (prefixWord ++ tailWord_759812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759812).length < 2 ^ (prefixWord ++ tailWord_759812).sum := by decide
  have hdescent : baseEnd_759812 < baseStart_759812 := by decide
  rcases family_descends (prefixWord ++ tailWord_759812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759851 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 4, 5]
def baseStart_759851 : Nat := 118140960795 + 759851 * 2 ^ 59
def prefixEnd_759851 : Nat := 4983230072969 + 3 ^ 40 * 759851 * 2
def baseEnd_759851 : Nat := 260112525866407875445343

theorem tailTrace_759851 : CollatzResearch.WordTrace tailWord_759851 prefixEnd_759851 260112525866407875445343 := by
  unfold tailWord_759851
  simp only [CollatzResearch.WordTrace]
  refine ⟨27714042770197074064215407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18476028513464716042810271 27714042770197074064215407)
  ·
    refine ⟨41571064155295611096323111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27714042770197074064215407 41571064155295611096323111)
    ·
      refine ⟨62356596232943416644484667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41571064155295611096323111 62356596232943416644484667)
      ·
        refine ⟨93534894349415124966727001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62356596232943416644484667 93534894349415124966727001)
        ·
          refine ⟨70151170762061343725045251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93534894349415124966727001 70151170762061343725045251)
          ·
            refine ⟨105226756143092015587567877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70151170762061343725045251 105226756143092015587567877)
            ·
              refine ⟨19730016776829752922668977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105226756143092015587567877 19730016776829752922668977)
              ·
                refine ⟨14797512582622314692001733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19730016776829752922668977 14797512582622314692001733)
                ·
                  refine ⟨2774533609241684004750325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14797512582622314692001733 2774533609241684004750325)
                  ·
                    refine ⟨260112525866407875445343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2774533609241684004750325 260112525866407875445343)
                    ·
                      rfl

theorem cell22_759851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 5].length) (baseStart_759851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759851 prefixEnd_759851 := by exact prefixLift 759851
  have htrace : WordTrace (prefixWord ++ tailWord_759851) baseStart_759851 baseEnd_759851 := by
    simpa [prefixWord, tailWord_759851, baseEnd_759851] using wordTrace_append hprefix tailTrace_759851
  have hstable : (prefixWord ++ tailWord_759851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759851).length < 2 ^ (prefixWord ++ tailWord_759851).sum := by decide
  have hdescent : baseEnd_759851 < baseStart_759851 := by decide
  rcases family_descends (prefixWord ++ tailWord_759851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759857 : List Nat := [1, 2, 2, 3, 1, 3, 3, 3, 1, 3]
def baseStart_759857 : Nat := 118140960795 + 759857 * 2 ^ 59
def prefixEnd_759857 : Nat := 4983230072969 + 3 ^ 40 * 759857 * 2
def baseEnd_759857 : Nat := 260114579789025859795325

theorem tailTrace_759857 : CollatzResearch.WordTrace tailWord_759857 prefixEnd_759857 260114579789025859795325 := by
  unfold tailWord_759857
  simp only [CollatzResearch.WordTrace]
  refine ⟨27714261608175337088933825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18476174405450224725955883 27714261608175337088933825)
  ·
    refine ⟨20785696206131502816700369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27714261608175337088933825 20785696206131502816700369)
    ·
      refine ⟨15589272154598627112525277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20785696206131502816700369 15589272154598627112525277)
      ·
        refine ⟨5845977057974485167196979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15589272154598627112525277 5845977057974485167196979)
        ·
          refine ⟨8768965586961727750795469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5845977057974485167196979 8768965586961727750795469)
          ·
            refine ⟨3288362095110647906548301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8768965586961727750795469 3288362095110647906548301)
            ·
              refine ⟨1233135785666492964955613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3288362095110647906548301 1233135785666492964955613)
              ·
                refine ⟨462425919624934861858355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1233135785666492964955613 462425919624934861858355)
                ·
                  refine ⟨693638879437402292787533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 462425919624934861858355 693638879437402292787533)
                  ·
                    refine ⟨260114579789025859795325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 693638879437402292787533 260114579789025859795325)
                    ·
                      rfl

theorem cell22_759857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 3, 1, 3].length) (baseStart_759857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759857 prefixEnd_759857 := by exact prefixLift 759857
  have htrace : WordTrace (prefixWord ++ tailWord_759857) baseStart_759857 baseEnd_759857 := by
    simpa [prefixWord, tailWord_759857, baseEnd_759857] using wordTrace_append hprefix tailTrace_759857
  have hstable : (prefixWord ++ tailWord_759857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759857).length < 2 ^ (prefixWord ++ tailWord_759857).sum := by decide
  have hdescent : baseEnd_759857 < baseStart_759857 := by decide
  rcases family_descends (prefixWord ++ tailWord_759857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759900 : List Nat := [2, 2, 4, 1, 1, 3, 1, 1, 3, 4]
def baseStart_759900 : Nat := 118140960795 + 759900 * 2 ^ 59
def prefixEnd_759900 : Nat := 4983230072969 + 3 ^ 40 * 759900 * 2
def baseEnd_759900 : Nat := 260129299567788080970193

theorem tailTrace_759900 : CollatzResearch.WordTrace tailWord_759900 prefixEnd_759900 260129299567788080970193 := by
  unfold tailWord_759900
  simp only [CollatzResearch.WordTrace]
  refine ⟨13857914973509777716374577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18477219964679703621832769 13857914973509777716374577)
  ·
    refine ⟨10393436230132333287280933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13857914973509777716374577 10393436230132333287280933)
    ·
      refine ⟨1948769293149812491365175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10393436230132333287280933 1948769293149812491365175)
      ·
        refine ⟨2923153939724718737047763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1948769293149812491365175 2923153939724718737047763)
        ·
          refine ⟨4384730909587078105571645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2923153939724718737047763 4384730909587078105571645)
          ·
            refine ⟨1644274091095154289589367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4384730909587078105571645 1644274091095154289589367)
            ·
              refine ⟨2466411136642731434384051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1644274091095154289589367 2466411136642731434384051)
              ·
                refine ⟨3699616704964097151576077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2466411136642731434384051 3699616704964097151576077)
                ·
                  refine ⟨1387356264361536431841029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3699616704964097151576077 1387356264361536431841029)
                  ·
                    refine ⟨260129299567788080970193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1387356264361536431841029 260129299567788080970193)
                    ·
                      rfl

theorem cell22_759900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_759900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759900 prefixEnd_759900 := by exact prefixLift 759900
  have htrace : WordTrace (prefixWord ++ tailWord_759900) baseStart_759900 baseEnd_759900 := by
    simpa [prefixWord, tailWord_759900, baseEnd_759900] using wordTrace_append hprefix tailTrace_759900
  have hstable : (prefixWord ++ tailWord_759900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759900).length < 2 ^ (prefixWord ++ tailWord_759900).sum := by decide
  have hdescent : baseEnd_759900 < baseStart_759900 := by decide
  rcases family_descends (prefixWord ++ tailWord_759900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759913 : List Nat := [1, 2, 1, 1, 1, 5, 3, 2, 1, 5]
def baseStart_759913 : Nat := 118140960795 + 759913 * 2 ^ 59
def prefixEnd_759913 : Nat := 4983230072969 + 3 ^ 40 * 759913 * 2
def baseEnd_759913 : Nat := 260133749733460380395153

theorem tailTrace_759913 : CollatzResearch.WordTrace tailWord_759913 prefixEnd_759913 260133749733460380395153 := by
  unfold tailWord_759913
  simp only [CollatzResearch.WordTrace]
  refine ⟨27716304095972458652972393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18477536063981639101981595 27716304095972458652972393)
  ·
    refine ⟨20787228071979343989729295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27716304095972458652972393 20787228071979343989729295)
    ·
      refine ⟨31180842107969015984593943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20787228071979343989729295 31180842107969015984593943)
      ·
        refine ⟨46771263161953523976890915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31180842107969015984593943 46771263161953523976890915)
        ·
          refine ⟨70156894742930285965336373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46771263161953523976890915 70156894742930285965336373)
          ·
            refine ⟨6577208882149714309250285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70156894742930285965336373 6577208882149714309250285)
            ·
              refine ⟨2466453330806142865968857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6577208882149714309250285 2466453330806142865968857)
              ·
                refine ⟨1849839998104607149476643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2466453330806142865968857 1849839998104607149476643)
                ·
                  refine ⟨2774759997156910724214965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1849839998104607149476643 2774759997156910724214965)
                  ·
                    refine ⟨260133749733460380395153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2774759997156910724214965 260133749733460380395153)
                    ·
                      rfl

theorem cell22_759913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 5].length) (baseStart_759913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759913 prefixEnd_759913 := by exact prefixLift 759913
  have htrace : WordTrace (prefixWord ++ tailWord_759913) baseStart_759913 baseEnd_759913 := by
    simpa [prefixWord, tailWord_759913, baseEnd_759913] using wordTrace_append hprefix tailTrace_759913
  have hstable : (prefixWord ++ tailWord_759913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759913).length < 2 ^ (prefixWord ++ tailWord_759913).sum := by decide
  have hdescent : baseEnd_759913 < baseStart_759913 := by decide
  rcases family_descends (prefixWord ++ tailWord_759913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759917 : List Nat := [1, 5, 1, 1, 2, 1, 5, 1, 1, 4]
def baseStart_759917 : Nat := 118140960795 + 759917 * 2 ^ 59
def prefixEnd_759917 : Nat := 4983230072969 + 3 ^ 40 * 759917 * 2
def baseEnd_759917 : Nat := 260135119015205703295141

theorem tailTrace_759917 : CollatzResearch.WordTrace tailWord_759917 prefixEnd_759917 260135119015205703295141 := by
  unfold tailWord_759917
  simp only [CollatzResearch.WordTrace]
  refine ⟨27716449987957967336118005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18477633325305311557412003 27716449987957967336118005)
  ·
    refine ⟨2598417186371059437761063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27716449987957967336118005 2598417186371059437761063)
    ·
      refine ⟨3897625779556589156641595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2598417186371059437761063 3897625779556589156641595)
      ·
        refine ⟨5846438669334883734962393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3897625779556589156641595 5846438669334883734962393)
        ·
          refine ⟨4384829002001162801221795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5846438669334883734962393 4384829002001162801221795)
          ·
            refine ⟨6577243503001744201832693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4384829002001162801221795 6577243503001744201832693)
            ·
              refine ⟨616616578406413518921815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6577243503001744201832693 616616578406413518921815)
              ·
                refine ⟨924924867609620278382723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 616616578406413518921815 924924867609620278382723)
                ·
                  refine ⟨1387387301414430417574085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 924924867609620278382723 1387387301414430417574085)
                  ·
                    refine ⟨260135119015205703295141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1387387301414430417574085 260135119015205703295141)
                    ·
                      rfl

theorem cell22_759917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_759917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759917 prefixEnd_759917 := by exact prefixLift 759917
  have htrace : WordTrace (prefixWord ++ tailWord_759917) baseStart_759917 baseEnd_759917 := by
    simpa [prefixWord, tailWord_759917, baseEnd_759917] using wordTrace_append hprefix tailTrace_759917
  have hstable : (prefixWord ++ tailWord_759917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759917).length < 2 ^ (prefixWord ++ tailWord_759917).sum := by decide
  have hdescent : baseEnd_759917 < baseStart_759917 := by decide
  rcases family_descends (prefixWord ++ tailWord_759917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759932 : List Nat := [2, 2, 2, 1, 1, 4, 4, 2, 4]
def baseStart_759932 : Nat := 118140960795 + 759932 * 2 ^ 59
def prefixEnd_759932 : Nat := 4983230072969 + 3 ^ 40 * 759932 * 2
def baseEnd_759932 : Nat := 86713417940583554723365

theorem tailTrace_759932 : CollatzResearch.WordTrace tailWord_759932 prefixEnd_759932 86713417940583554723365 := by
  unfold tailWord_759932
  simp only [CollatzResearch.WordTrace]
  refine ⟨13858498541451812448957025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18477998055269083265276033 13858498541451812448957025)
  ·
    refine ⟨10393873906088859336717769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13858498541451812448957025 10393873906088859336717769)
    ·
      refine ⟨7795405429566644502538327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10393873906088859336717769 7795405429566644502538327)
      ·
        refine ⟨11693108144349966753807491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7795405429566644502538327 11693108144349966753807491)
        ·
          refine ⟨17539662216524950130711237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11693108144349966753807491 17539662216524950130711237)
          ·
            refine ⟨3288686665598428149508357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17539662216524950130711237 3288686665598428149508357)
            ·
              refine ⟨616628749799705278032817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3288686665598428149508357 616628749799705278032817)
              ·
                refine ⟨462471562349778958524613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 616628749799705278032817 462471562349778958524613)
                ·
                  refine ⟨86713417940583554723365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 462471562349778958524613 86713417940583554723365)
                  ·
                    rfl

theorem cell22_759932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 2, 4].length) (baseStart_759932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759932 prefixEnd_759932 := by exact prefixLift 759932
  have htrace : WordTrace (prefixWord ++ tailWord_759932) baseStart_759932 baseEnd_759932 := by
    simpa [prefixWord, tailWord_759932, baseEnd_759932] using wordTrace_append hprefix tailTrace_759932
  have hstable : (prefixWord ++ tailWord_759932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759932).length < 2 ^ (prefixWord ++ tailWord_759932).sum := by decide
  have hdescent : baseEnd_759932 < baseStart_759932 := by decide
  rcases family_descends (prefixWord ++ tailWord_759932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759943 : List Nat := [1, 1, 4, 2, 1, 1, 5, 7]
def baseStart_759943 : Nat := 118140960795 + 759943 * 2 ^ 59
def prefixEnd_759943 : Nat := 4983230072969 + 3 ^ 40 * 759943 * 2
def baseEnd_759943 : Nat := 28904891038505589127229

theorem tailTrace_759943 : CollatzResearch.WordTrace tailWord_759943 prefixEnd_759943 28904891038505589127229 := by
  unfold tailWord_759943
  simp only [CollatzResearch.WordTrace]
  refine ⟨27717398285863773776564483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18478265523909182517709655 27717398285863773776564483)
  ·
    refine ⟨41576097428795660664846725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27717398285863773776564483 41576097428795660664846725)
    ·
      refine ⟨7795518267899186374658761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41576097428795660664846725 7795518267899186374658761)
      ·
        refine ⟨5846638700924389780994071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7795518267899186374658761 5846638700924389780994071)
        ·
          refine ⟨8769958051386584671491107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5846638700924389780994071 8769958051386584671491107)
          ·
            refine ⟨13154937077079877007236661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8769958051386584671491107 13154937077079877007236661)
            ·
              refine ⟨1233275350976238469428437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13154937077079877007236661 1233275350976238469428437)
              ·
                refine ⟨28904891038505589127229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1233275350976238469428437 28904891038505589127229)
                ·
                  rfl

theorem cell22_759943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 7].length) (baseStart_759943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759943 prefixEnd_759943 := by exact prefixLift 759943
  have htrace : WordTrace (prefixWord ++ tailWord_759943) baseStart_759943 baseEnd_759943 := by
    simpa [prefixWord, tailWord_759943, baseEnd_759943] using wordTrace_append hprefix tailTrace_759943
  have hstable : (prefixWord ++ tailWord_759943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759943).length < 2 ^ (prefixWord ++ tailWord_759943).sum := by decide
  have hdescent : baseEnd_759943 < baseStart_759943 := by decide
  rcases family_descends (prefixWord ++ tailWord_759943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_759992 : List Nat := [2, 1, 2, 1, 2, 1, 3, 6, 1, 3]
def baseStart_759992 : Nat := 118140960795 + 759992 * 2 ^ 59
def prefixEnd_759992 : Nat := 4983230072969 + 3 ^ 40 * 759992 * 2
def baseEnd_759992 : Nat := 260160793047930507669911

theorem tailTrace_759992 : CollatzResearch.WordTrace tailWord_759992 prefixEnd_759992 260160793047930507669911 := by
  unfold tailWord_759992
  simp only [CollatzResearch.WordTrace]
  refine ⟨13859592731343127572549115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18479456975124170096732153 13859592731343127572549115)
  ·
    refine ⟨20789389097014691358823673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13859592731343127572549115 20789389097014691358823673)
    ·
      refine ⟨15592041822761018519117755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20789389097014691358823673 15592041822761018519117755)
      ·
        refine ⟨23388062734141527778676633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15592041822761018519117755 23388062734141527778676633)
        ·
          refine ⟨17541047050606145834007475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23388062734141527778676633 17541047050606145834007475)
          ·
            refine ⟨26311570575909218751011213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17541047050606145834007475 26311570575909218751011213)
            ·
              refine ⟨9866838965965957031629205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26311570575909218751011213 9866838965965957031629205)
              ·
                refine ⟨462508076529654235857619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9866838965965957031629205 462508076529654235857619)
                ·
                  refine ⟨693762114794481353786429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 462508076529654235857619 693762114794481353786429)
                  ·
                    refine ⟨260160793047930507669911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 693762114794481353786429 260160793047930507669911)
                    ·
                      rfl

theorem cell22_759992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 6, 1, 3].length) (baseStart_759992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_759992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_759992 prefixEnd_759992 := by exact prefixLift 759992
  have htrace : WordTrace (prefixWord ++ tailWord_759992) baseStart_759992 baseEnd_759992 := by
    simpa [prefixWord, tailWord_759992, baseEnd_759992] using wordTrace_append hprefix tailTrace_759992
  have hstable : (prefixWord ++ tailWord_759992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_759992).length < 2 ^ (prefixWord ++ tailWord_759992).sum := by decide
  have hdescent : baseEnd_759992 < baseStart_759992 := by decide
  rcases family_descends (prefixWord ++ tailWord_759992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760022 : List Nat := [5, 2, 1, 2, 1, 1, 1, 2, 7]
def baseStart_760022 : Nat := 118140960795 + 760022 * 2 ^ 59
def prefixEnd_760022 : Nat := 4983230072969 + 3 ^ 40 * 760022 * 2
def baseEnd_760022 : Nat := 86723687553673476473273

theorem tailTrace_760022 : CollatzResearch.WordTrace tailWord_760022 prefixEnd_760022 86723687553673476473273 := by
  unfold tailWord_760022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1732517478286098141793145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18480186435051713512460213 1732517478286098141793145)
  ·
    refine ⟨1299388108714573606344859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1732517478286098141793145 1299388108714573606344859)
    ·
      refine ⟨1949082163071860409517289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1299388108714573606344859 1949082163071860409517289)
      ·
        refine ⟨1461811622303895307137967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1949082163071860409517289 1461811622303895307137967)
        ·
          refine ⟨2192717433455842960706951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1461811622303895307137967 2192717433455842960706951)
          ·
            refine ⟨3289076150183764441060427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2192717433455842960706951 3289076150183764441060427)
            ·
              refine ⟨4933614225275646661590641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3289076150183764441060427 4933614225275646661590641)
              ·
                refine ⟨3700210668956734996192981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4933614225275646661590641 3700210668956734996192981)
                ·
                  refine ⟨86723687553673476473273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3700210668956734996192981 86723687553673476473273)
                  ·
                    rfl

theorem cell22_760022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_760022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760022 prefixEnd_760022 := by exact prefixLift 760022
  have htrace : WordTrace (prefixWord ++ tailWord_760022) baseStart_760022 baseEnd_760022 := by
    simpa [prefixWord, tailWord_760022, baseEnd_760022] using wordTrace_append hprefix tailTrace_760022
  have hstable : (prefixWord ++ tailWord_760022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760022).length < 2 ^ (prefixWord ++ tailWord_760022).sum := by decide
  have hdescent : baseEnd_760022 < baseStart_760022 := by decide
  rcases family_descends (prefixWord ++ tailWord_760022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760065 : List Nat := [1, 2, 4, 1, 1, 2, 2, 3, 1, 5]
def baseStart_760065 : Nat := 118140960795 + 760065 * 2 ^ 59
def prefixEnd_760065 : Nat := 4983230072969 + 3 ^ 40 * 760065 * 2
def baseEnd_760065 : Nat := 260185782439782650594687

theorem tailTrace_760065 : CollatzResearch.WordTrace tailWord_760065 prefixEnd_760065 260185782439782650594687 := by
  unfold tailWord_760065
  simp only [CollatzResearch.WordTrace]
  refine ⟨27721847991421788612505649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18481231994281192408337099 27721847991421788612505649)
  ·
    refine ⟨20791385993566341459379237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27721847991421788612505649 20791385993566341459379237)
    ·
      refine ⟨3898384873793689023633607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20791385993566341459379237 3898384873793689023633607)
      ·
        refine ⟨5847577310690533535450411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3898384873793689023633607 5847577310690533535450411)
        ·
          refine ⟨8771365966035800303175617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5847577310690533535450411 8771365966035800303175617)
          ·
            refine ⟨6578524474526850227381713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8771365966035800303175617 6578524474526850227381713)
            ·
              refine ⟨4933893355895137670536285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6578524474526850227381713 4933893355895137670536285)
              ·
                refine ⟨1850210008460676626451107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4933893355895137670536285 1850210008460676626451107)
                ·
                  refine ⟨2775315012691014939676661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1850210008460676626451107 2775315012691014939676661)
                  ·
                    refine ⟨260185782439782650594687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2775315012691014939676661 260185782439782650594687)
                    ·
                      rfl

theorem cell22_760065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_760065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760065 prefixEnd_760065 := by exact prefixLift 760065
  have htrace : WordTrace (prefixWord ++ tailWord_760065) baseStart_760065 baseEnd_760065 := by
    simpa [prefixWord, tailWord_760065, baseEnd_760065] using wordTrace_append hprefix tailTrace_760065
  have hstable : (prefixWord ++ tailWord_760065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760065).length < 2 ^ (prefixWord ++ tailWord_760065).sum := by decide
  have hdescent : baseEnd_760065 < baseStart_760065 := by decide
  rcases family_descends (prefixWord ++ tailWord_760065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760101 : List Nat := [1, 3, 1, 2, 5, 2, 2, 2, 4]
def baseStart_760101 : Nat := 118140960795 + 760101 * 2 ^ 59
def prefixEnd_760101 : Nat := 4983230072969 + 3 ^ 40 * 760101 * 2
def baseEnd_760101 : Nat := 86732701991830185564859

theorem tailTrace_760101 : CollatzResearch.WordTrace tailWord_760101 prefixEnd_760101 86732701991830185564859 := by
  unfold tailWord_760101
  simp only [CollatzResearch.WordTrace]
  refine ⟨27723161019291366760816157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18482107346194244507210771 27723161019291366760816157)
  ·
    refine ⟨10396185382234262535306059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27723161019291366760816157 10396185382234262535306059)
    ·
      refine ⟨15594278073351393802959089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10396185382234262535306059 15594278073351393802959089)
      ·
        refine ⟨11695708555013545352219317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15594278073351393802959089 11695708555013545352219317)
        ·
          refine ⟨1096472677032519876770561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11695708555013545352219317 1096472677032519876770561)
          ·
            refine ⟨822354507774389907577921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1096472677032519876770561 822354507774389907577921)
            ·
              refine ⟨616765880830792430683441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 822354507774389907577921 616765880830792430683441)
              ·
                refine ⟨462574410623094323012581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 616765880830792430683441 462574410623094323012581)
                ·
                  refine ⟨86732701991830185564859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 462574410623094323012581 86732701991830185564859)
                  ·
                    rfl

theorem cell22_760101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 2, 4].length) (baseStart_760101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760101 prefixEnd_760101 := by exact prefixLift 760101
  have htrace : WordTrace (prefixWord ++ tailWord_760101) baseStart_760101 baseEnd_760101 := by
    simpa [prefixWord, tailWord_760101, baseEnd_760101] using wordTrace_append hprefix tailTrace_760101
  have hstable : (prefixWord ++ tailWord_760101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760101).length < 2 ^ (prefixWord ++ tailWord_760101).sum := by decide
  have hdescent : baseEnd_760101 < baseStart_760101 := by decide
  rcases family_descends (prefixWord ++ tailWord_760101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760127 : List Nat := [1, 1, 2, 2, 4, 1, 3, 2, 3, 3]
def baseStart_760127 : Nat := 118140960795 + 760127 * 2 ^ 59
def prefixEnd_760127 : Nat := 4983230072969 + 3 ^ 40 * 760127 * 2
def baseEnd_760127 : Nat := 260207006306835155544497

theorem tailTrace_760127 : CollatzResearch.WordTrace tailWord_760127 prefixEnd_760127 260207006306835155544497 := by
  unfold tailWord_760127
  simp only [CollatzResearch.WordTrace]
  refine ⟨27724109317197173201262635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18482739544798115467508423 27724109317197173201262635)
  ·
    refine ⟨41586163975795759801893953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27724109317197173201262635 41586163975795759801893953)
    ·
      refine ⟨31189622981846819851420465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41586163975795759801893953 31189622981846819851420465)
      ·
        refine ⟨23392217236385114888565349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31189622981846819851420465 23392217236385114888565349)
        ·
          refine ⟨4386040731822209041606003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23392217236385114888565349 4386040731822209041606003)
          ·
            refine ⟨6579061097733313562409005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4386040731822209041606003 6579061097733313562409005)
            ·
              refine ⟨2467147911649992585903377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6579061097733313562409005 2467147911649992585903377)
              ·
                refine ⟨1850360933737494439427533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2467147911649992585903377 1850360933737494439427533)
                ·
                  refine ⟨693885350151560414785325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1850360933737494439427533 693885350151560414785325)
                  ·
                    refine ⟨260207006306835155544497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 693885350151560414785325 260207006306835155544497)
                    ·
                      rfl

theorem cell22_760127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 3, 3].length) (baseStart_760127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760127 prefixEnd_760127 := by exact prefixLift 760127
  have htrace : WordTrace (prefixWord ++ tailWord_760127) baseStart_760127 baseEnd_760127 := by
    simpa [prefixWord, tailWord_760127, baseEnd_760127] using wordTrace_append hprefix tailTrace_760127
  have hstable : (prefixWord ++ tailWord_760127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760127).length < 2 ^ (prefixWord ++ tailWord_760127).sum := by decide
  have hdescent : baseEnd_760127 < baseStart_760127 := by decide
  rcases family_descends (prefixWord ++ tailWord_760127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760129 : List Nat := [1, 2, 5, 2, 2, 1, 3, 6]
def baseStart_760129 : Nat := 118140960795 + 760129 * 2 ^ 59
def prefixEnd_760129 : Nat := 4983230072969 + 3 ^ 40 * 760129 * 2
def baseEnd_760129 : Nat := 28911965660856424110499

theorem tailTrace_760129 : CollatzResearch.WordTrace tailWord_760129 prefixEnd_760129 28911965660856424110499 := by
  unfold tailWord_760129
  simp only [CollatzResearch.WordTrace]
  refine ⟨27724182263189927542835441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18482788175459951695223627 27724182263189927542835441)
  ·
    refine ⟨20793136697392445657126581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27724182263189927542835441 20793136697392445657126581)
    ·
      refine ⟨1949356565380541780355617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20793136697392445657126581 1949356565380541780355617)
      ·
        refine ⟨1462017424035406335266713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1949356565380541780355617 1462017424035406335266713)
        ·
          refine ⟨1096513068026554751450035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1462017424035406335266713 1096513068026554751450035)
          ·
            refine ⟨1644769602039832127175053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1096513068026554751450035 1644769602039832127175053)
            ·
              refine ⟨616788600764937047690645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1644769602039832127175053 616788600764937047690645)
              ·
                refine ⟨28911965660856424110499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 616788600764937047690645 28911965660856424110499)
                ·
                  rfl

theorem cell22_760129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 6].length) (baseStart_760129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760129 prefixEnd_760129 := by exact prefixLift 760129
  have htrace : WordTrace (prefixWord ++ tailWord_760129) baseStart_760129 baseEnd_760129 := by
    simpa [prefixWord, tailWord_760129, baseEnd_760129] using wordTrace_append hprefix tailTrace_760129
  have hstable : (prefixWord ++ tailWord_760129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760129).length < 2 ^ (prefixWord ++ tailWord_760129).sum := by decide
  have hdescent : baseEnd_760129 < baseStart_760129 := by decide
  rcases family_descends (prefixWord ++ tailWord_760129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760140 : List Nat := [2, 2, 1, 3, 2, 1, 2, 2, 7]
def baseStart_760140 : Nat := 118140960795 + 760140 * 2 ^ 59
def prefixEnd_760140 : Nat := 4983230072969 + 3 ^ 40 * 760140 * 2
def baseEnd_760140 : Nat := 86737152157502484989819

theorem tailTrace_760140 : CollatzResearch.WordTrace tailWord_760140 prefixEnd_760140 86737152157502484989819 := by
  unfold tailWord_760140
  simp only [CollatzResearch.WordTrace]
  refine ⟨13862291733075038210742937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18483055644100050947657249 13862291733075038210742937)
  ·
    refine ⟨10396718799806278658057203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13862291733075038210742937 10396718799806278658057203)
    ·
      refine ⟨15595078199709417987085805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10396718799806278658057203 15595078199709417987085805)
      ·
        refine ⟨5848154324891031745157177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15595078199709417987085805 5848154324891031745157177)
        ·
          refine ⟨4386115743668273808867883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5848154324891031745157177 4386115743668273808867883)
          ·
            refine ⟨6579173615502410713301825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4386115743668273808867883 6579173615502410713301825)
            ·
              refine ⟨4934380211626808034976369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6579173615502410713301825 4934380211626808034976369)
              ·
                refine ⟨3700785158720106026232277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4934380211626808034976369 3700785158720106026232277)
                ·
                  refine ⟨86737152157502484989819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3700785158720106026232277 86737152157502484989819)
                  ·
                    rfl

theorem cell22_760140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 7].length) (baseStart_760140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760140 prefixEnd_760140 := by exact prefixLift 760140
  have htrace : WordTrace (prefixWord ++ tailWord_760140) baseStart_760140 baseEnd_760140 := by
    simpa [prefixWord, tailWord_760140, baseEnd_760140] using wordTrace_append hprefix tailTrace_760140
  have hstable : (prefixWord ++ tailWord_760140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760140).length < 2 ^ (prefixWord ++ tailWord_760140).sum := by decide
  have hdescent : baseEnd_760140 < baseStart_760140 := by decide
  rcases family_descends (prefixWord ++ tailWord_760140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760144 : List Nat := [2, 1, 1, 1, 1, 6, 1, 5, 1, 3]
def baseStart_760144 : Nat := 118140960795 + 760144 * 2 ^ 59
def prefixEnd_760144 : Nat := 4983230072969 + 3 ^ 40 * 760144 * 2
def baseEnd_760144 : Nat := 260212825754252777869445

theorem tailTrace_760144 : CollatzResearch.WordTrace tailWord_760144 prefixEnd_760144 260212825754252777869445 := by
  unfold tailWord_760144
  simp only [CollatzResearch.WordTrace]
  refine ⟨13862364679067792552315743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18483152905423723403087657 13862364679067792552315743)
  ·
    refine ⟨20793547018601688828473615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13862364679067792552315743 20793547018601688828473615)
    ·
      refine ⟨31190320527902533242710423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20793547018601688828473615 31190320527902533242710423)
      ·
        refine ⟨46785480791853799864065635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31190320527902533242710423 46785480791853799864065635)
        ·
          refine ⟨70178221187780699796098453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46785480791853799864065635 70178221187780699796098453)
          ·
            refine ⟨3289604118177220302942115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 70178221187780699796098453 3289604118177220302942115)
            ·
              refine ⟨4934406177265830454413173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3289604118177220302942115 4934406177265830454413173)
              ·
                refine ⟨462600579118671605101235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4934406177265830454413173 462600579118671605101235)
                ·
                  refine ⟨693900868678007407651853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 462600579118671605101235 693900868678007407651853)
                  ·
                    refine ⟨260212825754252777869445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 693900868678007407651853 260212825754252777869445)
                    ·
                      rfl

theorem cell22_760144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 5, 1, 3].length) (baseStart_760144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760144 prefixEnd_760144 := by exact prefixLift 760144
  have htrace : WordTrace (prefixWord ++ tailWord_760144) baseStart_760144 baseEnd_760144 := by
    simpa [prefixWord, tailWord_760144, baseEnd_760144] using wordTrace_append hprefix tailTrace_760144
  have hstable : (prefixWord ++ tailWord_760144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760144).length < 2 ^ (prefixWord ++ tailWord_760144).sum := by decide
  have hdescent : baseEnd_760144 < baseStart_760144 := by decide
  rcases family_descends (prefixWord ++ tailWord_760144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760187 : List Nat := [1, 1, 1, 1, 1, 7, 1, 4, 1, 4]
def baseStart_760187 : Nat := 118140960795 + 760187 * 2 ^ 59
def prefixEnd_760187 : Nat := 4983230072969 + 3 ^ 40 * 760187 * 2
def baseEnd_760187 : Nat := 260227545533014999044313

theorem tailTrace_760187 : CollatzResearch.WordTrace tailWord_760187 prefixEnd_760187 260227545533014999044313 := by
  unfold tailWord_760187
  simp only [CollatzResearch.WordTrace]
  refine ⟨27726297696979803448446815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18484198464653202298964543 27726297696979803448446815)
  ·
    refine ⟨41589446545469705172670223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27726297696979803448446815 41589446545469705172670223)
    ·
      refine ⟨62384169818204557759005335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41589446545469705172670223 62384169818204557759005335)
      ·
        refine ⟨93576254727306836638508003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62384169818204557759005335 93576254727306836638508003)
        ·
          refine ⟨140364382090960254957762005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93576254727306836638508003 140364382090960254957762005)
          ·
            refine ⟨3289790205256880975572547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 140364382090960254957762005 3289790205256880975572547)
            ·
              refine ⟨4934685307885321463358821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3289790205256880975572547 4934685307885321463358821)
              ·
                refine ⟨925253495228497774379779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4934685307885321463358821 925253495228497774379779)
                ·
                  refine ⟨1387880242842746661569669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 925253495228497774379779 1387880242842746661569669)
                  ·
                    refine ⟨260227545533014999044313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1387880242842746661569669 260227545533014999044313)
                    ·
                      rfl

theorem cell22_760187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 4].length) (baseStart_760187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760187 prefixEnd_760187 := by exact prefixLift 760187
  have htrace : WordTrace (prefixWord ++ tailWord_760187) baseStart_760187 baseEnd_760187 := by
    simpa [prefixWord, tailWord_760187, baseEnd_760187] using wordTrace_append hprefix tailTrace_760187
  have hstable : (prefixWord ++ tailWord_760187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760187).length < 2 ^ (prefixWord ++ tailWord_760187).sum := by decide
  have hdescent : baseEnd_760187 < baseStart_760187 := by decide
  rcases family_descends (prefixWord ++ tailWord_760187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760217 : List Nat := [1, 2, 1, 2, 1, 4, 1, 3, 4, 3]
def baseStart_760217 : Nat := 118140960795 + 760217 * 2 ^ 59
def prefixEnd_760217 : Nat := 4983230072969 + 3 ^ 40 * 760217 * 2
def baseEnd_760217 : Nat := 260237815146104920794221

theorem tailTrace_760217 : CollatzResearch.WordTrace tailWord_760217 prefixEnd_760217 260237815146104920794221 := by
  unfold tailWord_760217
  simp only [CollatzResearch.WordTrace]
  refine ⟨27727391886871118572038905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18484927924580745714692603 27727391886871118572038905)
  ·
    refine ⟨20795543915153338929029179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27727391886871118572038905 20795543915153338929029179)
    ·
      refine ⟨31193315872730008393543769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20795543915153338929029179 31193315872730008393543769)
      ·
        refine ⟨23394986904547506295157827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31193315872730008393543769 23394986904547506295157827)
        ·
          refine ⟨35092480356821259442736741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23394986904547506295157827 35092480356821259442736741)
          ·
            refine ⟨6579840066903986145513139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35092480356821259442736741 6579840066903986145513139)
            ·
              refine ⟨9869760100355979218269709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6579840066903986145513139 9869760100355979218269709)
              ·
                refine ⟨3701160037633492206851141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9869760100355979218269709 3701160037633492206851141)
                ·
                  refine ⟨693967507056279788784589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3701160037633492206851141 693967507056279788784589)
                  ·
                    refine ⟨260237815146104920794221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 693967507056279788784589 260237815146104920794221)
                    ·
                      rfl

theorem cell22_760217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 4, 3].length) (baseStart_760217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760217 prefixEnd_760217 := by exact prefixLift 760217
  have htrace : WordTrace (prefixWord ++ tailWord_760217) baseStart_760217 baseEnd_760217 := by
    simpa [prefixWord, tailWord_760217, baseEnd_760217] using wordTrace_append hprefix tailTrace_760217
  have hstable : (prefixWord ++ tailWord_760217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760217).length < 2 ^ (prefixWord ++ tailWord_760217).sum := by decide
  have hdescent : baseEnd_760217 < baseStart_760217 := by decide
  rcases family_descends (prefixWord ++ tailWord_760217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760249 : List Nat := [1, 2, 1, 4, 3, 2, 2, 1, 2, 4]
def baseStart_760249 : Nat := 118140960795 + 760249 * 2 ^ 59
def prefixEnd_760249 : Nat := 4983230072969 + 3 ^ 40 * 760249 * 2
def baseEnd_760249 : Nat := 260248769400067503994123

theorem tailTrace_760249 : CollatzResearch.WordTrace tailWord_760249 prefixEnd_760249 260248769400067503994123 := by
  unfold tailWord_760249
  simp only [CollatzResearch.WordTrace]
  refine ⟨27728559022755188037203801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18485706015170125358135867 27728559022755188037203801)
  ·
    refine ⟨20796419267066391027902851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27728559022755188037203801 20796419267066391027902851)
    ·
      refine ⟨31194628900599586541854277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20796419267066391027902851 31194628900599586541854277)
      ·
        refine ⟨5848992918862422476597677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31194628900599586541854277 5848992918862422476597677)
        ·
          refine ⟨2193372344573408428724129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5848992918862422476597677 2193372344573408428724129)
          ·
            refine ⟨1645029258430056321543097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2193372344573408428724129 1645029258430056321543097)
            ·
              refine ⟨1233771943822542241157323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1645029258430056321543097 1233771943822542241157323)
              ·
                refine ⟨1850657915733813361735985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1233771943822542241157323 1850657915733813361735985)
                ·
                  refine ⟨1387993436800360021301989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1850657915733813361735985 1387993436800360021301989)
                  ·
                    refine ⟨260248769400067503994123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1387993436800360021301989 260248769400067503994123)
                    ·
                      rfl

theorem cell22_760249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 4].length) (baseStart_760249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760249 prefixEnd_760249 := by exact prefixLift 760249
  have htrace : WordTrace (prefixWord ++ tailWord_760249) baseStart_760249 baseEnd_760249 := by
    simpa [prefixWord, tailWord_760249, baseEnd_760249] using wordTrace_append hprefix tailTrace_760249
  have hstable : (prefixWord ++ tailWord_760249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760249).length < 2 ^ (prefixWord ++ tailWord_760249).sum := by decide
  have hdescent : baseEnd_760249 < baseStart_760249 := by decide
  rcases family_descends (prefixWord ++ tailWord_760249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760275 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 13]
def baseStart_760275 : Nat := 118140960795 + 760275 * 2 ^ 59
def prefixEnd_760275 : Nat := 4983230072969 + 3 ^ 40 * 760275 * 2
def baseEnd_760275 : Nat := 86752556577137367614681

theorem tailTrace_760275 : CollatzResearch.WordTrace tailWord_760275 prefixEnd_760275 86752556577137367614681 := by
  unfold tailWord_760275
  simp only [CollatzResearch.WordTrace]
  refine ⟨27729507320660994477650279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18486338213773996318433519 27729507320660994477650279)
  ·
    refine ⟨41594260980991491716475419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27729507320660994477650279 41594260980991491716475419)
    ·
      refine ⟨62391391471487237574713129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41594260980991491716475419 62391391471487237574713129)
      ·
        refine ⟨46793543603615428181034847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62391391471487237574713129 46793543603615428181034847)
        ·
          refine ⟨70190315405423142271552271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46793543603615428181034847 70190315405423142271552271)
          ·
            refine ⟨105285473108134713407328407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70190315405423142271552271 105285473108134713407328407)
            ·
              refine ⟨157928209662202070110992611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105285473108134713407328407 157928209662202070110992611)
              ·
                refine ⟨236892314493303105166488917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157928209662202070110992611 236892314493303105166488917)
                ·
                  refine ⟨86752556577137367614681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 236892314493303105166488917 86752556577137367614681)
                  ·
                    rfl

theorem cell22_760275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 13].length) (baseStart_760275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760275 prefixEnd_760275 := by exact prefixLift 760275
  have htrace : WordTrace (prefixWord ++ tailWord_760275) baseStart_760275 baseEnd_760275 := by
    simpa [prefixWord, tailWord_760275, baseEnd_760275] using wordTrace_append hprefix tailTrace_760275
  have hstable : (prefixWord ++ tailWord_760275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760275).length < 2 ^ (prefixWord ++ tailWord_760275).sum := by decide
  have hdescent : baseEnd_760275 < baseStart_760275 := by decide
  rcases family_descends (prefixWord ++ tailWord_760275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760277 : List Nat := [1, 3, 2, 3, 1, 2, 1, 1, 2, 6]
def baseStart_760277 : Nat := 118140960795 + 760277 * 2 ^ 59
def prefixEnd_760277 : Nat := 4983230072969 + 3 ^ 40 * 760277 * 2
def baseEnd_760277 : Nat := 260258354372284764294037

theorem tailTrace_760277 : CollatzResearch.WordTrace tailWord_760277 prefixEnd_760277 260258354372284764294037 := by
  unfold tailWord_760277
  simp only [CollatzResearch.WordTrace]
  refine ⟨27729580266653748819223085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18486386844435832546148723 27729580266653748819223085)
  ·
    refine ⟨10398592599995155807208657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27729580266653748819223085 10398592599995155807208657)
    ·
      refine ⟨7798944449996366855406493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10398592599995155807208657 7798944449996366855406493)
      ·
        refine ⟨2924604168748637570777435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7798944449996366855406493 2924604168748637570777435)
        ·
          refine ⟨4386906253122956356166153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2924604168748637570777435 4386906253122956356166153)
          ·
            refine ⟨3290179689842217267124615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4386906253122956356166153 3290179689842217267124615)
            ·
              refine ⟨4935269534763325900686923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3290179689842217267124615 4935269534763325900686923)
              ·
                refine ⟨7402904302144988851030385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4935269534763325900686923 7402904302144988851030385)
                ·
                  refine ⟨5552178226608741638272789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7402904302144988851030385 5552178226608741638272789)
                  ·
                    refine ⟨260258354372284764294037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5552178226608741638272789 260258354372284764294037)
                    ·
                      rfl

theorem cell22_760277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_760277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760277 prefixEnd_760277 := by exact prefixLift 760277
  have htrace : WordTrace (prefixWord ++ tailWord_760277) baseStart_760277 baseEnd_760277 := by
    simpa [prefixWord, tailWord_760277, baseEnd_760277] using wordTrace_append hprefix tailTrace_760277
  have hstable : (prefixWord ++ tailWord_760277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760277).length < 2 ^ (prefixWord ++ tailWord_760277).sum := by decide
  have hdescent : baseEnd_760277 < baseStart_760277 := by decide
  rcases family_descends (prefixWord ++ tailWord_760277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760324 : List Nat := [2, 3, 2, 3, 1, 1, 1, 2, 2, 5]
def baseStart_760324 : Nat := 118140960795 + 760324 * 2 ^ 59
def prefixEnd_760324 : Nat := 4983230072969 + 3 ^ 40 * 760324 * 2
def baseEnd_760324 : Nat := 260274443432792308368893

theorem tailTrace_760324 : CollatzResearch.WordTrace tailWord_760324 prefixEnd_760324 260274443432792308368893 := by
  unfold tailWord_760324
  simp only [CollatzResearch.WordTrace]
  refine ⟨13865647248741737923092013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18487529664988983897456017 13865647248741737923092013)
  ·
    refine ⟨5199617718278151721159505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13865647248741737923092013 5199617718278151721159505)
    ·
      refine ⟨3899713288708613790869629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5199617718278151721159505 3899713288708613790869629)
      ·
        refine ⟨1462392483265730171576111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3899713288708613790869629 1462392483265730171576111)
        ·
          refine ⟨2193588724898595257364167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1462392483265730171576111 2193588724898595257364167)
          ·
            refine ⟨3290383087347892886046251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2193588724898595257364167 3290383087347892886046251)
            ·
              refine ⟨4935574631021839329069377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3290383087347892886046251 4935574631021839329069377)
              ·
                refine ⟨3701680973266379496802033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4935574631021839329069377 3701680973266379496802033)
                ·
                  refine ⟨2776260729949784622601525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3701680973266379496802033 2776260729949784622601525)
                  ·
                    refine ⟨260274443432792308368893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2776260729949784622601525 260274443432792308368893)
                    ·
                      rfl

theorem cell22_760324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_760324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760324 prefixEnd_760324 := by exact prefixLift 760324
  have htrace : WordTrace (prefixWord ++ tailWord_760324) baseStart_760324 baseEnd_760324 := by
    simpa [prefixWord, tailWord_760324, baseEnd_760324] using wordTrace_append hprefix tailTrace_760324
  have hstable : (prefixWord ++ tailWord_760324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760324).length < 2 ^ (prefixWord ++ tailWord_760324).sum := by decide
  have hdescent : baseEnd_760324 < baseStart_760324 := by decide
  rcases family_descends (prefixWord ++ tailWord_760324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760343 : List Nat := [1, 1, 3, 6, 1, 1, 3, 1, 5]
def baseStart_760343 : Nat := 118140960795 + 760343 * 2 ^ 59
def prefixEnd_760343 : Nat := 4983230072969 + 3 ^ 40 * 760343 * 2
def baseEnd_760343 : Nat := 86760315840360864047945

theorem tailTrace_760343 : CollatzResearch.WordTrace tailWord_760343 prefixEnd_760343 86760315840360864047945 := by
  unfold tailWord_760343
  simp only [CollatzResearch.WordTrace]
  refine ⟨27731987484414642091125683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18487991656276428060750455 27731987484414642091125683)
  ·
    refine ⟨41597981226621963136688525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27731987484414642091125683 41597981226621963136688525)
    ·
      refine ⟨15599242959983236176258197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41597981226621963136688525 15599242959983236176258197)
      ·
        refine ⟨731214513749214195762103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15599242959983236176258197 731214513749214195762103)
        ·
          refine ⟨1096821770623821293643155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 731214513749214195762103 1096821770623821293643155)
          ·
            refine ⟨1645232655935731940464733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1096821770623821293643155 1645232655935731940464733)
            ·
              refine ⟨616962245975899477674275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1645232655935731940464733 616962245975899477674275)
              ·
                refine ⟨925443368963849216511413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 616962245975899477674275 925443368963849216511413)
                ·
                  refine ⟨86760315840360864047945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 925443368963849216511413 86760315840360864047945)
                  ·
                    rfl

theorem cell22_760343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 5].length) (baseStart_760343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760343 prefixEnd_760343 := by exact prefixLift 760343
  have htrace : WordTrace (prefixWord ++ tailWord_760343) baseStart_760343 baseEnd_760343 := by
    simpa [prefixWord, tailWord_760343, baseEnd_760343] using wordTrace_append hprefix tailTrace_760343
  have hstable : (prefixWord ++ tailWord_760343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760343).length < 2 ^ (prefixWord ++ tailWord_760343).sum := by decide
  have hdescent : baseEnd_760343 < baseStart_760343 := by decide
  rcases family_descends (prefixWord ++ tailWord_760343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760367 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 8, 4]
def baseStart_760367 : Nat := 118140960795 + 760367 * 2 ^ 59
def prefixEnd_760367 : Nat := 4983230072969 + 3 ^ 40 * 760367 * 2
def baseEnd_760367 : Nat := 260289163211554529543761

theorem tailTrace_760367 : CollatzResearch.WordTrace tailWord_760367 prefixEnd_760367 260289163211554529543761 := by
  unfold tailWord_760367
  simp only [CollatzResearch.WordTrace]
  refine ⟨27732862836327694189999355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18488575224218462793332903 27732862836327694189999355)
  ·
    refine ⟨41599294254491541284999033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27732862836327694189999355 41599294254491541284999033)
    ·
      refine ⟨31199470690868655963749275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41599294254491541284999033 31199470690868655963749275)
      ·
        refine ⟨46799206036302983945623913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31199470690868655963749275 46799206036302983945623913)
        ·
          refine ⟨35099404527227237959217935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46799206036302983945623913 35099404527227237959217935)
          ·
            refine ⟨52649106790840856938826903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35099404527227237959217935 52649106790840856938826903)
            ·
              refine ⟨78973660186261285408240355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52649106790840856938826903 78973660186261285408240355)
              ·
                refine ⟨118460490279391928112360533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78973660186261285408240355 118460490279391928112360533)
                ·
                  refine ⟨1388208870461624157566725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 118460490279391928112360533 1388208870461624157566725)
                  ·
                    refine ⟨260289163211554529543761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1388208870461624157566725 260289163211554529543761)
                    ·
                      rfl

theorem cell22_760367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 4].length) (baseStart_760367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760367 prefixEnd_760367 := by exact prefixLift 760367
  have htrace : WordTrace (prefixWord ++ tailWord_760367) baseStart_760367 baseEnd_760367 := by
    simpa [prefixWord, tailWord_760367, baseEnd_760367] using wordTrace_append hprefix tailTrace_760367
  have hstable : (prefixWord ++ tailWord_760367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760367).length < 2 ^ (prefixWord ++ tailWord_760367).sum := by decide
  have hdescent : baseEnd_760367 < baseStart_760367 := by decide
  rcases family_descends (prefixWord ++ tailWord_760367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760369 : List Nat := [1, 2, 2, 3, 1, 1, 3, 2, 4, 3]
def baseStart_760369 : Nat := 118140960795 + 760369 * 2 ^ 59
def prefixEnd_760369 : Nat := 4983230072969 + 3 ^ 40 * 760369 * 2
def baseEnd_760369 : Nat := 260289847852427190993755

theorem tailTrace_760369 : CollatzResearch.WordTrace tailWord_760369 prefixEnd_760369 260289847852427190993755 := by
  unfold tailWord_760369
  simp only [CollatzResearch.WordTrace]
  refine ⟨27732935782320448531572161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18488623854880299021048107 27732935782320448531572161)
  ·
    refine ⟨20799701836740336398679121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27732935782320448531572161 20799701836740336398679121)
    ·
      refine ⟨15599776377555252299009341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20799701836740336398679121 15599776377555252299009341)
      ·
        refine ⟨5849916141583219612128503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15599776377555252299009341 5849916141583219612128503)
        ·
          refine ⟨8774874212374829418192755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5849916141583219612128503 8774874212374829418192755)
          ·
            refine ⟨13162311318562244127289133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8774874212374829418192755 13162311318562244127289133)
            ·
              refine ⟨4935866744460841547733425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13162311318562244127289133 4935866744460841547733425)
              ·
                refine ⟨3701900058345631160800069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4935866744460841547733425 3701900058345631160800069)
                ·
                  refine ⟨694106260939805842650013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3701900058345631160800069 694106260939805842650013)
                  ·
                    refine ⟨260289847852427190993755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 694106260939805842650013 260289847852427190993755)
                    ·
                      rfl

theorem cell22_760369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 4, 3].length) (baseStart_760369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760369 prefixEnd_760369 := by exact prefixLift 760369
  have htrace : WordTrace (prefixWord ++ tailWord_760369) baseStart_760369 baseEnd_760369 := by
    simpa [prefixWord, tailWord_760369, baseEnd_760369] using wordTrace_append hprefix tailTrace_760369
  have hstable : (prefixWord ++ tailWord_760369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760369).length < 2 ^ (prefixWord ++ tailWord_760369).sum := by decide
  have hdescent : baseEnd_760369 < baseStart_760369 := by decide
  rcases family_descends (prefixWord ++ tailWord_760369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760427 : List Nat := [1, 1, 1, 1, 2, 2, 1, 6, 7]
def baseStart_760427 : Nat := 118140960795 + 760427 * 2 ^ 59
def prefixEnd_760427 : Nat := 4983230072969 + 3 ^ 40 * 760427 * 2
def baseEnd_760427 : Nat := 86769900812578124347859

theorem tailTrace_760427 : CollatzResearch.WordTrace tailWord_760427 prefixEnd_760427 86769900812578124347859 := by
  unfold tailWord_760427
  simp only [CollatzResearch.WordTrace]
  refine ⟨27735051216110324437183535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18490034144073549624789023 27735051216110324437183535)
  ·
    refine ⟨41602576824165486655775303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27735051216110324437183535 41602576824165486655775303)
    ·
      refine ⟨62403865236248229983662955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41602576824165486655775303 62403865236248229983662955)
      ·
        refine ⟨93605797854372344975494433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62403865236248229983662955 93605797854372344975494433)
        ·
          refine ⟨70204348390779258731620825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93605797854372344975494433 70204348390779258731620825)
          ·
            refine ⟨52653261293084444048715619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70204348390779258731620825 52653261293084444048715619)
            ·
              refine ⟨78979891939626666073073429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52653261293084444048715619 78979891939626666073073429)
              ·
                refine ⟨3702182434669999972175317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78979891939626666073073429 3702182434669999972175317)
                ·
                  refine ⟨86769900812578124347859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3702182434669999972175317 86769900812578124347859)
                  ·
                    rfl

theorem cell22_760427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 7].length) (baseStart_760427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760427 prefixEnd_760427 := by exact prefixLift 760427
  have htrace : WordTrace (prefixWord ++ tailWord_760427) baseStart_760427 baseEnd_760427 := by
    simpa [prefixWord, tailWord_760427, baseEnd_760427] using wordTrace_append hprefix tailTrace_760427
  have hstable : (prefixWord ++ tailWord_760427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760427).length < 2 ^ (prefixWord ++ tailWord_760427).sum := by decide
  have hdescent : baseEnd_760427 < baseStart_760427 := by decide
  rcases family_descends (prefixWord ++ tailWord_760427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760444 : List Nat := [2, 2, 2, 1, 1, 2, 3, 4, 5]
def baseStart_760444 : Nat := 118140960795 + 760444 * 2 ^ 59
def prefixEnd_760444 : Nat := 4983230072969 + 3 ^ 40 * 760444 * 2
def baseEnd_760444 : Nat := 86771840628383998456175

theorem tailTrace_760444 : CollatzResearch.WordTrace tailWord_760444 prefixEnd_760444 86771840628383998456175 := by
  unfold tailWord_760444
  simp only [CollatzResearch.WordTrace]
  refine ⟨13867835628524368170276193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18490447504699157560368257 13867835628524368170276193)
  ·
    refine ⟨10400876721393276127707145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13867835628524368170276193 10400876721393276127707145)
    ·
      refine ⟨7800657541044957095780359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10400876721393276127707145 7800657541044957095780359)
      ·
        refine ⟨11700986311567435643670539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7800657541044957095780359 11700986311567435643670539)
        ·
          refine ⟨17551479467351153465505809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11700986311567435643670539 17551479467351153465505809)
          ·
            refine ⟨13163609600513365099129357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17551479467351153465505809 13163609600513365099129357)
            ·
              refine ⟨4936353600192511912173509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13163609600513365099129357 4936353600192511912173509)
              ·
                refine ⟨925566300036095983532533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4936353600192511912173509 925566300036095983532533)
                ·
                  refine ⟨86771840628383998456175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 925566300036095983532533 86771840628383998456175)
                  ·
                    rfl

theorem cell22_760444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 5].length) (baseStart_760444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760444 prefixEnd_760444 := by exact prefixLift 760444
  have htrace : WordTrace (prefixWord ++ tailWord_760444) baseStart_760444 baseEnd_760444 := by
    simpa [prefixWord, tailWord_760444, baseEnd_760444] using wordTrace_append hprefix tailTrace_760444
  have hstable : (prefixWord ++ tailWord_760444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760444).length < 2 ^ (prefixWord ++ tailWord_760444).sum := by decide
  have hdescent : baseEnd_760444 < baseStart_760444 := by decide
  rcases family_descends (prefixWord ++ tailWord_760444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760448 : List Nat := [2, 1, 1, 2, 1, 6, 1, 4, 1, 3]
def baseStart_760448 : Nat := 118140960795 + 760448 * 2 ^ 59
def prefixEnd_760448 : Nat := 4983230072969 + 3 ^ 40 * 760448 * 2
def baseEnd_760448 : Nat := 260316891166897318268513

theorem tailTrace_760448 : CollatzResearch.WordTrace tailWord_760448 prefixEnd_760448 260316891166897318268513 := by
  unfold tailWord_760448
  simp only [CollatzResearch.WordTrace]
  refine ⟨13867908574517122511848999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18490544766022830015798665 13867908574517122511848999)
  ·
    refine ⟨20801862861775683767773499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13867908574517122511848999 20801862861775683767773499)
    ·
      refine ⟨31202794292663525651660249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20801862861775683767773499 31202794292663525651660249)
      ·
        refine ⟨23402095719497644238745187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31202794292663525651660249 23402095719497644238745187)
        ·
          refine ⟨35103143579246466358117781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23402095719497644238745187 35103143579246466358117781)
          ·
            refine ⟨1645459855277178110536771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35103143579246466358117781 1645459855277178110536771)
            ·
              refine ⟨2468189782915767165805157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1645459855277178110536771 2468189782915767165805157)
              ·
                refine ⟨462785584296706343588467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2468189782915767165805157 462785584296706343588467)
                ·
                  refine ⟨694178376445059515382701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 462785584296706343588467 694178376445059515382701)
                  ·
                    refine ⟨260316891166897318268513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 694178376445059515382701 260316891166897318268513)
                    ·
                      rfl

theorem cell22_760448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 4, 1, 3].length) (baseStart_760448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760448 prefixEnd_760448 := by exact prefixLift 760448
  have htrace : WordTrace (prefixWord ++ tailWord_760448) baseStart_760448 baseEnd_760448 := by
    simpa [prefixWord, tailWord_760448, baseEnd_760448] using wordTrace_append hprefix tailTrace_760448
  have hstable : (prefixWord ++ tailWord_760448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760448).length < 2 ^ (prefixWord ++ tailWord_760448).sum := by decide
  have hdescent : baseEnd_760448 < baseStart_760448 := by decide
  rcases family_descends (prefixWord ++ tailWord_760448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760506 : List Nat := [3, 1, 1, 1, 2, 3, 1, 6, 4]
def baseStart_760506 : Nat := 118140960795 + 760506 * 2 ^ 59
def prefixEnd_760506 : Nat := 4983230072969 + 3 ^ 40 * 760506 * 2
def baseEnd_760506 : Nat := 86778915250734833439445

theorem tailTrace_760506 : CollatzResearch.WordTrace tailWord_760506 prefixEnd_760506 86778915250734833439445 := by
  unfold tailWord_760506
  simp only [CollatzResearch.WordTrace]
  refine ⟨6934483145706030232327343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18491955055216080619539581 6934483145706030232327343)
  ·
    refine ⟨10401724718559045348491015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6934483145706030232327343 10401724718559045348491015)
    ·
      refine ⟨15602587077838568022736523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10401724718559045348491015 15602587077838568022736523)
      ·
        refine ⟨23403880616757852034104785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15602587077838568022736523 23403880616757852034104785)
        ·
          refine ⟨17552910462568389025578589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23403880616757852034104785 17552910462568389025578589)
          ·
            refine ⟨6582341423463145884591971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17552910462568389025578589 6582341423463145884591971)
            ·
              refine ⟨9873512135194718826887957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6582341423463145884591971 9873512135194718826887957)
              ·
                refine ⟨462820881337252445010373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9873512135194718826887957 462820881337252445010373)
                ·
                  refine ⟨86778915250734833439445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 462820881337252445010373 86778915250734833439445)
                  ·
                    rfl

theorem cell22_760506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 6, 4].length) (baseStart_760506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760506 prefixEnd_760506 := by exact prefixLift 760506
  have htrace : WordTrace (prefixWord ++ tailWord_760506) baseStart_760506 baseEnd_760506 := by
    simpa [prefixWord, tailWord_760506, baseEnd_760506] using wordTrace_append hprefix tailTrace_760506
  have hstable : (prefixWord ++ tailWord_760506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760506).length < 2 ^ (prefixWord ++ tailWord_760506).sum := by decide
  have hdescent : baseEnd_760506 < baseStart_760506 := by decide
  rcases family_descends (prefixWord ++ tailWord_760506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760519 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 6, 4]
def baseStart_760519 : Nat := 118140960795 + 760519 * 2 ^ 59
def prefixEnd_760519 : Nat := 4983230072969 + 3 ^ 40 * 760519 * 2
def baseEnd_760519 : Nat := 260341195917876799743295

theorem tailTrace_760519 : CollatzResearch.WordTrace tailWord_760519 prefixEnd_760519 260341195917876799743295 := by
  unfold tailWord_760519
  simp only [CollatzResearch.WordTrace]
  refine ⟨27738406731777024149532611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18492271154518016099688407 27738406731777024149532611)
  ·
    refine ⟨41607610097665536224298917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27738406731777024149532611 41607610097665536224298917)
    ·
      refine ⟨7801426893312288042056047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41607610097665536224298917 7801426893312288042056047)
      ·
        refine ⟨11702140339968432063084071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7801426893312288042056047 11702140339968432063084071)
        ·
          refine ⟨17553210509952648094626107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11702140339968432063084071 17553210509952648094626107)
          ·
            refine ⟨26329815764928972141939161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17553210509952648094626107 26329815764928972141939161)
            ·
              refine ⟨19747361823696729106454371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26329815764928972141939161 19747361823696729106454371)
              ·
                refine ⟨29621042735545093659681557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19747361823696729106454371 29621042735545093659681557)
                ·
                  refine ⟨1388486378228676265297573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29621042735545093659681557 1388486378228676265297573)
                  ·
                    refine ⟨260341195917876799743295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1388486378228676265297573 260341195917876799743295)
                    ·
                      rfl

theorem cell22_760519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_760519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760519 prefixEnd_760519 := by exact prefixLift 760519
  have htrace : WordTrace (prefixWord ++ tailWord_760519) baseStart_760519 baseEnd_760519 := by
    simpa [prefixWord, tailWord_760519, baseEnd_760519] using wordTrace_append hprefix tailTrace_760519
  have hstable : (prefixWord ++ tailWord_760519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760519).length < 2 ^ (prefixWord ++ tailWord_760519).sum := by decide
  have hdescent : baseEnd_760519 < baseStart_760519 := by decide
  rcases family_descends (prefixWord ++ tailWord_760519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760540 : List Nat := [2, 2, 5, 1, 1, 1, 3, 3, 4]
def baseStart_760540 : Nat := 118140960795 + 760540 * 2 ^ 59
def prefixEnd_760540 : Nat := 4983230072969 + 3 ^ 40 * 760540 * 2
def baseEnd_760540 : Nat := 86782794882346581656077

theorem tailTrace_760540 : CollatzResearch.WordTrace tailWord_760540 prefixEnd_760540 86782794882346581656077 := by
  unfold tailWord_760540
  simp only [CollatzResearch.WordTrace]
  refine ⟨13869586332350472368023537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18492781776467296490698049 13869586332350472368023537)
  ·
    refine ⟨10402189749262854276017653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13869586332350472368023537 10402189749262854276017653)
    ·
      refine ⟨975205288993392588376655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10402189749262854276017653 975205288993392588376655)
      ·
        refine ⟨1462807933490088882564983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 975205288993392588376655 1462807933490088882564983)
        ·
          refine ⟨2194211900235133323847475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1462807933490088882564983 2194211900235133323847475)
          ·
            refine ⟨3291317850352699985771213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2194211900235133323847475 3291317850352699985771213)
            ·
              refine ⟨1234244193882262494664205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3291317850352699985771213 1234244193882262494664205)
              ·
                refine ⟨462841572705848435499077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1234244193882262494664205 462841572705848435499077)
                ·
                  refine ⟨86782794882346581656077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 462841572705848435499077 86782794882346581656077)
                  ·
                    rfl

theorem cell22_760540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 3, 4].length) (baseStart_760540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760540 prefixEnd_760540 := by exact prefixLift 760540
  have htrace : WordTrace (prefixWord ++ tailWord_760540) baseStart_760540 baseEnd_760540 := by
    simpa [prefixWord, tailWord_760540, baseEnd_760540] using wordTrace_append hprefix tailTrace_760540
  have hstable : (prefixWord ++ tailWord_760540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760540).length < 2 ^ (prefixWord ++ tailWord_760540).sum := by decide
  have hdescent : baseEnd_760540 < baseStart_760540 := by decide
  rcases family_descends (prefixWord ++ tailWord_760540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760624 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 10]
def baseStart_760624 : Nat := 118140960795 + 760624 * 2 ^ 59
def prefixEnd_760624 : Nat := 4983230072969 + 3 ^ 40 * 760624 * 2
def baseEnd_760624 : Nat := 86792379854563841955991

theorem tailTrace_760624 : CollatzResearch.WordTrace tailWord_760624 prefixEnd_760624 86792379854563841955991 := by
  unfold tailWord_760624
  simp only [CollatzResearch.WordTrace]
  refine ⟨13871118198198313541052463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18494824264264418054736617 13871118198198313541052463)
  ·
    refine ⟨20806677297297470311578695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13871118198198313541052463 20806677297297470311578695)
    ·
      refine ⟨31210015945946205467368043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20806677297297470311578695 31210015945946205467368043)
      ·
        refine ⟨46815023918919308201052065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31210015945946205467368043 46815023918919308201052065)
        ·
          refine ⟨35111267939189481150789049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46815023918919308201052065 35111267939189481150789049)
          ·
            refine ⟨26333450954392110863091787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35111267939189481150789049 26333450954392110863091787)
            ·
              refine ⟨39500176431588166294637681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26333450954392110863091787 39500176431588166294637681)
              ·
                refine ⟨29625132323691124720978261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39500176431588166294637681 29625132323691124720978261)
                ·
                  refine ⟨86792379854563841955991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 29625132323691124720978261 86792379854563841955991)
                  ·
                    rfl

theorem cell22_760624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 10].length) (baseStart_760624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760624 prefixEnd_760624 := by exact prefixLift 760624
  have htrace : WordTrace (prefixWord ++ tailWord_760624) baseStart_760624 baseEnd_760624 := by
    simpa [prefixWord, tailWord_760624, baseEnd_760624] using wordTrace_append hprefix tailTrace_760624
  have hstable : (prefixWord ++ tailWord_760624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760624).length < 2 ^ (prefixWord ++ tailWord_760624).sum := by decide
  have hdescent : baseEnd_760624 < baseStart_760624 := by decide
  rcases family_descends (prefixWord ++ tailWord_760624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760626 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 5, 4]
def baseStart_760626 : Nat := 118140960795 + 760626 * 2 ^ 59
def prefixEnd_760626 : Nat := 4983230072969 + 3 ^ 40 * 760626 * 2
def baseEnd_760626 : Nat := 260377824204564187317967

theorem tailTrace_760626 : CollatzResearch.WordTrace tailWord_760626 prefixEnd_760626 260377824204564187317967 := by
  unfold tailWord_760626
  simp only [CollatzResearch.WordTrace]
  refine ⟨6935577335597345355919433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18494872894926254282451821 6935577335597345355919433)
  ·
    refine ⟨5201683001698009016939575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6935577335597345355919433 5201683001698009016939575)
    ·
      refine ⟨7802524502547013525409363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5201683001698009016939575 7802524502547013525409363)
      ·
        refine ⟨11703786753820520288114045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7802524502547013525409363 11703786753820520288114045)
        ·
          refine ⟨4388920032682695108042767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11703786753820520288114045 4388920032682695108042767)
          ·
            refine ⟨6583380049024042662064151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4388920032682695108042767 6583380049024042662064151)
            ·
              refine ⟨9875070073536063993096227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6583380049024042662064151 9875070073536063993096227)
              ·
                refine ⟨14812605110304095989644341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9875070073536063993096227 14812605110304095989644341)
                ·
                  refine ⟨1388681729091008999029157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14812605110304095989644341 1388681729091008999029157)
                  ·
                    refine ⟨260377824204564187317967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1388681729091008999029157 260377824204564187317967)
                    ·
                      rfl

theorem cell22_760626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_760626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760626 prefixEnd_760626 := by exact prefixLift 760626
  have htrace : WordTrace (prefixWord ++ tailWord_760626) baseStart_760626 baseEnd_760626 := by
    simpa [prefixWord, tailWord_760626, baseEnd_760626] using wordTrace_append hprefix tailTrace_760626
  have hstable : (prefixWord ++ tailWord_760626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760626).length < 2 ^ (prefixWord ++ tailWord_760626).sum := by decide
  have hdescent : baseEnd_760626 < baseStart_760626 := by decide
  rcases family_descends (prefixWord ++ tailWord_760626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760656 : List Nat := [2, 1, 1, 1, 1, 4, 4, 2, 1, 5]
def baseStart_760656 : Nat := 118140960795 + 760656 * 2 ^ 59
def prefixEnd_760656 : Nat := 4983230072969 + 3 ^ 40 * 760656 * 2
def baseEnd_760656 : Nat := 260388093817654109067875

theorem tailTrace_760656 : CollatzResearch.WordTrace tailWord_760656 prefixEnd_760656 260388093817654109067875 := by
  unfold tailWord_760656
  simp only [CollatzResearch.WordTrace]
  refine ⟨13871701766140348273634911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18495602354853797698179881 13871701766140348273634911)
  ·
    refine ⟨20807552649210522410452367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13871701766140348273634911 20807552649210522410452367)
    ·
      refine ⟨31211328973815783615678551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20807552649210522410452367 31211328973815783615678551)
      ·
        refine ⟨46816993460723675423517827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31211328973815783615678551 46816993460723675423517827)
        ·
          refine ⟨70225490191085513135276741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46816993460723675423517827 70225490191085513135276741)
          ·
            refine ⟨13167279410828533712864389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70225490191085513135276741 13167279410828533712864389)
            ·
              refine ⟨2468864889530350071162073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13167279410828533712864389 2468864889530350071162073)
              ·
                refine ⟨1851648667147762553371555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2468864889530350071162073 1851648667147762553371555)
                ·
                  refine ⟨2777473000721643830057333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1851648667147762553371555 2777473000721643830057333)
                  ·
                    refine ⟨260388093817654109067875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2777473000721643830057333 260388093817654109067875)
                    ·
                      rfl

theorem cell22_760656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 1, 5].length) (baseStart_760656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760656 prefixEnd_760656 := by exact prefixLift 760656
  have htrace : WordTrace (prefixWord ++ tailWord_760656) baseStart_760656 baseEnd_760656 := by
    simpa [prefixWord, tailWord_760656, baseEnd_760656] using wordTrace_append hprefix tailTrace_760656
  have hstable : (prefixWord ++ tailWord_760656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760656).length < 2 ^ (prefixWord ++ tailWord_760656).sum := by decide
  have hdescent : baseEnd_760656 < baseStart_760656 := by decide
  rcases family_descends (prefixWord ++ tailWord_760656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760660 : List Nat := [2, 4, 1, 1, 4, 1, 1, 3, 1, 4]
def baseStart_760660 : Nat := 118140960795 + 760660 * 2 ^ 59
def prefixEnd_760660 : Nat := 4983230072969 + 3 ^ 40 * 760660 * 2
def baseEnd_760660 : Nat := 260389463099399431967863

theorem tailTrace_760660 : CollatzResearch.WordTrace tailWord_760660 prefixEnd_760660 260389463099399431967863 := by
  unfold tailWord_760660
  simp only [CollatzResearch.WordTrace]
  refine ⟨13871774712133102615207717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18495699616177470153610289 13871774712133102615207717)
  ·
    refine ⟨2600957758524956740351447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13871774712133102615207717 2600957758524956740351447)
    ·
      refine ⟨3901436637787435110527171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2600957758524956740351447 3901436637787435110527171)
      ·
        refine ⟨5852154956681152665790757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3901436637787435110527171 5852154956681152665790757)
        ·
          refine ⟨1097279054377716124835767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5852154956681152665790757 1097279054377716124835767)
          ·
            refine ⟨1645918581566574187253651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1097279054377716124835767 1645918581566574187253651)
            ·
              refine ⟨2468877872349861280880477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1645918581566574187253651 2468877872349861280880477)
              ·
                refine ⟨925829202131197980330179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2468877872349861280880477 925829202131197980330179)
                ·
                  refine ⟨1388743803196796970495269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 925829202131197980330179 1388743803196796970495269)
                  ·
                    refine ⟨260389463099399431967863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1388743803196796970495269 260389463099399431967863)
                    ·
                      rfl

theorem cell22_760660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_760660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760660 prefixEnd_760660 := by exact prefixLift 760660
  have htrace : WordTrace (prefixWord ++ tailWord_760660) baseStart_760660 baseEnd_760660 := by
    simpa [prefixWord, tailWord_760660, baseEnd_760660] using wordTrace_append hprefix tailTrace_760660
  have hstable : (prefixWord ++ tailWord_760660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760660).length < 2 ^ (prefixWord ++ tailWord_760660).sum := by decide
  have hdescent : baseEnd_760660 < baseStart_760660 := by decide
  rcases family_descends (prefixWord ++ tailWord_760660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760671 : List Nat := [1, 1, 2, 3, 1, 3, 2, 1, 4, 4]
def baseStart_760671 : Nat := 118140960795 + 760671 * 2 ^ 59
def prefixEnd_760671 : Nat := 4983230072969 + 3 ^ 40 * 760671 * 2
def baseEnd_760671 : Nat := 260393228624199069942829

theorem tailTrace_760671 : CollatzResearch.WordTrace tailWord_760671 prefixEnd_760671 260393228624199069942829 := by
  unfold tailWord_760671
  simp only [CollatzResearch.WordTrace]
  refine ⟨27743950627226354109065867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18495967084817569406043911 27743950627226354109065867)
  ·
    refine ⟨41615925940839531163598801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27743950627226354109065867 41615925940839531163598801)
    ·
      refine ⟨31211944455629648372699101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41615925940839531163598801 31211944455629648372699101)
      ·
        refine ⟨11704479170861118139762163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31211944455629648372699101 11704479170861118139762163)
        ·
          refine ⟨17556718756291677209643245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11704479170861118139762163 17556718756291677209643245)
          ·
            refine ⟨6583769533609378953616217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17556718756291677209643245 6583769533609378953616217)
            ·
              refine ⟨4937827150207034215212163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6583769533609378953616217 4937827150207034215212163)
              ·
                refine ⟨7406740725310551322818245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4937827150207034215212163 7406740725310551322818245)
                ·
                  refine ⟨1388763885995728373028421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7406740725310551322818245 1388763885995728373028421)
                  ·
                    refine ⟨260393228624199069942829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1388763885995728373028421 260393228624199069942829)
                    ·
                      rfl

theorem cell22_760671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 4].length) (baseStart_760671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760671 prefixEnd_760671 := by exact prefixLift 760671
  have htrace : WordTrace (prefixWord ++ tailWord_760671) baseStart_760671 baseEnd_760671 := by
    simpa [prefixWord, tailWord_760671, baseEnd_760671] using wordTrace_append hprefix tailTrace_760671
  have hstable : (prefixWord ++ tailWord_760671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760671).length < 2 ^ (prefixWord ++ tailWord_760671).sum := by decide
  have hdescent : baseEnd_760671 < baseStart_760671 := by decide
  rcases family_descends (prefixWord ++ tailWord_760671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760673 : List Nat := [1, 2, 3, 1, 1, 1, 2, 6, 2, 3]
def baseStart_760673 : Nat := 118140960795 + 760673 * 2 ^ 59
def prefixEnd_760673 : Nat := 4983230072969 + 3 ^ 40 * 760673 * 2
def baseEnd_760673 : Nat := 260393913265071731392823

theorem tailTrace_760673 : CollatzResearch.WordTrace tailWord_760673 prefixEnd_760673 260393913265071731392823 := by
  unfold tailWord_760673
  simp only [CollatzResearch.WordTrace]
  refine ⟨27744023573219108450638673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18496015715479405633759115 27744023573219108450638673)
  ·
    refine ⟨20808017679914331337979005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27744023573219108450638673 20808017679914331337979005)
    ·
      refine ⟨7803006629967874251742127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20808017679914331337979005 7803006629967874251742127)
      ·
        refine ⟨11704509944951811377613191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7803006629967874251742127 11704509944951811377613191)
        ·
          refine ⟨17556764917427717066419787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11704509944951811377613191 17556764917427717066419787)
          ·
            refine ⟨26335147376141575599629681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17556764917427717066419787 26335147376141575599629681)
            ·
              refine ⟨19751360532106181699722261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26335147376141575599629681 19751360532106181699722261)
              ·
                refine ⟨925845024942477267174481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19751360532106181699722261 925845024942477267174481)
                ·
                  refine ⟨694383768706857950380861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 925845024942477267174481 694383768706857950380861)
                  ·
                    refine ⟨260393913265071731392823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 694383768706857950380861 260393913265071731392823)
                    ·
                      rfl

theorem cell22_760673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_760673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760673 prefixEnd_760673 := by exact prefixLift 760673
  have htrace : WordTrace (prefixWord ++ tailWord_760673) baseStart_760673 baseEnd_760673 := by
    simpa [prefixWord, tailWord_760673, baseEnd_760673] using wordTrace_append hprefix tailTrace_760673
  have hstable : (prefixWord ++ tailWord_760673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760673).length < 2 ^ (prefixWord ++ tailWord_760673).sum := by decide
  have hdescent : baseEnd_760673 < baseStart_760673 := by decide
  rcases family_descends (prefixWord ++ tailWord_760673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760726 : List Nat := [5, 3, 1, 1, 1, 2, 3, 2, 4]
def baseStart_760726 : Nat := 118140960795 + 760726 * 2 ^ 59
def prefixEnd_760726 : Nat := 4983230072969 + 3 ^ 40 * 760726 * 2
def baseEnd_760726 : Nat := 86804018749399086605887

theorem tailTrace_760726 : CollatzResearch.WordTrace tailWord_760726 prefixEnd_760726 86804018749399086605887 := by
  unfold tailWord_760726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1734122290126693656394877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18497304428018065668212021 1734122290126693656394877)
  ·
    refine ⟨650295858797510121148079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1734122290126693656394877 650295858797510121148079)
    ·
      refine ⟨975443788196265181722119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 650295858797510121148079 975443788196265181722119)
      ·
        refine ⟨1463165682294397772583179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 975443788196265181722119 1463165682294397772583179)
        ·
          refine ⟨2194748523441596658874769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1463165682294397772583179 2194748523441596658874769)
          ·
            refine ⟨1646061392581197494156077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2194748523441596658874769 1646061392581197494156077)
            ·
              refine ⟨617273022217949060308529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1646061392581197494156077 617273022217949060308529)
              ·
                refine ⟨462954766663461795231397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 617273022217949060308529 462954766663461795231397)
                ·
                  refine ⟨86804018749399086605887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 462954766663461795231397 86804018749399086605887)
                  ·
                    rfl

theorem cell22_760726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_760726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760726 prefixEnd_760726 := by exact prefixLift 760726
  have htrace : WordTrace (prefixWord ++ tailWord_760726) baseStart_760726 baseEnd_760726 := by
    simpa [prefixWord, tailWord_760726, baseEnd_760726] using wordTrace_append hprefix tailTrace_760726
  have hstable : (prefixWord ++ tailWord_760726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760726).length < 2 ^ (prefixWord ++ tailWord_760726).sum := by decide
  have hdescent : baseEnd_760726 < baseStart_760726 := by decide
  rcases family_descends (prefixWord ++ tailWord_760726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760735 : List Nat := [1, 1, 2, 5, 2, 1, 3, 1, 3, 3]
def baseStart_760735 : Nat := 118140960795 + 760735 * 2 ^ 59
def prefixEnd_760735 : Nat := 4983230072969 + 3 ^ 40 * 760735 * 2
def baseEnd_760735 : Nat := 260415137132124236342633

theorem tailTrace_760735 : CollatzResearch.WordTrace tailWord_760735 prefixEnd_760735 260415137132124236342633 := by
  unfold tailWord_760735
  simp only [CollatzResearch.WordTrace]
  refine ⟨27746284898994493039395659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18497523265996328692930439 27746284898994493039395659)
  ·
    refine ⟨41619427348491739559093489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27746284898994493039395659 41619427348491739559093489)
    ·
      refine ⟨31214570511368804669320117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41619427348491739559093489 31214570511368804669320117)
      ·
        refine ⟨2926365985440825437748761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31214570511368804669320117 2926365985440825437748761)
        ·
          refine ⟨2194774489080619078311571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2926365985440825437748761 2194774489080619078311571)
          ·
            refine ⟨3292161733620928617467357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2194774489080619078311571 3292161733620928617467357)
            ·
              refine ⟨1234560650107848231550259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3292161733620928617467357 1234560650107848231550259)
              ·
                refine ⟨1851840975161772347325389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1234560650107848231550259 1851840975161772347325389)
                ·
                  refine ⟨694440365685664630247021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1851840975161772347325389 694440365685664630247021)
                  ·
                    refine ⟨260415137132124236342633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 694440365685664630247021 260415137132124236342633)
                    ·
                      rfl

theorem cell22_760735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 3, 3].length) (baseStart_760735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760735 prefixEnd_760735 := by exact prefixLift 760735
  have htrace : WordTrace (prefixWord ++ tailWord_760735) baseStart_760735 baseEnd_760735 := by
    simpa [prefixWord, tailWord_760735, baseEnd_760735] using wordTrace_append hprefix tailTrace_760735
  have hstable : (prefixWord ++ tailWord_760735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760735).length < 2 ^ (prefixWord ++ tailWord_760735).sum := by decide
  have hdescent : baseEnd_760735 < baseStart_760735 := by decide
  rcases family_descends (prefixWord ++ tailWord_760735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760786 : List Nat := [3, 2, 2, 3, 1, 3, 2, 2, 1, 3]
def baseStart_760786 : Nat := 118140960795 + 760786 * 2 ^ 59
def prefixEnd_760786 : Nat := 4983230072969 + 3 ^ 40 * 760786 * 2
def baseEnd_760786 : Nat := 260432595474377103317477

theorem tailTrace_760786 : CollatzResearch.WordTrace tailWord_760786 prefixEnd_760786 260432595474377103317477 := by
  unfold tailWord_760786
  simp only [CollatzResearch.WordTrace]
  refine ⟨6937036255452432187375553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18498763347873152499668141 6937036255452432187375553)
  ·
    refine ⟨5202777191589324140531665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6937036255452432187375553 5202777191589324140531665)
    ·
      refine ⟨3902082893691993105398749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5202777191589324140531665 3902082893691993105398749)
      ·
        refine ⟨1463281085134497414524531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3902082893691993105398749 1463281085134497414524531)
        ·
          refine ⟨2194921627701746121786797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1463281085134497414524531 2194921627701746121786797)
          ·
            refine ⟨823095610388154795670049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2194921627701746121786797 823095610388154795670049)
            ·
              refine ⟨617321707791116096752537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 823095610388154795670049 617321707791116096752537)
              ·
                refine ⟨462991280843337072564403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 617321707791116096752537 462991280843337072564403)
                ·
                  refine ⟨694486921265005608846605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 462991280843337072564403 694486921265005608846605)
                  ·
                    refine ⟨260432595474377103317477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 694486921265005608846605 260432595474377103317477)
                    ·
                      rfl

theorem cell22_760786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_760786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760786 prefixEnd_760786 := by exact prefixLift 760786
  have htrace : WordTrace (prefixWord ++ tailWord_760786) baseStart_760786 baseEnd_760786 := by
    simpa [prefixWord, tailWord_760786, baseEnd_760786] using wordTrace_append hprefix tailTrace_760786
  have hstable : (prefixWord ++ tailWord_760786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760786).length < 2 ^ (prefixWord ++ tailWord_760786).sum := by decide
  have hdescent : baseEnd_760786 < baseStart_760786 := by decide
  rcases family_descends (prefixWord ++ tailWord_760786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760808 : List Nat := [2, 1, 4, 1, 1, 1, 3, 3, 1, 5]
def baseStart_760808 : Nat := 118140960795 + 760808 * 2 ^ 59
def prefixEnd_760808 : Nat := 4983230072969 + 3 ^ 40 * 760808 * 2
def baseEnd_760808 : Nat := 260440126523976379267409

theorem tailTrace_760808 : CollatzResearch.WordTrace tailWord_760808 prefixEnd_760808 260440126523976379267409 := by
  unfold tailWord_760808
  simp only [CollatzResearch.WordTrace]
  refine ⟨13874473713865013253401539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18499298285153351004535385 13874473713865013253401539)
  ·
    refine ⟨20811710570797519880102309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13874473713865013253401539 20811710570797519880102309)
    ·
      refine ⟨3902195732024534977519183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20811710570797519880102309 3902195732024534977519183)
      ·
        refine ⟨5853293598036802466278775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3902195732024534977519183 5853293598036802466278775)
        ·
          refine ⟨8779940397055203699418163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5853293598036802466278775 8779940397055203699418163)
          ·
            refine ⟨13169910595582805549127245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8779940397055203699418163 13169910595582805549127245)
            ·
              refine ⟨4938716473343552080922717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13169910595582805549127245 4938716473343552080922717)
              ·
                refine ⟨1852018677503832030346019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4938716473343552080922717 1852018677503832030346019)
                ·
                  refine ⟨2778028016255748045519029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1852018677503832030346019 2778028016255748045519029)
                  ·
                    refine ⟨260440126523976379267409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2778028016255748045519029 260440126523976379267409)
                    ·
                      rfl

theorem cell22_760808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_760808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760808 prefixEnd_760808 := by exact prefixLift 760808
  have htrace : WordTrace (prefixWord ++ tailWord_760808) baseStart_760808 baseEnd_760808 := by
    simpa [prefixWord, tailWord_760808, baseEnd_760808] using wordTrace_append hprefix tailTrace_760808
  have hstable : (prefixWord ++ tailWord_760808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760808).length < 2 ^ (prefixWord ++ tailWord_760808).sum := by decide
  have hdescent : baseEnd_760808 < baseStart_760808 := by decide
  rcases family_descends (prefixWord ++ tailWord_760808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760820 : List Nat := [2, 6, 2, 1, 1, 1, 2, 3, 1, 3]
def baseStart_760820 : Nat := 118140960795 + 760820 * 2 ^ 59
def prefixEnd_760820 : Nat := 4983230072969 + 3 ^ 40 * 760820 * 2
def baseEnd_760820 : Nat := 260444234369212347967373

theorem tailTrace_760820 : CollatzResearch.WordTrace tailWord_760820 prefixEnd_760820 260444234369212347967373 := by
  unfold tailWord_760820
  simp only [CollatzResearch.WordTrace]
  refine ⟨13874692551843276278119957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18499590069124368370826609 13874692551843276278119957)
  ·
    refine ⟨650376213367653575536873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13874692551843276278119957 650376213367653575536873)
    ·
      refine ⟨487782160025740181652655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 650376213367653575536873 487782160025740181652655)
      ·
        refine ⟨731673240038610272478983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487782160025740181652655 731673240038610272478983)
        ·
          refine ⟨1097509860057915408718475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 731673240038610272478983 1097509860057915408718475)
          ·
            refine ⟨1646264790086873113077713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1097509860057915408718475 1646264790086873113077713)
            ·
              refine ⟨1234698592565154834808285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1646264790086873113077713 1234698592565154834808285)
              ·
                refine ⟨463011972211933063053107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1234698592565154834808285 463011972211933063053107)
                ·
                  refine ⟨694517958317899594579661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 463011972211933063053107 694517958317899594579661)
                  ·
                    refine ⟨260444234369212347967373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 694517958317899594579661 260444234369212347967373)
                    ·
                      rfl

theorem cell22_760820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_760820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760820 prefixEnd_760820 := by exact prefixLift 760820
  have htrace : WordTrace (prefixWord ++ tailWord_760820) baseStart_760820 baseEnd_760820 := by
    simpa [prefixWord, tailWord_760820, baseEnd_760820] using wordTrace_append hprefix tailTrace_760820
  have hstable : (prefixWord ++ tailWord_760820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760820).length < 2 ^ (prefixWord ++ tailWord_760820).sum := by decide
  have hdescent : baseEnd_760820 < baseStart_760820 := by decide
  rcases family_descends (prefixWord ++ tailWord_760820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760842 : List Nat := [3, 1, 2, 2, 3, 1, 3, 2, 2, 3]
def baseStart_760842 : Nat := 118140960795 + 760842 * 2 ^ 59
def prefixEnd_760842 : Nat := 4983230072969 + 3 ^ 40 * 760842 * 2
def baseEnd_760842 : Nat := 260451765418811623917305

theorem tailTrace_760842 : CollatzResearch.WordTrace tailWord_760842 prefixEnd_760842 260451765418811623917305 := by
  unfold tailWord_760842
  simp only [CollatzResearch.WordTrace]
  refine ⟨6937546877401712578385195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18500125006404566875693853 6937546877401712578385195)
  ·
    refine ⟨10406320316102568867577793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6937546877401712578385195 10406320316102568867577793)
    ·
      refine ⟨7804740237076926650683345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10406320316102568867577793 7804740237076926650683345)
      ·
        refine ⟨5853555177807694988012509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7804740237076926650683345 5853555177807694988012509)
        ·
          refine ⟨2195083191677885620504691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5853555177807694988012509 2195083191677885620504691)
          ·
            refine ⟨3292624787516828430757037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2195083191677885620504691 3292624787516828430757037)
            ·
              refine ⟨1234734295318810661533889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3292624787516828430757037 1234734295318810661533889)
              ·
                refine ⟨926050721489107996150417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1234734295318810661533889 926050721489107996150417)
                ·
                  refine ⟨694538041116830997112813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 926050721489107996150417 694538041116830997112813)
                  ·
                    refine ⟨260451765418811623917305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 694538041116830997112813 260451765418811623917305)
                    ·
                      rfl

theorem cell22_760842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_760842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760842 prefixEnd_760842 := by exact prefixLift 760842
  have htrace : WordTrace (prefixWord ++ tailWord_760842) baseStart_760842 baseEnd_760842 := by
    simpa [prefixWord, tailWord_760842, baseEnd_760842] using wordTrace_append hprefix tailTrace_760842
  have hstable : (prefixWord ++ tailWord_760842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760842).length < 2 ^ (prefixWord ++ tailWord_760842).sum := by decide
  have hdescent : baseEnd_760842 < baseStart_760842 := by decide
  rcases family_descends (prefixWord ++ tailWord_760842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760904 : List Nat := [2, 1, 3, 1, 1, 1, 7, 2, 1, 3]
def baseStart_760904 : Nat := 118140960795 + 760904 * 2 ^ 59
def prefixEnd_760904 : Nat := 4983230072969 + 3 ^ 40 * 760904 * 2
def baseEnd_760904 : Nat := 260472989285864128867115

theorem tailTrace_760904 : CollatzResearch.WordTrace tailWord_760904 prefixEnd_760904 260472989285864128867115 := by
  unfold tailWord_760904
  simp only [CollatzResearch.WordTrace]
  refine ⟨13876224417691117451148883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18501632556921489934865177 13876224417691117451148883)
  ·
    refine ⟨20814336626536676176723325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13876224417691117451148883 20814336626536676176723325)
    ·
      refine ⟨7805376234951253566271247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20814336626536676176723325 7805376234951253566271247)
      ·
        refine ⟨11708064352426880349406871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7805376234951253566271247 11708064352426880349406871)
        ·
          refine ⟨17562096528640320524110307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11708064352426880349406871 17562096528640320524110307)
          ·
            refine ⟨26343144792960480786165461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17562096528640320524110307 26343144792960480786165461)
            ·
              refine ⟨617417456085011268425753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 26343144792960480786165461 617417456085011268425753)
              ·
                refine ⟨463063092063758451319315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 617417456085011268425753 463063092063758451319315)
                ·
                  refine ⟨694594638095637676978973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 463063092063758451319315 694594638095637676978973)
                  ·
                    refine ⟨260472989285864128867115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 694594638095637676978973 260472989285864128867115)
                    ·
                      rfl

theorem cell22_760904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 2, 1, 3].length) (baseStart_760904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760904 prefixEnd_760904 := by exact prefixLift 760904
  have htrace : WordTrace (prefixWord ++ tailWord_760904) baseStart_760904 baseEnd_760904 := by
    simpa [prefixWord, tailWord_760904, baseEnd_760904] using wordTrace_append hprefix tailTrace_760904
  have hstable : (prefixWord ++ tailWord_760904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760904).length < 2 ^ (prefixWord ++ tailWord_760904).sum := by decide
  have hdescent : baseEnd_760904 < baseStart_760904 := by decide
  rcases family_descends (prefixWord ++ tailWord_760904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760928 : List Nat := [2, 1, 1, 3, 2, 2, 2, 1, 8]
def baseStart_760928 : Nat := 118140960795 + 760928 * 2 ^ 59
def prefixEnd_760928 : Nat := 4983230072969 + 3 ^ 40 * 760928 * 2
def baseEnd_760928 : Nat := 86827068325445355422347

theorem tailTrace_760928 : CollatzResearch.WordTrace tailWord_760928 prefixEnd_760928 86827068325445355422347 := by
  unfold tailWord_760928
  simp only [CollatzResearch.WordTrace]
  refine ⟨13876662093647643500585719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18502216124863524667447625 13876662093647643500585719)
  ·
    refine ⟨20814993140471465250878579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13876662093647643500585719 20814993140471465250878579)
    ·
      refine ⟨31222489710707197876317869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20814993140471465250878579 31222489710707197876317869)
      ·
        refine ⟨11708433641515199203619201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31222489710707197876317869 11708433641515199203619201)
        ·
          refine ⟨8781325231136399402714401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11708433641515199203619201 8781325231136399402714401)
          ·
            refine ⟨6585993923352299552035801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8781325231136399402714401 6585993923352299552035801)
            ·
              refine ⟨4939495442514224664026851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6585993923352299552035801 4939495442514224664026851)
              ·
                refine ⟨7409243163771336996040277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4939495442514224664026851 7409243163771336996040277)
                ·
                  refine ⟨86827068325445355422347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7409243163771336996040277 86827068325445355422347)
                  ·
                    rfl

theorem cell22_760928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 8].length) (baseStart_760928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760928 prefixEnd_760928 := by exact prefixLift 760928
  have htrace : WordTrace (prefixWord ++ tailWord_760928) baseStart_760928 baseEnd_760928 := by
    simpa [prefixWord, tailWord_760928, baseEnd_760928] using wordTrace_append hprefix tailTrace_760928
  have hstable : (prefixWord ++ tailWord_760928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760928).length < 2 ^ (prefixWord ++ tailWord_760928).sum := by decide
  have hdescent : baseEnd_760928 < baseStart_760928 := by decide
  rcases family_descends (prefixWord ++ tailWord_760928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_760960 : List Nat := [2, 1, 1, 2, 1, 3, 2, 3, 4, 3]
def baseStart_760960 : Nat := 118140960795 + 760960 * 2 ^ 59
def prefixEnd_760960 : Nat := 4983230072969 + 3 ^ 40 * 760960 * 2
def baseEnd_760960 : Nat := 260492159230298649466943

theorem tailTrace_760960 : CollatzResearch.WordTrace tailWord_760960 prefixEnd_760960 260492159230298649466943 := by
  unfold tailWord_760960
  simp only [CollatzResearch.WordTrace]
  refine ⟨13877245661589678233168167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18502994215452904310890889 13877245661589678233168167)
  ·
    refine ⟨20815868492384517349752251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13877245661589678233168167 20815868492384517349752251)
    ·
      refine ⟨31223802738576776024628377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20815868492384517349752251 31223802738576776024628377)
      ·
        refine ⟨23417852053932582018471283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31223802738576776024628377 23417852053932582018471283)
        ·
          refine ⟨35126778080898873027706925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23417852053932582018471283 35126778080898873027706925)
          ·
            refine ⟨13172541780337077385390097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35126778080898873027706925 13172541780337077385390097)
            ·
              refine ⟨9879406335252808039042573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13172541780337077385390097 9879406335252808039042573)
              ·
                refine ⟨3704777375719803014640965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9879406335252808039042573 3704777375719803014640965)
                ·
                  refine ⟨694645757947463065245181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3704777375719803014640965 694645757947463065245181)
                  ·
                    refine ⟨260492159230298649466943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 694645757947463065245181 260492159230298649466943)
                    ·
                      rfl

theorem cell22_760960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 4, 3].length) (baseStart_760960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_760960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_760960 prefixEnd_760960 := by exact prefixLift 760960
  have htrace : WordTrace (prefixWord ++ tailWord_760960) baseStart_760960 baseEnd_760960 := by
    simpa [prefixWord, tailWord_760960, baseEnd_760960] using wordTrace_append hprefix tailTrace_760960
  have hstable : (prefixWord ++ tailWord_760960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_760960).length < 2 ^ (prefixWord ++ tailWord_760960).sum := by decide
  have hdescent : baseEnd_760960 < baseStart_760960 := by decide
  rcases family_descends (prefixWord ++ tailWord_760960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761056 : List Nat := [2, 1, 1, 3, 1, 6, 1, 3, 1, 3]
def baseStart_761056 : Nat := 118140960795 + 761056 * 2 ^ 59
def prefixEnd_761056 : Nat := 4983230072969 + 3 ^ 40 * 761056 * 2
def baseEnd_761056 : Nat := 260525021992186399066649

theorem tailTrace_761056 : CollatzResearch.WordTrace tailWord_761056 prefixEnd_761056 260525021992186399066649 := by
  unfold tailWord_761056
  simp only [CollatzResearch.WordTrace]
  refine ⟨13878996365415782430915511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18505328487221043241220681 13878996365415782430915511)
  ·
    refine ⟨20818494548123673646373267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13878996365415782430915511 20818494548123673646373267)
    ·
      refine ⟨31227741822185510469559901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20818494548123673646373267 31227741822185510469559901)
      ·
        refine ⟨11710403183319566426084963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31227741822185510469559901 11710403183319566426084963)
        ·
          refine ⟨17565604774979349639127445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11710403183319566426084963 17565604774979349639127445)
          ·
            refine ⟨823387723827157014334099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17565604774979349639127445 823387723827157014334099)
            ·
              refine ⟨1235081585740735521501149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 823387723827157014334099 1235081585740735521501149)
              ·
                refine ⟨463155594652775820562931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1235081585740735521501149 463155594652775820562931)
                ·
                  refine ⟨694733391979163730844397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 463155594652775820562931 694733391979163730844397)
                  ·
                    refine ⟨260525021992186399066649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 694733391979163730844397 260525021992186399066649)
                    ·
                      rfl

theorem cell22_761056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 3, 1, 3].length) (baseStart_761056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761056 prefixEnd_761056 := by exact prefixLift 761056
  have htrace : WordTrace (prefixWord ++ tailWord_761056) baseStart_761056 baseEnd_761056 := by
    simpa [prefixWord, tailWord_761056, baseEnd_761056] using wordTrace_append hprefix tailTrace_761056
  have hstable : (prefixWord ++ tailWord_761056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761056).length < 2 ^ (prefixWord ++ tailWord_761056).sum := by decide
  have hdescent : baseEnd_761056 < baseStart_761056 := by decide
  rcases family_descends (prefixWord ++ tailWord_761056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761086 : List Nat := [4, 2, 2, 1, 1, 4, 2, 1, 5]
def baseStart_761086 : Nat := 118140960795 + 761086 * 2 ^ 59
def prefixEnd_761086 : Nat := 4983230072969 + 3 ^ 40 * 761086 * 2
def baseEnd_761086 : Nat := 86845097201758773605519

theorem tailTrace_761086 : CollatzResearch.WordTrace tailWord_761086 prefixEnd_761086 86845097201758773605519 := by
  unfold tailWord_761086
  simp only [CollatzResearch.WordTrace]
  refine ⟨3469885865090359998177889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18506057947148586656948741 3469885865090359998177889)
  ·
    refine ⟨2602414398817769998633417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3469885865090359998177889 2602414398817769998633417)
    ·
      refine ⟨1951810799113327498975063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2602414398817769998633417 1951810799113327498975063)
      ·
        refine ⟨2927716198669991248462595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1951810799113327498975063 2927716198669991248462595)
        ·
          refine ⟨4391574298004986872693893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2927716198669991248462595 4391574298004986872693893)
          ·
            refine ⟨823420180875935038630105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4391574298004986872693893 823420180875935038630105)
            ·
              refine ⟨617565135656951278972579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 823420180875935038630105 617565135656951278972579)
              ·
                refine ⟨926347703485426918458869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 617565135656951278972579 926347703485426918458869)
                ·
                  refine ⟨86845097201758773605519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 926347703485426918458869 86845097201758773605519)
                  ·
                    rfl

theorem cell22_761086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_761086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761086 prefixEnd_761086 := by exact prefixLift 761086
  have htrace : WordTrace (prefixWord ++ tailWord_761086) baseStart_761086 baseEnd_761086 := by
    simpa [prefixWord, tailWord_761086, baseEnd_761086] using wordTrace_append hprefix tailTrace_761086
  have hstable : (prefixWord ++ tailWord_761086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761086).length < 2 ^ (prefixWord ++ tailWord_761086).sum := by decide
  have hdescent : baseEnd_761086 < baseStart_761086 := by decide
  rcases family_descends (prefixWord ++ tailWord_761086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761099 : List Nat := [1, 1, 1, 1, 5, 5, 1, 2, 1, 4]
def baseStart_761099 : Nat := 118140960795 + 761099 * 2 ^ 59
def prefixEnd_761099 : Nat := 4983230072969 + 3 ^ 40 * 761099 * 2
def baseEnd_761099 : Nat := 260539741770948620241517

theorem tailTrace_761099 : CollatzResearch.WordTrace tailWord_761099 prefixEnd_761099 260539741770948620241517 := by
  unfold tailWord_761099
  simp only [CollatzResearch.WordTrace]
  refine ⟨27759561069675783205646351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18506374046450522137097567 27759561069675783205646351)
  ·
    refine ⟨41639341604513674808469527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27759561069675783205646351 41639341604513674808469527)
    ·
      refine ⟨62459012406770512212704291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41639341604513674808469527 62459012406770512212704291)
      ·
        refine ⟨93688518610155768319056437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62459012406770512212704291 93688518610155768319056437)
        ·
          refine ⟨8783298619702103279911541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93688518610155768319056437 8783298619702103279911541)
          ·
            refine ⟨823434245597072182491707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8783298619702103279911541 823434245597072182491707)
            ·
              refine ⟨1235151368395608273737561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 823434245597072182491707 1235151368395608273737561)
              ·
                refine ⟨926363526296706205303171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1235151368395608273737561 926363526296706205303171)
                ·
                  refine ⟨1389545289445059307954757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 926363526296706205303171 1389545289445059307954757)
                  ·
                    refine ⟨260539741770948620241517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1389545289445059307954757 260539741770948620241517)
                    ·
                      rfl

theorem cell22_761099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 4].length) (baseStart_761099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761099 prefixEnd_761099 := by exact prefixLift 761099
  have htrace : WordTrace (prefixWord ++ tailWord_761099) baseStart_761099 baseEnd_761099 := by
    simpa [prefixWord, tailWord_761099, baseEnd_761099] using wordTrace_append hprefix tailTrace_761099
  have hstable : (prefixWord ++ tailWord_761099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761099).length < 2 ^ (prefixWord ++ tailWord_761099).sum := by decide
  have hdescent : baseEnd_761099 < baseStart_761099 := by decide
  rcases family_descends (prefixWord ++ tailWord_761099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761112 : List Nat := [2, 1, 2, 3, 1, 4, 1, 2, 1, 5]
def baseStart_761112 : Nat := 118140960795 + 761112 * 2 ^ 59
def prefixEnd_761112 : Nat := 4983230072969 + 3 ^ 40 * 761112 * 2
def baseEnd_761112 : Nat := 260544191936620919666477

theorem tailTrace_761112 : CollatzResearch.WordTrace tailWord_761112 prefixEnd_761112 260544191936620919666477 := by
  unfold tailWord_761112
  simp only [CollatzResearch.WordTrace]
  refine ⟨13880017609314343212934795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18506690145752457617246393 13880017609314343212934795)
  ·
    refine ⟨20820026413971514819402193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13880017609314343212934795 20820026413971514819402193)
    ·
      refine ⟨15615019810478636114551645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20820026413971514819402193 15615019810478636114551645)
      ·
        refine ⟨5855632428929488542956867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15615019810478636114551645 5855632428929488542956867)
        ·
          refine ⟨8783448643394232814435301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5855632428929488542956867 8783448643394232814435301)
          ·
            refine ⟨1646896620636418652706619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8783448643394232814435301 1646896620636418652706619)
            ·
              refine ⟨2470344930954627979059929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1646896620636418652706619 2470344930954627979059929)
              ·
                refine ⟨1852758698215970984294947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2470344930954627979059929 1852758698215970984294947)
                ·
                  refine ⟨2779138047323956476442421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1852758698215970984294947 2779138047323956476442421)
                  ·
                    refine ⟨260544191936620919666477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2779138047323956476442421 260544191936620919666477)
                    ·
                      rfl

theorem cell22_761112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_761112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761112 prefixEnd_761112 := by exact prefixLift 761112
  have htrace : WordTrace (prefixWord ++ tailWord_761112) baseStart_761112 baseEnd_761112 := by
    simpa [prefixWord, tailWord_761112, baseEnd_761112] using wordTrace_append hprefix tailTrace_761112
  have hstable : (prefixWord ++ tailWord_761112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761112).length < 2 ^ (prefixWord ++ tailWord_761112).sum := by decide
  have hdescent : baseEnd_761112 < baseStart_761112 := by decide
  rcases family_descends (prefixWord ++ tailWord_761112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761125 : List Nat := [1, 3, 1, 2, 4, 11]
def baseStart_761125 : Nat := 118140960795 + 761125 * 2 ^ 59
def prefixEnd_761125 : Nat := 4983230072969 + 3 ^ 40 * 761125 * 2
def baseEnd_761125 : Nat := 3216649902497447149277

theorem tailTrace_761125 : CollatzResearch.WordTrace tailWord_761125 prefixEnd_761125 3216649902497447149277 := by
  unfold tailWord_761125
  simp only [CollatzResearch.WordTrace]
  refine ⟨27760509367581589646092829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18507006245054393097395219 27760509367581589646092829)
  ·
    refine ⟨10410191012843096117284811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27760509367581589646092829 10410191012843096117284811)
    ·
      refine ⟨15615286519264644175927217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10410191012843096117284811 15615286519264644175927217)
      ·
        refine ⟨11711464889448483131945413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15615286519264644175927217 11711464889448483131945413)
        ·
          refine ⟨2195899666771590587239765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11711464889448483131945413 2195899666771590587239765)
          ·
            refine ⟨3216649902497447149277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2195899666771590587239765 3216649902497447149277)
            ·
              rfl

theorem cell22_761125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 11].length) (baseStart_761125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761125 prefixEnd_761125 := by exact prefixLift 761125
  have htrace : WordTrace (prefixWord ++ tailWord_761125) baseStart_761125 baseEnd_761125 := by
    simpa [prefixWord, tailWord_761125, baseEnd_761125] using wordTrace_append hprefix tailTrace_761125
  have hstable : (prefixWord ++ tailWord_761125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761125).length < 2 ^ (prefixWord ++ tailWord_761125).sum := by decide
  have hdescent : baseEnd_761125 < baseStart_761125 := by decide
  rcases family_descends (prefixWord ++ tailWord_761125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761155 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 4, 6]
def baseStart_761155 : Nat := 118140960795 + 761155 * 2 ^ 59
def prefixEnd_761155 : Nat := 4983230072969 + 3 ^ 40 * 761155 * 2
def baseEnd_761155 : Nat := 260558911715383140841345

theorem tailTrace_761155 : CollatzResearch.WordTrace tailWord_761155 prefixEnd_761155 260558911715383140841345 := by
  unfold tailWord_761155
  simp only [CollatzResearch.WordTrace]
  refine ⟨27761603557472904769684919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18507735704981936513123279 27761603557472904769684919)
  ·
    refine ⟨41642405336209357154527379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27761603557472904769684919 41642405336209357154527379)
    ·
      refine ⟨62463608004314035731791069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41642405336209357154527379 62463608004314035731791069)
      ·
        refine ⟨23423853001617763399421651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62463608004314035731791069 23423853001617763399421651)
        ·
          refine ⟨35135779502426645099132477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23423853001617763399421651 35135779502426645099132477)
          ·
            refine ⟨13175917313409991912174679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35135779502426645099132477 13175917313409991912174679)
            ·
              refine ⟨19763875970114987868262019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13175917313409991912174679 19763875970114987868262019)
              ·
                refine ⟨29645813955172481802393029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19763875970114987868262019 29645813955172481802393029)
                ·
                  refine ⟨5558590116594840337948693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29645813955172481802393029 5558590116594840337948693)
                  ·
                    refine ⟨260558911715383140841345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5558590116594840337948693 260558911715383140841345)
                    ·
                      rfl

theorem cell22_761155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 6].length) (baseStart_761155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761155 prefixEnd_761155 := by exact prefixLift 761155
  have htrace : WordTrace (prefixWord ++ tailWord_761155) baseStart_761155 baseEnd_761155 := by
    simpa [prefixWord, tailWord_761155, baseEnd_761155] using wordTrace_append hprefix tailTrace_761155
  have hstable : (prefixWord ++ tailWord_761155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761155).length < 2 ^ (prefixWord ++ tailWord_761155).sum := by decide
  have hdescent : baseEnd_761155 < baseStart_761155 := by decide
  rcases family_descends (prefixWord ++ tailWord_761155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761187 : List Nat := [1, 1, 1, 5, 2, 3, 1, 1, 7]
def baseStart_761187 : Nat := 118140960795 + 761187 * 2 ^ 59
def prefixEnd_761187 : Nat := 4983230072969 + 3 ^ 40 * 761187 * 2
def baseEnd_761187 : Nat := 86856621989781908013749

theorem tailTrace_761187 : CollatzResearch.WordTrace tailWord_761187 prefixEnd_761187 86856621989781908013749 := by
  unfold tailWord_761187
  simp only [CollatzResearch.WordTrace]
  refine ⟨27762770693356974234849815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18508513795571316156566543 27762770693356974234849815)
  ·
    refine ⟨41644156040035461352274723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27762770693356974234849815 41644156040035461352274723)
    ·
      refine ⟨62466234060053192028412085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41644156040035461352274723 62466234060053192028412085)
      ·
        refine ⟨5856209443129986752663633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62466234060053192028412085 5856209443129986752663633)
        ·
          refine ⟨4392157082347490064497725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5856209443129986752663633 4392157082347490064497725)
          ·
            refine ⟨1647058905880308774186647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4392157082347490064497725 1647058905880308774186647)
            ·
              refine ⟨2470588358820463161279971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1647058905880308774186647 2470588358820463161279971)
              ·
                refine ⟨3705882538230694741919957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2470588358820463161279971 3705882538230694741919957)
                ·
                  refine ⟨86856621989781908013749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3705882538230694741919957 86856621989781908013749)
                  ·
                    rfl

theorem cell22_761187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 7].length) (baseStart_761187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761187 prefixEnd_761187 := by exact prefixLift 761187
  have htrace : WordTrace (prefixWord ++ tailWord_761187) baseStart_761187 baseEnd_761187 := by
    simpa [prefixWord, tailWord_761187, baseEnd_761187] using wordTrace_append hprefix tailTrace_761187
  have hstable : (prefixWord ++ tailWord_761187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761187).length < 2 ^ (prefixWord ++ tailWord_761187).sum := by decide
  have hdescent : baseEnd_761187 < baseStart_761187 := by decide
  rcases family_descends (prefixWord ++ tailWord_761187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761191 : List Nat := [1, 1, 5, 1, 4, 1, 2, 1, 3, 3]
def baseStart_761191 : Nat := 118140960795 + 761191 * 2 ^ 59
def prefixEnd_761191 : Nat := 4983230072969 + 3 ^ 40 * 761191 * 2
def baseEnd_761191 : Nat := 260571235251091046941235

theorem tailTrace_761191 : CollatzResearch.WordTrace tailWord_761191 prefixEnd_761191 260571235251091046941235 := by
  unfold tailWord_761191
  simp only [CollatzResearch.WordTrace]
  refine ⟨27762916585342482917995427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18508611056894988611996951 27762916585342482917995427)
  ·
    refine ⟨41644374878013724376993141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27762916585342482917995427 41644374878013724376993141)
    ·
      refine ⟨3904160144813786660343107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41644374878013724376993141 3904160144813786660343107)
      ·
        refine ⟨5856240217220679990514661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3904160144813786660343107 5856240217220679990514661)
        ·
          refine ⟨1098045040728877498221499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5856240217220679990514661 1098045040728877498221499)
          ·
            refine ⟨1647067561093316247332249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1098045040728877498221499 1647067561093316247332249)
            ·
              refine ⟨1235300670819987185499187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1647067561093316247332249 1235300670819987185499187)
              ·
                refine ⟨1852951006229980778248781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1235300670819987185499187 1852951006229980778248781)
                ·
                  refine ⟨694856627336242791843293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1852951006229980778248781 694856627336242791843293)
                  ·
                    refine ⟨260571235251091046941235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 694856627336242791843293 260571235251091046941235)
                    ·
                      rfl

theorem cell22_761191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_761191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761191 prefixEnd_761191 := by exact prefixLift 761191
  have htrace : WordTrace (prefixWord ++ tailWord_761191) baseStart_761191 baseEnd_761191 := by
    simpa [prefixWord, tailWord_761191, baseEnd_761191] using wordTrace_append hprefix tailTrace_761191
  have hstable : (prefixWord ++ tailWord_761191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761191).length < 2 ^ (prefixWord ++ tailWord_761191).sum := by decide
  have hdescent : baseEnd_761191 < baseStart_761191 := by decide
  rcases family_descends (prefixWord ++ tailWord_761191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761202 : List Nat := [3, 2, 1, 2, 1, 2, 1, 3, 2, 5]
def baseStart_761202 : Nat := 118140960795 + 761202 * 2 ^ 59
def prefixEnd_761202 : Nat := 4983230072969 + 3 ^ 40 * 761202 * 2
def baseEnd_761202 : Nat := 260575000775890684916201

theorem tailTrace_761202 : CollatzResearch.WordTrace tailWord_761202 prefixEnd_761202 260575000775890684916201 := by
  unfold tailWord_761202
  simp only [CollatzResearch.WordTrace]
  refine ⟨6940829447075657949161465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18508878525535087864430573 6940829447075657949161465)
  ·
    refine ⟨5205622085306743461871099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6940829447075657949161465 5205622085306743461871099)
    ·
      refine ⟨7808433127960115192806649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5205622085306743461871099 7808433127960115192806649)
      ·
        refine ⟨5856324845970086394604987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7808433127960115192806649 5856324845970086394604987)
        ·
          refine ⟨8784487268955129591907481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5856324845970086394604987 8784487268955129591907481)
          ·
            refine ⟨6588365451716347193930611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8784487268955129591907481 6588365451716347193930611)
            ·
              refine ⟨9882548177574520790895917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6588365451716347193930611 9882548177574520790895917)
              ·
                refine ⟨3705955566590445296585969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9882548177574520790895917 3705955566590445296585969)
                ·
                  refine ⟨2779466674942833972439477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3705955566590445296585969 2779466674942833972439477)
                  ·
                    refine ⟨260575000775890684916201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2779466674942833972439477 260575000775890684916201)
                    ·
                      rfl

theorem cell22_761202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_761202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761202 prefixEnd_761202 := by exact prefixLift 761202
  have htrace : WordTrace (prefixWord ++ tailWord_761202) baseStart_761202 baseEnd_761202 := by
    simpa [prefixWord, tailWord_761202, baseEnd_761202] using wordTrace_append hprefix tailTrace_761202
  have hstable : (prefixWord ++ tailWord_761202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761202).length < 2 ^ (prefixWord ++ tailWord_761202).sum := by decide
  have hdescent : baseEnd_761202 < baseStart_761202 := by decide
  rcases family_descends (prefixWord ++ tailWord_761202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761225 : List Nat := [1, 2, 1, 1, 8, 1, 1, 3, 1, 3]
def baseStart_761225 : Nat := 118140960795 + 761225 * 2 ^ 59
def prefixEnd_761225 : Nat := 4983230072969 + 3 ^ 40 * 761225 * 2
def baseEnd_761225 : Nat := 260582874145926291591131

theorem tailTrace_761225 : CollatzResearch.WordTrace tailWord_761225 prefixEnd_761225 260582874145926291591131 := by
  unfold tailWord_761225
  simp only [CollatzResearch.WordTrace]
  refine ⟨27764156667219306724733129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18509437778146204483155419 27764156667219306724733129)
  ·
    refine ⟨20823117500414480043549847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27764156667219306724733129 20823117500414480043549847)
    ·
      refine ⟨31234676250621720065324771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20823117500414480043549847 31234676250621720065324771)
      ·
        refine ⟨46852014375932580097987157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31234676250621720065324771 46852014375932580097987157)
        ·
          refine ⟨549047043467959923023287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 46852014375932580097987157 549047043467959923023287)
          ·
            refine ⟨823570565201939884534931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549047043467959923023287 823570565201939884534931)
            ·
              refine ⟨1235355847802909826802397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 823570565201939884534931 1235355847802909826802397)
              ·
                refine ⟨463258442926091185050899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1235355847802909826802397 463258442926091185050899)
                ·
                  refine ⟨694887664389136777576349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 463258442926091185050899 694887664389136777576349)
                  ·
                    refine ⟨260582874145926291591131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 694887664389136777576349 260582874145926291591131)
                    ·
                      rfl

theorem cell22_761225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 3, 1, 3].length) (baseStart_761225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761225 prefixEnd_761225 := by exact prefixLift 761225
  have htrace : WordTrace (prefixWord ++ tailWord_761225) baseStart_761225 baseEnd_761225 := by
    simpa [prefixWord, tailWord_761225, baseEnd_761225] using wordTrace_append hprefix tailTrace_761225
  have hstable : (prefixWord ++ tailWord_761225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761225).length < 2 ^ (prefixWord ++ tailWord_761225).sum := by decide
  have hdescent : baseEnd_761225 < baseStart_761225 := by decide
  rcases family_descends (prefixWord ++ tailWord_761225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761277 : List Nat := [1, 4, 1, 2, 2, 1, 1, 10]
def baseStart_761277 : Nat := 118140960795 + 761277 * 2 ^ 59
def prefixEnd_761277 : Nat := 4983230072969 + 3 ^ 40 * 761277 * 2
def baseEnd_761277 : Nat := 28955630534290609921219

theorem tailTrace_761277 : CollatzResearch.WordTrace tailWord_761277 prefixEnd_761277 28955630534290609921219 := by
  unfold tailWord_761277
  simp only [CollatzResearch.WordTrace]
  refine ⟨27766053263030919605626085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18510702175353946403750723 27766053263030919605626085)
  ·
    refine ⟨5206134986818297426054891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27766053263030919605626085 5206134986818297426054891)
    ·
      refine ⟨7809202480227446139082337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5206134986818297426054891 7809202480227446139082337)
      ·
        refine ⟨5856901860170584604311753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7809202480227446139082337 5856901860170584604311753)
        ·
          refine ⟨4392676395127938453233815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5856901860170584604311753 4392676395127938453233815)
          ·
            refine ⟨6589014592691907679850723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4392676395127938453233815 6589014592691907679850723)
            ·
              refine ⟨9883521889037861519776085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6589014592691907679850723 9883521889037861519776085)
              ·
                refine ⟨28955630534290609921219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 9883521889037861519776085 28955630534290609921219)
                ·
                  rfl

theorem cell22_761277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 10].length) (baseStart_761277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761277 prefixEnd_761277 := by exact prefixLift 761277
  have htrace : WordTrace (prefixWord ++ tailWord_761277) baseStart_761277 baseEnd_761277 := by
    simpa [prefixWord, tailWord_761277, baseEnd_761277] using wordTrace_append hprefix tailTrace_761277
  have hstable : (prefixWord ++ tailWord_761277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761277).length < 2 ^ (prefixWord ++ tailWord_761277).sum := by decide
  have hdescent : baseEnd_761277 < baseStart_761277 := by decide
  rcases family_descends (prefixWord ++ tailWord_761277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761300 : List Nat := [2, 4, 1, 2, 3, 2, 2, 2, 4]
def baseStart_761300 : Nat := 118140960795 + 761300 * 2 ^ 59
def prefixEnd_761300 : Nat := 4983230072969 + 3 ^ 40 * 761300 * 2
def baseEnd_761300 : Nat := 86869516059550365321967

theorem tailTrace_761300 : CollatzResearch.WordTrace tailWord_761300 prefixEnd_761300 86869516059550365321967 := by
  unfold tailWord_761300
  simp only [CollatzResearch.WordTrace]
  refine ⟨13883446070973797266856677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18511261427965063022475569 13883446070973797266856677)
  ·
    refine ⟨2603146138307586987535627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13883446070973797266856677 2603146138307586987535627)
    ·
      refine ⟨3904719207461380481303441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2603146138307586987535627 3904719207461380481303441)
      ·
        refine ⟨2928539405596035360977581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3904719207461380481303441 2928539405596035360977581)
        ·
          refine ⟨1098202277098513260366593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2928539405596035360977581 1098202277098513260366593)
          ·
            refine ⟨823651707823884945274945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1098202277098513260366593 823651707823884945274945)
            ·
              refine ⟨617738780867913708956209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 823651707823884945274945 617738780867913708956209)
              ·
                refine ⟨463304085650935281717157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 617738780867913708956209 463304085650935281717157)
                ·
                  refine ⟨86869516059550365321967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 463304085650935281717157 86869516059550365321967)
                  ·
                    rfl

theorem cell22_761300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_761300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761300 prefixEnd_761300 := by exact prefixLift 761300
  have htrace : WordTrace (prefixWord ++ tailWord_761300) baseStart_761300 baseEnd_761300 := by
    simpa [prefixWord, tailWord_761300, baseEnd_761300] using wordTrace_append hprefix tailTrace_761300
  have hstable : (prefixWord ++ tailWord_761300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761300).length < 2 ^ (prefixWord ++ tailWord_761300).sum := by decide
  have hdescent : baseEnd_761300 < baseStart_761300 := by decide
  rcases family_descends (prefixWord ++ tailWord_761300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761326 : List Nat := [4, 1, 2, 1, 2, 1, 3, 2, 3, 3]
def baseStart_761326 : Nat := 118140960795 + 761326 * 2 ^ 59
def prefixEnd_761326 : Nat := 4983230072969 + 3 ^ 40 * 761326 * 2
def baseEnd_761326 : Nat := 260617448509995694815821

theorem tailTrace_761326 : CollatzResearch.WordTrace tailWord_761326 prefixEnd_761326 260617448509995694815821 := by
  unfold tailWord_761326
  simp only [CollatzResearch.WordTrace]
  refine ⟨3470980054981675121769979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18511893626568933982773221 3470980054981675121769979)
  ·
    refine ⟨5206470082472512682654969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3470980054981675121769979 5206470082472512682654969)
    ·
      refine ⟨3904852561854384511991227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5206470082472512682654969 3904852561854384511991227)
      ·
        refine ⟨5857278842781576767986841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3904852561854384511991227 5857278842781576767986841)
        ·
          refine ⟨4392959132086182575990131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5857278842781576767986841 4392959132086182575990131)
          ·
            refine ⟨6589438698129273863985197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4392959132086182575990131 6589438698129273863985197)
            ·
              refine ⟨2471039511798477698994449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6589438698129273863985197 2471039511798477698994449)
              ·
                refine ⟨1853279633848858274245837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2471039511798477698994449 1853279633848858274245837)
                ·
                  refine ⟨694979862693321852842189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1853279633848858274245837 694979862693321852842189)
                  ·
                    refine ⟨260617448509995694815821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 694979862693321852842189 260617448509995694815821)
                    ·
                      rfl

theorem cell22_761326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_761326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761326 prefixEnd_761326 := by exact prefixLift 761326
  have htrace : WordTrace (prefixWord ++ tailWord_761326) baseStart_761326 baseEnd_761326 := by
    simpa [prefixWord, tailWord_761326, baseEnd_761326] using wordTrace_append hprefix tailTrace_761326
  have hstable : (prefixWord ++ tailWord_761326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761326).length < 2 ^ (prefixWord ++ tailWord_761326).sum := by decide
  have hdescent : baseEnd_761326 < baseStart_761326 := by decide
  rcases family_descends (prefixWord ++ tailWord_761326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761337 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 3, 7]
def baseStart_761337 : Nat := 118140960795 + 761337 * 2 ^ 59
def prefixEnd_761337 : Nat := 4983230072969 + 3 ^ 40 * 761337 * 2
def baseEnd_761337 : Nat := 260621214034795332790787

theorem tailTrace_761337 : CollatzResearch.WordTrace tailWord_761337 prefixEnd_761337 260621214034795332790787 := by
  unfold tailWord_761337
  simp only [CollatzResearch.WordTrace]
  refine ⟨27768241642813549852810265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18512161095209033235206843 27768241642813549852810265)
  ·
    refine ⟨20826181232110162389607699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27768241642813549852810265 20826181232110162389607699)
    ·
      refine ⟨31239271848165243584411549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20826181232110162389607699 31239271848165243584411549)
      ·
        refine ⟨11714726943061966344154331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31239271848165243584411549 11714726943061966344154331)
        ·
          refine ⟨17572090414592949516231497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11714726943061966344154331 17572090414592949516231497)
          ·
            refine ⟨13179067810944712137173623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17572090414592949516231497 13179067810944712137173623)
            ·
              refine ⟨19768601716417068205760435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13179067810944712137173623 19768601716417068205760435)
              ·
                refine ⟨29652902574625602308640653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19768601716417068205760435 29652902574625602308640653)
                ·
                  refine ⟨11119838465484600865740245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29652902574625602308640653 11119838465484600865740245)
                  ·
                    refine ⟨260621214034795332790787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11119838465484600865740245 260621214034795332790787)
                    ·
                      rfl

theorem cell22_761337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 7].length) (baseStart_761337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761337 prefixEnd_761337 := by exact prefixLift 761337
  have htrace : WordTrace (prefixWord ++ tailWord_761337) baseStart_761337 baseEnd_761337 := by
    simpa [prefixWord, tailWord_761337, baseEnd_761337] using wordTrace_append hprefix tailTrace_761337
  have hstable : (prefixWord ++ tailWord_761337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761337).length < 2 ^ (prefixWord ++ tailWord_761337).sum := by decide
  have hdescent : baseEnd_761337 < baseStart_761337 := by decide
  rcases family_descends (prefixWord ++ tailWord_761337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761354 : List Nat := [3, 1, 2, 2, 2, 2, 1, 2, 2, 5]
def baseStart_761354 : Nat := 118140960795 + 761354 * 2 ^ 59
def prefixEnd_761354 : Nat := 4983230072969 + 3 ^ 40 * 761354 * 2
def baseEnd_761354 : Nat := 260627033482212955115735

theorem tailTrace_761354 : CollatzResearch.WordTrace tailWord_761354 prefixEnd_761354 260627033482212955115735 := by
  unfold tailWord_761354
  simp only [CollatzResearch.WordTrace]
  refine ⟨6942215420937990439044779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18512574455834641170786077 6942215420937990439044779)
  ·
    refine ⟨10413323131406985658567169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6942215420937990439044779 10413323131406985658567169)
    ·
      refine ⟨7809992348555239243925377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10413323131406985658567169 7809992348555239243925377)
      ·
        refine ⟨5857494261416429432944033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7809992348555239243925377 5857494261416429432944033)
        ·
          refine ⟨4393120696062322074708025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5857494261416429432944033 4393120696062322074708025)
          ·
            refine ⟨3294840522046741556031019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4393120696062322074708025 3294840522046741556031019)
            ·
              refine ⟨4942260783070112334046529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3294840522046741556031019 4942260783070112334046529)
              ·
                refine ⟨3706695587302584250534897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4942260783070112334046529 3706695587302584250534897)
                ·
                  refine ⟨2780021690476938187901173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3706695587302584250534897 2780021690476938187901173)
                  ·
                    refine ⟨260627033482212955115735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2780021690476938187901173 260627033482212955115735)
                    ·
                      rfl

theorem cell22_761354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_761354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761354 prefixEnd_761354 := by exact prefixLift 761354
  have htrace : WordTrace (prefixWord ++ tailWord_761354) baseStart_761354 baseEnd_761354 := by
    simpa [prefixWord, tailWord_761354, baseEnd_761354] using wordTrace_append hprefix tailTrace_761354
  have hstable : (prefixWord ++ tailWord_761354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761354).length < 2 ^ (prefixWord ++ tailWord_761354).sum := by decide
  have hdescent : baseEnd_761354 < baseStart_761354 := by decide
  rcases family_descends (prefixWord ++ tailWord_761354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761418 : List Nat := [3, 1, 2, 1, 1, 3, 5, 2, 4]
def baseStart_761418 : Nat := 118140960795 + 761418 * 2 ^ 59
def prefixEnd_761418 : Nat := 4983230072969 + 3 ^ 40 * 761418 * 2
def baseEnd_761418 : Nat := 86882980663379373838513

theorem tailTrace_761418 : CollatzResearch.WordTrace tailWord_761418 prefixEnd_761418 86882980663379373838513 := by
  unfold tailWord_761418
  simp only [CollatzResearch.WordTrace]
  refine ⟨6942798988880025171627227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18514130637013400457672605 6942798988880025171627227)
  ·
    refine ⟨10414198483320037757440841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6942798988880025171627227 10414198483320037757440841)
    ·
      refine ⟨7810648862490028318080631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10414198483320037757440841 7810648862490028318080631)
      ·
        refine ⟨11715973293735042477120947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7810648862490028318080631 11715973293735042477120947)
        ·
          refine ⟨17573959940602563715681421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11715973293735042477120947 17573959940602563715681421)
          ·
            refine ⟨6590234977725961393380533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17573959940602563715681421 6590234977725961393380533)
            ·
              refine ⟨617834529161808880629425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6590234977725961393380533 617834529161808880629425)
              ·
                refine ⟨463375896871356660472069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 617834529161808880629425 463375896871356660472069)
                ·
                  refine ⟨86882980663379373838513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 463375896871356660472069 86882980663379373838513)
                  ·
                    rfl

theorem cell22_761418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 2, 4].length) (baseStart_761418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761418 prefixEnd_761418 := by exact prefixLift 761418
  have htrace : WordTrace (prefixWord ++ tailWord_761418) baseStart_761418 baseEnd_761418 := by
    simpa [prefixWord, tailWord_761418, baseEnd_761418] using wordTrace_append hprefix tailTrace_761418
  have hstable : (prefixWord ++ tailWord_761418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761418).length < 2 ^ (prefixWord ++ tailWord_761418).sum := by decide
  have hdescent : baseEnd_761418 < baseStart_761418 := by decide
  rcases family_descends (prefixWord ++ tailWord_761418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761437 : List Nat := [1, 4, 4, 2, 1, 2, 1, 2, 1, 4]
def baseStart_761437 : Nat := 118140960795 + 761437 * 2 ^ 59
def prefixEnd_761437 : Nat := 4983230072969 + 3 ^ 40 * 761437 * 2
def baseEnd_761437 : Nat := 260655446078428405290481

theorem tailTrace_761437 : CollatzResearch.WordTrace tailWord_761437 prefixEnd_761437 260655446078428405290481 := by
  unfold tailWord_761437
  simp only [CollatzResearch.WordTrace]
  refine ⟨27771888942451266931450565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18514592628300844620967043 27771888942451266931450565)
  ·
    refine ⟨5207229176709612549646981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27771888942451266931450565 5207229176709612549646981)
    ·
      refine ⟨976355470633052353058809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5207229176709612549646981 976355470633052353058809)
      ·
        refine ⟨732266602974789264794107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 976355470633052353058809 732266602974789264794107)
        ·
          refine ⟨1098399904462183897191161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 732266602974789264794107 1098399904462183897191161)
          ·
            refine ⟨823799928346637922893371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1098399904462183897191161 823799928346637922893371)
            ·
              refine ⟨1235699892519956884340057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 823799928346637922893371 1235699892519956884340057)
              ·
                refine ⟨926774919389967663255043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1235699892519956884340057 926774919389967663255043)
                ·
                  refine ⟨1390162379084951494882565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 926774919389967663255043 1390162379084951494882565)
                  ·
                    refine ⟨260655446078428405290481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1390162379084951494882565 260655446078428405290481)
                    ·
                      rfl

theorem cell22_761437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_761437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761437 prefixEnd_761437 := by exact prefixLift 761437
  have htrace : WordTrace (prefixWord ++ tailWord_761437) baseStart_761437 baseEnd_761437 := by
    simpa [prefixWord, tailWord_761437, baseEnd_761437] using wordTrace_append hprefix tailTrace_761437
  have hstable : (prefixWord ++ tailWord_761437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761437).length < 2 ^ (prefixWord ++ tailWord_761437).sum := by decide
  have hdescent : baseEnd_761437 < baseStart_761437 := by decide
  rcases family_descends (prefixWord ++ tailWord_761437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761448 : List Nat := [2, 1, 4, 3, 1, 2, 2, 1, 2, 4]
def baseStart_761448 : Nat := 118140960795 + 761448 * 2 ^ 59
def prefixEnd_761448 : Nat := 4983230072969 + 3 ^ 40 * 761448 * 2
def baseEnd_761448 : Nat := 260659211603228043265447

theorem tailTrace_761448 : CollatzResearch.WordTrace tailWord_761448 prefixEnd_761448 260659211603228043265447 := by
  unfold tailWord_761448
  simp only [CollatzResearch.WordTrace]
  refine ⟨13886145072705707905050499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18514860096940943873400665 13886145072705707905050499)
  ·
    refine ⟨20829217609058561857575749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13886145072705707905050499 20829217609058561857575749)
    ·
      refine ⟨3905478301698480348295453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20829217609058561857575749 3905478301698480348295453)
      ·
        refine ⟨1464554363136930130610795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3905478301698480348295453 1464554363136930130610795)
        ·
          refine ⟨2196831544705395195916193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1464554363136930130610795 2196831544705395195916193)
          ·
            refine ⟨1647623658529046396937145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2196831544705395195916193 1647623658529046396937145)
            ·
              refine ⟨1235717743896784797702859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1647623658529046396937145 1235717743896784797702859)
              ·
                refine ⟨1853576615845177196554289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1235717743896784797702859 1853576615845177196554289)
                ·
                  refine ⟨1390182461883882897415717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1853576615845177196554289 1390182461883882897415717)
                  ·
                    refine ⟨260659211603228043265447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1390182461883882897415717 260659211603228043265447)
                    ·
                      rfl

theorem cell22_761448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_761448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761448 prefixEnd_761448 := by exact prefixLift 761448
  have htrace : WordTrace (prefixWord ++ tailWord_761448) baseStart_761448 baseEnd_761448 := by
    simpa [prefixWord, tailWord_761448, baseEnd_761448] using wordTrace_append hprefix tailTrace_761448
  have hstable : (prefixWord ++ tailWord_761448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761448).length < 2 ^ (prefixWord ++ tailWord_761448).sum := by decide
  have hdescent : baseEnd_761448 < baseStart_761448 := by decide
  rcases family_descends (prefixWord ++ tailWord_761448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761480 : List Nat := [2, 1, 3, 5, 2, 1, 1, 7]
def baseStart_761480 : Nat := 118140960795 + 761480 * 2 ^ 59
def prefixEnd_761480 : Nat := 4983230072969 + 3 ^ 40 * 761480 * 2
def baseEnd_761480 : Nat := 28963351761910069607261

theorem tailTrace_761480 : CollatzResearch.WordTrace tailWord_761480 prefixEnd_761480 28963351761910069607261 := by
  unfold tailWord_761480
  simp only [CollatzResearch.WordTrace]
  refine ⟨13886728640647742637632947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18515638187530323516843929 13886728640647742637632947)
  ·
    refine ⟨20830092960971613956449421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13886728640647742637632947 20830092960971613956449421)
    ·
      refine ⟨7811284860364355233668533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20830092960971613956449421 7811284860364355233668533)
      ·
        refine ⟨732307955659158303156425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7811284860364355233668533 732307955659158303156425)
        ·
          refine ⟨549230966744368727367319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 732307955659158303156425 549230966744368727367319)
          ·
            refine ⟨823846450116553091050979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549230966744368727367319 823846450116553091050979)
            ·
              refine ⟨1235769675174829636576469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 823846450116553091050979 1235769675174829636576469)
              ·
                refine ⟨28963351761910069607261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1235769675174829636576469 28963351761910069607261)
                ·
                  rfl

theorem cell22_761480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 7].length) (baseStart_761480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761480 prefixEnd_761480 := by exact prefixLift 761480
  have htrace : WordTrace (prefixWord ++ tailWord_761480) baseStart_761480 baseEnd_761480 := by
    simpa [prefixWord, tailWord_761480, baseEnd_761480] using wordTrace_append hprefix tailTrace_761480
  have hstable : (prefixWord ++ tailWord_761480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761480).length < 2 ^ (prefixWord ++ tailWord_761480).sum := by decide
  have hdescent : baseEnd_761480 < baseStart_761480 := by decide
  rcases family_descends (prefixWord ++ tailWord_761480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761519 : List Nat := [1, 1, 2, 1, 2, 4, 1, 2, 8]
def baseStart_761519 : Nat := 118140960795 + 761519 * 2 ^ 59
def prefixEnd_761519 : Nat := 4983230072969 + 3 ^ 40 * 761519 * 2
def baseEnd_761519 : Nat := 86894505451402508246743

theorem tailTrace_761519 : CollatzResearch.WordTrace tailWord_761519 prefixEnd_761519 86894505451402508246743 := by
  unfold tailWord_761519
  simp only [CollatzResearch.WordTrace]
  refine ⟨27774879728154194935935611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18516586485436129957290407 27774879728154194935935611)
  ·
    refine ⟨41662319592231292403903417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27774879728154194935935611 41662319592231292403903417)
    ·
      refine ⟨31246739694173469302927563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41662319592231292403903417 31246739694173469302927563)
      ·
        refine ⟨46870109541260203954391345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31246739694173469302927563 46870109541260203954391345)
        ·
          refine ⟨35152582155945152965793509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46870109541260203954391345 35152582155945152965793509)
          ·
            refine ⟨6591109154239716181086283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35152582155945152965793509 6591109154239716181086283)
            ·
              refine ⟨9886663731359574271629425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6591109154239716181086283 9886663731359574271629425)
              ·
                refine ⟨7414997798519680703722069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9886663731359574271629425 7414997798519680703722069)
                ·
                  refine ⟨86894505451402508246743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7414997798519680703722069 86894505451402508246743)
                  ·
                    rfl

theorem cell22_761519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 8].length) (baseStart_761519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761519 prefixEnd_761519 := by exact prefixLift 761519
  have htrace : WordTrace (prefixWord ++ tailWord_761519) baseStart_761519 baseEnd_761519 := by
    simpa [prefixWord, tailWord_761519, baseEnd_761519] using wordTrace_append hprefix tailTrace_761519
  have hstable : (prefixWord ++ tailWord_761519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761519).length < 2 ^ (prefixWord ++ tailWord_761519).sum := by decide
  have hdescent : baseEnd_761519 < baseStart_761519 := by decide
  rcases family_descends (prefixWord ++ tailWord_761519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761525 : List Nat := [1, 3, 3, 3, 2, 2, 1, 2, 5]
def baseStart_761525 : Nat := 118140960795 + 761525 * 2 ^ 59
def prefixEnd_761525 : Nat := 4983230072969 + 3 ^ 40 * 761525 * 2
def baseEnd_761525 : Nat := 86895190092275169696737

theorem tailTrace_761525 : CollatzResearch.WordTrace tailWord_761525 prefixEnd_761525 86895190092275169696737 := by
  unfold tailWord_761525
  simp only [CollatzResearch.WordTrace]
  refine ⟨27775098566132457960654029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18516732377421638640436019 27775098566132457960654029)
  ·
    refine ⟨10415661962299671735245261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27775098566132457960654029 10415661962299671735245261)
    ·
      refine ⟨3905873235862376900716973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10415661962299671735245261 3905873235862376900716973)
      ·
        refine ⟨1464702463448391337768865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3905873235862376900716973 1464702463448391337768865)
        ·
          refine ⟨1098526847586293503326649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1464702463448391337768865 1098526847586293503326649)
          ·
            refine ⟨823895135689720127494987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1098526847586293503326649 823895135689720127494987)
            ·
              refine ⟨1235842703534580191242481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 823895135689720127494987 1235842703534580191242481)
              ·
                refine ⟨926882027650935143431861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1235842703534580191242481 926882027650935143431861)
                ·
                  refine ⟨86895190092275169696737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 926882027650935143431861 86895190092275169696737)
                  ·
                    rfl

theorem cell22_761525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 5].length) (baseStart_761525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761525 prefixEnd_761525 := by exact prefixLift 761525
  have htrace : WordTrace (prefixWord ++ tailWord_761525) baseStart_761525 baseEnd_761525 := by
    simpa [prefixWord, tailWord_761525, baseEnd_761525] using wordTrace_append hprefix tailTrace_761525
  have hstable : (prefixWord ++ tailWord_761525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761525).length < 2 ^ (prefixWord ++ tailWord_761525).sum := by decide
  have hdescent : baseEnd_761525 < baseStart_761525 := by decide
  rcases family_descends (prefixWord ++ tailWord_761525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761536 : List Nat := [2, 1, 1, 2, 4, 1, 4, 1, 6]
def baseStart_761536 : Nat := 118140960795 + 761536 * 2 ^ 59
def prefixEnd_761536 : Nat := 4983230072969 + 3 ^ 40 * 761536 * 2
def baseEnd_761536 : Nat := 86896445267208382355059

theorem tailTrace_761536 : CollatzResearch.WordTrace tailWord_761536 prefixEnd_761536 86896445267208382355059 := by
  unfold tailWord_761536
  simp only [CollatzResearch.WordTrace]
  refine ⟨13887749884546303419652231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18516999846061737892869641 13887749884546303419652231)
  ·
    refine ⟨20831624826819455129478347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13887749884546303419652231 20831624826819455129478347)
    ·
      refine ⟨31247437240229182694217521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20831624826819455129478347 31247437240229182694217521)
      ·
        refine ⟨23435577930171887020663141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31247437240229182694217521 23435577930171887020663141)
        ·
          refine ⟨4394170861907228816374339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23435577930171887020663141 4394170861907228816374339)
          ·
            refine ⟨6591256292860843224561509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4394170861907228816374339 6591256292860843224561509)
            ·
              refine ⟨1235860554911408104605283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6591256292860843224561509 1235860554911408104605283)
              ·
                refine ⟨1853790832367112156907925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1235860554911408104605283 1853790832367112156907925)
                ·
                  refine ⟨86896445267208382355059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1853790832367112156907925 86896445267208382355059)
                  ·
                    rfl

theorem cell22_761536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 6].length) (baseStart_761536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761536 prefixEnd_761536 := by exact prefixLift 761536
  have htrace : WordTrace (prefixWord ++ tailWord_761536) baseStart_761536 baseEnd_761536 := by
    simpa [prefixWord, tailWord_761536, baseEnd_761536] using wordTrace_append hprefix tailTrace_761536
  have hstable : (prefixWord ++ tailWord_761536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761536).length < 2 ^ (prefixWord ++ tailWord_761536).sum := by decide
  have hdescent : baseEnd_761536 < baseStart_761536 := by decide
  rcases family_descends (prefixWord ++ tailWord_761536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761581 : List Nat := [1, 5, 1, 2, 1, 2, 10]
def baseStart_761581 : Nat := 118140960795 + 761581 * 2 ^ 59
def prefixEnd_761581 : Nat := 4983230072969 + 3 ^ 40 * 761581 * 2
def baseEnd_761581 : Nat := 9655731119305927025557

theorem tailTrace_761581 : CollatzResearch.WordTrace tailWord_761581 prefixEnd_761581 9655731119305927025557 := by
  unfold tailWord_761581
  simp only [CollatzResearch.WordTrace]
  refine ⟨27777141053929579524692597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18518094035953053016461731 27777141053929579524692597)
  ·
    refine ⟨2604106973805898080439931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27777141053929579524692597 2604106973805898080439931)
    ·
      refine ⟨3906160460708847120659897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2604106973805898080439931 3906160460708847120659897)
      ·
        refine ⟨2929620345531635340494923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3906160460708847120659897 2929620345531635340494923)
        ·
          refine ⟨4394430518297453010742385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2929620345531635340494923 4394430518297453010742385)
          ·
            refine ⟨3295822888723089758056789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4394430518297453010742385 3295822888723089758056789)
            ·
              refine ⟨9655731119305927025557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3295822888723089758056789 9655731119305927025557)
              ·
                rfl

theorem cell22_761581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 10].length) (baseStart_761581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761581 prefixEnd_761581 := by exact prefixLift 761581
  have htrace : WordTrace (prefixWord ++ tailWord_761581) baseStart_761581 baseEnd_761581 := by
    simpa [prefixWord, tailWord_761581, baseEnd_761581] using wordTrace_append hprefix tailTrace_761581
  have hstable : (prefixWord ++ tailWord_761581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761581).length < 2 ^ (prefixWord ++ tailWord_761581).sum := by decide
  have hdescent : baseEnd_761581 < baseStart_761581 := by decide
  rcases family_descends (prefixWord ++ tailWord_761581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761606 : List Nat := [6, 2, 2, 1, 1, 1, 1, 1, 3, 4]
def baseStart_761606 : Nat := 118140960795 + 761606 * 2 ^ 59
def prefixEnd_761606 : Nat := 4983230072969 + 3 ^ 40 * 761606 * 2
def baseEnd_761606 : Nat := 260713298232168297814963

theorem tailTrace_761606 : CollatzResearch.WordTrace tailWord_761606 prefixEnd_761606 260713298232168297814963 := by
  unfold tailWord_761606
  simp only [CollatzResearch.WordTrace]
  refine ⟨868064152463719024823521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18518701919226005862901781 868064152463719024823521)
  ·
    refine ⟨651048114347789268617641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 868064152463719024823521 651048114347789268617641)
    ·
      refine ⟨488286085760841951463231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 651048114347789268617641 488286085760841951463231)
      ·
        refine ⟨732429128641262927194847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488286085760841951463231 732429128641262927194847)
        ·
          refine ⟨1098643692961894390792271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 732429128641262927194847 1098643692961894390792271)
          ·
            refine ⟨1647965539442841586188407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1098643692961894390792271 1647965539442841586188407)
            ·
              refine ⟨2471948309164262379282611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1647965539442841586188407 2471948309164262379282611)
              ·
                refine ⟨3707922463746393568923917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2471948309164262379282611 3707922463746393568923917)
                ·
                  refine ⟨1390470923904897588346469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3707922463746393568923917 1390470923904897588346469)
                  ·
                    refine ⟨260713298232168297814963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1390470923904897588346469 260713298232168297814963)
                    ·
                      rfl

theorem cell22_761606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_761606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761606 prefixEnd_761606 := by exact prefixLift 761606
  have htrace : WordTrace (prefixWord ++ tailWord_761606) baseStart_761606 baseEnd_761606 := by
    simpa [prefixWord, tailWord_761606, baseEnd_761606] using wordTrace_append hprefix tailTrace_761606
  have hstable : (prefixWord ++ tailWord_761606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761606).length < 2 ^ (prefixWord ++ tailWord_761606).sum := by decide
  have hdescent : baseEnd_761606 < baseStart_761606 := by decide
  rcases family_descends (prefixWord ++ tailWord_761606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761658 : List Nat := [3, 1, 1, 1, 5, 2, 1, 1, 2, 5]
def baseStart_761658 : Nat := 118140960795 + 761658 * 2 ^ 59
def prefixEnd_761658 : Nat := 4983230072969 + 3 ^ 40 * 761658 * 2
def baseEnd_761658 : Nat := 260731098894857495514803

theorem tailTrace_761658 : CollatzResearch.WordTrace tailWord_761658 prefixEnd_761658 260731098894857495514803 := by
  unfold tailWord_761658
  simp only [CollatzResearch.WordTrace]
  refine ⟨6944987368662655418811407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18519966316433747783497085 6944987368662655418811407)
  ·
    refine ⟨10417481052993983128217111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6944987368662655418811407 10417481052993983128217111)
    ·
      refine ⟨15626221579490974692325667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10417481052993983128217111 15626221579490974692325667)
      ·
        refine ⟨23439332369236462038488501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15626221579490974692325667 23439332369236462038488501)
        ·
          refine ⟨2197437409615918316108297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23439332369236462038488501 2197437409615918316108297)
          ·
            refine ⟨1648078057211938737081223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2197437409615918316108297 1648078057211938737081223)
            ·
              refine ⟨2472117085817908105621835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1648078057211938737081223 2472117085817908105621835)
              ·
                refine ⟨3708175628726862158432753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2472117085817908105621835 3708175628726862158432753)
                ·
                  refine ⟨2781131721545146618824565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3708175628726862158432753 2781131721545146618824565)
                  ·
                    refine ⟨260731098894857495514803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2781131721545146618824565 260731098894857495514803)
                    ·
                      rfl

theorem cell22_761658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_761658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761658 prefixEnd_761658 := by exact prefixLift 761658
  have htrace : WordTrace (prefixWord ++ tailWord_761658) baseStart_761658 baseEnd_761658 := by
    simpa [prefixWord, tailWord_761658, baseEnd_761658] using wordTrace_append hprefix tailTrace_761658
  have hstable : (prefixWord ++ tailWord_761658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761658).length < 2 ^ (prefixWord ++ tailWord_761658).sum := by decide
  have hdescent : baseEnd_761658 < baseStart_761658 := by decide
  rcases family_descends (prefixWord ++ tailWord_761658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761671 : List Nat := [1, 1, 4, 1, 2, 1, 3, 1, 8]
def baseStart_761671 : Nat := 118140960795 + 761671 * 2 ^ 59
def prefixEnd_761671 : Nat := 4983230072969 + 3 ^ 40 * 761671 * 2
def baseEnd_761671 : Nat := 86911849686843264979921

theorem tailTrace_761671 : CollatzResearch.WordTrace tailWord_761671 prefixEnd_761671 86911849686843264979921 := by
  unfold tailWord_761671
  simp only [CollatzResearch.WordTrace]
  refine ⟨27780423623603524895468867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18520282415735683263645911 27780423623603524895468867)
  ·
    refine ⟨41670635435405287343203301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27780423623603524895468867 41670635435405287343203301)
    ·
      refine ⟨7813244144138491376850619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41670635435405287343203301 7813244144138491376850619)
      ·
        refine ⟨11719866216207737065275929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7813244144138491376850619 11719866216207737065275929)
        ·
          refine ⟨8789899662155802798956947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11719866216207737065275929 8789899662155802798956947)
          ·
            refine ⟨13184849493233704198435421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8789899662155802798956947 13184849493233704198435421)
            ·
              refine ⟨4944318559962639074413283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13184849493233704198435421 4944318559962639074413283)
              ·
                refine ⟨7416477839943958611619925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4944318559962639074413283 7416477839943958611619925)
                ·
                  refine ⟨86911849686843264979921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7416477839943958611619925 86911849686843264979921)
                  ·
                    rfl

theorem cell22_761671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 8].length) (baseStart_761671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761671 prefixEnd_761671 := by exact prefixLift 761671
  have htrace : WordTrace (prefixWord ++ tailWord_761671) baseStart_761671 baseEnd_761671 := by
    simpa [prefixWord, tailWord_761671, baseEnd_761671] using wordTrace_append hprefix tailTrace_761671
  have hstable : (prefixWord ++ tailWord_761671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761671).length < 2 ^ (prefixWord ++ tailWord_761671).sum := by decide
  have hdescent : baseEnd_761671 < baseStart_761671 := by decide
  rcases family_descends (prefixWord ++ tailWord_761671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761673 : List Nat := [1, 2, 1, 1, 2, 4, 2, 4, 1, 4]
def baseStart_761673 : Nat := 118140960795 + 761673 * 2 ^ 59
def prefixEnd_761673 : Nat := 4983230072969 + 3 ^ 40 * 761673 * 2
def baseEnd_761673 : Nat := 260736233701402456389757

theorem tailTrace_761673 : CollatzResearch.WordTrace tailWord_761673 prefixEnd_761673 260736233701402456389757 := by
  unfold tailWord_761673
  simp only [CollatzResearch.WordTrace]
  refine ⟨27780496569596279237041673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18520331046397519491361115 27780496569596279237041673)
  ·
    refine ⟨20835372427197209427781255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27780496569596279237041673 20835372427197209427781255)
    ·
      refine ⟨31253058640795814141671883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20835372427197209427781255 31253058640795814141671883)
      ·
        refine ⟨46879587961193721212507825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31253058640795814141671883 46879587961193721212507825)
        ·
          refine ⟨35159690970895290909380869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46879587961193721212507825 35159690970895290909380869)
          ·
            refine ⟨6592442057042867045508913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35159690970895290909380869 6592442057042867045508913)
            ·
              refine ⟨4944331542782150284131685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6592442057042867045508913 4944331542782150284131685)
              ·
                refine ⟨927062164271653178274691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4944331542782150284131685 927062164271653178274691)
                ·
                  refine ⟨1390593246407479767412037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 927062164271653178274691 1390593246407479767412037)
                  ·
                    refine ⟨260736233701402456389757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1390593246407479767412037 260736233701402456389757)
                    ·
                      rfl

theorem cell22_761673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 4].length) (baseStart_761673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761673 prefixEnd_761673 := by exact prefixLift 761673
  have htrace : WordTrace (prefixWord ++ tailWord_761673) baseStart_761673 baseEnd_761673 := by
    simpa [prefixWord, tailWord_761673, baseEnd_761673] using wordTrace_append hprefix tailTrace_761673
  have hstable : (prefixWord ++ tailWord_761673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761673).length < 2 ^ (prefixWord ++ tailWord_761673).sum := by decide
  have hdescent : baseEnd_761673 < baseStart_761673 := by decide
  rcases family_descends (prefixWord ++ tailWord_761673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761752 : List Nat := [2, 1, 2, 6, 1, 1, 1, 2, 2, 4]
def baseStart_761752 : Nat := 118140960795 + 761752 * 2 ^ 59
def prefixEnd_761752 : Nat := 4983230072969 + 3 ^ 40 * 761752 * 2
def baseEnd_761752 : Nat := 260763277015872583664515

theorem tailTrace_761752 : CollatzResearch.WordTrace tailWord_761752 prefixEnd_761752 260763277015872583664515 := by
  unfold tailWord_761752
  simp only [CollatzResearch.WordTrace]
  refine ⟨13891688968155037864583755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18522251957540050486111673 13891688968155037864583755)
  ·
    refine ⟨20837533452232556796875633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13891688968155037864583755 20837533452232556796875633)
    ·
      refine ⟨15628150089174417597656725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20837533452232556796875633 15628150089174417597656725)
      ·
        refine ⟨732569535430050824890159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15628150089174417597656725 732569535430050824890159)
        ·
          refine ⟨1098854303145076237335239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 732569535430050824890159 1098854303145076237335239)
          ·
            refine ⟨1648281454717614356002859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1098854303145076237335239 1648281454717614356002859)
            ·
              refine ⟨2472422182076421534004289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1648281454717614356002859 2472422182076421534004289)
              ·
                refine ⟨1854316636557316150503217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2472422182076421534004289 1854316636557316150503217)
                ·
                  refine ⟨1390737477417987112877413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1854316636557316150503217 1390737477417987112877413)
                  ·
                    refine ⟨260763277015872583664515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1390737477417987112877413 260763277015872583664515)
                    ·
                      rfl

theorem cell22_761752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 2, 4].length) (baseStart_761752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761752 prefixEnd_761752 := by exact prefixLift 761752
  have htrace : WordTrace (prefixWord ++ tailWord_761752) baseStart_761752 baseEnd_761752 := by
    simpa [prefixWord, tailWord_761752, baseEnd_761752] using wordTrace_append hprefix tailTrace_761752
  have hstable : (prefixWord ++ tailWord_761752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761752).length < 2 ^ (prefixWord ++ tailWord_761752).sum := by decide
  have hdescent : baseEnd_761752 < baseStart_761752 := by decide
  rcases family_descends (prefixWord ++ tailWord_761752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761857 : List Nat := [1, 2, 4, 1, 2, 1, 4, 3, 4]
def baseStart_761857 : Nat := 118140960795 + 761857 * 2 ^ 59
def prefixEnd_761857 : Nat := 4983230072969 + 3 ^ 40 * 761857 * 2
def baseEnd_761857 : Nat := 86933073553895769929731

theorem tailTrace_761857 : CollatzResearch.WordTrace tailWord_761857 prefixEnd_761857 86933073553895769929731 := by
  unfold tailWord_761857
  simp only [CollatzResearch.WordTrace]
  refine ⟨27787207600929678661739825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18524805067286452441159883 27787207600929678661739825)
  ·
    refine ⟨20840405700697258996304869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27787207600929678661739825 20840405700697258996304869)
    ·
      refine ⟨3907576068880736061807163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20840405700697258996304869 3907576068880736061807163)
      ·
        refine ⟨5861364103321104092710745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3907576068880736061807163 5861364103321104092710745)
        ·
          refine ⟨4396023077490828069533059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5861364103321104092710745 4396023077490828069533059)
          ·
            refine ⟨6594034616236242104299589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4396023077490828069533059 6594034616236242104299589)
            ·
              refine ⟨1236381490544295394556173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6594034616236242104299589 1236381490544295394556173)
              ·
                refine ⟨463643058954110772958565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1236381490544295394556173 463643058954110772958565)
                ·
                  refine ⟨86933073553895769929731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 463643058954110772958565 86933073553895769929731)
                  ·
                    rfl

theorem cell22_761857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 3, 4].length) (baseStart_761857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761857 prefixEnd_761857 := by exact prefixLift 761857
  have htrace : WordTrace (prefixWord ++ tailWord_761857) baseStart_761857 baseEnd_761857 := by
    simpa [prefixWord, tailWord_761857, baseEnd_761857] using wordTrace_append hprefix tailTrace_761857
  have hstable : (prefixWord ++ tailWord_761857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761857).length < 2 ^ (prefixWord ++ tailWord_761857).sum := by decide
  have hdescent : baseEnd_761857 < baseStart_761857 := by decide
  rcases family_descends (prefixWord ++ tailWord_761857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761868 : List Nat := [2, 2, 1, 2, 3, 1, 11]
def baseStart_761868 : Nat := 118140960795 + 761868 * 2 ^ 59
def prefixEnd_761868 : Nat := 4983230072969 + 3 ^ 40 * 761868 * 2
def baseEnd_761868 : Nat := 9659369858758775843117

theorem tailTrace_761868 : CollatzResearch.WordTrace tailWord_761868 prefixEnd_761868 9659369858758775843117 := by
  unfold tailWord_761868
  simp only [CollatzResearch.WordTrace]
  refine ⟨13893804401944913770195129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18525072535926551693593505 13893804401944913770195129)
  ·
    refine ⟨10420353301458685327646347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13893804401944913770195129 10420353301458685327646347)
    ·
      refine ⟨15630529952188027991469521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10420353301458685327646347 15630529952188027991469521)
      ·
        refine ⟨11722897464141020993602141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15630529952188027991469521 11722897464141020993602141)
        ·
          refine ⟨4396086549052882872600803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11722897464141020993602141 4396086549052882872600803)
          ·
            refine ⟨6594129823579324308901205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4396086549052882872600803 6594129823579324308901205)
            ·
              refine ⟨9659369858758775843117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 6594129823579324308901205 9659369858758775843117)
              ·
                rfl

theorem cell22_761868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 11].length) (baseStart_761868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761868 prefixEnd_761868 := by exact prefixLift 761868
  have htrace : WordTrace (prefixWord ++ tailWord_761868) baseStart_761868 baseEnd_761868 := by
    simpa [prefixWord, tailWord_761868, baseEnd_761868] using wordTrace_append hprefix tailTrace_761868
  have hstable : (prefixWord ++ tailWord_761868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761868).length < 2 ^ (prefixWord ++ tailWord_761868).sum := by decide
  have hdescent : baseEnd_761868 < baseStart_761868 := by decide
  rcases family_descends (prefixWord ++ tailWord_761868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761870 : List Nat := [4, 1, 1, 2, 2, 1, 2, 1, 4, 4]
def baseStart_761870 : Nat := 118140960795 + 761870 * 2 ^ 59
def prefixEnd_761870 : Nat := 4983230072969 + 3 ^ 40 * 761870 * 2
def baseEnd_761870 : Nat := 260803670827359609214153

theorem tailTrace_761870 : CollatzResearch.WordTrace tailWord_761870 prefixEnd_761870 260803670827359609214153 := by
  unfold tailWord_761870
  simp only [CollatzResearch.WordTrace]
  refine ⟨3473460218735322735245383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18525121166588387921308709 3473460218735322735245383)
  ·
    refine ⟨5210190328102984102868075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3473460218735322735245383 5210190328102984102868075)
    ·
      refine ⟨7815285492154476154302113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5210190328102984102868075 7815285492154476154302113)
      ·
        refine ⟨5861464119115857115726585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7815285492154476154302113 5861464119115857115726585)
        ·
          refine ⟨4396098089336892836794939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5861464119115857115726585 4396098089336892836794939)
          ·
            refine ⟨6594147134005339255192409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4396098089336892836794939 6594147134005339255192409)
            ·
              refine ⟨4945610350504004441394307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6594147134005339255192409 4945610350504004441394307)
              ·
                refine ⟨7418415525756006662091461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4945610350504004441394307 7418415525756006662091461)
                ·
                  refine ⟨1390952911079251249142149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7418415525756006662091461 1390952911079251249142149)
                  ·
                    refine ⟨260803670827359609214153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1390952911079251249142149 260803670827359609214153)
                    ·
                      rfl

theorem cell22_761870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_761870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761870 prefixEnd_761870 := by exact prefixLift 761870
  have htrace : WordTrace (prefixWord ++ tailWord_761870) baseStart_761870 baseEnd_761870 := by
    simpa [prefixWord, tailWord_761870, baseEnd_761870] using wordTrace_append hprefix tailTrace_761870
  have hstable : (prefixWord ++ tailWord_761870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761870).length < 2 ^ (prefixWord ++ tailWord_761870).sum := by decide
  have hdescent : baseEnd_761870 < baseStart_761870 := by decide
  rcases family_descends (prefixWord ++ tailWord_761870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761889 : List Nat := [1, 2, 3, 2, 5, 1, 1, 1, 1, 5]
def baseStart_761889 : Nat := 118140960795 + 761889 * 2 ^ 59
def prefixEnd_761889 : Nat := 4983230072969 + 3 ^ 40 * 761889 * 2
def baseEnd_761889 : Nat := 260810174915649892989095

theorem tailTrace_761889 : CollatzResearch.WordTrace tailWord_761889 prefixEnd_761889 260810174915649892989095 := by
  unfold tailWord_761889
  simp only [CollatzResearch.WordTrace]
  refine ⟨27788374736813748126904721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18525583157875832084603147 27788374736813748126904721)
  ·
    refine ⟨20841281052610311095178541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27788374736813748126904721 20841281052610311095178541)
    ·
      refine ⟨7815480394728866660691953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20841281052610311095178541 7815480394728866660691953)
      ·
        refine ⟨5861610296046649995518965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7815480394728866660691953 5861610296046649995518965)
        ·
          refine ⟨549525965254373437079903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5861610296046649995518965 549525965254373437079903)
          ·
            refine ⟨824288947881560155619855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549525965254373437079903 824288947881560155619855)
            ·
              refine ⟨1236433421822340233429783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 824288947881560155619855 1236433421822340233429783)
              ·
                refine ⟨1854650132733510350144675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1236433421822340233429783 1854650132733510350144675)
                ·
                  refine ⟨2781975199100265525217013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1854650132733510350144675 2781975199100265525217013)
                  ·
                    refine ⟨260810174915649892989095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2781975199100265525217013 260810174915649892989095)
                    ·
                      rfl

theorem cell22_761889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 1, 5].length) (baseStart_761889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761889 prefixEnd_761889 := by exact prefixLift 761889
  have htrace : WordTrace (prefixWord ++ tailWord_761889) baseStart_761889 baseEnd_761889 := by
    simpa [prefixWord, tailWord_761889, baseEnd_761889] using wordTrace_append hprefix tailTrace_761889
  have hstable : (prefixWord ++ tailWord_761889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761889).length < 2 ^ (prefixWord ++ tailWord_761889).sum := by decide
  have hdescent : baseEnd_761889 < baseStart_761889 := by decide
  rcases family_descends (prefixWord ++ tailWord_761889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761900 : List Nat := [2, 2, 1, 1, 1, 2, 2, 3, 5, 3]
def baseStart_761900 : Nat := 118140960795 + 761900 * 2 ^ 59
def prefixEnd_761900 : Nat := 4983230072969 + 3 ^ 40 * 761900 * 2
def baseEnd_761900 : Nat := 260813940440449530964061

theorem tailTrace_761900 : CollatzResearch.WordTrace tailWord_761900 prefixEnd_761900 260813940440449530964061 := by
  unfold tailWord_761900
  simp only [CollatzResearch.WordTrace]
  refine ⟨13894387969886948502777577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18525850626515931337036769 13894387969886948502777577)
  ·
    refine ⟨10420790977415211377083183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13894387969886948502777577 10420790977415211377083183)
    ·
      refine ⟨15631186466122817065624775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10420790977415211377083183 15631186466122817065624775)
      ·
        refine ⟨23446779699184225598437163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15631186466122817065624775 23446779699184225598437163)
        ·
          refine ⟨35170169548776338397655745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23446779699184225598437163 35170169548776338397655745)
          ·
            refine ⟨26377627161582253798241809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35170169548776338397655745 26377627161582253798241809)
            ·
              refine ⟨19783220371186690348681357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26377627161582253798241809 19783220371186690348681357)
              ·
                refine ⟨7418707639195008880755509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19783220371186690348681357 7418707639195008880755509)
                ·
                  refine ⟨695503841174532082570829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7418707639195008880755509 695503841174532082570829)
                  ·
                    refine ⟨260813940440449530964061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 695503841174532082570829 260813940440449530964061)
                    ·
                      rfl

theorem cell22_761900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 3].length) (baseStart_761900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761900 prefixEnd_761900 := by exact prefixLift 761900
  have htrace : WordTrace (prefixWord ++ tailWord_761900) baseStart_761900 baseEnd_761900 := by
    simpa [prefixWord, tailWord_761900, baseEnd_761900] using wordTrace_append hprefix tailTrace_761900
  have hstable : (prefixWord ++ tailWord_761900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761900).length < 2 ^ (prefixWord ++ tailWord_761900).sum := by decide
  have hdescent : baseEnd_761900 < baseStart_761900 := by decide
  rcases family_descends (prefixWord ++ tailWord_761900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761902 : List Nat := [4, 1, 3, 1, 1, 2, 4, 6]
def baseStart_761902 : Nat := 118140960795 + 761902 * 2 ^ 59
def prefixEnd_761902 : Nat := 4983230072969 + 3 ^ 40 * 761902 * 2
def baseEnd_761902 : Nat := 28979402786813576934895

theorem tailTrace_761902 : CollatzResearch.WordTrace tailWord_761902 prefixEnd_761902 28979402786813576934895 := by
  unfold tailWord_761902
  simp only [CollatzResearch.WordTrace]
  refine ⟨3473606110720831418390995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18525899257177767564751973 3473606110720831418390995)
  ·
    refine ⟨5210409166081247127586493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3473606110720831418390995 5210409166081247127586493)
    ·
      refine ⟨1953903437280467672844935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5210409166081247127586493 1953903437280467672844935)
      ·
        refine ⟨2930855155920701509267403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1953903437280467672844935 2930855155920701509267403)
        ·
          refine ⟨4396282733881052263901105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2930855155920701509267403 4396282733881052263901105)
          ·
            refine ⟨3297212050410789197925829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4396282733881052263901105 3297212050410789197925829)
            ·
              refine ⟨618227259452022974611093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3297212050410789197925829 618227259452022974611093)
              ·
                refine ⟨28979402786813576934895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 618227259452022974611093 28979402786813576934895)
                ·
                  rfl

theorem cell22_761902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 6].length) (baseStart_761902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761902 prefixEnd_761902 := by exact prefixLift 761902
  have htrace : WordTrace (prefixWord ++ tailWord_761902) baseStart_761902 baseEnd_761902 := by
    simpa [prefixWord, tailWord_761902, baseEnd_761902] using wordTrace_append hprefix tailTrace_761902
  have hstable : (prefixWord ++ tailWord_761902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761902).length < 2 ^ (prefixWord ++ tailWord_761902).sum := by decide
  have hdescent : baseEnd_761902 < baseStart_761902 := by decide
  rcases family_descends (prefixWord ++ tailWord_761902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761908 : List Nat := [2, 5, 1, 2, 3, 1, 1, 3, 4]
def baseStart_761908 : Nat := 118140960795 + 761908 * 2 ^ 59
def prefixEnd_761908 : Nat := 4983230072969 + 3 ^ 40 * 761908 * 2
def baseEnd_761908 : Nat := 86938893001313392254679

theorem tailTrace_761908 : CollatzResearch.WordTrace tailWord_761908 prefixEnd_761908 86938893001313392254679 := by
  unfold tailWord_761908
  simp only [CollatzResearch.WordTrace]
  refine ⟨13894533861872457185923189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18526045149163276247897585 13894533861872457185923189)
  ·
    refine ⟨1302612549550542861180299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13894533861872457185923189 1302612549550542861180299)
    ·
      refine ⟨1953918824325814291770449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1302612549550542861180299 1953918824325814291770449)
      ·
        refine ⟨1465439118244360718827837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1953918824325814291770449 1465439118244360718827837)
        ·
          refine ⟨549539669341635269560439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1465439118244360718827837 549539669341635269560439)
          ·
            refine ⟨824309504012452904340659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549539669341635269560439 824309504012452904340659)
            ·
              refine ⟨1236464256018679356510989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 824309504012452904340659 1236464256018679356510989)
              ·
                refine ⟨463674096007004758691621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1236464256018679356510989 463674096007004758691621)
                ·
                  refine ⟨86938893001313392254679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 463674096007004758691621 86938893001313392254679)
                  ·
                    rfl

theorem cell22_761908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_761908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761908 prefixEnd_761908 := by exact prefixLift 761908
  have htrace : WordTrace (prefixWord ++ tailWord_761908) baseStart_761908 baseEnd_761908 := by
    simpa [prefixWord, tailWord_761908, baseEnd_761908] using wordTrace_append hprefix tailTrace_761908
  have hstable : (prefixWord ++ tailWord_761908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761908).length < 2 ^ (prefixWord ++ tailWord_761908).sum := by decide
  have hdescent : baseEnd_761908 < baseStart_761908 := by decide
  rcases family_descends (prefixWord ++ tailWord_761908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761930 : List Nat := [3, 1, 2, 1, 1, 2, 1, 6, 5]
def baseStart_761930 : Nat := 118140960795 + 761930 * 2 ^ 59
def prefixEnd_761930 : Nat := 4983230072969 + 3 ^ 40 * 761930 * 2
def baseEnd_761930 : Nat := 86941403351179817571323

theorem tailTrace_761930 : CollatzResearch.WordTrace tailWord_761930 prefixEnd_761930 86941403351179817571323 := by
  unfold tailWord_761930
  simp only [CollatzResearch.WordTrace]
  refine ⟨6947467532416303032286811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18526580086443474752764829 6947467532416303032286811)
  ·
    refine ⟨10421201298624454548430217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6947467532416303032286811 10421201298624454548430217)
    ·
      refine ⟨7815900973968340911322663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10421201298624454548430217 7815900973968340911322663)
      ·
        refine ⟨11723851460952511366983995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7815900973968340911322663 11723851460952511366983995)
        ·
          refine ⟨17585777191428767050475993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11723851460952511366983995 17585777191428767050475993)
          ·
            refine ⟨13189332893571575287856995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17585777191428767050475993 13189332893571575287856995)
            ·
              refine ⟨19783999340357362931785493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13189332893571575287856995 19783999340357362931785493)
              ·
                refine ⟨927374969079251387427445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19783999340357362931785493 927374969079251387427445)
                ·
                  refine ⟨86941403351179817571323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 927374969079251387427445 86941403351179817571323)
                  ·
                    rfl

theorem cell22_761930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 5].length) (baseStart_761930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761930 prefixEnd_761930 := by exact prefixLift 761930
  have htrace : WordTrace (prefixWord ++ tailWord_761930) baseStart_761930 baseEnd_761930 := by
    simpa [prefixWord, tailWord_761930, baseEnd_761930] using wordTrace_append hprefix tailTrace_761930
  have hstable : (prefixWord ++ tailWord_761930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761930).length < 2 ^ (prefixWord ++ tailWord_761930).sum := by decide
  have hdescent : baseEnd_761930 < baseStart_761930 := by decide
  rcases family_descends (prefixWord ++ tailWord_761930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761934 : List Nat := [4, 1, 1, 1, 1, 6, 1, 1, 3, 3]
def baseStart_761934 : Nat := 118140960795 + 761934 * 2 ^ 59
def prefixEnd_761934 : Nat := 4983230072969 + 3 ^ 40 * 761934 * 2
def baseEnd_761934 : Nat := 260825579335284775613957

theorem tailTrace_761934 : CollatzResearch.WordTrace tailWord_761934 prefixEnd_761934 260825579335284775613957 := by
  unfold tailWord_761934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3473752002706340101536607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18526677347767147208195237 3473752002706340101536607)
  ·
    refine ⟨5210628004059510152304911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3473752002706340101536607 5210628004059510152304911)
    ·
      refine ⟨7815942006089265228457367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5210628004059510152304911 7815942006089265228457367)
      ·
        refine ⟨11723913009133897842686051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7815942006089265228457367 11723913009133897842686051)
        ·
          refine ⟨17585869513700846764029077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11723913009133897842686051 17585869513700846764029077)
          ·
            refine ⟨824337633454727192063863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17585869513700846764029077 824337633454727192063863)
            ·
              refine ⟨1236506450182090788095795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 824337633454727192063863 1236506450182090788095795)
              ·
                refine ⟨1854759675273136182143693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1236506450182090788095795 1854759675273136182143693)
                ·
                  refine ⟨695534878227426068303885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1854759675273136182143693 695534878227426068303885)
                  ·
                    refine ⟨260825579335284775613957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 695534878227426068303885 260825579335284775613957)
                    ·
                      rfl

theorem cell22_761934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_761934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761934 prefixEnd_761934 := by exact prefixLift 761934
  have htrace : WordTrace (prefixWord ++ tailWord_761934) baseStart_761934 baseEnd_761934 := by
    simpa [prefixWord, tailWord_761934, baseEnd_761934] using wordTrace_append hprefix tailTrace_761934
  have hstable : (prefixWord ++ tailWord_761934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761934).length < 2 ^ (prefixWord ++ tailWord_761934).sum := by decide
  have hdescent : baseEnd_761934 < baseStart_761934 := by decide
  rcases family_descends (prefixWord ++ tailWord_761934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_761985 : List Nat := [1, 2, 4, 2, 4, 1, 2, 2, 1, 3]
def baseStart_761985 : Nat := 118140960795 + 761985 * 2 ^ 59
def prefixEnd_761985 : Nat := 4983230072969 + 3 ^ 40 * 761985 * 2
def baseEnd_761985 : Nat := 260843037677537642588801

theorem tailTrace_761985 : CollatzResearch.WordTrace tailWord_761985 prefixEnd_761985 260843037677537642588801 := by
  unfold tailWord_761985
  simp only [CollatzResearch.WordTrace]
  refine ⟨27791876144465956522399409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18527917429643971014932939 27791876144465956522399409)
  ·
    refine ⟨20843907108349467391799557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27791876144465956522399409 20843907108349467391799557)
    ·
      refine ⟨3908232582815525135962417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20843907108349467391799557 3908232582815525135962417)
      ·
        refine ⟨2931174437111643851971813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3908232582815525135962417 2931174437111643851971813)
        ·
          refine ⟨549595206958433222244715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2931174437111643851971813 549595206958433222244715)
          ·
            refine ⟨824392810437649833367073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549595206958433222244715 824392810437649833367073)
            ·
              refine ⟨618294607828237375025305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 824392810437649833367073 618294607828237375025305)
              ·
                refine ⟨463720955871178031268979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 618294607828237375025305 463720955871178031268979)
                ·
                  refine ⟨695581433806767046903469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 463720955871178031268979 695581433806767046903469)
                  ·
                    refine ⟨260843037677537642588801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 695581433806767046903469 260843037677537642588801)
                    ·
                      rfl

theorem cell22_761985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_761985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_761985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_761985 prefixEnd_761985 := by exact prefixLift 761985
  have htrace : WordTrace (prefixWord ++ tailWord_761985) baseStart_761985 baseEnd_761985 := by
    simpa [prefixWord, tailWord_761985, baseEnd_761985] using wordTrace_append hprefix tailTrace_761985
  have hstable : (prefixWord ++ tailWord_761985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_761985).length < 2 ^ (prefixWord ++ tailWord_761985).sum := by decide
  have hdescent : baseEnd_761985 < baseStart_761985 := by decide
  rcases family_descends (prefixWord ++ tailWord_761985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
