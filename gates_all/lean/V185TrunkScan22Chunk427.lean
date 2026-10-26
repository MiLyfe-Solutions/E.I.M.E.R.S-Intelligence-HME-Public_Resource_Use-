import V185TrunkScan22Chunk426

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3807883 : List Nat := [1, 1, 1, 1, 4, 1, 2, 5, 6]
def baseStart_3807883 : Nat := 118140960795 + 3807883 * 2 ^ 59
def prefixEnd_3807883 : Nat := 4983230072969 + 3 ^ 40 * 3807883 * 2
def baseEnd_3807883 : Nat := 434505390018806749766749

theorem tailTrace_3807883 : CollatzResearch.WordTrace tailWord_3807883 prefixEnd_3807883 434505390018806749766749 := by
  unfold tailWord_3807883
  simp only [CollatzResearch.WordTrace]
  refine ⟨138884902863697700485724303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92589935242465133657149535 138884902863697700485724303)
  ·
    refine ⟨208327354295546550728586455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138884902863697700485724303 208327354295546550728586455)
    ·
      refine ⟨312491031443319826092879683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208327354295546550728586455 312491031443319826092879683)
      ·
        refine ⟨468736547164979739139319525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312491031443319826092879683 468736547164979739139319525)
        ·
          refine ⟨87888102593433701088622411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 468736547164979739139319525 87888102593433701088622411)
          ·
            refine ⟨131832153890150551632933617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87888102593433701088622411 131832153890150551632933617)
            ·
              refine ⟨98874115417612913724700213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131832153890150551632933617 98874115417612913724700213)
              ·
                refine ⟨9269448320401210661690645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98874115417612913724700213 9269448320401210661690645)
                ·
                  refine ⟨434505390018806749766749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9269448320401210661690645 434505390018806749766749)
                  ·
                    rfl

theorem cell22_3807883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 6].length) (baseStart_3807883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3807883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3807883 prefixEnd_3807883 := by exact prefixLift 3807883
  have htrace : WordTrace (prefixWord ++ tailWord_3807883) baseStart_3807883 baseEnd_3807883 := by
    simpa [prefixWord, tailWord_3807883, baseEnd_3807883] using wordTrace_append hprefix tailTrace_3807883
  have hstable : (prefixWord ++ tailWord_3807883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807883).length < 2 ^ (prefixWord ++ tailWord_3807883).sum := by decide
  have hdescent : baseEnd_3807883 < baseStart_3807883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807902 : List Nat := [4, 3, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_3807902 : Nat := 118140960795 + 3807902 * 2 ^ 59
def prefixEnd_3807902 : Nat := 4983230072969 + 3 ^ 40 * 3807902 * 2
def baseEnd_3807902 : Nat := 1303522674144710533075189

theorem tailTrace_3807902 : CollatzResearch.WordTrace tailWord_3807902 prefixEnd_3807902 1303522674144710533075189 := by
  unfold tailWord_3807902
  simp only [CollatzResearch.WordTrace]
  refine ⟨17360699481328608341333245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92590397233752577820443973 17360699481328608341333245)
  ·
    refine ⟨6510262305498228127999967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17360699481328608341333245 6510262305498228127999967)
    ·
      refine ⟨9765393458247342191999951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6510262305498228127999967 9765393458247342191999951)
      ·
        refine ⟨14648090187371013287999927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9765393458247342191999951 14648090187371013287999927)
        ·
          refine ⟨21972135281056519931999891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14648090187371013287999927 21972135281056519931999891)
          ·
            refine ⟨32958202921584779897999837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21972135281056519931999891 32958202921584779897999837)
            ·
              refine ⟨12359326095594292461749939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32958202921584779897999837 12359326095594292461749939)
              ·
                refine ⟨18538989143391438692624909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12359326095594292461749939 18538989143391438692624909)
                ·
                  refine ⟨6952120928771789509734341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18538989143391438692624909 6952120928771789509734341)
                  ·
                    refine ⟨1303522674144710533075189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6952120928771789509734341 1303522674144710533075189)
                    ·
                      rfl

theorem cell22_3807902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_3807902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3807902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3807902 prefixEnd_3807902 := by exact prefixLift 3807902
  have htrace : WordTrace (prefixWord ++ tailWord_3807902) baseStart_3807902 baseEnd_3807902 := by
    simpa [prefixWord, tailWord_3807902, baseEnd_3807902] using wordTrace_append hprefix tailTrace_3807902
  have hstable : (prefixWord ++ tailWord_3807902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807902).length < 2 ^ (prefixWord ++ tailWord_3807902).sum := by decide
  have hdescent : baseEnd_3807902 < baseStart_3807902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807930 : List Nat := [3, 1, 1, 1, 2, 3, 1, 4, 2, 4]
def baseStart_3807930 : Nat := 118140960795 + 3807930 * 2 ^ 59
def prefixEnd_3807930 : Nat := 4983230072969 + 3 ^ 40 * 3807930 * 2
def baseEnd_3807930 : Nat := 1303532259116927793375103

theorem tailTrace_3807930 : CollatzResearch.WordTrace tailWord_3807930 prefixEnd_3807930 1303532259116927793375103 := by
  unfold tailWord_3807930
  simp only [CollatzResearch.WordTrace]
  refine ⟨34721654273631856878171311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92591078063018285008456829 34721654273631856878171311)
  ·
    refine ⟨52082481410447785317256967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34721654273631856878171311 52082481410447785317256967)
    ·
      refine ⟨78123722115671677975885451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52082481410447785317256967 78123722115671677975885451)
      ·
        refine ⟨117185583173507516963828177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78123722115671677975885451 117185583173507516963828177)
        ·
          refine ⟨87889187380130637722871133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117185583173507516963828177 87889187380130637722871133)
          ·
            refine ⟨32958445267548989146076675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87889187380130637722871133 32958445267548989146076675)
            ·
              refine ⟨49437667901323483719115013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32958445267548989146076675 49437667901323483719115013)
              ·
                refine ⟨9269562731498153197334065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49437667901323483719115013 9269562731498153197334065)
                ·
                  refine ⟨6952172048623614898000549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9269562731498153197334065 6952172048623614898000549)
                  ·
                    refine ⟨1303532259116927793375103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6952172048623614898000549 1303532259116927793375103)
                    ·
                      rfl

theorem cell22_3807930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_3807930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3807930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3807930 prefixEnd_3807930 := by exact prefixLift 3807930
  have htrace : WordTrace (prefixWord ++ tailWord_3807930) baseStart_3807930 baseEnd_3807930 := by
    simpa [prefixWord, tailWord_3807930, baseEnd_3807930] using wordTrace_append hprefix tailTrace_3807930
  have hstable : (prefixWord ++ tailWord_3807930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807930).length < 2 ^ (prefixWord ++ tailWord_3807930).sum := by decide
  have hdescent : baseEnd_3807930 < baseStart_3807930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807964 : List Nat := [2, 2, 5, 1, 1, 1, 3, 1, 2, 4]
def baseStart_3807964 : Nat := 118140960795 + 3807964 * 2 ^ 59
def prefixEnd_3807964 : Nat := 4983230072969 + 3 ^ 40 * 3807964 * 2
def baseEnd_3807964 : Nat := 1303543898011763038024999

theorem tailTrace_3807964 : CollatzResearch.WordTrace tailWord_3807964 prefixEnd_3807964 1303543898011763038024999 := by
  unfold tailWord_3807964
  simp only [CollatzResearch.WordTrace]
  refine ⟨69443928588202125659711473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92591904784269500879615297 69443928588202125659711473)
  ·
    refine ⟨52082946441151594244783605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69443928588202125659711473 52082946441151594244783605)
    ·
      refine ⟨4882776228857961960448463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52082946441151594244783605 4882776228857961960448463)
      ·
        refine ⟨7324164343286942940672695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4882776228857961960448463 7324164343286942940672695)
        ·
          refine ⟨10986246514930414411009043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7324164343286942940672695 10986246514930414411009043)
          ·
            refine ⟨16479369772395621616513565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10986246514930414411009043 16479369772395621616513565)
            ·
              refine ⟨6179763664648358106192587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16479369772395621616513565 6179763664648358106192587)
              ·
                refine ⟨9269645496972537159288881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6179763664648358106192587 9269645496972537159288881)
                ·
                  refine ⟨6952234122729402869466661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9269645496972537159288881 6952234122729402869466661)
                  ·
                    refine ⟨1303543898011763038024999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6952234122729402869466661 1303543898011763038024999)
                    ·
                      rfl

theorem cell22_3807964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_3807964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3807964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3807964 prefixEnd_3807964 := by exact prefixLift 3807964
  have htrace : WordTrace (prefixWord ++ tailWord_3807964) baseStart_3807964 baseEnd_3807964 := by
    simpa [prefixWord, tailWord_3807964, baseEnd_3807964] using wordTrace_append hprefix tailTrace_3807964
  have hstable : (prefixWord ++ tailWord_3807964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807964).length < 2 ^ (prefixWord ++ tailWord_3807964).sum := by decide
  have hdescent : baseEnd_3807964 < baseStart_3807964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3807994 : List Nat := [3, 1, 1, 1, 1, 3, 4, 4, 1, 3]
def baseStart_3807994 : Nat := 118140960795 + 3807994 * 2 ^ 59
def prefixEnd_3807994 : Nat := 4983230072969 + 3 ^ 40 * 3807994 * 2
def baseEnd_3807994 : Nat := 1303554167624852959774907

theorem tailTrace_3807994 : CollatzResearch.WordTrace tailWord_3807994 prefixEnd_3807994 1303554167624852959774907 := by
  unfold tailWord_3807994
  simp only [CollatzResearch.WordTrace]
  refine ⟨34722237841573891610753759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92592634244197044295343357 34722237841573891610753759)
  ·
    refine ⟨52083356762360837416130639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34722237841573891610753759 52083356762360837416130639)
    ·
      refine ⟨78125035143541256124195959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52083356762360837416130639 78125035143541256124195959)
      ·
        refine ⟨117187552715311884186293939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78125035143541256124195959 117187552715311884186293939)
        ·
          refine ⟨175781329072967826279440909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117187552715311884186293939 175781329072967826279440909)
          ·
            refine ⟨65917998402362934854790341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175781329072967826279440909 65917998402362934854790341)
            ·
              refine ⟨12359624700443050285273189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65917998402362934854790341 12359624700443050285273189)
              ·
                refine ⟨2317429631333071928488723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12359624700443050285273189 2317429631333071928488723)
                ·
                  refine ⟨3476144446999607892733085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2317429631333071928488723 3476144446999607892733085)
                  ·
                    refine ⟨1303554167624852959774907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3476144446999607892733085 1303554167624852959774907)
                    ·
                      rfl

theorem cell22_3807994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 4, 1, 3].length) (baseStart_3807994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3807994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3807994 prefixEnd_3807994 := by exact prefixLift 3807994
  have htrace : WordTrace (prefixWord ++ tailWord_3807994) baseStart_3807994 baseEnd_3807994 := by
    simpa [prefixWord, tailWord_3807994, baseEnd_3807994] using wordTrace_append hprefix tailTrace_3807994
  have hstable : (prefixWord ++ tailWord_3807994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3807994).length < 2 ^ (prefixWord ++ tailWord_3807994).sum := by decide
  have hdescent : baseEnd_3807994 < baseStart_3807994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3807994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808037 : List Nat := [1, 3, 1, 2, 3, 1, 1, 5, 1, 4]
def baseStart_3808037 : Nat := 118140960795 + 3808037 * 2 ^ 59
def prefixEnd_3808037 : Nat := 4983230072969 + 3 ^ 40 * 3808037 * 2
def baseEnd_3808037 : Nat := 1303568887403615180949775

theorem tailTrace_3808037 : CollatzResearch.WordTrace tailWord_3808037 prefixEnd_3808037 1303568887403615180949775 := by
  unfold tailWord_3808037
  simp only [CollatzResearch.WordTrace]
  refine ⟨138890519705139784786830365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92593679803426523191220243 138890519705139784786830365)
  ·
    refine ⟨52083944889427419295061387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138890519705139784786830365 52083944889427419295061387)
    ·
      refine ⟨78125917334141128942592081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52083944889427419295061387 78125917334141128942592081)
      ·
        refine ⟨58594438000605846706944061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78125917334141128942592081 58594438000605846706944061)
        ·
          refine ⟨21972914250227192515104023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58594438000605846706944061 21972914250227192515104023)
          ·
            refine ⟨32959371375340788772656035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21972914250227192515104023 32959371375340788772656035)
            ·
              refine ⟨49439057063011183158984053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32959371375340788772656035 49439057063011183158984053)
              ·
                refine ⟨4634911599657298421154755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49439057063011183158984053 4634911599657298421154755)
                ·
                  refine ⟨6952367399485947631732133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4634911599657298421154755 6952367399485947631732133)
                  ·
                    refine ⟨1303568887403615180949775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6952367399485947631732133 1303568887403615180949775)
                    ·
                      rfl

theorem cell22_3808037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 4].length) (baseStart_3808037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3808037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3808037 prefixEnd_3808037 := by exact prefixLift 3808037
  have htrace : WordTrace (prefixWord ++ tailWord_3808037) baseStart_3808037 baseEnd_3808037 := by
    simpa [prefixWord, tailWord_3808037, baseEnd_3808037] using wordTrace_append hprefix tailTrace_3808037
  have hstable : (prefixWord ++ tailWord_3808037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808037).length < 2 ^ (prefixWord ++ tailWord_3808037).sum := by decide
  have hdescent : baseEnd_3808037 < baseStart_3808037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808045 : List Nat := [1, 5, 3, 2, 2, 1, 1, 1, 3, 3]
def baseStart_3808045 : Nat := 118140960795 + 3808045 * 2 ^ 59
def prefixEnd_3808045 : Nat := 4983230072969 + 3 ^ 40 * 3808045 * 2
def baseEnd_3808045 : Nat := 1303571625967105826749751

theorem tailTrace_3808045 : CollatzResearch.WordTrace tailWord_3808045 prefixEnd_3808045 1303571625967105826749751 := by
  unfold tailWord_3808045
  simp only [CollatzResearch.WordTrace]
  refine ⟨138890811489110802153121589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92593874326073868102081059 138890811489110802153121589)
  ·
    refine ⟨13021013577104137701855149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138890811489110802153121589 13021013577104137701855149)
    ·
      refine ⟨4882880091414051638195681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13021013577104137701855149 4882880091414051638195681)
      ·
        refine ⟨3662160068560538728646761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4882880091414051638195681 3662160068560538728646761)
        ·
          refine ⟨2746620051420404046485071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3662160068560538728646761 2746620051420404046485071)
          ·
            refine ⟨4119930077130606069727607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2746620051420404046485071 4119930077130606069727607)
            ·
              refine ⟨6179895115695909104591411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4119930077130606069727607 6179895115695909104591411)
              ·
                refine ⟨9269842673543863656887117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6179895115695909104591411 9269842673543863656887117)
                ·
                  refine ⟨3476191002578948871332669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9269842673543863656887117 3476191002578948871332669)
                  ·
                    refine ⟨1303571625967105826749751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3476191002578948871332669 1303571625967105826749751)
                    ·
                      rfl

theorem cell22_3808045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_3808045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3808045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3808045 prefixEnd_3808045 := by exact prefixLift 3808045
  have htrace : WordTrace (prefixWord ++ tailWord_3808045) baseStart_3808045 baseEnd_3808045 := by
    simpa [prefixWord, tailWord_3808045, baseEnd_3808045] using wordTrace_append hprefix tailTrace_3808045
  have hstable : (prefixWord ++ tailWord_3808045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808045).length < 2 ^ (prefixWord ++ tailWord_3808045).sum := by decide
  have hdescent : baseEnd_3808045 < baseStart_3808045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808080 : List Nat := [2, 1, 1, 1, 1, 4, 4, 8]
def baseStart_3808080 : Nat := 118140960795 + 3808080 * 2 ^ 59
def prefixEnd_3808080 : Nat := 4983230072969 + 3 ^ 40 * 3808080 * 2
def baseEnd_3808080 : Nat := 144842623020264155791627

theorem tailTrace_3808080 : CollatzResearch.WordTrace tailWord_3808080 prefixEnd_3808080 144842623020264155791627 := by
  unfold tailWord_3808080
  simp only [CollatzResearch.WordTrace]
  refine ⟨69446044021992001565322847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92594725362656002087097129 69446044021992001565322847)
  ·
    refine ⟨104169066032988002347984271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69446044021992001565322847 104169066032988002347984271)
    ·
      refine ⟨156253599049482003521976407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104169066032988002347984271 156253599049482003521976407)
      ·
        refine ⟨234380398574223005282964611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156253599049482003521976407 234380398574223005282964611)
        ·
          refine ⟨351570597861334507924446917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234380398574223005282964611 351570597861334507924446917)
          ·
            refine ⟨65919487099000220235833797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 351570597861334507924446917 65919487099000220235833797)
            ·
              refine ⟨12359903831062541294218837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65919487099000220235833797 12359903831062541294218837)
              ·
                refine ⟨144842623020264155791627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12359903831062541294218837 144842623020264155791627)
                ·
                  rfl

theorem cell22_3808080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 8].length) (baseStart_3808080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3808080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3808080 prefixEnd_3808080 := by exact prefixLift 3808080
  have htrace : WordTrace (prefixWord ++ tailWord_3808080) baseStart_3808080 baseEnd_3808080 := by
    simpa [prefixWord, tailWord_3808080, baseEnd_3808080] using wordTrace_append hprefix tailTrace_3808080
  have hstable : (prefixWord ++ tailWord_3808080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808080).length < 2 ^ (prefixWord ++ tailWord_3808080).sum := by decide
  have hdescent : baseEnd_3808080 < baseStart_3808080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808084 : List Nat := [2, 4, 1, 1, 4, 1, 1, 2, 1, 5]
def baseStart_3808084 : Nat := 118140960795 + 3808084 * 2 ^ 59
def prefixEnd_3808084 : Nat := 4983230072969 + 3 ^ 40 * 3808084 * 2
def baseEnd_3808084 : Nat := 1303584976464122725024631

theorem tailTrace_3808084 : CollatzResearch.WordTrace tailWord_3808084 prefixEnd_3808084 1303584976464122725024631 := by
  unfold tailWord_3808084
  simp only [CollatzResearch.WordTrace]
  refine ⟨69446116967984755906895653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92594822623979674542527537 69446116967984755906895653)
  ·
    refine ⟨13021146931497141732542935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69446116967984755906895653 13021146931497141732542935)
    ·
      refine ⟨19531720397245712598814403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13021146931497141732542935 19531720397245712598814403)
      ·
        refine ⟨29297580595868568898221605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19531720397245712598814403 29297580595868568898221605)
        ·
          refine ⟨5493296361725356668416551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29297580595868568898221605 5493296361725356668416551)
          ·
            refine ⟨8239944542588035002624827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5493296361725356668416551 8239944542588035002624827)
            ·
              refine ⟨12359916813882052503937241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8239944542588035002624827 12359916813882052503937241)
              ·
                refine ⟨9269937610411539377952931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12359916813882052503937241 9269937610411539377952931)
                ·
                  refine ⟨13904906415617309066929397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9269937610411539377952931 13904906415617309066929397)
                  ·
                    refine ⟨1303584976464122725024631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13904906415617309066929397 1303584976464122725024631)
                    ·
                      rfl

theorem cell22_3808084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_3808084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3808084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3808084 prefixEnd_3808084 := by exact prefixLift 3808084
  have htrace : WordTrace (prefixWord ++ tailWord_3808084) baseStart_3808084 baseEnd_3808084 := by
    simpa [prefixWord, tailWord_3808084, baseEnd_3808084] using wordTrace_append hprefix tailTrace_3808084
  have hstable : (prefixWord ++ tailWord_3808084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808084).length < 2 ^ (prefixWord ++ tailWord_3808084).sum := by decide
  have hdescent : baseEnd_3808084 < baseStart_3808084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808157 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 4, 5]
def baseStart_3808157 : Nat := 118140960795 + 3808157 * 2 ^ 59
def prefixEnd_3808157 : Nat := 4983230072969 + 3 ^ 40 * 3808157 * 2
def baseEnd_3808157 : Nat := 1303609965855974867949407

theorem tailTrace_3808157 : CollatzResearch.WordTrace tailWord_3808157 prefixEnd_3808157 1303609965855974867949407 := by
  unfold tailWord_3808157
  simp only [CollatzResearch.WordTrace]
  refine ⟨138894896464705045281198725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92596597643136696854132483 138894896464705045281198725)
  ·
    refine ⟨26042793087132195990224761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138894896464705045281198725 26042793087132195990224761)
    ·
      refine ⟨19532094815349146992668571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26042793087132195990224761 19532094815349146992668571)
      ·
        refine ⟨29298142223023720489002857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19532094815349146992668571 29298142223023720489002857)
        ·
          refine ⟨21973606667267790366752143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29298142223023720489002857 21973606667267790366752143)
          ·
            refine ⟨32960410000901685550128215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21973606667267790366752143 32960410000901685550128215)
            ·
              refine ⟨49440615001352528325192323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32960410000901685550128215 49440615001352528325192323)
              ·
                refine ⟨74160922502028792487788485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49440615001352528325192323 74160922502028792487788485)
                ·
                  refine ⟨13905172969130398591460341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74160922502028792487788485 13905172969130398591460341)
                  ·
                    refine ⟨1303609965855974867949407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13905172969130398591460341 1303609965855974867949407)
                    ·
                      rfl

theorem cell22_3808157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_3808157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3808157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3808157 prefixEnd_3808157 := by exact prefixLift 3808157
  have htrace : WordTrace (prefixWord ++ tailWord_3808157) baseStart_3808157 baseEnd_3808157 := by
    simpa [prefixWord, tailWord_3808157, baseEnd_3808157] using wordTrace_append hprefix tailTrace_3808157
  have hstable : (prefixWord ++ tailWord_3808157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808157).length < 2 ^ (prefixWord ++ tailWord_3808157).sum := by decide
  have hdescent : baseEnd_3808157 < baseStart_3808157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808159 : List Nat := [1, 1, 2, 5, 2, 1, 3, 2, 5]
def baseStart_3808159 : Nat := 118140960795 + 3808159 * 2 ^ 59
def prefixEnd_3808159 : Nat := 4983230072969 + 3 ^ 40 * 3808159 * 2
def baseEnd_3808159 : Nat := 434536883498949176466467

theorem tailTrace_3808159 : CollatzResearch.WordTrace tailWord_3808159 prefixEnd_3808159 434536883498949176466467 := by
  unfold tailWord_3808159
  simp only [CollatzResearch.WordTrace]
  refine ⟨138894969410697799622771531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92596646273798533081847687 138894969410697799622771531)
  ·
    refine ⟨208342454116046699434157297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138894969410697799622771531 208342454116046699434157297)
    ·
      refine ⟨156256840587035024575617973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208342454116046699434157297 156256840587035024575617973)
      ·
        refine ⟨14649078805034533553964185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156256840587035024575617973 14649078805034533553964185)
        ·
          refine ⟨10986809103775900165473139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14649078805034533553964185 10986809103775900165473139)
          ·
            refine ⟨16480213655663850248209709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10986809103775900165473139 16480213655663850248209709)
            ·
              refine ⟨6180080120873943843078641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16480213655663850248209709 6180080120873943843078641)
              ·
                refine ⟨4635060090655457882308981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6180080120873943843078641 4635060090655457882308981)
                ·
                  refine ⟨434536883498949176466467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4635060090655457882308981 434536883498949176466467)
                  ·
                    rfl

theorem cell22_3808159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 5].length) (baseStart_3808159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3808159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3808159 prefixEnd_3808159 := by exact prefixLift 3808159
  have htrace : WordTrace (prefixWord ++ tailWord_3808159) baseStart_3808159 baseEnd_3808159 := by
    simpa [prefixWord, tailWord_3808159, baseEnd_3808159] using wordTrace_append hprefix tailTrace_3808159
  have hstable : (prefixWord ++ tailWord_3808159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808159).length < 2 ^ (prefixWord ++ tailWord_3808159).sum := by decide
  have hdescent : baseEnd_3808159 < baseStart_3808159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808182 : List Nat := [5, 1, 4, 1, 2, 1, 2, 6]
def baseStart_3808182 : Nat := 118140960795 + 3808182 * 2 ^ 59
def prefixEnd_3808182 : Nat := 4983230072969 + 3 ^ 40 * 3808182 * 2
def baseEnd_3808182 : Nat := 144846502651875904008259

theorem tailTrace_3808182 : CollatzResearch.WordTrace tailWord_3808182 prefixEnd_3808182 144846502651875904008259 := by
  unfold tailWord_3808182
  simp only [CollatzResearch.WordTrace]
  refine ⟨8680988018100904659428675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92597205526409649700572533 8680988018100904659428675)
  ·
    refine ⟨13021482027151356989143013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8680988018100904659428675 13021482027151356989143013)
    ·
      refine ⟨2441527880090879435464315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13021482027151356989143013 2441527880090879435464315)
      ·
        refine ⟨3662291820136319153196473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2441527880090879435464315 3662291820136319153196473)
        ·
          refine ⟨2746718865102239364897355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3662291820136319153196473 2746718865102239364897355)
          ·
            refine ⟨4120078297653359047346033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2746718865102239364897355 4120078297653359047346033)
            ·
              refine ⟨3090058723240019285509525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4120078297653359047346033 3090058723240019285509525)
              ·
                refine ⟨144846502651875904008259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3090058723240019285509525 144846502651875904008259)
                ·
                  rfl

theorem cell22_3808182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_3808182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3808182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3808182 prefixEnd_3808182 := by exact prefixLift 3808182
  have htrace : WordTrace (prefixWord ++ tailWord_3808182) baseStart_3808182 baseEnd_3808182 := by
    simpa [prefixWord, tailWord_3808182, baseEnd_3808182] using wordTrace_append hprefix tailTrace_3808182
  have hstable : (prefixWord ++ tailWord_3808182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808182).length < 2 ^ (prefixWord ++ tailWord_3808182).sum := by decide
  have hdescent : baseEnd_3808182 < baseStart_3808182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808202 : List Nat := [3, 1, 2, 1, 2, 1, 1, 3, 3, 5]
def baseStart_3808202 : Nat := 118140960795 + 3808202 * 2 ^ 59
def prefixEnd_3808202 : Nat := 4983230072969 + 3 ^ 40 * 3808202 * 2
def baseEnd_3808202 : Nat := 1303625370275609750574269

theorem tailTrace_3808202 : CollatzResearch.WordTrace tailWord_3808202 prefixEnd_3808202 1303625370275609750574269 := by
  unfold tailWord_3808202
  simp only [CollatzResearch.WordTrace]
  refine ⟨34724134437385504491646715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92597691833028011977724573 34724134437385504491646715)
  ·
    refine ⟨52086201656078256737470073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34724134437385504491646715 52086201656078256737470073)
    ·
      refine ⟨39064651242058692553102555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52086201656078256737470073 39064651242058692553102555)
      ·
        refine ⟨58596976863088038829653833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39064651242058692553102555 58596976863088038829653833)
        ·
          refine ⟨43947732647316029122240375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58596976863088038829653833 43947732647316029122240375)
          ·
            refine ⟨65921598970974043683360563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43947732647316029122240375 65921598970974043683360563)
            ·
              refine ⟨98882398456461065525040845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65921598970974043683360563 98882398456461065525040845)
              ·
                refine ⟨37080899421172899571890317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98882398456461065525040845 37080899421172899571890317)
                ·
                  refine ⟨13905337282939837339458869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37080899421172899571890317 13905337282939837339458869)
                  ·
                    refine ⟨1303625370275609750574269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13905337282939837339458869 1303625370275609750574269)
                    ·
                      rfl

theorem cell22_3808202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_3808202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3808202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3808202 prefixEnd_3808202 := by exact prefixLift 3808202
  have htrace : WordTrace (prefixWord ++ tailWord_3808202) baseStart_3808202 baseEnd_3808202 := by
    simpa [prefixWord, tailWord_3808202, baseEnd_3808202] using wordTrace_append hprefix tailTrace_3808202
  have hstable : (prefixWord ++ tailWord_3808202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808202).length < 2 ^ (prefixWord ++ tailWord_3808202).sum := by decide
  have hdescent : baseEnd_3808202 < baseStart_3808202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808221 : List Nat := [1, 4, 3, 1, 2, 3, 1, 1, 6]
def baseStart_3808221 : Nat := 118140960795 + 3808221 * 2 ^ 59
def prefixEnd_3808221 : Nat := 4983230072969 + 3 ^ 40 * 3808221 * 2
def baseEnd_3808221 : Nat := 434543958121300011449737

theorem tailTrace_3808221 : CollatzResearch.WordTrace tailWord_3808221 prefixEnd_3808221 434543958121300011449737 := by
  unfold tailWord_3808221
  simp only [CollatzResearch.WordTrace]
  refine ⟨138897230736473184211528517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92598153824315456141019011 138897230736473184211528517)
  ·
    refine ⟨26043230763088722039661597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138897230736473184211528517 26043230763088722039661597)
    ·
      refine ⟨9766211536158270764873099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26043230763088722039661597 9766211536158270764873099)
      ·
        refine ⟨14649317304237406147309649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9766211536158270764873099 14649317304237406147309649)
        ·
          refine ⟨10986987978178054610482237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14649317304237406147309649 10986987978178054610482237)
          ·
            refine ⟨4120120491816770478930839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10986987978178054610482237 4120120491816770478930839)
            ·
              refine ⟨6180180737725155718396259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4120120491816770478930839 6180180737725155718396259)
              ·
                refine ⟨9270271106587733577594389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6180180737725155718396259 9270271106587733577594389)
                ·
                  refine ⟨434543958121300011449737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9270271106587733577594389 434543958121300011449737)
                  ·
                    rfl

theorem cell22_3808221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_3808221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3808221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3808221 prefixEnd_3808221 := by exact prefixLift 3808221
  have htrace : WordTrace (prefixWord ++ tailWord_3808221) baseStart_3808221 baseEnd_3808221 := by
    simpa [prefixWord, tailWord_3808221, baseEnd_3808221] using wordTrace_append hprefix tailTrace_3808221
  have hstable : (prefixWord ++ tailWord_3808221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808221).length < 2 ^ (prefixWord ++ tailWord_3808221).sum := by decide
  have hdescent : baseEnd_3808221 < baseStart_3808221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808232 : List Nat := [2, 1, 4, 1, 1, 1, 3, 9]
def baseStart_3808232 : Nat := 118140960795 + 3808232 * 2 ^ 59
def prefixEnd_3808232 : Nat := 4983230072969 + 3 ^ 40 * 3808232 * 2
def baseEnd_3808232 : Nat := 144848404432077741369353

theorem tailTrace_3808232 : CollatzResearch.WordTrace tailWord_3808232 prefixEnd_3808232 144848404432077741369353 := by
  unfold tailWord_3808232
  simp only [CollatzResearch.WordTrace]
  refine ⟨69448815969716666545089475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92598421292955555393452633 69448815969716666545089475)
  ·
    refine ⟨104173223954574999817634213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69448815969716666545089475 104173223954574999817634213)
    ·
      refine ⟨19532479491482812465806415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104173223954574999817634213 19532479491482812465806415)
      ·
        refine ⟨29298719237224218698709623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19532479491482812465806415 29298719237224218698709623)
        ·
          refine ⟨43948078855836328048064435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29298719237224218698709623 43948078855836328048064435)
          ·
            refine ⟨65922118283754492072096653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43948078855836328048064435 65922118283754492072096653)
            ·
              refine ⟨24720794356407934527036245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65922118283754492072096653 24720794356407934527036245)
              ·
                refine ⟨144848404432077741369353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24720794356407934527036245 144848404432077741369353)
                ·
                  rfl

theorem cell22_3808232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 9].length) (baseStart_3808232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3808232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3808232 prefixEnd_3808232 := by exact prefixLift 3808232
  have htrace : WordTrace (prefixWord ++ tailWord_3808232) baseStart_3808232 baseEnd_3808232 := by
    simpa [prefixWord, tailWord_3808232, baseEnd_3808232] using wordTrace_append hprefix tailTrace_3808232
  have hstable : (prefixWord ++ tailWord_3808232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808232).length < 2 ^ (prefixWord ++ tailWord_3808232).sum := by decide
  have hdescent : baseEnd_3808232 < baseStart_3808232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808279 : List Nat := [1, 1, 3, 5, 1, 1, 1, 1, 2, 6]
def baseStart_3808279 : Nat := 118140960795 + 3808279 * 2 ^ 59
def prefixEnd_3808279 : Nat := 4983230072969 + 3 ^ 40 * 3808279 * 2
def baseEnd_3808279 : Nat := 1303651728949207216399033

theorem tailTrace_3808279 : CollatzResearch.WordTrace tailWord_3808279 prefixEnd_3808279 1303651728949207216399033 := by
  unfold tailWord_3808279
  simp only [CollatzResearch.WordTrace]
  refine ⟨138899346170263060117139891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92599564113508706744759927 138899346170263060117139891)
  ·
    refine ⟨208349019255394590175709837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138899346170263060117139891 208349019255394590175709837)
    ·
      refine ⟨78130882220772971315891189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208349019255394590175709837 78130882220772971315891189)
      ·
        refine ⟨7324770208197466060864799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78130882220772971315891189 7324770208197466060864799)
        ·
          refine ⟨10987155312296199091297199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7324770208197466060864799 10987155312296199091297199)
          ·
            refine ⟨16480732968444298636945799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10987155312296199091297199 16480732968444298636945799)
            ·
              refine ⟨24721099452666447955418699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16480732968444298636945799 24721099452666447955418699)
              ·
                refine ⟨37081649178999671933128049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24721099452666447955418699 37081649178999671933128049)
                ·
                  refine ⟨27811236884249753949846037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37081649178999671933128049 27811236884249753949846037)
                  ·
                    refine ⟨1303651728949207216399033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27811236884249753949846037 1303651728949207216399033)
                    ·
                      rfl

theorem cell22_3808279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_3808279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3808279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3808279 prefixEnd_3808279 := by exact prefixLift 3808279
  have htrace : WordTrace (prefixWord ++ tailWord_3808279) baseStart_3808279 baseEnd_3808279 := by
    simpa [prefixWord, tailWord_3808279, baseEnd_3808279] using wordTrace_append hprefix tailTrace_3808279
  have hstable : (prefixWord ++ tailWord_3808279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808279).length < 2 ^ (prefixWord ++ tailWord_3808279).sum := by decide
  have hdescent : baseEnd_3808279 < baseStart_3808279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808298 : List Nat := [3, 1, 4, 1, 3, 1, 1, 2, 3, 3]
def baseStart_3808298 : Nat := 118140960795 + 3808298 * 2 ^ 59
def prefixEnd_3808298 : Nat := 4983230072969 + 3 ^ 40 * 3808298 * 2
def baseEnd_3808298 : Nat := 1303658233037497500173975

theorem tailTrace_3808298 : CollatzResearch.WordTrace tailWord_3808298 prefixEnd_3808298 1303658233037497500173975 := by
  unfold tailWord_3808298
  simp only [CollatzResearch.WordTrace]
  refine ⟨34725009789298556590520387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92600026104796150908054365 34725009789298556590520387)
  ·
    refine ⟨52087514683947834885780581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34725009789298556590520387 52087514683947834885780581)
    ·
      refine ⟨9766409003240219041083859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52087514683947834885780581 9766409003240219041083859)
      ·
        refine ⟨14649613504860328561625789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9766409003240219041083859 14649613504860328561625789)
        ·
          refine ⟨5493605064322623210609671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14649613504860328561625789 5493605064322623210609671)
          ·
            refine ⟨8240407596483934815914507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5493605064322623210609671 8240407596483934815914507)
            ·
              refine ⟨12360611394725902223871761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8240407596483934815914507 12360611394725902223871761)
              ·
                refine ⟨9270458546044426667903821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12360611394725902223871761 9270458546044426667903821)
                ·
                  refine ⟨3476421954766660000463933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9270458546044426667903821 3476421954766660000463933)
                  ·
                    refine ⟨1303658233037497500173975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3476421954766660000463933 1303658233037497500173975)
                    ·
                      rfl

theorem cell22_3808298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_3808298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3808298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3808298 prefixEnd_3808298 := by exact prefixLift 3808298
  have htrace : WordTrace (prefixWord ++ tailWord_3808298) baseStart_3808298 baseEnd_3808298 := by
    simpa [prefixWord, tailWord_3808298, baseEnd_3808298] using wordTrace_append hprefix tailTrace_3808298
  have hstable : (prefixWord ++ tailWord_3808298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808298).length < 2 ^ (prefixWord ++ tailWord_3808298).sum := by decide
  have hdescent : baseEnd_3808298 < baseStart_3808298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808416 : List Nat := [2, 1, 1, 4, 2, 1, 2, 1, 5, 3]
def baseStart_3808416 : Nat := 118140960795 + 3808416 * 2 ^ 59
def prefixEnd_3808416 : Nat := 4983230072969 + 3 ^ 40 * 3808416 * 2
def baseEnd_3808416 : Nat := 1303698626848984525723613

theorem tailTrace_3808416 : CollatzResearch.WordTrace tailWord_3808416 prefixEnd_3808416 1303698626848984525723613 := by
  unfold tailWord_3808416
  simp only [CollatzResearch.WordTrace]
  refine ⟨69452171485383366257438551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92602895313844488343251401 69452171485383366257438551)
  ·
    refine ⟨104178257228075049386157827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69452171485383366257438551 104178257228075049386157827)
    ·
      refine ⟨156267385842112574079236741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104178257228075049386157827 156267385842112574079236741)
      ·
        refine ⟨29300134845396107639856889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156267385842112574079236741 29300134845396107639856889)
        ·
          refine ⟨21975101134047080729892667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29300134845396107639856889 21975101134047080729892667)
          ·
            refine ⟨32962651701070621094839001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21975101134047080729892667 32962651701070621094839001)
            ·
              refine ⟨24721988775802965821129251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32962651701070621094839001 24721988775802965821129251)
              ·
                refine ⟨37082983163704448731693877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24721988775802965821129251 37082983163704448731693877)
                ·
                  refine ⟨3476529671597292068596301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37082983163704448731693877 3476529671597292068596301)
                  ·
                    refine ⟨1303698626848984525723613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3476529671597292068596301 1303698626848984525723613)
                    ·
                      rfl

theorem cell22_3808416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 5, 3].length) (baseStart_3808416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3808416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3808416 prefixEnd_3808416 := by exact prefixLift 3808416
  have htrace : WordTrace (prefixWord ++ tailWord_3808416) baseStart_3808416 baseEnd_3808416 := by
    simpa [prefixWord, tailWord_3808416, baseEnd_3808416] using wordTrace_append hprefix tailTrace_3808416
  have hstable : (prefixWord ++ tailWord_3808416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808416).length < 2 ^ (prefixWord ++ tailWord_3808416).sum := by decide
  have hdescent : baseEnd_3808416 < baseStart_3808416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808508 : List Nat := [2, 2, 2, 1, 5, 1, 2, 1, 6]
def baseStart_3808508 : Nat := 118140960795 + 3808508 * 2 ^ 59
def prefixEnd_3808508 : Nat := 4983230072969 + 3 ^ 40 * 3808508 * 2
def baseEnd_3808508 : Nat := 434576706776375650807777

theorem tailTrace_3808508 : CollatzResearch.WordTrace tailWord_3808508 prefixEnd_3808508 434576706776375650807777 := by
  unfold tailWord_3808508
  simp only [CollatzResearch.WordTrace]
  refine ⟨69453849243216716113613089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92605132324288954818150785 69453849243216716113613089)
  ·
    refine ⟨52090386932412537085209817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69453849243216716113613089 52090386932412537085209817)
    ·
      refine ⟨39067790199309402813907363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52090386932412537085209817 39067790199309402813907363)
      ·
        refine ⟨58601685298964104220861045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39067790199309402813907363 58601685298964104220861045)
        ·
          refine ⟨5493907996777884770705723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58601685298964104220861045 5493907996777884770705723)
          ·
            refine ⟨8240861995166827156058585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5493907996777884770705723 8240861995166827156058585)
            ·
              refine ⟨6180646496375120367043939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8240861995166827156058585 6180646496375120367043939)
              ·
                refine ⟨9270969744562680550565909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6180646496375120367043939 9270969744562680550565909)
                ·
                  refine ⟨434576706776375650807777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9270969744562680550565909 434576706776375650807777)
                  ·
                    rfl

theorem cell22_3808508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 6].length) (baseStart_3808508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3808508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3808508 prefixEnd_3808508 := by exact prefixLift 3808508
  have htrace : WordTrace (prefixWord ++ tailWord_3808508) baseStart_3808508 baseEnd_3808508 := by
    simpa [prefixWord, tailWord_3808508, baseEnd_3808508] using wordTrace_append hprefix tailTrace_3808508
  have hstable : (prefixWord ++ tailWord_3808508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808508).length < 2 ^ (prefixWord ++ tailWord_3808508).sum := by decide
  have hdescent : baseEnd_3808508 < baseStart_3808508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808523 : List Nat := [1, 1, 1, 1, 5, 5, 1, 1, 1, 5]
def baseStart_3808523 : Nat := 118140960795 + 3808523 * 2 ^ 59
def prefixEnd_3808523 : Nat := 4983230072969 + 3 ^ 40 * 3808523 * 2
def baseEnd_3808523 : Nat := 1303735255135671913298285

theorem tailTrace_3808523 : CollatzResearch.WordTrace tailWord_3808523 prefixEnd_3808523 1303735255135671913298285 := by
  unfold tailWord_3808523
  simp only [CollatzResearch.WordTrace]
  refine ⟨138908245581379089789022223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92605497054252726526014815 138908245581379089789022223)
  ·
    refine ⟨208362368372068634683533335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138908245581379089789022223 208362368372068634683533335)
    ·
      refine ⟨312543552558102952025300003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208362368372068634683533335 312543552558102952025300003)
      ·
        refine ⟨468815328837154428037950005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312543552558102952025300003 468815328837154428037950005)
        ·
          refine ⟨43951437078483227628557813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 468815328837154428037950005 43951437078483227628557813)
          ·
            refine ⟨4120447226107802590177295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43951437078483227628557813 4120447226107802590177295)
            ·
              refine ⟨6180670839161703885265943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4120447226107802590177295 6180670839161703885265943)
              ·
                refine ⟨9271006258742555827898915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6180670839161703885265943 9271006258742555827898915)
                ·
                  refine ⟨13906509388113833741848373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9271006258742555827898915 13906509388113833741848373)
                  ·
                    refine ⟨1303735255135671913298285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13906509388113833741848373 1303735255135671913298285)
                    ·
                      rfl

theorem cell22_3808523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 5].length) (baseStart_3808523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3808523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3808523 prefixEnd_3808523 := by exact prefixLift 3808523
  have htrace : WordTrace (prefixWord ++ tailWord_3808523) baseStart_3808523 baseEnd_3808523 := by
    simpa [prefixWord, tailWord_3808523, baseEnd_3808523] using wordTrace_append hprefix tailTrace_3808523
  have hstable : (prefixWord ++ tailWord_3808523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808523).length < 2 ^ (prefixWord ++ tailWord_3808523).sum := by decide
  have hdescent : baseEnd_3808523 < baseStart_3808523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808536 : List Nat := [2, 1, 2, 3, 1, 4, 1, 8]
def baseStart_3808536 : Nat := 118140960795 + 3808536 * 2 ^ 59
def prefixEnd_3808536 : Nat := 4983230072969 + 3 ^ 40 * 3808536 * 2
def baseEnd_3808536 : Nat := 144859967255704912524805

theorem tailTrace_3808536 : CollatzResearch.WordTrace tailWord_3808536 prefixEnd_3808536 144859967255704912524805 := by
  unfold tailWord_3808536
  simp only [CollatzResearch.WordTrace]
  refine ⟨69454359865165996504622731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92605813153554662006163641 69454359865165996504622731)
  ·
    refine ⟨104181539797748994756934097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69454359865165996504622731 104181539797748994756934097)
    ·
      refine ⟨78136154848311746067700573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104181539797748994756934097 78136154848311746067700573)
      ·
        refine ⟨29301058068116904775387715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78136154848311746067700573 29301058068116904775387715)
        ·
          refine ⟨43951587102175357163081573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29301058068116904775387715 43951587102175357163081573)
          ·
            refine ⟨8240922581657879468077795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43951587102175357163081573 8240922581657879468077795)
            ·
              refine ⟨12361383872486819202116693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8240922581657879468077795 12361383872486819202116693)
              ·
                refine ⟨144859967255704912524805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12361383872486819202116693 144859967255704912524805)
                ·
                  rfl

theorem cell22_3808536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 8].length) (baseStart_3808536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3808536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3808536 prefixEnd_3808536 := by exact prefixLift 3808536
  have htrace : WordTrace (prefixWord ++ tailWord_3808536) baseStart_3808536 baseEnd_3808536 := by
    simpa [prefixWord, tailWord_3808536, baseEnd_3808536] using wordTrace_append hprefix tailTrace_3808536
  have hstable : (prefixWord ++ tailWord_3808536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808536).length < 2 ^ (prefixWord ++ tailWord_3808536).sum := by decide
  have hdescent : baseEnd_3808536 < baseStart_3808536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808615 : List Nat := [1, 1, 5, 1, 4, 1, 2, 2, 5]
def baseStart_3808615 : Nat := 118140960795 + 3808615 * 2 ^ 59
def prefixEnd_3808615 : Nat := 4983230072969 + 3 ^ 40 * 3808615 * 2
def baseEnd_3808615 : Nat := 434588916205271446666001

theorem tailTrace_3808615 : CollatzResearch.WordTrace tailWord_3808615 prefixEnd_3808615 434588916205271446666001 := by
  unfold tailWord_3808615
  simp only [CollatzResearch.WordTrace]
  refine ⟨138911601097045789501371299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92607734064697193000914199 138911601097045789501371299)
  ·
    refine ⟨208367401645568684252056949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138911601097045789501371299 208367401645568684252056949)
    ·
      refine ⟨19534443904272064148630339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 208367401645568684252056949 19534443904272064148630339)
      ·
        refine ⟨29301665856408096222945509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19534443904272064148630339 29301665856408096222945509)
        ·
          refine ⟨5494062348076518041802283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29301665856408096222945509 5494062348076518041802283)
          ·
            refine ⟨8241093522114777062703425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5494062348076518041802283 8241093522114777062703425)
            ·
              refine ⟨6180820141586082797027569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8241093522114777062703425 6180820141586082797027569)
              ·
                refine ⟨4635615106189562097770677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6180820141586082797027569 4635615106189562097770677)
                ·
                  refine ⟨434588916205271446666001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4635615106189562097770677 434588916205271446666001)
                  ·
                    rfl

theorem cell22_3808615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 5].length) (baseStart_3808615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3808615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3808615 prefixEnd_3808615 := by exact prefixLift 3808615
  have htrace : WordTrace (prefixWord ++ tailWord_3808615) baseStart_3808615 baseEnd_3808615 := by
    simpa [prefixWord, tailWord_3808615, baseEnd_3808615] using wordTrace_append hprefix tailTrace_3808615
  have hstable : (prefixWord ++ tailWord_3808615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808615).length < 2 ^ (prefixWord ++ tailWord_3808615).sum := by decide
  have hdescent : baseEnd_3808615 < baseStart_3808615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808643 : List Nat := [1, 1, 1, 3, 5, 2, 1, 2, 6]
def baseStart_3808643 : Nat := 118140960795 + 3808643 * 2 ^ 59
def prefixEnd_3808643 : Nat := 4983230072969 + 3 ^ 40 * 3808643 * 2
def baseEnd_3808643 : Nat := 434592111196010533432639

theorem tailTrace_3808643 : CollatzResearch.WordTrace tailWord_3808643 prefixEnd_3808643 434592111196010533432639 := by
  unfold tailWord_3808643
  simp only [CollatzResearch.WordTrace]
  refine ⟨138912622340944350283390583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92608414893962900188927055 138912622340944350283390583)
  ·
    refine ⟨208368933511416525425085875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138912622340944350283390583 208368933511416525425085875)
    ·
      refine ⟨312553400267124788137628813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208368933511416525425085875 312553400267124788137628813)
      ·
        refine ⟨117207525100171795551610805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312553400267124788137628813 117207525100171795551610805)
        ·
          refine ⟨10988205478141105832963513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117207525100171795551610805 10988205478141105832963513)
          ·
            refine ⟨8241154108605829374722635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10988205478141105832963513 8241154108605829374722635)
            ·
              refine ⟨12361731162908744062083953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8241154108605829374722635 12361731162908744062083953)
              ·
                refine ⟨9271298372181558046562965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12361731162908744062083953 9271298372181558046562965)
                ·
                  refine ⟨434592111196010533432639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9271298372181558046562965 434592111196010533432639)
                  ·
                    rfl

theorem cell22_3808643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 6].length) (baseStart_3808643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3808643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3808643 prefixEnd_3808643 := by exact prefixLift 3808643
  have htrace : WordTrace (prefixWord ++ tailWord_3808643) baseStart_3808643 baseEnd_3808643 := by
    simpa [prefixWord, tailWord_3808643, baseEnd_3808643] using wordTrace_append hprefix tailTrace_3808643
  have hstable : (prefixWord ++ tailWord_3808643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808643).length < 2 ^ (prefixWord ++ tailWord_3808643).sum := by decide
  have hdescent : baseEnd_3808643 < baseStart_3808643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808737 : List Nat := [1, 2, 3, 1, 2, 5, 1, 1, 3, 3]
def baseStart_3808737 : Nat := 118140960795 + 3808737 * 2 ^ 59
def prefixEnd_3808737 : Nat := 4983230072969 + 3 ^ 40 * 3808737 * 2
def baseEnd_3808737 : Nat := 1303808511709046688447629

theorem tailTrace_3808737 : CollatzResearch.WordTrace tailWord_3808737 prefixEnd_3808737 1303808511709046688447629 := by
  unfold tailWord_3808737
  simp only [CollatzResearch.WordTrace]
  refine ⟨138916050802603804337312465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92610700535069202891541643 138916050802603804337312465)
  ·
    refine ⟨104187038101952853252984349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138916050802603804337312465 104187038101952853252984349)
    ·
      refine ⟨39070139288232319969869131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104187038101952853252984349 39070139288232319969869131)
      ·
        refine ⟨58605208932348479954803697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39070139288232319969869131 58605208932348479954803697)
        ·
          refine ⟨43953906699261359966102773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58605208932348479954803697 43953906699261359966102773)
          ·
            refine ⟨4120678753055752496822135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43953906699261359966102773 4120678753055752496822135)
            ·
              refine ⟨6181018129583628745233203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4120678753055752496822135 6181018129583628745233203)
              ·
                refine ⟨9271527194375443117849805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6181018129583628745233203 9271527194375443117849805)
                ·
                  refine ⟨3476822697890791169193677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9271527194375443117849805 3476822697890791169193677)
                  ·
                    refine ⟨1303808511709046688447629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3476822697890791169193677 1303808511709046688447629)
                    ·
                      rfl

theorem cell22_3808737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_3808737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3808737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3808737 prefixEnd_3808737 := by exact prefixLift 3808737
  have htrace : WordTrace (prefixWord ++ tailWord_3808737) baseStart_3808737 baseEnd_3808737 := by
    simpa [prefixWord, tailWord_3808737, baseEnd_3808737] using wordTrace_append hprefix tailTrace_3808737
  have hstable : (prefixWord ++ tailWord_3808737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808737).length < 2 ^ (prefixWord ++ tailWord_3808737).sum := by decide
  have hdescent : baseEnd_3808737 < baseStart_3808737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808750 : List Nat := [4, 1, 2, 1, 2, 1, 3, 3, 5]
def baseStart_3808750 : Nat := 118140960795 + 3808750 * 2 ^ 59
def prefixEnd_3808750 : Nat := 4983230072969 + 3 ^ 40 * 3808750 * 2
def baseEnd_3808750 : Nat := 434604320624906329290863

theorem tailTrace_3808750 : CollatzResearch.WordTrace tailWord_3808750 prefixEnd_3808750 434604320624906329290863 := by
  unfold tailWord_3808750
  simp only [CollatzResearch.WordTrace]
  refine ⟨17364565618944588444691963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92611016634371138371690469 17364565618944588444691963)
  ·
    refine ⟨26046848428416882667037945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17364565618944588444691963 26046848428416882667037945)
    ·
      refine ⟨19535136321312662000278459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26046848428416882667037945 19535136321312662000278459)
      ·
        refine ⟨29302704481968993000417689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19535136321312662000278459 29302704481968993000417689)
        ·
          refine ⟨21977028361476744750313267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29302704481968993000417689 21977028361476744750313267)
          ·
            refine ⟨32965542542215117125469901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21977028361476744750313267 32965542542215117125469901)
            ·
              refine ⟨12362078453330668922051213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32965542542215117125469901 12362078453330668922051213)
              ·
                refine ⟨4635779419999000845769205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12362078453330668922051213 4635779419999000845769205)
                ·
                  refine ⟨434604320624906329290863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4635779419999000845769205 434604320624906329290863)
                  ·
                    rfl

theorem cell22_3808750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_3808750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3808750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3808750 prefixEnd_3808750 := by exact prefixLift 3808750
  have htrace : WordTrace (prefixWord ++ tailWord_3808750) baseStart_3808750 baseEnd_3808750 := by
    simpa [prefixWord, tailWord_3808750, baseEnd_3808750] using wordTrace_append hprefix tailTrace_3808750
  have hstable : (prefixWord ++ tailWord_3808750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808750).length < 2 ^ (prefixWord ++ tailWord_3808750).sum := by decide
  have hdescent : baseEnd_3808750 < baseStart_3808750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808763 : List Nat := [1, 1, 1, 1, 1, 3, 2, 5, 3, 4]
def baseStart_3808763 : Nat := 118140960795 + 3808763 * 2 ^ 59
def prefixEnd_3808763 : Nat := 4983230072969 + 3 ^ 40 * 3808763 * 2
def baseEnd_3808763 : Nat := 1303817412040391287297549

theorem tailTrace_3808763 : CollatzResearch.WordTrace tailWord_3808763 prefixEnd_3808763 1303817412040391287297549 := by
  unfold tailWord_3808763
  simp only [CollatzResearch.WordTrace]
  refine ⟨138916999100509610777758943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92611332733673073851839295 138916999100509610777758943)
  ·
    refine ⟨208375498650764416166638415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138916999100509610777758943 208375498650764416166638415)
    ·
      refine ⟨312563247976146624249957623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208375498650764416166638415 312563247976146624249957623)
      ·
        refine ⟨468844871964219936374936435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312563247976146624249957623 468844871964219936374936435)
        ·
          refine ⟨703267307946329904562404653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468844871964219936374936435 703267307946329904562404653)
          ·
            refine ⟨263725240479873714210901745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 703267307946329904562404653 263725240479873714210901745)
            ·
              refine ⟨197793930359905285658176309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263725240479873714210901745 197793930359905285658176309)
              ·
                refine ⟨18543180971241120530454029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 197793930359905285658176309 18543180971241120530454029)
                ·
                  refine ⟨6953692864215420198920261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18543180971241120530454029 6953692864215420198920261)
                  ·
                    refine ⟨1303817412040391287297549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6953692864215420198920261 1303817412040391287297549)
                    ·
                      rfl

theorem cell22_3808763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 4].length) (baseStart_3808763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3808763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3808763 prefixEnd_3808763 := by exact prefixLift 3808763
  have htrace : WordTrace (prefixWord ++ tailWord_3808763) baseStart_3808763 baseEnd_3808763 := by
    simpa [prefixWord, tailWord_3808763, baseEnd_3808763] using wordTrace_append hprefix tailTrace_3808763
  have hstable : (prefixWord ++ tailWord_3808763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808763).length < 2 ^ (prefixWord ++ tailWord_3808763).sum := by decide
  have hdescent : baseEnd_3808763 < baseStart_3808763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808825 : List Nat := [1, 2, 1, 5, 1, 3, 1, 1, 1, 6]
def baseStart_3808825 : Nat := 118140960795 + 3808825 * 2 ^ 59
def prefixEnd_3808825 : Nat := 4983230072969 + 3 ^ 40 * 3808825 * 2
def baseEnd_3808825 : Nat := 1303838635907443792247359

theorem tailTrace_3808825 : CollatzResearch.WordTrace tailWord_3808825 prefixEnd_3808825 1303838635907443792247359 := by
  unfold tailWord_3808825
  simp only [CollatzResearch.WordTrace]
  refine ⟨138919260426284995366515929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92612840284189996911010619 138919260426284995366515929)
  ·
    refine ⟨104189445319713746524886947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138919260426284995366515929 104189445319713746524886947)
    ·
      refine ⟨156284167979570619787330421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104189445319713746524886947 156284167979570619787330421)
      ·
        refine ⟨14651640748084745605062227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156284167979570619787330421 14651640748084745605062227)
        ·
          refine ⟨21977461122127118407593341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14651640748084745605062227 21977461122127118407593341)
          ·
            refine ⟨8241547920797669402847503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21977461122127118407593341 8241547920797669402847503)
            ·
              refine ⟨12362321881196504104271255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8241547920797669402847503 12362321881196504104271255)
              ·
                refine ⟨18543482821794756156406883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12362321881196504104271255 18543482821794756156406883)
                ·
                  refine ⟨27815224232692134234610325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18543482821794756156406883 27815224232692134234610325)
                  ·
                    refine ⟨1303838635907443792247359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27815224232692134234610325 1303838635907443792247359)
                    ·
                      rfl

theorem cell22_3808825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 6].length) (baseStart_3808825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3808825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3808825 prefixEnd_3808825 := by exact prefixLift 3808825
  have htrace : WordTrace (prefixWord ++ tailWord_3808825) baseStart_3808825 baseEnd_3808825 := by
    simpa [prefixWord, tailWord_3808825, baseEnd_3808825] using wordTrace_append hprefix tailTrace_3808825
  have hstable : (prefixWord ++ tailWord_3808825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808825).length < 2 ^ (prefixWord ++ tailWord_3808825).sum := by decide
  have hdescent : baseEnd_3808825 < baseStart_3808825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808829 : List Nat := [1, 4, 1, 3, 3, 1, 2, 3, 4]
def baseStart_3808829 : Nat := 118140960795 + 3808829 * 2 ^ 59
def prefixEnd_3808829 : Nat := 4983230072969 + 3 ^ 40 * 3808829 * 2
def baseEnd_3808829 : Nat := 434613335063063038382449

theorem tailTrace_3808829 : CollatzResearch.WordTrace tailWord_3808829 prefixEnd_3808829 434613335063063038382449 := by
  unfold tailWord_3808829
  simp only [CollatzResearch.WordTrace]
  refine ⟨138919406318270504049661541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92612937545513669366441027 138919406318270504049661541)
  ·
    refine ⟨26047388684675719509311539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138919406318270504049661541 26047388684675719509311539)
    ·
      refine ⟨39071083027013579263967309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26047388684675719509311539 39071083027013579263967309)
      ·
        refine ⟨14651656135130092223987741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39071083027013579263967309 14651656135130092223987741)
        ·
          refine ⟨5494371050673784583995403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14651656135130092223987741 5494371050673784583995403)
          ·
            refine ⟨8241556576010676875993105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5494371050673784583995403 8241556576010676875993105)
            ·
              refine ⟨6181167432008007656994829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8241556576010676875993105 6181167432008007656994829)
              ·
                refine ⟨2317937787003002871373061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6181167432008007656994829 2317937787003002871373061)
                ·
                  refine ⟨434613335063063038382449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2317937787003002871373061 434613335063063038382449)
                  ·
                    rfl

theorem cell22_3808829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_3808829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3808829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3808829 prefixEnd_3808829 := by exact prefixLift 3808829
  have htrace : WordTrace (prefixWord ++ tailWord_3808829) baseStart_3808829 baseEnd_3808829 := by
    simpa [prefixWord, tailWord_3808829, baseEnd_3808829] using wordTrace_append hprefix tailTrace_3808829
  have hstable : (prefixWord ++ tailWord_3808829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808829).length < 2 ^ (prefixWord ++ tailWord_3808829).sum := by decide
  have hdescent : baseEnd_3808829 < baseStart_3808829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808844 : List Nat := [2, 2, 1, 3, 1, 5, 1, 2, 2, 3]
def baseStart_3808844 : Nat := 118140960795 + 3808844 * 2 ^ 59
def prefixEnd_3808844 : Nat := 4983230072969 + 3 ^ 40 * 3808844 * 2
def baseEnd_3808844 : Nat := 1303845139995734076022301

theorem tailTrace_3808844 : CollatzResearch.WordTrace tailWord_3808844 prefixEnd_3808844 1303845139995734076022301 := by
  unfold tailWord_3808844
  simp only [CollatzResearch.WordTrace]
  refine ⟨69459976706608080805728793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92613302275477441074305057 69459976706608080805728793)
  ·
    refine ⟨52094982529956060604296595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69459976706608080805728793 52094982529956060604296595)
    ·
      refine ⟨78142473794934090906444893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52094982529956060604296595 78142473794934090906444893)
      ·
        refine ⟨29303427673100284089916835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78142473794934090906444893 29303427673100284089916835)
        ·
          refine ⟨43955141509650426134875253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29303427673100284089916835 43955141509650426134875253)
          ·
            refine ⟨4120794516529727450144555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43955141509650426134875253 4120794516529727450144555)
            ·
              refine ⟨6181191774794591175216833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4120794516529727450144555 6181191774794591175216833)
              ·
                refine ⟨4635893831095943381412625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6181191774794591175216833 4635893831095943381412625)
                ·
                  refine ⟨3476920373321957536059469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4635893831095943381412625 3476920373321957536059469)
                  ·
                    refine ⟨1303845139995734076022301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3476920373321957536059469 1303845139995734076022301)
                    ·
                      rfl

theorem cell22_3808844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 2, 3].length) (baseStart_3808844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3808844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3808844 prefixEnd_3808844 := by exact prefixLift 3808844
  have htrace : WordTrace (prefixWord ++ tailWord_3808844) baseStart_3808844 baseEnd_3808844 := by
    simpa [prefixWord, tailWord_3808844, baseEnd_3808844] using wordTrace_append hprefix tailTrace_3808844
  have hstable : (prefixWord ++ tailWord_3808844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808844).length < 2 ^ (prefixWord ++ tailWord_3808844).sum := by decide
  have hdescent : baseEnd_3808844 < baseStart_3808844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808861 : List Nat := [1, 4, 4, 2, 1, 2, 1, 1, 1, 5]
def baseStart_3808861 : Nat := 118140960795 + 3808861 * 2 ^ 59
def prefixEnd_3808861 : Nat := 4983230072969 + 3 ^ 40 * 3808861 * 2
def baseEnd_3808861 : Nat := 1303850959443151698347249

theorem tailTrace_3808861 : CollatzResearch.WordTrace tailWord_3808861 prefixEnd_3808861 1303850959443151698347249 := by
  unfold tailWord_3808861
  simp only [CollatzResearch.WordTrace]
  refine ⟨138920573454154573514826437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92613715636103049009884291 138920573454154573514826437)
  ·
    refine ⟨26047607522653982534029957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138920573454154573514826437 26047607522653982534029957)
    ·
      refine ⟨4883926410497621725130617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26047607522653982534029957 4883926410497621725130617)
      ·
        refine ⟨3662944807873216293847963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4883926410497621725130617 3662944807873216293847963)
        ·
          refine ⟨5494417211809824440771945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3662944807873216293847963 5494417211809824440771945)
          ·
            refine ⟨4120812908857368330578959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5494417211809824440771945 4120812908857368330578959)
            ·
              refine ⟨6181219363286052495868439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4120812908857368330578959 6181219363286052495868439)
              ·
                refine ⟨9271829044929078743802659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6181219363286052495868439 9271829044929078743802659)
                ·
                  refine ⟨13907743567393618115703989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9271829044929078743802659 13907743567393618115703989)
                  ·
                    refine ⟨1303850959443151698347249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13907743567393618115703989 1303850959443151698347249)
                    ·
                      rfl

theorem cell22_3808861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_3808861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3808861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3808861 prefixEnd_3808861 := by exact prefixLift 3808861
  have htrace : WordTrace (prefixWord ++ tailWord_3808861) baseStart_3808861 baseEnd_3808861 := by
    simpa [prefixWord, tailWord_3808861, baseEnd_3808861] using wordTrace_append hprefix tailTrace_3808861
  have hstable : (prefixWord ++ tailWord_3808861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808861).length < 2 ^ (prefixWord ++ tailWord_3808861).sum := by decide
  have hdescent : baseEnd_3808861 < baseStart_3808861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808919 : List Nat := [1, 1, 3, 3, 2, 4, 2, 1, 5]
def baseStart_3808919 : Nat := 118140960795 + 3808919 * 2 ^ 59
def prefixEnd_3808919 : Nat := 4983230072969 + 3 ^ 40 * 3808919 * 2
def baseEnd_3808919 : Nat := 434623604676152960132357

theorem tailTrace_3808919 : CollatzResearch.WordTrace tailWord_3808919 prefixEnd_3808919 434623604676152960132357 := by
  unfold tailWord_3808919
  simp only [CollatzResearch.WordTrace]
  refine ⟨138922688887944449420437811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92615125925296299613625207 138922688887944449420437811)
  ·
    refine ⟨208384033331916674130656717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138922688887944449420437811 208384033331916674130656717)
    ·
      refine ⟨78144012499468752798996269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208384033331916674130656717 78144012499468752798996269)
      ·
        refine ⟨29304004687300782299623601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78144012499468752798996269 29304004687300782299623601)
        ·
          refine ⟨21978003515475586724717701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29304004687300782299623601 21978003515475586724717701)
          ·
            refine ⟨4120875659151672510884569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21978003515475586724717701 4120875659151672510884569)
            ·
              refine ⟨3090656744363754383163427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4120875659151672510884569 3090656744363754383163427)
              ·
                refine ⟨4635985116545631574745141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3090656744363754383163427 4635985116545631574745141)
                ·
                  refine ⟨434623604676152960132357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4635985116545631574745141 434623604676152960132357)
                  ·
                    rfl

theorem cell22_3808919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 5].length) (baseStart_3808919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3808919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3808919 prefixEnd_3808919 := by exact prefixLift 3808919
  have htrace : WordTrace (prefixWord ++ tailWord_3808919) baseStart_3808919 baseEnd_3808919 := by
    simpa [prefixWord, tailWord_3808919, baseEnd_3808919] using wordTrace_append hprefix tailTrace_3808919
  have hstable : (prefixWord ++ tailWord_3808919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808919).length < 2 ^ (prefixWord ++ tailWord_3808919).sum := by decide
  have hdescent : baseEnd_3808919 < baseStart_3808919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808932 : List Nat := [2, 3, 1, 2, 2, 3, 1, 1, 3, 4]
def baseStart_3808932 : Nat := 118140960795 + 3808932 * 2 ^ 59
def prefixEnd_3808932 : Nat := 4983230072969 + 3 ^ 40 * 3808932 * 2
def baseEnd_3808932 : Nat := 1303875264194131179822031

theorem tailTrace_3808932 : CollatzResearch.WordTrace tailWord_3808932 prefixEnd_3808932 1303875264194131179822031 := by
  unfold tailWord_3808932
  simp only [CollatzResearch.WordTrace]
  refine ⟨69461581518448676320330525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92615442024598235093774033 69461581518448676320330525)
  ·
    refine ⟨26048093069418253620123947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69461581518448676320330525 26048093069418253620123947)
    ·
      refine ⟨39072139604127380430185921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26048093069418253620123947 39072139604127380430185921)
      ·
        refine ⟨29304104703095535322639441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39072139604127380430185921 29304104703095535322639441)
        ·
          refine ⟨21978078527321651491979581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29304104703095535322639441 21978078527321651491979581)
          ·
            refine ⟨8241779447745619309492343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21978078527321651491979581 8241779447745619309492343)
            ·
              refine ⟨12362669171618428964238515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8241779447745619309492343 12362669171618428964238515)
              ·
                refine ⟨18544003757427643446357773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12362669171618428964238515 18544003757427643446357773)
                ·
                  refine ⟨6954001409035366292384165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18544003757427643446357773 6954001409035366292384165)
                  ·
                    refine ⟨1303875264194131179822031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6954001409035366292384165 1303875264194131179822031)
                    ·
                      rfl

theorem cell22_3808932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_3808932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3808932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3808932 prefixEnd_3808932 := by exact prefixLift 3808932
  have htrace : WordTrace (prefixWord ++ tailWord_3808932) baseStart_3808932 baseEnd_3808932 := by
    simpa [prefixWord, tailWord_3808932, baseEnd_3808932] using wordTrace_append hprefix tailTrace_3808932
  have hstable : (prefixWord ++ tailWord_3808932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808932).length < 2 ^ (prefixWord ++ tailWord_3808932).sum := by decide
  have hdescent : baseEnd_3808932 < baseStart_3808932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808947 : List Nat := [1, 1, 1, 2, 3, 3, 2, 5, 4]
def baseStart_3808947 : Nat := 118140960795 + 3808947 * 2 ^ 59
def prefixEnd_3808947 : Nat := 4983230072969 + 3 ^ 40 * 3808947 * 2
def baseEnd_3808947 : Nat := 434626799666892046898995

theorem tailTrace_3808947 : CollatzResearch.WordTrace tailWord_3808947 prefixEnd_3808947 434626799666892046898995 := by
  unfold tailWord_3808947
  simp only [CollatzResearch.WordTrace]
  refine ⟨138923710131843010202457095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92615806754562006801638063 138923710131843010202457095)
  ·
    refine ⟨208385565197764515303685643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138923710131843010202457095 208385565197764515303685643)
    ·
      refine ⟨312578347796646772955528465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208385565197764515303685643 312578347796646772955528465)
      ·
        refine ⟨234433760847485079716646349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312578347796646772955528465 234433760847485079716646349)
        ·
          refine ⟨87912660317806904893742381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234433760847485079716646349 87912660317806904893742381)
          ·
            refine ⟨32967247619177589335153393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87912660317806904893742381 32967247619177589335153393)
            ·
              refine ⟨24725435714383192001365045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32967247619177589335153393 24725435714383192001365045)
              ·
                refine ⟨2318009598223424250127973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24725435714383192001365045 2318009598223424250127973)
                ·
                  refine ⟨434626799666892046898995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2318009598223424250127973 434626799666892046898995)
                  ·
                    rfl

theorem cell22_3808947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 5, 4].length) (baseStart_3808947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3808947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3808947 prefixEnd_3808947 := by exact prefixLift 3808947
  have htrace : WordTrace (prefixWord ++ tailWord_3808947) baseStart_3808947 baseEnd_3808947 := by
    simpa [prefixWord, tailWord_3808947, baseEnd_3808947] using wordTrace_append hprefix tailTrace_3808947
  have hstable : (prefixWord ++ tailWord_3808947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808947).length < 2 ^ (prefixWord ++ tailWord_3808947).sum := by decide
  have hdescent : baseEnd_3808947 < baseStart_3808947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808964 : List Nat := [2, 3, 3, 1, 1, 1, 3, 4, 4]
def baseStart_3808964 : Nat := 118140960795 + 3808964 * 2 ^ 59
def prefixEnd_3808964 : Nat := 4983230072969 + 3 ^ 40 * 3808964 * 2
def baseEnd_3808964 : Nat := 434628739482697921007311

theorem tailTrace_3808964 : CollatzResearch.WordTrace tailWord_3808964 prefixEnd_3808964 434628739482697921007311 := by
  unfold tailWord_3808964
  simp only [CollatzResearch.WordTrace]
  refine ⟨69462165086390711052912973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92616220115187614737217297 69462165086390711052912973)
  ·
    refine ⟨26048311907396516644842365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69462165086390711052912973 26048311907396516644842365)
    ·
      refine ⟨9768116965273693741815887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26048311907396516644842365 9768116965273693741815887)
      ·
        refine ⟨14652175447910540612723831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9768116965273693741815887 14652175447910540612723831)
        ·
          refine ⟨21978263171865810919085747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14652175447910540612723831 21978263171865810919085747)
          ·
            refine ⟨32967394757798716378628621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21978263171865810919085747 32967394757798716378628621)
            ·
              refine ⟨12362773034174518641985733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32967394757798716378628621 12362773034174518641985733)
              ·
                refine ⟨2318019943907722245372325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12362773034174518641985733 2318019943907722245372325)
                ·
                  refine ⟨434628739482697921007311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2318019943907722245372325 434628739482697921007311)
                  ·
                    rfl

theorem cell22_3808964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_3808964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3808964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3808964 prefixEnd_3808964 := by exact prefixLift 3808964
  have htrace : WordTrace (prefixWord ++ tailWord_3808964) baseStart_3808964 baseEnd_3808964 := by
    simpa [prefixWord, tailWord_3808964, baseEnd_3808964] using wordTrace_append hprefix tailTrace_3808964
  have hstable : (prefixWord ++ tailWord_3808964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808964).length < 2 ^ (prefixWord ++ tailWord_3808964).sum := by decide
  have hdescent : baseEnd_3808964 < baseStart_3808964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3808966 : List Nat := [6, 1, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_3808966 : Nat := 118140960795 + 3808966 * 2 ^ 59
def prefixEnd_3808966 : Nat := 4983230072969 + 3 ^ 40 * 3808966 * 2
def baseEnd_3808966 : Nat := 1303886903088966424471927

theorem tailTrace_3808966 : CollatzResearch.WordTrace tailWord_3808966 prefixEnd_3808966 1303886903088966424471927 := by
  unfold tailWord_3808966
  simp only [CollatzResearch.WordTrace]
  refine ⟨4341387597461693013981211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 92616268745849450964932501 4341387597461693013981211)
  ·
    refine ⟨6512081396192539520971817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4341387597461693013981211 6512081396192539520971817)
    ·
      refine ⟨4884061047144404640728863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6512081396192539520971817 4884061047144404640728863)
      ·
        refine ⟨7326091570716606961093295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4884061047144404640728863 7326091570716606961093295)
        ·
          refine ⟨10989137356074910441639943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7326091570716606961093295 10989137356074910441639943)
          ·
            refine ⟨16483706034112365662459915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10989137356074910441639943 16483706034112365662459915)
            ·
              refine ⟨24725559051168548493689873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16483706034112365662459915 24725559051168548493689873)
              ·
                refine ⟨18544169288376411370267405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24725559051168548493689873 18544169288376411370267405)
                ·
                  refine ⟨6954063483141154263850277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18544169288376411370267405 6954063483141154263850277)
                  ·
                    refine ⟨1303886903088966424471927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6954063483141154263850277 1303886903088966424471927)
                    ·
                      rfl

theorem cell22_3808966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_3808966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3808966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3808966 prefixEnd_3808966 := by exact prefixLift 3808966
  have htrace : WordTrace (prefixWord ++ tailWord_3808966) baseStart_3808966 baseEnd_3808966 := by
    simpa [prefixWord, tailWord_3808966, baseEnd_3808966] using wordTrace_append hprefix tailTrace_3808966
  have hstable : (prefixWord ++ tailWord_3808966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3808966).length < 2 ^ (prefixWord ++ tailWord_3808966).sum := by decide
  have hdescent : baseEnd_3808966 < baseStart_3808966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3808966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809007 : List Nat := [1, 1, 2, 1, 5, 1, 1, 2, 5, 3]
def baseStart_3809007 : Nat := 118140960795 + 3809007 * 2 ^ 59
def prefixEnd_3809007 : Nat := 4983230072969 + 3 ^ 40 * 3809007 * 2
def baseEnd_3809007 : Nat := 1303900938226855984196801

theorem tailTrace_3809007 : CollatzResearch.WordTrace tailWord_3809007 prefixEnd_3809007 1303900938226855984196801 := by
  unfold tailWord_3809007
  simp only [CollatzResearch.WordTrace]
  refine ⟨138925898511625640449641275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92617265674417093633094183 138925898511625640449641275)
  ·
    refine ⟨208388847767438460674461913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138925898511625640449641275 208388847767438460674461913)
    ·
      refine ⟨156291635825578845505846435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208388847767438460674461913 156291635825578845505846435)
      ·
        refine ⟨234437453738368268258769653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156291635825578845505846435 234437453738368268258769653)
        ·
          refine ⟨21978511287972025149259655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 234437453738368268258769653 21978511287972025149259655)
          ·
            refine ⟨32967766931958037723889483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21978511287972025149259655 32967766931958037723889483)
            ·
              refine ⟨49451650397937056585834225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32967766931958037723889483 49451650397937056585834225)
              ·
                refine ⟨37088737798452792439375669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49451650397937056585834225 37088737798452792439375669)
                ·
                  refine ⟨3477069168604949291191469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37088737798452792439375669 3477069168604949291191469)
                  ·
                    refine ⟨1303900938226855984196801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3477069168604949291191469 1303900938226855984196801)
                    ·
                      rfl

theorem cell22_3809007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 5, 3].length) (baseStart_3809007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809007 prefixEnd_3809007 := by exact prefixLift 3809007
  have htrace : WordTrace (prefixWord ++ tailWord_3809007) baseStart_3809007 baseEnd_3809007 := by
    simpa [prefixWord, tailWord_3809007, baseEnd_3809007] using wordTrace_append hprefix tailTrace_3809007
  have hstable : (prefixWord ++ tailWord_3809007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809007).length < 2 ^ (prefixWord ++ tailWord_3809007).sum := by decide
  have hdescent : baseEnd_3809007 < baseStart_3809007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809097 : List Nat := [1, 2, 1, 1, 2, 4, 2, 3, 1, 5]
def baseStart_3809097 : Nat := 118140960795 + 3809097 * 2 ^ 59
def prefixEnd_3809097 : Nat := 4983230072969 + 3 ^ 40 * 3809097 * 2
def baseEnd_3809097 : Nat := 1303931747066125749446525

theorem tailTrace_3809097 : CollatzResearch.WordTrace tailWord_3809097 prefixEnd_3809097 1303931747066125749446525 := by
  unfold tailWord_3809097
  simp only [CollatzResearch.WordTrace]
  refine ⟨138929181081299585820417545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92619454054199723880278363 138929181081299585820417545)
  ·
    refine ⟨104196885810974689365313159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138929181081299585820417545 104196885810974689365313159)
    ·
      refine ⟨156295328716462034047969739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104196885810974689365313159 156295328716462034047969739)
      ·
        refine ⟨234442993074693051071954609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156295328716462034047969739 234442993074693051071954609)
        ·
          refine ⟨175832244806019788303965957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234442993074693051071954609 175832244806019788303965957)
          ·
            refine ⟨32968545901128710306993617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175832244806019788303965957 32968545901128710306993617)
            ·
              refine ⟨24726409425846532730245213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32968545901128710306993617 24726409425846532730245213)
              ·
                refine ⟨9272403534692449773841955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24726409425846532730245213 9272403534692449773841955)
                ·
                  refine ⟨13908605302038674660762933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9272403534692449773841955 13908605302038674660762933)
                  ·
                    refine ⟨1303931747066125749446525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13908605302038674660762933 1303931747066125749446525)
                    ·
                      rfl

theorem cell22_3809097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 5].length) (baseStart_3809097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809097 prefixEnd_3809097 := by exact prefixLift 3809097
  have htrace : WordTrace (prefixWord ++ tailWord_3809097) baseStart_3809097 baseEnd_3809097 := by
    simpa [prefixWord, tailWord_3809097, baseEnd_3809097] using wordTrace_append hprefix tailTrace_3809097
  have hstable : (prefixWord ++ tailWord_3809097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809097).length < 2 ^ (prefixWord ++ tailWord_3809097).sum := by decide
  have hdescent : baseEnd_3809097 < baseStart_3809097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809101 : List Nat := [1, 6, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_3809101 : Nat := 118140960795 + 3809101 * 2 ^ 59
def prefixEnd_3809101 : Nat := 4983230072969 + 3 ^ 40 * 3809101 * 2
def baseEnd_3809101 : Nat := 1303933116347871072346513

theorem tailTrace_3809101 : CollatzResearch.WordTrace tailWord_3809101 prefixEnd_3809101 1303933116347871072346513 := by
  unfold tailWord_3809101
  simp only [CollatzResearch.WordTrace]
  refine ⟨138929326973285094503563157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92619551315523396335708771 138929326973285094503563157)
  ·
    refine ⟨6512312201872738804854523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 138929326973285094503563157 6512312201872738804854523)
    ·
      refine ⟨9768468302809108207281785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6512312201872738804854523 9768468302809108207281785)
      ·
        refine ⟨7326351227106831155461339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9768468302809108207281785 7326351227106831155461339)
        ·
          refine ⟨10989526840660246733192009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7326351227106831155461339 10989526840660246733192009)
          ·
            refine ⟨8242145130495185049894007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10989526840660246733192009 8242145130495185049894007)
            ·
              refine ⟨12363217695742777574841011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8242145130495185049894007 12363217695742777574841011)
              ·
                refine ⟨18544826543614166362261517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12363217695742777574841011 18544826543614166362261517)
                ·
                  refine ⟨6954309953855312385848069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18544826543614166362261517 6954309953855312385848069)
                  ·
                    refine ⟨1303933116347871072346513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6954309953855312385848069 1303933116347871072346513)
                    ·
                      rfl

theorem cell22_3809101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_3809101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809101 prefixEnd_3809101 := by exact prefixLift 3809101
  have htrace : WordTrace (prefixWord ++ tailWord_3809101) baseStart_3809101 baseEnd_3809101 := by
    simpa [prefixWord, tailWord_3809101, baseEnd_3809101] using wordTrace_append hprefix tailTrace_3809101
  have hstable : (prefixWord ++ tailWord_3809101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809101).length < 2 ^ (prefixWord ++ tailWord_3809101).sum := by decide
  have hdescent : baseEnd_3809101 < baseStart_3809101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809157 : List Nat := [1, 3, 1, 1, 3, 2, 1, 2, 2, 6]
def baseStart_3809157 : Nat := 118140960795 + 3809157 * 2 ^ 59
def prefixEnd_3809157 : Nat := 4983230072969 + 3 ^ 40 * 3809157 * 2
def baseEnd_3809157 : Nat := 1303952286292305592946341

theorem tailTrace_3809157 : CollatzResearch.WordTrace tailWord_3809157 prefixEnd_3809157 1303952286292305592946341 := by
  unfold tailWord_3809157
  simp only [CollatzResearch.WordTrace]
  refine ⟨138931369461082216067601725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92620912974054810711734483 138931369461082216067601725)
  ·
    refine ⟨52099263547905831025350647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138931369461082216067601725 52099263547905831025350647)
    ·
      refine ⟨78148895321858746538025971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52099263547905831025350647 78148895321858746538025971)
      ·
        refine ⟨117223342982788119807038957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78148895321858746538025971 117223342982788119807038957)
        ·
          refine ⟨43958753618545544927639609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117223342982788119807038957 43958753618545544927639609)
          ·
            refine ⟨32969065213909158695729707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43958753618545544927639609 32969065213909158695729707)
            ·
              refine ⟨49453597820863738043594561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32969065213909158695729707 49453597820863738043594561)
              ·
                refine ⟨37090198365647803532695921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49453597820863738043594561 37090198365647803532695921)
                ·
                  refine ⟨27817648774235852649521941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37090198365647803532695921 27817648774235852649521941)
                  ·
                    refine ⟨1303952286292305592946341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27817648774235852649521941 1303952286292305592946341)
                    ·
                      rfl

theorem cell22_3809157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_3809157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809157 prefixEnd_3809157 := by exact prefixLift 3809157
  have htrace : WordTrace (prefixWord ++ tailWord_3809157) baseStart_3809157 baseEnd_3809157 := by
    simpa [prefixWord, tailWord_3809157, baseEnd_3809157] using wordTrace_append hprefix tailTrace_3809157
  have hstable : (prefixWord ++ tailWord_3809157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809157).length < 2 ^ (prefixWord ++ tailWord_3809157).sum := by decide
  have hdescent : baseEnd_3809157 < baseStart_3809157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809182 : List Nat := [4, 3, 1, 3, 1, 2, 1, 2, 2, 3]
def baseStart_3809182 : Nat := 118140960795 + 3809182 * 2 ^ 59
def prefixEnd_3809182 : Nat := 4983230072969 + 3 ^ 40 * 3809182 * 2
def baseEnd_3809182 : Nat := 1303960844303213861071265

theorem tailTrace_3809182 : CollatzResearch.WordTrace tailWord_3809182 prefixEnd_3809182 1303960844303213861071265 := by
  unfold tailWord_3809182
  simp only [CollatzResearch.WordTrace]
  refine ⟨17366535160748955667157725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92621520857327763558174533 17366535160748955667157725)
  ·
    refine ⟨6512450685280858375184147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17366535160748955667157725 6512450685280858375184147)
    ·
      refine ⟨9768676027921287562776221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6512450685280858375184147 9768676027921287562776221)
      ·
        refine ⟨3663253510470482836041083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9768676027921287562776221 3663253510470482836041083)
        ·
          refine ⟨5494880265705724254061625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3663253510470482836041083 5494880265705724254061625)
          ·
            refine ⟨4121160199279293190546219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5494880265705724254061625 4121160199279293190546219)
            ·
              refine ⟨6181740298918939785819329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4121160199279293190546219 6181740298918939785819329)
              ·
                refine ⟨4636305224189204839364497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6181740298918939785819329 4636305224189204839364497)
                ·
                  refine ⟨3477228918141903629523373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4636305224189204839364497 3477228918141903629523373)
                  ·
                    refine ⟨1303960844303213861071265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3477228918141903629523373 1303960844303213861071265)
                    ·
                      rfl

theorem cell22_3809182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_3809182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809182 prefixEnd_3809182 := by exact prefixLift 3809182
  have htrace : WordTrace (prefixWord ++ tailWord_3809182) baseStart_3809182 baseEnd_3809182 := by
    simpa [prefixWord, tailWord_3809182, baseEnd_3809182] using wordTrace_append hprefix tailTrace_3809182
  have hstable : (prefixWord ++ tailWord_3809182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809182).length < 2 ^ (prefixWord ++ tailWord_3809182).sum := by decide
  have hdescent : baseEnd_3809182 < baseStart_3809182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809236 : List Nat := [2, 4, 1, 2, 1, 1, 1, 5, 1, 4]
def baseStart_3809236 : Nat := 118140960795 + 3809236 * 2 ^ 59
def prefixEnd_3809236 : Nat := 4983230072969 + 3 ^ 40 * 3809236 * 2
def baseEnd_3809236 : Nat := 1303979329606775720221099

theorem tailTrace_3809236 : CollatzResearch.WordTrace tailWord_3809236 prefixEnd_3809236 1303979329606775720221099 := by
  unfold tailWord_3809236
  simp only [CollatzResearch.WordTrace]
  refine ⟨69467125413898006279863781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92622833885197341706485041 69467125413898006279863781)
  ·
    refine ⟨13025086015105876177474459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69467125413898006279863781 13025086015105876177474459)
    ·
      refine ⟨19537629022658814266211689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13025086015105876177474459 19537629022658814266211689)
      ·
        refine ⟨14653221766994110699658767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19537629022658814266211689 14653221766994110699658767)
        ·
          refine ⟨21979832650491166049488151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14653221766994110699658767 21979832650491166049488151)
          ·
            refine ⟨32969748975736749074232227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21979832650491166049488151 32969748975736749074232227)
            ·
              refine ⟨49454623463605123611348341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32969748975736749074232227 49454623463605123611348341)
              ·
                refine ⟨4636370949712980338563907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49454623463605123611348341 4636370949712980338563907)
                ·
                  refine ⟨6954556424569470507845861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4636370949712980338563907 6954556424569470507845861)
                  ·
                    refine ⟨1303979329606775720221099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6954556424569470507845861 1303979329606775720221099)
                    ·
                      rfl

theorem cell22_3809236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_3809236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809236 prefixEnd_3809236 := by exact prefixLift 3809236
  have htrace : WordTrace (prefixWord ++ tailWord_3809236) baseStart_3809236 baseEnd_3809236 := by
    simpa [prefixWord, tailWord_3809236, baseEnd_3809236] using wordTrace_append hprefix tailTrace_3809236
  have hstable : (prefixWord ++ tailWord_3809236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809236).length < 2 ^ (prefixWord ++ tailWord_3809236).sum := by decide
  have hdescent : baseEnd_3809236 < baseStart_3809236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809244 : List Nat := [2, 2, 6, 1, 2, 1, 1, 1, 3, 3]
def baseStart_3809244 : Nat := 118140960795 + 3809244 * 2 ^ 59
def prefixEnd_3809244 : Nat := 4983230072969 + 3 ^ 40 * 3809244 * 2
def baseEnd_3809244 : Nat := 1303982068170266366021075

theorem tailTrace_3809244 : CollatzResearch.WordTrace tailWord_3809244 prefixEnd_3809244 1303982068170266366021075 := by
  unfold tailWord_3809244
  simp only [CollatzResearch.WordTrace]
  refine ⟨69467271305883514963009393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92623028407844686617345857 69467271305883514963009393)
  ·
    refine ⟨52100453479412636222257045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69467271305883514963009393 52100453479412636222257045)
    ·
      refine ⟨2442208756847467322918299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52100453479412636222257045 2442208756847467322918299)
      ·
        refine ⟨3663313135271200984377449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2442208756847467322918299 3663313135271200984377449)
        ·
          refine ⟨2747484851453400738283087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3663313135271200984377449 2747484851453400738283087)
          ·
            refine ⟨4121227277180101107424631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2747484851453400738283087 4121227277180101107424631)
            ·
              refine ⟨6181840915770151661136947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4121227277180101107424631 6181840915770151661136947)
              ·
                refine ⟨9272761373655227491705421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6181840915770151661136947 9272761373655227491705421)
                ·
                  refine ⟨3477285515120710309389533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9272761373655227491705421 3477285515120710309389533)
                  ·
                    refine ⟨1303982068170266366021075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3477285515120710309389533 1303982068170266366021075)
                    ·
                      rfl

theorem cell22_3809244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_3809244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809244 prefixEnd_3809244 := by exact prefixLift 3809244
  have htrace : WordTrace (prefixWord ++ tailWord_3809244) baseStart_3809244 baseEnd_3809244 := by
    simpa [prefixWord, tailWord_3809244, baseEnd_3809244] using wordTrace_append hprefix tailTrace_3809244
  have hstable : (prefixWord ++ tailWord_3809244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809244).length < 2 ^ (prefixWord ++ tailWord_3809244).sum := by decide
  have hdescent : baseEnd_3809244 < baseStart_3809244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809251 : List Nat := [1, 1, 1, 6, 1, 4, 1, 1, 6]
def baseStart_3809251 : Nat := 118140960795 + 3809251 * 2 ^ 59
def prefixEnd_3809251 : Nat := 4983230072969 + 3 ^ 40 * 3809251 * 2
def baseEnd_3809251 : Nat := 434661488137773560365351

theorem tailTrace_3809251 : CollatzResearch.WordTrace tailWord_3809251 prefixEnd_3809251 434661488137773560365351 := by
  unfold tailWord_3809251
  simp only [CollatzResearch.WordTrace]
  refine ⟨138934797922741670121523607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92623198615161113414349071 138934797922741670121523607)
  ·
    refine ⟨208402196884112505182285411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138934797922741670121523607 208402196884112505182285411)
    ·
      refine ⟨312603295326168757773428117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208402196884112505182285411 312603295326168757773428117)
      ·
        refine ⟨14653279468414160520629443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 312603295326168757773428117 14653279468414160520629443)
        ·
          refine ⟨21979919202621240780944165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14653279468414160520629443 21979919202621240780944165)
          ·
            refine ⟨4121234850491482646427031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21979919202621240780944165 4121234850491482646427031)
            ·
              refine ⟨6181852275737223969640547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4121234850491482646427031 6181852275737223969640547)
              ·
                refine ⟨9272778413605835954460821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6181852275737223969640547 9272778413605835954460821)
                ·
                  refine ⟨434661488137773560365351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9272778413605835954460821 434661488137773560365351)
                  ·
                    rfl

theorem cell22_3809251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 6].length) (baseStart_3809251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809251 prefixEnd_3809251 := by exact prefixLift 3809251
  have htrace : WordTrace (prefixWord ++ tailWord_3809251) baseStart_3809251 baseEnd_3809251 := by
    simpa [prefixWord, tailWord_3809251, baseEnd_3809251] using wordTrace_append hprefix tailTrace_3809251
  have hstable : (prefixWord ++ tailWord_3809251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809251).length < 2 ^ (prefixWord ++ tailWord_3809251).sum := by decide
  have hdescent : baseEnd_3809251 < baseStart_3809251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809270 : List Nat := [5, 1, 1, 1, 4, 2, 1, 2, 1, 4]
def baseStart_3809270 : Nat := 118140960795 + 3809270 * 2 ^ 59
def prefixEnd_3809270 : Nat := 4983230072969 + 3 ^ 40 * 3809270 * 2
def baseEnd_3809270 : Nat := 1303990968501610964870995

theorem tailTrace_3809270 : CollatzResearch.WordTrace tailWord_3809270 prefixEnd_3809270 1303990968501610964870995 := by
  unfold tailWord_3809270
  simp only [CollatzResearch.WordTrace]
  refine ⟨8683468181854552272904079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92623660606448557577643509 8683468181854552272904079)
  ·
    refine ⟨13025202272781828409356119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8683468181854552272904079 13025202272781828409356119)
    ·
      refine ⟨19537803409172742614034179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13025202272781828409356119 19537803409172742614034179)
      ·
        refine ⟨29306705113759113921051269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19537803409172742614034179 29306705113759113921051269)
        ·
          refine ⟨5495007208829833860197113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29306705113759113921051269 5495007208829833860197113)
          ·
            refine ⟨4121255406622375395147835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5495007208829833860197113 4121255406622375395147835)
            ·
              refine ⟨6181883109933563092721753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4121255406622375395147835 6181883109933563092721753)
              ·
                refine ⟨4636412332450172319541315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6181883109933563092721753 4636412332450172319541315)
                ·
                  refine ⟨6954618498675258479311973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4636412332450172319541315 6954618498675258479311973)
                  ·
                    refine ⟨1303990968501610964870995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6954618498675258479311973 1303990968501610964870995)
                    ·
                      rfl

theorem cell22_3809270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_3809270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809270 prefixEnd_3809270 := by exact prefixLift 3809270
  have htrace : WordTrace (prefixWord ++ tailWord_3809270) baseStart_3809270 baseEnd_3809270 := by
    simpa [prefixWord, tailWord_3809270, baseEnd_3809270] using wordTrace_append hprefix tailTrace_3809270
  have hstable : (prefixWord ++ tailWord_3809270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809270).length < 2 ^ (prefixWord ++ tailWord_3809270).sum := by decide
  have hdescent : baseEnd_3809270 < baseStart_3809270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809281 : List Nat := [1, 2, 4, 1, 2, 1, 4, 1, 2, 4]
def baseStart_3809281 : Nat := 118140960795 + 3809281 * 2 ^ 59
def prefixEnd_3809281 : Nat := 4983230072969 + 3 ^ 40 * 3809281 * 2
def baseEnd_3809281 : Nat := 1303994734026410602845961

theorem tailTrace_3809281 : CollatzResearch.WordTrace tailWord_3809281 prefixEnd_3809281 1303994734026410602845961 := by
  unfold tailWord_3809281
  simp only [CollatzResearch.WordTrace]
  refine ⟨138935892112632985245115697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92623928075088656830077131 138935892112632985245115697)
  ·
    refine ⟨104201919084474738933836773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138935892112632985245115697 104201919084474738933836773)
    ·
      refine ⟨19537859828339013550094395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104201919084474738933836773 19537859828339013550094395)
      ·
        refine ⟨29306789742508520325141593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19537859828339013550094395 29306789742508520325141593)
        ·
          refine ⟨21980092306881390243856195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29306789742508520325141593 21980092306881390243856195)
          ·
            refine ⟨32970138460322085365784293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21980092306881390243856195 32970138460322085365784293)
            ·
              refine ⟨6181900961310391006084555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32970138460322085365784293 6181900961310391006084555)
              ·
                refine ⟨9272851441965586509126833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6181900961310391006084555 9272851441965586509126833)
                ·
                  refine ⟨6954638581474189881845125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9272851441965586509126833 6954638581474189881845125)
                  ·
                    refine ⟨1303994734026410602845961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6954638581474189881845125 1303994734026410602845961)
                    ·
                      rfl

theorem cell22_3809281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_3809281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809281 prefixEnd_3809281 := by exact prefixLift 3809281
  have htrace : WordTrace (prefixWord ++ tailWord_3809281) baseStart_3809281 baseEnd_3809281 := by
    simpa [prefixWord, tailWord_3809281, baseEnd_3809281] using wordTrace_append hprefix tailTrace_3809281
  have hstable : (prefixWord ++ tailWord_3809281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809281).length < 2 ^ (prefixWord ++ tailWord_3809281).sum := by decide
  have hdescent : baseEnd_3809281 < baseStart_3809281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809311 : List Nat := [1, 1, 2, 4, 1, 2, 2, 3, 3, 3]
def baseStart_3809311 : Nat := 118140960795 + 3809311 * 2 ^ 59
def prefixEnd_3809311 : Nat := 4983230072969 + 3 ^ 40 * 3809311 * 2
def baseEnd_3809311 : Nat := 1304005003639500524595869

theorem tailTrace_3809311 : CollatzResearch.WordTrace tailWord_3809311 prefixEnd_3809311 1304005003639500524595869 := by
  unfold tailWord_3809311
  simp only [CollatzResearch.WordTrace]
  refine ⟨138936986302524300368707787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92624657535016200245805191 138936986302524300368707787)
  ·
    refine ⟨208405479453786450553061681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138936986302524300368707787 208405479453786450553061681)
    ·
      refine ⟨156304109590339837914796261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208405479453786450553061681 156304109590339837914796261)
      ·
        refine ⟨29307020548188719609024299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156304109590339837914796261 29307020548188719609024299)
        ·
          refine ⟨43960530822283079413536449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29307020548188719609024299 43960530822283079413536449)
          ·
            refine ⟨32970398116712309560152337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43960530822283079413536449 32970398116712309560152337)
            ·
              refine ⟨24727798587534232170114253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32970398116712309560152337 24727798587534232170114253)
              ·
                refine ⟨9272924470325337063792845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24727798587534232170114253 9272924470325337063792845)
                ·
                  refine ⟨3477346676372001398922317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9272924470325337063792845 3477346676372001398922317)
                  ·
                    refine ⟨1304005003639500524595869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3477346676372001398922317 1304005003639500524595869)
                    ·
                      rfl

theorem cell22_3809311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 3, 3].length) (baseStart_3809311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809311 prefixEnd_3809311 := by exact prefixLift 3809311
  have htrace : WordTrace (prefixWord ++ tailWord_3809311) baseStart_3809311 baseEnd_3809311 := by
    simpa [prefixWord, tailWord_3809311, baseEnd_3809311] using wordTrace_append hprefix tailTrace_3809311
  have hstable : (prefixWord ++ tailWord_3809311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809311).length < 2 ^ (prefixWord ++ tailWord_3809311).sum := by decide
  have hdescent : baseEnd_3809311 < baseStart_3809311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809313 : List Nat := [1, 2, 3, 2, 5, 1, 1, 7]
def baseStart_3809313 : Nat := 118140960795 + 3809313 * 2 ^ 59
def prefixEnd_3809313 : Nat := 4983230072969 + 3 ^ 40 * 3809313 * 2
def baseEnd_3809313 : Nat := 144889520920041465116207

theorem tailTrace_3809313 : CollatzResearch.WordTrace tailWord_3809313 prefixEnd_3809313 144889520920041465116207 := by
  unfold tailWord_3809313
  simp only [CollatzResearch.WordTrace]
  refine ⟨138937059248517054710280593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92624706165678036473520395 138937059248517054710280593)
  ·
    refine ⟨104202794436387791032710445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138937059248517054710280593 104202794436387791032710445)
    ·
      refine ⟨39076047913645421637266417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104202794436387791032710445 39076047913645421637266417)
      ·
        refine ⟨29307035935234066227949813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39076047913645421637266417 29307035935234066227949813)
        ·
          refine ⟨2747534618928193708870295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29307035935234066227949813 2747534618928193708870295)
          ·
            refine ⟨4121301928392290563305443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2747534618928193708870295 4121301928392290563305443)
            ·
              refine ⟨6181952892588435844958165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4121301928392290563305443 6181952892588435844958165)
              ·
                refine ⟨144889520920041465116207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6181952892588435844958165 144889520920041465116207)
                ·
                  rfl

theorem cell22_3809313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 7].length) (baseStart_3809313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809313 prefixEnd_3809313 := by exact prefixLift 3809313
  have htrace : WordTrace (prefixWord ++ tailWord_3809313) baseStart_3809313 baseEnd_3809313 := by
    simpa [prefixWord, tailWord_3809313, baseEnd_3809313] using wordTrace_append hprefix tailTrace_3809313
  have hstable : (prefixWord ++ tailWord_3809313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809313).length < 2 ^ (prefixWord ++ tailWord_3809313).sum := by decide
  have hdescent : baseEnd_3809313 < baseStart_3809313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809332 : List Nat := [2, 5, 1, 2, 3, 1, 1, 1, 2, 4]
def baseStart_3809332 : Nat := 118140960795 + 3809332 * 2 ^ 59
def prefixEnd_3809332 : Nat := 4983230072969 + 3 ^ 40 * 3809332 * 2
def baseEnd_3809332 : Nat := 1304012192368663469820805

theorem tailTrace_3809332 : CollatzResearch.WordTrace tailWord_3809332 prefixEnd_3809332 1304012192368663469820805 := by
  unfold tailWord_3809332
  simp only [CollatzResearch.WordTrace]
  refine ⟨69468876117724110477611125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92625168156965480636814833 69468876117724110477611125)
  ·
    refine ⟨6512707136036635357276043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69468876117724110477611125 6512707136036635357276043)
    ·
      refine ⟨9769060704054953035914065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6512707136036635357276043 9769060704054953035914065)
      ·
        refine ⟨7326795528041214776935549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9769060704054953035914065 7326795528041214776935549)
        ·
          refine ⟨2747548323015455541350831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7326795528041214776935549 2747548323015455541350831)
          ·
            refine ⟨4121322484523183312026247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2747548323015455541350831 4121322484523183312026247)
            ·
              refine ⟨6181983726784774968039371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4121322484523183312026247 6181983726784774968039371)
              ·
                refine ⟨9272975590177162452059057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6181983726784774968039371 9272975590177162452059057)
                ·
                  refine ⟨6954731692632871839044293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9272975590177162452059057 6954731692632871839044293)
                  ·
                    refine ⟨1304012192368663469820805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6954731692632871839044293 1304012192368663469820805)
                    ·
                      rfl

theorem cell22_3809332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_3809332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809332 prefixEnd_3809332 := by exact prefixLift 3809332
  have htrace : WordTrace (prefixWord ++ tailWord_3809332) baseStart_3809332 baseEnd_3809332 := by
    simpa [prefixWord, tailWord_3809332, baseEnd_3809332] using wordTrace_append hprefix tailTrace_3809332
  have hstable : (prefixWord ++ tailWord_3809332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809332).length < 2 ^ (prefixWord ++ tailWord_3809332).sum := by decide
  have hdescent : baseEnd_3809332 < baseStart_3809332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809345 : List Nat := [1, 2, 5, 1, 2, 1, 1, 5, 1, 3]
def baseStart_3809345 : Nat := 118140960795 + 3809345 * 2 ^ 59
def prefixEnd_3809345 : Nat := 4983230072969 + 3 ^ 40 * 3809345 * 2
def baseEnd_3809345 : Nat := 1304016642534335769245765

theorem tailTrace_3809345 : CollatzResearch.WordTrace tailWord_3809345 prefixEnd_3809345 1304016642534335769245765 := by
  unfold tailWord_3809345
  simp only [CollatzResearch.WordTrace]
  refine ⟨138938226384401124175445489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92625484256267416116963659 138938226384401124175445489)
  ·
    refine ⟨104203669788300843131584117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138938226384401124175445489 104203669788300843131584117)
    ·
      refine ⟨9769094042653204043586011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104203669788300843131584117 9769094042653204043586011)
      ·
        refine ⟨14653641063979806065379017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9769094042653204043586011 14653641063979806065379017)
        ·
          refine ⟨10990230797984854549034263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14653641063979806065379017 10990230797984854549034263)
          ·
            refine ⟨16485346196977281823551395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10990230797984854549034263 16485346196977281823551395)
            ·
              refine ⟨24728019295465922735327093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16485346196977281823551395 24728019295465922735327093)
              ·
                refine ⟨2318251808949930256436915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24728019295465922735327093 2318251808949930256436915)
                ·
                  refine ⟨3477377713424895384655373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2318251808949930256436915 3477377713424895384655373)
                  ·
                    refine ⟨1304016642534335769245765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3477377713424895384655373 1304016642534335769245765)
                    ·
                      rfl

theorem cell22_3809345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_3809345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809345 prefixEnd_3809345 := by exact prefixLift 3809345
  have htrace : WordTrace (prefixWord ++ tailWord_3809345) baseStart_3809345 baseEnd_3809345 := by
    simpa [prefixWord, tailWord_3809345, baseEnd_3809345] using wordTrace_append hprefix tailTrace_3809345
  have hstable : (prefixWord ++ tailWord_3809345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809345).length < 2 ^ (prefixWord ++ tailWord_3809345).sum := by decide
  have hdescent : baseEnd_3809345 < baseStart_3809345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809358 : List Nat := [4, 1, 1, 1, 1, 6, 1, 2, 5]
def baseStart_3809358 : Nat := 118140960795 + 3809358 * 2 ^ 59
def prefixEnd_3809358 : Nat := 4983230072969 + 3 ^ 40 * 3809358 * 2
def baseEnd_3809358 : Nat := 434673697566669356223575

theorem tailTrace_3809358 : CollatzResearch.WordTrace tailWord_3809358 prefixEnd_3809358 434673697566669356223575 := by
  unfold tailWord_3809358
  simp only [CollatzResearch.WordTrace]
  refine ⟨17367337566669253424458591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92625800355569351597112485 17367337566669253424458591)
  ·
    refine ⟨26051006350003880136687887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17367337566669253424458591 26051006350003880136687887)
    ·
      refine ⟨39076509525005820205031831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26051006350003880136687887 39076509525005820205031831)
      ·
        refine ⟨58614764287508730307547747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39076509525005820205031831 58614764287508730307547747)
        ·
          refine ⟨87922146431263095461321621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58614764287508730307547747 87922146431263095461321621)
          ·
            refine ⟨4121350613965457599749451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 87922146431263095461321621 4121350613965457599749451)
            ·
              refine ⟨6182025920948186399624177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4121350613965457599749451 6182025920948186399624177)
              ·
                refine ⟨4636519440711139799718133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6182025920948186399624177 4636519440711139799718133)
                ·
                  refine ⟨434673697566669356223575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4636519440711139799718133 434673697566669356223575)
                  ·
                    rfl

theorem cell22_3809358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_3809358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809358 prefixEnd_3809358 := by exact prefixLift 3809358
  have htrace : WordTrace (prefixWord ++ tailWord_3809358) baseStart_3809358 baseEnd_3809358 := by
    simpa [prefixWord, tailWord_3809358, baseEnd_3809358] using wordTrace_append hprefix tailTrace_3809358
  have hstable : (prefixWord ++ tailWord_3809358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809358).length < 2 ^ (prefixWord ++ tailWord_3809358).sum := by decide
  have hdescent : baseEnd_3809358 < baseStart_3809358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809373 : List Nat := [1, 4, 4, 1, 1, 1, 2, 1, 2, 5]
def baseStart_3809373 : Nat := 118140960795 + 3809373 * 2 ^ 59
def prefixEnd_3809373 : Nat := 4983230072969 + 3 ^ 40 * 3809373 * 2
def baseEnd_3809373 : Nat := 1304026227506553029545679

theorem tailTrace_3809373 : CollatzResearch.WordTrace tailWord_3809373 prefixEnd_3809373 1304026227506553029545679 := by
  unfold tailWord_3809373
  simp only [CollatzResearch.WordTrace]
  refine ⟨138939247628299684957464773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92626165085533123304976515 138939247628299684957464773)
  ·
    refine ⟨26051108930306190929524645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138939247628299684957464773 26051108930306190929524645)
    ·
      refine ⟨4884582924432410799285871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26051108930306190929524645 4884582924432410799285871)
      ·
        refine ⟨7326874386648616198928807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4884582924432410799285871 7326874386648616198928807)
        ·
          refine ⟨10990311579972924298393211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7326874386648616198928807 10990311579972924298393211)
          ·
            refine ⟨16485467369959386447589817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10990311579972924298393211 16485467369959386447589817)
            ·
              refine ⟨12364100527469539835692363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16485467369959386447589817 12364100527469539835692363)
              ·
                refine ⟨18546150791204309753538545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12364100527469539835692363 18546150791204309753538545)
                ·
                  refine ⟨13909613093403232315153909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18546150791204309753538545 13909613093403232315153909)
                  ·
                    refine ⟨1304026227506553029545679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13909613093403232315153909 1304026227506553029545679)
                    ·
                      rfl

theorem cell22_3809373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_3809373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809373 prefixEnd_3809373 := by exact prefixLift 3809373
  have htrace : WordTrace (prefixWord ++ tailWord_3809373) baseStart_3809373 baseEnd_3809373 := by
    simpa [prefixWord, tailWord_3809373, baseEnd_3809373] using wordTrace_append hprefix tailTrace_3809373
  have hstable : (prefixWord ++ tailWord_3809373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809373).length < 2 ^ (prefixWord ++ tailWord_3809373).sum := by decide
  have hdescent : baseEnd_3809373 < baseStart_3809373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809388 : List Nat := [2, 2, 1, 1, 3, 4, 2, 2, 1, 4]
def baseStart_3809388 : Nat := 118140960795 + 3809388 * 2 ^ 59
def prefixEnd_3809388 : Nat := 4983230072969 + 3 ^ 40 * 3809388 * 2
def baseEnd_3809388 : Nat := 1304031362313097990420633

theorem tailTrace_3809388 : CollatzResearch.WordTrace tailWord_3809388 prefixEnd_3809388 1304031362313097990420633 := by
  unfold tailWord_3809388
  simp only [CollatzResearch.WordTrace]
  refine ⟨69469897361622671259630409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92626529815496895012840545 69469897361622671259630409)
  ·
    refine ⟨52102423021217003444722807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69469897361622671259630409 52102423021217003444722807)
    ·
      refine ⟨78153634531825505167084211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52102423021217003444722807 78153634531825505167084211)
      ·
        refine ⟨117230451797738257750626317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78153634531825505167084211 117230451797738257750626317)
        ·
          refine ⟨43961419424151846656484869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117230451797738257750626317 43961419424151846656484869)
          ·
            refine ⟨8242766142028471248090913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43961419424151846656484869 8242766142028471248090913)
            ·
              refine ⟨6182074606521353436068185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8242766142028471248090913 6182074606521353436068185)
              ·
                refine ⟨4636555954891015077051139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6182074606521353436068185 4636555954891015077051139)
                ·
                  refine ⟨6954833932336522615576709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4636555954891015077051139 6954833932336522615576709)
                  ·
                    refine ⟨1304031362313097990420633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6954833932336522615576709 1304031362313097990420633)
                    ·
                      rfl

theorem cell22_3809388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 4].length) (baseStart_3809388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809388 prefixEnd_3809388 := by exact prefixLift 3809388
  have htrace : WordTrace (prefixWord ++ tailWord_3809388) baseStart_3809388 baseEnd_3809388 := by
    simpa [prefixWord, tailWord_3809388, baseEnd_3809388] using wordTrace_append hprefix tailTrace_3809388
  have hstable : (prefixWord ++ tailWord_3809388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809388).length < 2 ^ (prefixWord ++ tailWord_3809388).sum := by decide
  have hdescent : baseEnd_3809388 < baseStart_3809388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809418 : List Nat := [3, 1, 2, 3, 1, 2, 2, 1, 4, 3]
def baseStart_3809418 : Nat := 118140960795 + 3809418 * 2 ^ 59
def prefixEnd_3809418 : Nat := 4983230072969 + 3 ^ 40 * 3809418 * 2
def baseEnd_3809418 : Nat := 1304041631926187912170541

theorem tailTrace_3809418 : CollatzResearch.WordTrace tailWord_3809418 prefixEnd_3809418 1304041631926187912170541 := by
  unfold tailWord_3809418
  simp only [CollatzResearch.WordTrace]
  refine ⟨34735222228284164410713227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92627259275424438428568605 34735222228284164410713227)
  ·
    refine ⟨52102833342426246616069841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34735222228284164410713227 52102833342426246616069841)
    ·
      refine ⟨39077125006819684962052381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52102833342426246616069841 39077125006819684962052381)
      ·
        refine ⟨14653921877557381860769643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39077125006819684962052381 14653921877557381860769643)
        ·
          refine ⟨21980882816336072791154465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14653921877557381860769643 21980882816336072791154465)
          ·
            refine ⟨16485662112252054593365849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21980882816336072791154465 16485662112252054593365849)
            ·
              refine ⟨12364246584189040945024387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16485662112252054593365849 12364246584189040945024387)
              ·
                refine ⟨18546369876283561417536581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12364246584189040945024387 18546369876283561417536581)
                ·
                  refine ⟨3477444351803167765788109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18546369876283561417536581 3477444351803167765788109)
                  ·
                    refine ⟨1304041631926187912170541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3477444351803167765788109 1304041631926187912170541)
                    ·
                      rfl

theorem cell22_3809418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_3809418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809418 prefixEnd_3809418 := by exact prefixLift 3809418
  have htrace : WordTrace (prefixWord ++ tailWord_3809418) baseStart_3809418 baseEnd_3809418 := by
    simpa [prefixWord, tailWord_3809418, baseEnd_3809418] using wordTrace_append hprefix tailTrace_3809418
  have hstable : (prefixWord ++ tailWord_3809418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809418).length < 2 ^ (prefixWord ++ tailWord_3809418).sum := by decide
  have hdescent : baseEnd_3809418 < baseStart_3809418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809523 : List Nat := [1, 1, 1, 2, 2, 4, 3, 3, 1, 4]
def baseStart_3809523 : Nat := 118140960795 + 3809523 * 2 ^ 59
def prefixEnd_3809523 : Nat := 4983230072969 + 3 ^ 40 * 3809523 * 2
def baseEnd_3809523 : Nat := 1304077575572002638295219

theorem tailTrace_3809523 : CollatzResearch.WordTrace tailWord_3809523 prefixEnd_3809523 1304077575572002638295219 := by
  unfold tailWord_3809523
  simp only [CollatzResearch.WordTrace]
  refine ⟨138944718577756260575425223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92629812385170840383616815 138944718577756260575425223)
  ·
    refine ⟨208417077866634390863137835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138944718577756260575425223 208417077866634390863137835)
    ·
      refine ⟨312625616799951586294706753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208417077866634390863137835 312625616799951586294706753)
      ·
        refine ⟨234469212599963689721030065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312625616799951586294706753 234469212599963689721030065)
        ·
          refine ⟨175851909449972767290772549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234469212599963689721030065 175851909449972767290772549)
          ·
            refine ⟨32972233021869893867019853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175851909449972767290772549 32972233021869893867019853)
            ·
              refine ⟨12364587383201210200132445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32972233021869893867019853 12364587383201210200132445)
              ·
                refine ⟨4636720268700453825049667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12364587383201210200132445 4636720268700453825049667)
                ·
                  refine ⟨6955080403050680737574501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4636720268700453825049667 6955080403050680737574501)
                  ·
                    refine ⟨1304077575572002638295219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6955080403050680737574501 1304077575572002638295219)
                    ·
                      rfl

theorem cell22_3809523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 4].length) (baseStart_3809523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809523 prefixEnd_3809523 := by exact prefixLift 3809523
  have htrace : WordTrace (prefixWord ++ tailWord_3809523) baseStart_3809523 baseEnd_3809523 := by
    simpa [prefixWord, tailWord_3809523, baseEnd_3809523] using wordTrace_append hprefix tailTrace_3809523
  have hstable : (prefixWord ++ tailWord_3809523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809523).length < 2 ^ (prefixWord ++ tailWord_3809523).sum := by decide
  have hdescent : baseEnd_3809523 < baseStart_3809523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809536 : List Nat := [2, 1, 1, 2, 1, 1, 4, 2, 3, 5]
def baseStart_3809536 : Nat := 118140960795 + 3809536 * 2 ^ 59
def prefixEnd_3809536 : Nat := 4983230072969 + 3 ^ 40 * 3809536 * 2
def baseEnd_3809536 : Nat := 1304082025737674937720179

theorem tailTrace_3809536 : CollatzResearch.WordTrace tailWord_3809536 prefixEnd_3809536 1304082025737674937720179 := by
  unfold tailWord_3809536
  simp only [CollatzResearch.WordTrace]
  refine ⟨69472596363354581897824231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92630128484472775863765641 69472596363354581897824231)
  ·
    refine ⟨104208894545031872846736347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69472596363354581897824231 104208894545031872846736347)
    ·
      refine ⟨156313341817547809270104521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104208894545031872846736347 156313341817547809270104521)
      ·
        refine ⟨117235006363160856952578391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156313341817547809270104521 117235006363160856952578391)
        ·
          refine ⟨175852509544741285428867587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117235006363160856952578391 175852509544741285428867587)
          ·
            refine ⟨263778764317111928143301381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175852509544741285428867587 263778764317111928143301381)
            ·
              refine ⟨49458518309458486526869009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 263778764317111928143301381 49458518309458486526869009)
              ·
                refine ⟨37093888732093864895151757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49458518309458486526869009 37093888732093864895151757)
                ·
                  refine ⟨13910208274535199335681909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37093888732093864895151757 13910208274535199335681909)
                  ·
                    refine ⟨1304082025737674937720179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13910208274535199335681909 1304082025737674937720179)
                    ·
                      rfl

theorem cell22_3809536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 3, 5].length) (baseStart_3809536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809536 prefixEnd_3809536 := by exact prefixLift 3809536
  have htrace : WordTrace (prefixWord ++ tailWord_3809536) baseStart_3809536 baseEnd_3809536 := by
    simpa [prefixWord, tailWord_3809536, baseEnd_3809536] using wordTrace_append hprefix tailTrace_3809536
  have hstable : (prefixWord ++ tailWord_3809536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809536).length < 2 ^ (prefixWord ++ tailWord_3809536).sum := by decide
  have hdescent : baseEnd_3809536 < baseStart_3809536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809553 : List Nat := [1, 2, 2, 1, 1, 5, 3, 1, 1, 5]
def baseStart_3809553 : Nat := 118140960795 + 3809553 * 2 ^ 59
def prefixEnd_3809553 : Nat := 4983230072969 + 3 ^ 40 * 3809553 * 2
def baseEnd_3809553 : Nat := 1304087845185092560045127

theorem tailTrace_3809553 : CollatzResearch.WordTrace tailWord_3809553 prefixEnd_3809553 1304087845185092560045127 := by
  unfold tailWord_3809553
  simp only [CollatzResearch.WordTrace]
  refine ⟨138945812767647575699017313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92630541845098383799344875 138945812767647575699017313)
  ·
    refine ⟨104209359575735681774262985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138945812767647575699017313 104209359575735681774262985)
    ·
      refine ⟨78157019681801761330697239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104209359575735681774262985 78157019681801761330697239)
      ·
        refine ⟨117235529522702641996045859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78157019681801761330697239 117235529522702641996045859)
        ·
          refine ⟨175853294284053962994068789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117235529522702641996045859 175853294284053962994068789)
          ·
            refine ⟨16486246339130059030693949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 175853294284053962994068789 16486246339130059030693949)
            ·
              refine ⟨6182342377173772136510231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16486246339130059030693949 6182342377173772136510231)
              ·
                refine ⟨9273513565760658204765347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6182342377173772136510231 9273513565760658204765347)
                ·
                  refine ⟨13910270348640987307148021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9273513565760658204765347 13910270348640987307148021)
                  ·
                    refine ⟨1304087845185092560045127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13910270348640987307148021 1304087845185092560045127)
                    ·
                      rfl

theorem cell22_3809553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 5].length) (baseStart_3809553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809553 prefixEnd_3809553 := by exact prefixLift 3809553
  have htrace : WordTrace (prefixWord ++ tailWord_3809553) baseStart_3809553 baseEnd_3809553 := by
    simpa [prefixWord, tailWord_3809553, baseEnd_3809553] using wordTrace_append hprefix tailTrace_3809553
  have hstable : (prefixWord ++ tailWord_3809553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809553).length < 2 ^ (prefixWord ++ tailWord_3809553).sum := by decide
  have hdescent : baseEnd_3809553 < baseStart_3809553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809568 : List Nat := [2, 1, 1, 5, 2, 1, 2, 1, 1, 6]
def baseStart_3809568 : Nat := 118140960795 + 3809568 * 2 ^ 59
def prefixEnd_3809568 : Nat := 4983230072969 + 3 ^ 40 * 3809568 * 2
def baseEnd_3809568 : Nat := 1304092979991637520920081

theorem tailTrace_3809568 : CollatzResearch.WordTrace tailWord_3809568 prefixEnd_3809568 1304092979991637520920081 := by
  unfold tailWord_3809568
  simp only [CollatzResearch.WordTrace]
  refine ⟨69473179931296616630406679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92630906575062155507208905 69473179931296616630406679)
  ·
    refine ⟨104209769896944924945610019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69473179931296616630406679 104209769896944924945610019)
    ·
      refine ⟨156314654845417387418415029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104209769896944924945610019 156314654845417387418415029)
      ·
        refine ⟨14654498891757880070476409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156314654845417387418415029 14654498891757880070476409)
        ·
          refine ⟨10990874168818410052857307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14654498891757880070476409 10990874168818410052857307)
          ·
            refine ⟨16486311253227615079285961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10990874168818410052857307 16486311253227615079285961)
            ·
              refine ⟨12364733439920711309464471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16486311253227615079285961 12364733439920711309464471)
              ·
                refine ⟨18547100159881066964196707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12364733439920711309464471 18547100159881066964196707)
                ·
                  refine ⟨27820650239821600446295061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18547100159881066964196707 27820650239821600446295061)
                  ·
                    refine ⟨1304092979991637520920081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27820650239821600446295061 1304092979991637520920081)
                    ·
                      rfl

theorem cell22_3809568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 1, 6].length) (baseStart_3809568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809568 prefixEnd_3809568 := by exact prefixLift 3809568
  have htrace : WordTrace (prefixWord ++ tailWord_3809568) baseStart_3809568 baseEnd_3809568 := by
    simpa [prefixWord, tailWord_3809568, baseEnd_3809568] using wordTrace_append hprefix tailTrace_3809568
  have hstable : (prefixWord ++ tailWord_3809568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809568).length < 2 ^ (prefixWord ++ tailWord_3809568).sum := by decide
  have hdescent : baseEnd_3809568 < baseStart_3809568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809570 : List Nat := [3, 3, 1, 1, 3, 1, 1, 2, 4, 3]
def baseStart_3809570 : Nat := 118140960795 + 3809570 * 2 ^ 59
def prefixEnd_3809570 : Nat := 4983230072969 + 3 ^ 40 * 3809570 * 2
def baseEnd_3809570 : Nat := 1304093664632510182370075

theorem tailTrace_3809570 : CollatzResearch.WordTrace tailWord_3809570 prefixEnd_3809570 1304093664632510182370075 := by
  unfold tailWord_3809570
  simp only [CollatzResearch.WordTrace]
  refine ⟨34736608202146496900596541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92630955205723991734924109 34736608202146496900596541)
  ·
    refine ⟨13026228075804936337723703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34736608202146496900596541 13026228075804936337723703)
    ·
      refine ⟨19539342113707404506585555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13026228075804936337723703 19539342113707404506585555)
      ·
        refine ⟨29309013170561106759878333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19539342113707404506585555 29309013170561106759878333)
        ·
          refine ⟨10990879938960415034954375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29309013170561106759878333 10990879938960415034954375)
          ·
            refine ⟨16486319908440622552431563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10990879938960415034954375 16486319908440622552431563)
            ·
              refine ⟨24729479862660933828647345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16486319908440622552431563 24729479862660933828647345)
              ·
                refine ⟨18547109896995700371485509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24729479862660933828647345 18547109896995700371485509)
                ·
                  refine ⟨3477583105686693819653533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18547109896995700371485509 3477583105686693819653533)
                  ·
                    refine ⟨1304093664632510182370075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3477583105686693819653533 1304093664632510182370075)
                    ·
                      rfl

theorem cell22_3809570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_3809570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809570 prefixEnd_3809570 := by exact prefixLift 3809570
  have htrace : WordTrace (prefixWord ++ tailWord_3809570) baseStart_3809570 baseEnd_3809570 := by
    simpa [prefixWord, tailWord_3809570, baseEnd_3809570] using wordTrace_append hprefix tailTrace_3809570
  have hstable : (prefixWord ++ tailWord_3809570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809570).length < 2 ^ (prefixWord ++ tailWord_3809570).sum := by decide
  have hdescent : baseEnd_3809570 < baseStart_3809570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809572 : List Nat := [2, 3, 1, 3, 1, 4, 1, 3, 4]
def baseStart_3809572 : Nat := 118140960795 + 3809572 * 2 ^ 59
def prefixEnd_3809572 : Nat := 4983230072969 + 3 ^ 40 * 3809572 * 2
def baseEnd_3809572 : Nat := 434698116424460947940023

theorem tailTrace_3809572 : CollatzResearch.WordTrace tailWord_3809572 prefixEnd_3809572 434698116424460947940023 := by
  unfold tailWord_3809572
  simp only [CollatzResearch.WordTrace]
  refine ⟨69473252877289370971979485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92631003836385827962639313 69473252877289370971979485)
  ·
    refine ⟨26052469828983514114492307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69473252877289370971979485 26052469828983514114492307)
    ·
      refine ⟨39078704743475271171738461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26052469828983514114492307 39078704743475271171738461)
      ·
        refine ⟨14654514278803226689401923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39078704743475271171738461 14654514278803226689401923)
        ·
          refine ⟨21981771418204840034102885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14654514278803226689401923 21981771418204840034102885)
          ·
            refine ⟨4121582140913407506394291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21981771418204840034102885 4121582140913407506394291)
            ·
              refine ⟨6182373211370111259591437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4121582140913407506394291 6182373211370111259591437)
              ·
                refine ⟨2318389954263791722346789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6182373211370111259591437 2318389954263791722346789)
                ·
                  refine ⟨434698116424460947940023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2318389954263791722346789 434698116424460947940023)
                  ·
                    rfl

theorem cell22_3809572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_3809572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809572 prefixEnd_3809572 := by exact prefixLift 3809572
  have htrace : WordTrace (prefixWord ++ tailWord_3809572) baseStart_3809572 baseEnd_3809572 := by
    simpa [prefixWord, tailWord_3809572, baseEnd_3809572] using wordTrace_append hprefix tailTrace_3809572
  have hstable : (prefixWord ++ tailWord_3809572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809572).length < 2 ^ (prefixWord ++ tailWord_3809572).sum := by decide
  have hdescent : baseEnd_3809572 < baseStart_3809572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809585 : List Nat := [1, 2, 2, 3, 4, 1, 1, 2, 2, 4]
def baseStart_3809585 : Nat := 118140960795 + 3809585 * 2 ^ 59
def prefixEnd_3809585 : Nat := 4983230072969 + 3 ^ 40 * 3809585 * 2
def baseEnd_3809585 : Nat := 1304098799439055143245029

theorem tailTrace_3809585 : CollatzResearch.WordTrace tailWord_3809585 prefixEnd_3809585 1304098799439055143245029 := by
  unfold tailWord_3809585
  simp only [CollatzResearch.WordTrace]
  refine ⟨138946979903531645164182209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92631319935687763442788139 138946979903531645164182209)
  ·
    refine ⟨104210234927648733873136657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138946979903531645164182209 104210234927648733873136657)
    ·
      refine ⟨78157676195736550404852493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104210234927648733873136657 78157676195736550404852493)
      ·
        refine ⟨29309128573401206401819685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78157676195736550404852493 29309128573401206401819685)
        ·
          refine ⟨5495461607512726200341191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29309128573401206401819685 5495461607512726200341191)
          ·
            refine ⟨8243192411269089300511787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5495461607512726200341191 8243192411269089300511787)
            ·
              refine ⟨12364788616903633950767681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8243192411269089300511787 12364788616903633950767681)
              ·
                refine ⟨9273591462677725463075761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12364788616903633950767681 9273591462677725463075761)
                ·
                  refine ⟨6955193597008294097306821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9273591462677725463075761 6955193597008294097306821)
                  ·
                    refine ⟨1304098799439055143245029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6955193597008294097306821 1304098799439055143245029)
                    ·
                      rfl

theorem cell22_3809585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 4].length) (baseStart_3809585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809585 prefixEnd_3809585 := by exact prefixLift 3809585
  have htrace : WordTrace (prefixWord ++ tailWord_3809585) baseStart_3809585 baseEnd_3809585 := by
    simpa [prefixWord, tailWord_3809585, baseEnd_3809585] using wordTrace_append hprefix tailTrace_3809585
  have hstable : (prefixWord ++ tailWord_3809585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809585).length < 2 ^ (prefixWord ++ tailWord_3809585).sum := by decide
  have hdescent : baseEnd_3809585 < baseStart_3809585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809604 : List Nat := [2, 3, 4, 1, 2, 1, 1, 3, 2, 3]
def baseStart_3809604 : Nat := 118140960795 + 3809604 * 2 ^ 59
def prefixEnd_3809604 : Nat := 4983230072969 + 3 ^ 40 * 3809604 * 2
def baseEnd_3809604 : Nat := 1304105303527345427019971

theorem tailTrace_3809604 : CollatzResearch.WordTrace tailWord_3809604 prefixEnd_3809604 1304105303527345427019971 := by
  unfold tailWord_3809604
  simp only [CollatzResearch.WordTrace]
  refine ⟨69473836445231405704561933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92631781926975207606082577 69473836445231405704561933)
  ·
    refine ⟨26052688666961777139210725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69473836445231405704561933 26052688666961777139210725)
    ·
      refine ⟨4884879125055333213602011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26052688666961777139210725 4884879125055333213602011)
      ·
        refine ⟨7327318687582999820403017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4884879125055333213602011 7327318687582999820403017)
        ·
          refine ⟨5495489015687249865302263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7327318687582999820403017 5495489015687249865302263)
          ·
            refine ⟨8243233523530874797953395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5495489015687249865302263 8243233523530874797953395)
            ·
              refine ⟨12364850285296312196930093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8243233523530874797953395 12364850285296312196930093)
              ·
                refine ⟨4636818856986117073848785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12364850285296312196930093 4636818856986117073848785)
                ·
                  refine ⟨3477614142739587805386589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4636818856986117073848785 3477614142739587805386589)
                  ·
                    refine ⟨1304105303527345427019971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3477614142739587805386589 1304105303527345427019971)
                    ·
                      rfl

theorem cell22_3809604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_3809604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809604 prefixEnd_3809604 := by exact prefixLift 3809604
  have htrace : WordTrace (prefixWord ++ tailWord_3809604) baseStart_3809604 baseEnd_3809604 := by
    simpa [prefixWord, tailWord_3809604, baseEnd_3809604] using wordTrace_append hprefix tailTrace_3809604
  have hstable : (prefixWord ++ tailWord_3809604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809604).length < 2 ^ (prefixWord ++ tailWord_3809604).sum := by decide
  have hdescent : baseEnd_3809604 < baseStart_3809604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809611 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 9]
def baseStart_3809611 : Nat := 118140960795 + 3809611 * 2 ^ 59
def prefixEnd_3809611 : Nat := 4983230072969 + 3 ^ 40 * 3809611 * 2
def baseEnd_3809611 : Nat := 434702566590133247364983

theorem tailTrace_3809611 : CollatzResearch.WordTrace tailWord_3809611 prefixEnd_3809611 434702566590133247364983 := by
  unfold tailWord_3809611
  simp only [CollatzResearch.WordTrace]
  refine ⟨138947928201437451604628687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92631952134291634403085791 138947928201437451604628687)
  ·
    refine ⟨208421892302156177406943031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138947928201437451604628687 208421892302156177406943031)
    ·
      refine ⟨312632838453234266110414547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208421892302156177406943031 312632838453234266110414547)
      ·
        refine ⟨468949257679851399165621821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312632838453234266110414547 468949257679851399165621821)
        ·
          refine ⟨175855971629944274687108183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 468949257679851399165621821 175855971629944274687108183)
          ·
            refine ⟨263783957444916412030662275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175855971629944274687108183 263783957444916412030662275)
            ·
              refine ⟨395675936167374618045993413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263783957444916412030662275 395675936167374618045993413)
              ·
                refine ⟨74189238031382740883623765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 395675936167374618045993413 74189238031382740883623765)
                ·
                  refine ⟨434702566590133247364983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 74189238031382740883623765 434702566590133247364983)
                  ·
                    rfl

theorem cell22_3809611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 9].length) (baseStart_3809611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809611 prefixEnd_3809611 := by exact prefixLift 3809611
  have htrace : WordTrace (prefixWord ++ tailWord_3809611) baseStart_3809611 baseEnd_3809611 := by
    simpa [prefixWord, tailWord_3809611, baseEnd_3809611] using wordTrace_append hprefix tailTrace_3809611
  have hstable : (prefixWord ++ tailWord_3809611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809611).length < 2 ^ (prefixWord ++ tailWord_3809611).sum := by decide
  have hdescent : baseEnd_3809611 < baseStart_3809611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809645 : List Nat := [1, 5, 1, 1, 1, 2, 4, 2, 5]
def baseStart_3809645 : Nat := 118140960795 + 3809645 * 2 ^ 59
def prefixEnd_3809645 : Nat := 4983230072969 + 3 ^ 40 * 3809645 * 2
def baseEnd_3809645 : Nat := 434706446221744995581615

theorem tailTrace_3809645 : CollatzResearch.WordTrace tailWord_3809645 prefixEnd_3809645 434706446221744995581615 := by
  unfold tailWord_3809645
  simp only [CollatzResearch.WordTrace]
  refine ⟨138949168283314275411366389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92632778855542850274244259 138949168283314275411366389)
  ·
    refine ⟨13026484526560713319815599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 138949168283314275411366389 13026484526560713319815599)
    ·
      refine ⟨19539726789841069979723399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13026484526560713319815599 19539726789841069979723399)
      ·
        refine ⟨29309590184761604969585099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19539726789841069979723399 29309590184761604969585099)
        ·
          refine ⟨43964385277142407454377649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29309590184761604969585099 43964385277142407454377649)
          ·
            refine ⟨32973288957856805590783237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43964385277142407454377649 32973288957856805590783237)
            ·
              refine ⟨6182491679598151048271857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32973288957856805590783237 6182491679598151048271857)
              ·
                refine ⟨4636868759698613286203893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6182491679598151048271857 4636868759698613286203893)
                ·
                  refine ⟨434706446221744995581615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4636868759698613286203893 434706446221744995581615)
                  ·
                    rfl

theorem cell22_3809645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_3809645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809645 prefixEnd_3809645 := by exact prefixLift 3809645
  have htrace : WordTrace (prefixWord ++ tailWord_3809645) baseStart_3809645 baseEnd_3809645 := by
    simpa [prefixWord, tailWord_3809645, baseEnd_3809645] using wordTrace_append hprefix tailTrace_3809645
  have hstable : (prefixWord ++ tailWord_3809645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809645).length < 2 ^ (prefixWord ++ tailWord_3809645).sum := by decide
  have hdescent : baseEnd_3809645 < baseStart_3809645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809673 : List Nat := [1, 2, 1, 1, 6, 1, 1, 1, 8]
def baseStart_3809673 : Nat := 118140960795 + 3809673 * 2 ^ 59
def prefixEnd_3809673 : Nat := 4983230072969 + 3 ^ 40 * 3809673 * 2
def baseEnd_3809673 : Nat := 434709641212484082348253

theorem tailTrace_3809673 : CollatzResearch.WordTrace tailWord_3809673 prefixEnd_3809673 434709641212484082348253 := by
  unfold tailWord_3809673
  simp only [CollatzResearch.WordTrace]
  refine ⟨138950189527212836193385673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92633459684808557462257115 138950189527212836193385673)
  ·
    refine ⟨104212642145409627145039255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138950189527212836193385673 104212642145409627145039255)
    ·
      refine ⟨156318963218114440717558883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104212642145409627145039255 156318963218114440717558883)
      ·
        refine ⟨234478444827171661076338325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156318963218114440717558883 234478444827171661076338325)
        ·
          refine ⟨10991177101273671612953359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 234478444827171661076338325 10991177101273671612953359)
          ·
            refine ⟨16486765651910507419430039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10991177101273671612953359 16486765651910507419430039)
            ·
              refine ⟨24730148477865761129145059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16486765651910507419430039 24730148477865761129145059)
              ·
                refine ⟨37095222716798641693717589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24730148477865761129145059 37095222716798641693717589)
                ·
                  refine ⟨434709641212484082348253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37095222716798641693717589 434709641212484082348253)
                  ·
                    rfl

theorem cell22_3809673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 8].length) (baseStart_3809673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809673 prefixEnd_3809673 := by exact prefixLift 3809673
  have htrace : WordTrace (prefixWord ++ tailWord_3809673) baseStart_3809673 baseEnd_3809673 := by
    simpa [prefixWord, tailWord_3809673, baseEnd_3809673] using wordTrace_append hprefix tailTrace_3809673
  have hstable : (prefixWord ++ tailWord_3809673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809673).length < 2 ^ (prefixWord ++ tailWord_3809673).sum := by decide
  have hdescent : baseEnd_3809673 < baseStart_3809673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809735 : List Nat := [1, 1, 4, 1, 1, 4, 4, 6]
def baseStart_3809735 : Nat := 118140960795 + 3809735 * 2 ^ 59
def prefixEnd_3809735 : Nat := 4983230072969 + 3 ^ 40 * 3809735 * 2
def baseEnd_3809735 : Nat := 144905571944944972443841

theorem tailTrace_3809735 : CollatzResearch.WordTrace tailWord_3809735 prefixEnd_3809735 144905571944944972443841 := by
  unfold tailWord_3809735
  simp only [CollatzResearch.WordTrace]
  refine ⟨138952450852988220782142659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92634967235325480521428439 138952450852988220782142659)
  ·
    refine ⟨208428676279482331173213989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138952450852988220782142659 208428676279482331173213989)
    ·
      refine ⟨39080376802402937094977623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208428676279482331173213989 39080376802402937094977623)
      ·
        refine ⟨58620565203604405642466435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39080376802402937094977623 58620565203604405642466435)
        ·
          refine ⟨87930847805406608463699653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58620565203604405642466435 87930847805406608463699653)
          ·
            refine ⟨16487033963513739086943685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87930847805406608463699653 16487033963513739086943685)
            ·
              refine ⟨3091318868158826078801941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16487033963513739086943685 3091318868158826078801941)
              ·
                refine ⟨144905571944944972443841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3091318868158826078801941 144905571944944972443841)
                ·
                  rfl

theorem cell22_3809735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 6].length) (baseStart_3809735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809735 prefixEnd_3809735 := by exact prefixLift 3809735
  have htrace : WordTrace (prefixWord ++ tailWord_3809735) baseStart_3809735 baseEnd_3809735 := by
    simpa [prefixWord, tailWord_3809735, baseEnd_3809735] using wordTrace_append hprefix tailTrace_3809735
  have hstable : (prefixWord ++ tailWord_3809735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809735).length < 2 ^ (prefixWord ++ tailWord_3809735).sum := by decide
  have hdescent : baseEnd_3809735 < baseStart_3809735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809825 : List Nat := [1, 2, 3, 2, 2, 1, 2, 3, 6]
def baseStart_3809825 : Nat := 118140960795 + 3809825 * 2 ^ 59
def prefixEnd_3809825 : Nat := 4983230072969 + 3 ^ 40 * 3809825 * 2
def baseEnd_3809825 : Nat := 434726985447924839081431

theorem tailTrace_3809825 : CollatzResearch.WordTrace tailWord_3809825 prefixEnd_3809825 434726985447924839081431 := by
  unfold tailWord_3809825
  simp only [CollatzResearch.WordTrace]
  refine ⟨138955733422662166152918929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92637155615108110768612619 138955733422662166152918929)
  ·
    refine ⟨104216800066996624614689197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138955733422662166152918929 104216800066996624614689197)
    ·
      refine ⟨39081300025123734230508449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104216800066996624614689197 39081300025123734230508449)
      ·
        refine ⟨29310975018842800672881337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39081300025123734230508449 29310975018842800672881337)
        ·
          refine ⟨21983231264132100504661003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29310975018842800672881337 21983231264132100504661003)
          ·
            refine ⟨32974846896198150756991505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21983231264132100504661003 32974846896198150756991505)
            ·
              refine ⟨24731135172148613067743629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32974846896198150756991505 24731135172148613067743629)
              ·
                refine ⟨9274175689555729900403861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24731135172148613067743629 9274175689555729900403861)
                ·
                  refine ⟨434726985447924839081431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9274175689555729900403861 434726985447924839081431)
                  ·
                    rfl

theorem cell22_3809825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 6].length) (baseStart_3809825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809825 prefixEnd_3809825 := by exact prefixLift 3809825
  have htrace : WordTrace (prefixWord ++ tailWord_3809825) baseStart_3809825 baseEnd_3809825 := by
    simpa [prefixWord, tailWord_3809825, baseEnd_3809825] using wordTrace_append hprefix tailTrace_3809825
  have hstable : (prefixWord ++ tailWord_3809825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809825).length < 2 ^ (prefixWord ++ tailWord_3809825).sum := by decide
  have hdescent : baseEnd_3809825 < baseStart_3809825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809840 : List Nat := [2, 1, 1, 1, 2, 3, 3, 3, 1, 5]
def baseStart_3809840 : Nat := 118140960795 + 3809840 * 2 ^ 59
def prefixEnd_3809840 : Nat := 4983230072969 + 3 ^ 40 * 3809840 * 2
def baseEnd_3809840 : Nat := 1304186091150319478119247

theorem tailTrace_3809840 : CollatzResearch.WordTrace tailWord_3809840 prefixEnd_3809840 1304186091150319478119247 := by
  unfold tailWord_3809840
  simp only [CollatzResearch.WordTrace]
  refine ⟨69478140258803911857357487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92637520345071882476476649 69478140258803911857357487)
  ·
    refine ⟨104217210388205867786036231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69478140258803911857357487 104217210388205867786036231)
    ·
      refine ⟨156325815582308801679054347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104217210388205867786036231 156325815582308801679054347)
      ·
        refine ⟨234488723373463202518581521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156325815582308801679054347 234488723373463202518581521)
        ·
          refine ⟨175866542530097401888936141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234488723373463202518581521 175866542530097401888936141)
          ·
            refine ⟨65949953448786525708351053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175866542530097401888936141 65949953448786525708351053)
            ·
              refine ⟨24731232543294947140631645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65949953448786525708351053 24731232543294947140631645)
              ·
                refine ⟨9274212203735605177736867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24731232543294947140631645 9274212203735605177736867)
                ·
                  refine ⟨13911318305603407766605301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9274212203735605177736867 13911318305603407766605301)
                  ·
                    refine ⟨1304186091150319478119247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13911318305603407766605301 1304186091150319478119247)
                    ·
                      rfl

theorem cell22_3809840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 1, 5].length) (baseStart_3809840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809840 prefixEnd_3809840 := by exact prefixLift 3809840
  have htrace : WordTrace (prefixWord ++ tailWord_3809840) baseStart_3809840 baseEnd_3809840 := by
    simpa [prefixWord, tailWord_3809840, baseEnd_3809840] using wordTrace_append hprefix tailTrace_3809840
  have hstable : (prefixWord ++ tailWord_3809840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809840).length < 2 ^ (prefixWord ++ tailWord_3809840).sum := by decide
  have hdescent : baseEnd_3809840 < baseStart_3809840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809855 : List Nat := [1, 1, 2, 2, 3, 2, 3, 1, 1, 6]
def baseStart_3809855 : Nat := 118140960795 + 3809855 * 2 ^ 59
def prefixEnd_3809855 : Nat := 4983230072969 + 3 ^ 40 * 3809855 * 2
def baseEnd_3809855 : Nat := 1304191225956864438994201

theorem tailTrace_3809855 : CollatzResearch.WordTrace tailWord_3809855 prefixEnd_3809855 1304191225956864438994201 := by
  unfold tailWord_3809855
  simp only [CollatzResearch.WordTrace]
  refine ⟨138956827612553481276511019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92637885075035654184340679 138956827612553481276511019)
  ·
    refine ⟨208435241418830221914766529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138956827612553481276511019 208435241418830221914766529)
    ·
      refine ⟨156326431064122666436074897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208435241418830221914766529 156326431064122666436074897)
      ·
        refine ⟨117244823298091999827056173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156326431064122666436074897 117244823298091999827056173)
        ·
          refine ⟨43966808736784499935146065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117244823298091999827056173 43966808736784499935146065)
          ·
            refine ⟨32975106552588374951359549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43966808736784499935146065 32975106552588374951359549)
            ·
              refine ⟨12365664957220640606759831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32975106552588374951359549 12365664957220640606759831)
              ·
                refine ⟨18548497435830960910139747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12365664957220640606759831 18548497435830960910139747)
                ·
                  refine ⟨27822746153746441365209621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18548497435830960910139747 27822746153746441365209621)
                  ·
                    refine ⟨1304191225956864438994201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27822746153746441365209621 1304191225956864438994201)
                    ·
                      rfl

theorem cell22_3809855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 6].length) (baseStart_3809855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809855 prefixEnd_3809855 := by exact prefixLift 3809855
  have htrace : WordTrace (prefixWord ++ tailWord_3809855) baseStart_3809855 baseEnd_3809855 := by
    simpa [prefixWord, tailWord_3809855, baseEnd_3809855] using wordTrace_append hprefix tailTrace_3809855
  have hstable : (prefixWord ++ tailWord_3809855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809855).length < 2 ^ (prefixWord ++ tailWord_3809855).sum := by decide
  have hdescent : baseEnd_3809855 < baseStart_3809855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809857 : List Nat := [1, 2, 5, 1, 1, 2, 2, 2, 1, 5]
def baseStart_3809857 : Nat := 118140960795 + 3809857 * 2 ^ 59
def prefixEnd_3809857 : Nat := 4983230072969 + 3 ^ 40 * 3809857 * 2
def baseEnd_3809857 : Nat := 1304191910597737100444195

theorem tailTrace_3809857 : CollatzResearch.WordTrace tailWord_3809857 prefixEnd_3809857 1304191910597737100444195 := by
  unfold tailWord_3809857
  simp only [CollatzResearch.WordTrace]
  refine ⟨138956900558546235618083825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92637933705697490412055883 138956900558546235618083825)
  ·
    refine ⟨104217675418909676713562869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138956900558546235618083825 104217675418909676713562869)
    ·
      refine ⟨9770407070522782191896519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104217675418909676713562869 9770407070522782191896519)
      ·
        refine ⟨14655610605784173287844779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9770407070522782191896519 14655610605784173287844779)
        ·
          refine ⟨21983415908676259931767169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14655610605784173287844779 21983415908676259931767169)
          ·
            refine ⟨16487561931507194948825377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21983415908676259931767169 16487561931507194948825377)
            ·
              refine ⟨12365671448630396211619033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16487561931507194948825377 12365671448630396211619033)
              ·
                refine ⟨9274253586472797158714275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12365671448630396211619033 9274253586472797158714275)
                ·
                  refine ⟨13911380379709195738071413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9274253586472797158714275 13911380379709195738071413)
                  ·
                    refine ⟨1304191910597737100444195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13911380379709195738071413 1304191910597737100444195)
                    ·
                      rfl

theorem cell22_3809857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_3809857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809857 prefixEnd_3809857 := by exact prefixLift 3809857
  have htrace : WordTrace (prefixWord ++ tailWord_3809857) baseStart_3809857 baseEnd_3809857 := by
    simpa [prefixWord, tailWord_3809857, baseEnd_3809857] using wordTrace_append hprefix tailTrace_3809857
  have hstable : (prefixWord ++ tailWord_3809857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809857).length < 2 ^ (prefixWord ++ tailWord_3809857).sum := by decide
  have hdescent : baseEnd_3809857 < baseStart_3809857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809900 : List Nat := [2, 2, 1, 1, 3, 1, 2, 2, 2, 6]
def baseStart_3809900 : Nat := 118140960795 + 3809900 * 2 ^ 59
def prefixEnd_3809900 : Nat := 4983230072969 + 3 ^ 40 * 3809900 * 2
def baseEnd_3809900 : Nat := 1304206630376499321619063

theorem tailTrace_3809900 : CollatzResearch.WordTrace tailWord_3809900 prefixEnd_3809900 1304206630376499321619063 := by
  unfold tailWord_3809900
  simp only [CollatzResearch.WordTrace]
  refine ⟨69479234448695226980949577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92638979264926969307932769 69479234448695226980949577)
  ·
    refine ⟨52109425836521420235712183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69479234448695226980949577 52109425836521420235712183)
    ·
      refine ⟨78164138754782130353568275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52109425836521420235712183 78164138754782130353568275)
      ·
        refine ⟨117246208132173195530352413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78164138754782130353568275 117246208132173195530352413)
        ·
          refine ⟨43967328049564948323882155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117246208132173195530352413 43967328049564948323882155)
          ·
            refine ⟨65950992074347422485823233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43967328049564948323882155 65950992074347422485823233)
            ·
              refine ⟨49463244055760566864367425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65950992074347422485823233 49463244055760566864367425)
              ·
                refine ⟨37097433041820425148275569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49463244055760566864367425 37097433041820425148275569)
                ·
                  refine ⟨27823074781365318861206677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37097433041820425148275569 27823074781365318861206677)
                  ·
                    refine ⟨1304206630376499321619063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27823074781365318861206677 1304206630376499321619063)
                    ·
                      rfl

theorem cell22_3809900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_3809900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809900 prefixEnd_3809900 := by exact prefixLift 3809900
  have htrace : WordTrace (prefixWord ++ tailWord_3809900) baseStart_3809900 baseEnd_3809900 := by
    simpa [prefixWord, tailWord_3809900, baseEnd_3809900] using wordTrace_append hprefix tailTrace_3809900
  have hstable : (prefixWord ++ tailWord_3809900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809900).length < 2 ^ (prefixWord ++ tailWord_3809900).sum := by decide
  have hdescent : baseEnd_3809900 < baseStart_3809900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809904 : List Nat := [2, 1, 1, 1, 7, 2, 2, 6]
def baseStart_3809904 : Nat := 118140960795 + 3809904 * 2 ^ 59
def prefixEnd_3809904 : Nat := 4983230072969 + 3 ^ 40 * 3809904 * 2
def baseEnd_3809904 : Nat := 144911999962027182724339

theorem tailTrace_3809904 : CollatzResearch.WordTrace tailWord_3809904 prefixEnd_3809904 144911999962027182724339 := by
  unfold tailWord_3809904
  simp only [CollatzResearch.WordTrace]
  refine ⟨69479307394687981322522383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92639076526250641763363177 69479307394687981322522383)
  ·
    refine ⟨104218961092031971983783575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69479307394687981322522383 104218961092031971983783575)
    ·
      refine ⟨156328441638047957975675363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104218961092031971983783575 156328441638047957975675363)
      ·
        refine ⟨234492662457071936963513045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156328441638047957975675363 234492662457071936963513045)
        ·
          refine ⟨5495921776337623522582337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 234492662457071936963513045 5495921776337623522582337)
          ·
            refine ⟨4121941332253217641936753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5495921776337623522582337 4121941332253217641936753)
            ·
              refine ⟨3091455999189913231452565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4121941332253217641936753 3091455999189913231452565)
              ·
                refine ⟨144911999962027182724339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3091455999189913231452565 144911999962027182724339)
                ·
                  rfl

theorem cell22_3809904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 6].length) (baseStart_3809904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809904 prefixEnd_3809904 := by exact prefixLift 3809904
  have htrace : WordTrace (prefixWord ++ tailWord_3809904) baseStart_3809904 baseEnd_3809904 := by
    simpa [prefixWord, tailWord_3809904, baseEnd_3809904] using wordTrace_append hprefix tailTrace_3809904
  have hstable : (prefixWord ++ tailWord_3809904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809904).length < 2 ^ (prefixWord ++ tailWord_3809904).sum := by decide
  have hdescent : baseEnd_3809904 < baseStart_3809904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809919 : List Nat := [1, 1, 2, 2, 1, 1, 1, 9, 1, 3]
def baseStart_3809919 : Nat := 118140960795 + 3809919 * 2 ^ 59
def prefixEnd_3809919 : Nat := 4983230072969 + 3 ^ 40 * 3809919 * 2
def baseEnd_3809919 : Nat := 1304213134464789605394005

theorem tailTrace_3809919 : CollatzResearch.WordTrace tailWord_3809919 prefixEnd_3809919 1304213134464789605394005 := by
  unfold tailWord_3809919
  simp only [CollatzResearch.WordTrace]
  refine ⟨138959161884321620206840811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92639441256214413471227207 138959161884321620206840811)
  ·
    refine ⟨208438742826482430310261217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138959161884321620206840811 208438742826482430310261217)
    ·
      refine ⟨156329057119861822732695913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208438742826482430310261217 156329057119861822732695913)
      ·
        refine ⟨117246792839896367049521935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156329057119861822732695913 117246792839896367049521935)
        ·
          refine ⟨175870189259844550574282903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117246792839896367049521935 175870189259844550574282903)
          ·
            refine ⟨263805283889766825861424355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175870189259844550574282903 263805283889766825861424355)
            ·
              refine ⟨395707925834650238792136533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263805283889766825861424355 395707925834650238792136533)
              ·
                refine ⟨2318601127937403742922675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 395707925834650238792136533 2318601127937403742922675)
                ·
                  refine ⟨3477901691906105614384013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2318601127937403742922675 3477901691906105614384013)
                  ·
                    refine ⟨1304213134464789605394005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3477901691906105614384013 1304213134464789605394005)
                    ·
                      rfl

theorem cell22_3809919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 9, 1, 3].length) (baseStart_3809919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809919 prefixEnd_3809919 := by exact prefixLift 3809919
  have htrace : WordTrace (prefixWord ++ tailWord_3809919) baseStart_3809919 baseEnd_3809919 := by
    simpa [prefixWord, tailWord_3809919, baseEnd_3809919] using wordTrace_append hprefix tailTrace_3809919
  have hstable : (prefixWord ++ tailWord_3809919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809919).length < 2 ^ (prefixWord ++ tailWord_3809919).sum := by decide
  have hdescent : baseEnd_3809919 < baseStart_3809919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3809949 : List Nat := [1, 4, 2, 1, 1, 1, 6, 1, 5]
def baseStart_3809949 : Nat := 118140960795 + 3809949 * 2 ^ 59
def prefixEnd_3809949 : Nat := 4983230072969 + 3 ^ 40 * 3809949 * 2
def baseEnd_3809949 : Nat := 434741134692626509047971

theorem tailTrace_3809949 : CollatzResearch.WordTrace tailWord_3809949 prefixEnd_3809949 434741134692626509047971 := by
  unfold tailWord_3809949
  simp only [CollatzResearch.WordTrace]
  refine ⟨138960256074212935330432901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92640170716141956886955267 138960256074212935330432901)
  ·
    refine ⟨26055048013914925374456169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138960256074212935330432901 26055048013914925374456169)
    ·
      refine ⟨19541286010436194030842127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26055048013914925374456169 19541286010436194030842127)
      ·
        refine ⟨29311929015654291046263191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19541286010436194030842127 29311929015654291046263191)
        ·
          refine ⟨43967893523481436569394787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29311929015654291046263191 43967893523481436569394787)
          ·
            refine ⟨65951840285222154854092181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43967893523481436569394787 65951840285222154854092181)
            ·
              refine ⟨3091492513369788508785571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 65951840285222154854092181 3091492513369788508785571)
              ·
                refine ⟨4637238770054682763178357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3091492513369788508785571 4637238770054682763178357)
                ·
                  refine ⟨434741134692626509047971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4637238770054682763178357 434741134692626509047971)
                  ·
                    rfl

theorem cell22_3809949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_3809949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3809949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3809949 prefixEnd_3809949 := by exact prefixLift 3809949
  have htrace : WordTrace (prefixWord ++ tailWord_3809949) baseStart_3809949 baseEnd_3809949 := by
    simpa [prefixWord, tailWord_3809949, baseEnd_3809949] using wordTrace_append hprefix tailTrace_3809949
  have hstable : (prefixWord ++ tailWord_3809949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3809949).length < 2 ^ (prefixWord ++ tailWord_3809949).sum := by decide
  have hdescent : baseEnd_3809949 < baseStart_3809949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3809949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810009 : List Nat := [1, 2, 1, 2, 3, 2, 1, 5, 2, 3]
def baseStart_3810009 : Nat := 118140960795 + 3810009 * 2 ^ 59
def prefixEnd_3810009 : Nat := 4983230072969 + 3 ^ 40 * 3810009 * 2
def baseEnd_3810009 : Nat := 1304243943304059370643729

theorem tailTrace_3810009 : CollatzResearch.WordTrace tailWord_3810009 prefixEnd_3810009 1304243943304059370643729 := by
  unfold tailWord_3810009
  simp only [CollatzResearch.WordTrace]
  refine ⟨138962444453995565577617081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92641629635997043718411387 138962444453995565577617081)
  ·
    refine ⟨104221833340496674183212811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138962444453995565577617081 104221833340496674183212811)
    ·
      refine ⟨156332750010745011274819217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104221833340496674183212811 156332750010745011274819217)
      ·
        refine ⟨117249562508058758456114413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156332750010745011274819217 117249562508058758456114413)
        ·
          refine ⟨43968585940522034421042905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117249562508058758456114413 43968585940522034421042905)
          ·
            refine ⟨32976439455391525815782179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43968585940522034421042905 32976439455391525815782179)
            ·
              refine ⟨49464659183087288723673269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32976439455391525815782179 49464659183087288723673269)
              ·
                refine ⟨4637311798414433317844369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49464659183087288723673269 4637311798414433317844369)
                ·
                  refine ⟨3477983848810824988383277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4637311798414433317844369 3477983848810824988383277)
                  ·
                    refine ⟨1304243943304059370643729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3477983848810824988383277 1304243943304059370643729)
                    ·
                      rfl

theorem cell22_3810009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 2, 3].length) (baseStart_3810009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3810009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3810009 prefixEnd_3810009 := by exact prefixLift 3810009
  have htrace : WordTrace (prefixWord ++ tailWord_3810009) baseStart_3810009 baseEnd_3810009 := by
    simpa [prefixWord, tailWord_3810009, baseEnd_3810009] using wordTrace_append hprefix tailTrace_3810009
  have hstable : (prefixWord ++ tailWord_3810009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810009).length < 2 ^ (prefixWord ++ tailWord_3810009).sum := by decide
  have hdescent : baseEnd_3810009 < baseStart_3810009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810024 : List Nat := [2, 1, 4, 1, 4, 1, 1, 1, 1, 6]
def baseStart_3810024 : Nat := 118140960795 + 3810024 * 2 ^ 59
def prefixEnd_3810024 : Nat := 4983230072969 + 3 ^ 40 * 3810024 * 2
def baseEnd_3810024 : Nat := 1304249078110604331518683

theorem tailTrace_3810024 : CollatzResearch.WordTrace tailWord_3810024 prefixEnd_3810024 1304249078110604331518683 := by
  unfold tailWord_3810024
  simp only [CollatzResearch.WordTrace]
  refine ⟨69481495774470611569706563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92641994365960815426275417 69481495774470611569706563)
  ·
    refine ⟨104222243661705917354559845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69481495774470611569706563 104222243661705917354559845)
    ·
      refine ⟨19541670686569859503979971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104222243661705917354559845 19541670686569859503979971)
      ·
        refine ⟨29312506029854789255969957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19541670686569859503979971 29312506029854789255969957)
        ·
          refine ⟨5496094880597772985494367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29312506029854789255969957 5496094880597772985494367)
          ·
            refine ⟨8244142320896659478241551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5496094880597772985494367 8244142320896659478241551)
            ·
              refine ⟨12366213481344989217362327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8244142320896659478241551 12366213481344989217362327)
              ·
                refine ⟨18549320222017483826043491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12366213481344989217362327 18549320222017483826043491)
                ·
                  refine ⟨27823980333026225739065237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18549320222017483826043491 27823980333026225739065237)
                  ·
                    refine ⟨1304249078110604331518683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27823980333026225739065237 1304249078110604331518683)
                    ·
                      rfl

theorem cell22_3810024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_3810024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3810024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3810024 prefixEnd_3810024 := by exact prefixLift 3810024
  have htrace : WordTrace (prefixWord ++ tailWord_3810024) baseStart_3810024 baseEnd_3810024 := by
    simpa [prefixWord, tailWord_3810024, baseEnd_3810024] using wordTrace_append hprefix tailTrace_3810024
  have hstable : (prefixWord ++ tailWord_3810024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810024).length < 2 ^ (prefixWord ++ tailWord_3810024).sum := by decide
  have hdescent : baseEnd_3810024 < baseStart_3810024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810127 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 7, 5]
def baseStart_3810127 : Nat := 118140960795 + 3810127 * 2 ^ 59
def prefixEnd_3810127 : Nat := 4983230072969 + 3 ^ 40 * 3810127 * 2
def baseEnd_3810127 : Nat := 1304284337115546396193367

theorem tailTrace_3810127 : CollatzResearch.WordTrace tailWord_3810127 prefixEnd_3810127 1304284337115546396193367 := by
  unfold tailWord_3810127
  simp only [CollatzResearch.WordTrace]
  refine ⟨138966748267568071730412635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92644498845045381153608423 138966748267568071730412635)
  ·
    refine ⟨208450122401352107595618953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138966748267568071730412635 208450122401352107595618953)
    ·
      refine ⟨156337591801014080696714215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208450122401352107595618953 156337591801014080696714215)
      ·
        refine ⟨234506387701521121045071323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156337591801014080696714215 234506387701521121045071323)
        ·
          refine ⟨351759581552281681567606985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234506387701521121045071323 351759581552281681567606985)
          ·
            refine ⟨263819686164211261175705239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351759581552281681567606985 263819686164211261175705239)
            ·
              refine ⟨395729529246316891763557859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263819686164211261175705239 395729529246316891763557859)
              ·
                refine ⟨593594293869475337645336789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395729529246316891763557859 593594293869475337645336789)
                ·
                  refine ⟨13912366262565828226062581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 593594293869475337645336789 13912366262565828226062581)
                  ·
                    refine ⟨1304284337115546396193367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13912366262565828226062581 1304284337115546396193367)
                    ·
                      rfl

theorem cell22_3810127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 5].length) (baseStart_3810127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3810127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3810127 prefixEnd_3810127 := by exact prefixLift 3810127
  have htrace : WordTrace (prefixWord ++ tailWord_3810127) baseStart_3810127 baseEnd_3810127 := by
    simpa [prefixWord, tailWord_3810127, baseEnd_3810127] using wordTrace_append hprefix tailTrace_3810127
  have hstable : (prefixWord ++ tailWord_3810127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810127).length < 2 ^ (prefixWord ++ tailWord_3810127).sum := by decide
  have hdescent : baseEnd_3810127 < baseStart_3810127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810144 : List Nat := [2, 1, 1, 3, 3, 1, 3, 2, 1, 5]
def baseStart_3810144 : Nat := 118140960795 + 3810144 * 2 ^ 59
def prefixEnd_3810144 : Nat := 4983230072969 + 3 ^ 40 * 3810144 * 2
def baseEnd_3810144 : Nat := 1304290156562964018518315

theorem tailTrace_3810144 : CollatzResearch.WordTrace tailWord_3810144 prefixEnd_3810144 1304290156562964018518315 := by
  unfold tailWord_3810144
  simp only [CollatzResearch.WordTrace]
  refine ⟨69483684154253241816890743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92644912205670989089187657 69483684154253241816890743)
  ·
    refine ⟨104225526231379862725336115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69483684154253241816890743 104225526231379862725336115)
    ·
      refine ⟨156338289347069794088004173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104225526231379862725336115 156338289347069794088004173)
      ·
        refine ⟨58626858505151172783001565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156338289347069794088004173 58626858505151172783001565)
        ·
          refine ⟨21985071939431689793625587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58626858505151172783001565 21985071939431689793625587)
          ·
            refine ⟨32977607909147534690438381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21985071939431689793625587 32977607909147534690438381)
            ·
              refine ⟨12366602965930325508914393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32977607909147534690438381 12366602965930325508914393)
              ·
                refine ⟨9274952224447744131685795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12366602965930325508914393 9274952224447744131685795)
                ·
                  refine ⟨13912428336671616197528693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9274952224447744131685795 13912428336671616197528693)
                  ·
                    refine ⟨1304290156562964018518315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13912428336671616197528693 1304290156562964018518315)
                    ·
                      rfl

theorem cell22_3810144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 1, 5].length) (baseStart_3810144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3810144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3810144 prefixEnd_3810144 := by exact prefixLift 3810144
  have htrace : WordTrace (prefixWord ++ tailWord_3810144) baseStart_3810144 baseEnd_3810144 := by
    simpa [prefixWord, tailWord_3810144, baseEnd_3810144] using wordTrace_append hprefix tailTrace_3810144
  have hstable : (prefixWord ++ tailWord_3810144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810144).length < 2 ^ (prefixWord ++ tailWord_3810144).sum := by decide
  have hdescent : baseEnd_3810144 < baseStart_3810144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810148 : List Nat := [2, 3, 1, 1, 4, 2, 3, 1, 1, 4]
def baseStart_3810148 : Nat := 118140960795 + 3810148 * 2 ^ 59
def prefixEnd_3810148 : Nat := 4983230072969 + 3 ^ 40 * 3810148 * 2
def baseEnd_3810148 : Nat := 1304291525844709341418303

theorem tailTrace_3810148 : CollatzResearch.WordTrace tailWord_3810148 prefixEnd_3810148 1304291525844709341418303 := by
  unfold tailWord_3810148
  simp only [CollatzResearch.WordTrace]
  refine ⟨69483757100245996158463549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92645009466994661544618065 69483757100245996158463549)
  ·
    refine ⟨26056408912592248559423831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69483757100245996158463549 26056408912592248559423831)
    ·
      refine ⟨39084613368888372839135747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26056408912592248559423831 39084613368888372839135747)
      ·
        refine ⟨58626920053332559258703621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39084613368888372839135747 58626920053332559258703621)
        ·
          refine ⟨10992547509999854861006929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58626920053332559258703621 10992547509999854861006929)
          ·
            refine ⟨8244410632499891145755197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10992547509999854861006929 8244410632499891145755197)
            ·
              refine ⟨3091653987187459179658199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8244410632499891145755197 3091653987187459179658199)
              ·
                refine ⟨4637480980781188769487299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3091653987187459179658199 4637480980781188769487299)
                ·
                  refine ⟨6956221471171783154230949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4637480980781188769487299 6956221471171783154230949)
                  ·
                    refine ⟨1304291525844709341418303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6956221471171783154230949 1304291525844709341418303)
                    ·
                      rfl

theorem cell22_3810148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 1, 4].length) (baseStart_3810148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3810148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3810148 prefixEnd_3810148 := by exact prefixLift 3810148
  have htrace : WordTrace (prefixWord ++ tailWord_3810148) baseStart_3810148 baseEnd_3810148 := by
    simpa [prefixWord, tailWord_3810148, baseEnd_3810148] using wordTrace_append hprefix tailTrace_3810148
  have hstable : (prefixWord ++ tailWord_3810148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810148).length < 2 ^ (prefixWord ++ tailWord_3810148).sum := by decide
  have hdescent : baseEnd_3810148 < baseStart_3810148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810161 : List Nat := [1, 2, 2, 2, 1, 4, 1, 4, 2, 3]
def baseStart_3810161 : Nat := 118140960795 + 3810161 * 2 ^ 59
def prefixEnd_3810161 : Nat := 4983230072969 + 3 ^ 40 * 3810161 * 2
def baseEnd_3810161 : Nat := 1304295976010381640843263

theorem tailTrace_3810161 : CollatzResearch.WordTrace tailWord_3810161 prefixEnd_3810161 1304295976010381640843263 := by
  unfold tailWord_3810161
  simp only [CollatzResearch.WordTrace]
  refine ⟨138967988349444895537150337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92645325566296597024766891 138967988349444895537150337)
  ·
    refine ⟨104225991262083671652862753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138967988349444895537150337 104225991262083671652862753)
    ·
      refine ⟨78169493446562753739647065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104225991262083671652862753 78169493446562753739647065)
      ·
        refine ⟨58627120084922065304735299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78169493446562753739647065 58627120084922065304735299)
        ·
          refine ⟨87940680127383097957102949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58627120084922065304735299 87940680127383097957102949)
          ·
            refine ⟨16488877523884330866956803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87940680127383097957102949 16488877523884330866956803)
            ·
              refine ⟨24733316285826496300435205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16488877523884330866956803 24733316285826496300435205)
              ·
                refine ⟨4637496803592468056331601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24733316285826496300435205 4637496803592468056331601)
                ·
                  refine ⟨3478122602694351042248701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4637496803592468056331601 3478122602694351042248701)
                  ·
                    refine ⟨1304295976010381640843263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3478122602694351042248701 1304295976010381640843263)
                    ·
                      rfl

theorem cell22_3810161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 2, 3].length) (baseStart_3810161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3810161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3810161 prefixEnd_3810161 := by exact prefixLift 3810161
  have htrace : WordTrace (prefixWord ++ tailWord_3810161) baseStart_3810161 baseEnd_3810161 := by
    simpa [prefixWord, tailWord_3810161, baseEnd_3810161] using wordTrace_append hprefix tailTrace_3810161
  have hstable : (prefixWord ++ tailWord_3810161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810161).length < 2 ^ (prefixWord ++ tailWord_3810161).sum := by decide
  have hdescent : baseEnd_3810161 < baseStart_3810161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810234 : List Nat := [3, 1, 1, 1, 2, 1, 3, 3, 2, 5]
def baseStart_3810234 : Nat := 118140960795 + 3810234 * 2 ^ 59
def prefixEnd_3810234 : Nat := 4983230072969 + 3 ^ 40 * 3810234 * 2
def baseEnd_3810234 : Nat := 1304320965402233783768039

theorem tailTrace_3810234 : CollatzResearch.WordTrace tailWord_3810234 prefixEnd_3810234 1304320965402233783768039 := by
  unfold tailWord_3810234
  simp only [CollatzResearch.WordTrace]
  refine ⟨34742662719545107251139439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92647100585453619336371837 34742662719545107251139439)
  ·
    refine ⟨52113994079317660876709159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34742662719545107251139439 52113994079317660876709159)
    ·
      refine ⟨78170991118976491315063739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52113994079317660876709159 78170991118976491315063739)
      ·
        refine ⟨117256486678464736972595609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78170991118976491315063739 117256486678464736972595609)
        ·
          refine ⟨87942365008848552729446707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117256486678464736972595609 87942365008848552729446707)
          ·
            refine ⟨131913547513272829094170061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87942365008848552729446707 131913547513272829094170061)
            ·
              refine ⟨49467580317477310910313773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131913547513272829094170061 49467580317477310910313773)
              ·
                refine ⟨18550342619053991591367665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49467580317477310910313773 18550342619053991591367665)
                ·
                  refine ⟨13912756964290493693525749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18550342619053991591367665 13912756964290493693525749)
                  ·
                    refine ⟨1304320965402233783768039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13912756964290493693525749 1304320965402233783768039)
                    ·
                      rfl

theorem cell22_3810234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_3810234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3810234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3810234 prefixEnd_3810234 := by exact prefixLift 3810234
  have htrace : WordTrace (prefixWord ++ tailWord_3810234) baseStart_3810234 baseEnd_3810234 := by
    simpa [prefixWord, tailWord_3810234, baseEnd_3810234] using wordTrace_append hprefix tailTrace_3810234
  have hstable : (prefixWord ++ tailWord_3810234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810234).length < 2 ^ (prefixWord ++ tailWord_3810234).sum := by decide
  have hdescent : baseEnd_3810234 < baseStart_3810234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810274 : List Nat := [3, 3, 3, 1, 1, 2, 3, 2, 1, 3]
def baseStart_3810274 : Nat := 118140960795 + 3810274 * 2 ^ 59
def prefixEnd_3810274 : Nat := 4983230072969 + 3 ^ 40 * 3810274 * 2
def baseEnd_3810274 : Nat := 1304334658219687012767917

theorem tailTrace_3810274 : CollatzResearch.WordTrace tailWord_3810274 prefixEnd_3810274 1304334658219687012767917 := by
  unfold tailWord_3810274
  simp only [CollatzResearch.WordTrace]
  refine ⟨34743027449508878959003469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92648073198690343890675917 34743027449508878959003469)
  ·
    refine ⟨13028635293565829609626301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34743027449508878959003469 13028635293565829609626301)
    ·
      refine ⟨4885738235087186103609863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13028635293565829609626301 4885738235087186103609863)
      ·
        refine ⟨7328607352630779155414795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4885738235087186103609863 7328607352630779155414795)
        ·
          refine ⟨10992911028946168733122193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7328607352630779155414795 10992911028946168733122193)
          ·
            refine ⟨8244683271709626549841645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10992911028946168733122193 8244683271709626549841645)
            ·
              refine ⟨3091756226891109956190617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8244683271709626549841645 3091756226891109956190617)
              ·
                refine ⟨2318817170168332467142963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3091756226891109956190617 2318817170168332467142963)
                ·
                  refine ⟨3478225755252498700714445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2318817170168332467142963 3478225755252498700714445)
                  ·
                    refine ⟨1304334658219687012767917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3478225755252498700714445 1304334658219687012767917)
                    ·
                      rfl

theorem cell22_3810274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_3810274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3810274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3810274 prefixEnd_3810274 := by exact prefixLift 3810274
  have htrace : WordTrace (prefixWord ++ tailWord_3810274) baseStart_3810274 baseEnd_3810274 := by
    simpa [prefixWord, tailWord_3810274, baseEnd_3810274] using wordTrace_append hprefix tailTrace_3810274
  have hstable : (prefixWord ++ tailWord_3810274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810274).length < 2 ^ (prefixWord ++ tailWord_3810274).sum := by decide
  have hdescent : baseEnd_3810274 < baseStart_3810274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810309 : List Nat := [1, 3, 1, 1, 2, 3, 1, 10]
def baseStart_3810309 : Nat := 118140960795 + 3810309 * 2 ^ 59
def prefixEnd_3810309 : Nat := 4983230072969 + 3 ^ 40 * 3810309 * 2
def baseEnd_3810309 : Nat := 144927404381662065349201

theorem tailTrace_3810309 : CollatzResearch.WordTrace tailWord_3810309 prefixEnd_3810309 144927404381662065349201 := by
  unfold tailWord_3810309
  simp only [CollatzResearch.WordTrace]
  refine ⟨138973386352908716813537981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92648924235272477875691987 138973386352908716813537981)
  ·
    refine ⟨52115019882340768805076743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138973386352908716813537981 52115019882340768805076743)
    ·
      refine ⟨78172529823511153207615115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52115019882340768805076743 78172529823511153207615115)
      ·
        refine ⟨117258794735266729811422673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78172529823511153207615115 117258794735266729811422673)
        ·
          refine ⟨87944096051450047358567005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117258794735266729811422673 87944096051450047358567005)
          ·
            refine ⟨32979036019293767759462627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87944096051450047358567005 32979036019293767759462627)
            ·
              refine ⟨49468554028940651639193941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32979036019293767759462627 49468554028940651639193941)
              ·
                refine ⟨144927404381662065349201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49468554028940651639193941 144927404381662065349201)
                ·
                  rfl

theorem cell22_3810309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 10].length) (baseStart_3810309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3810309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3810309 prefixEnd_3810309 := by exact prefixLift 3810309
  have htrace : WordTrace (prefixWord ++ tailWord_3810309) baseStart_3810309 baseEnd_3810309 := by
    simpa [prefixWord, tailWord_3810309, baseEnd_3810309] using wordTrace_append hprefix tailTrace_3810309
  have hstable : (prefixWord ++ tailWord_3810309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810309).length < 2 ^ (prefixWord ++ tailWord_3810309).sum := by decide
  have hdescent : baseEnd_3810309 < baseStart_3810309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810332 : List Nat := [2, 2, 3, 1, 4, 2, 2, 2, 4]
def baseStart_3810332 : Nat := 118140960795 + 3810332 * 2 ^ 59
def prefixEnd_3810332 : Nat := 4983230072969 + 3 ^ 40 * 3810332 * 2
def baseEnd_3810332 : Nat := 434784837601664731605913

theorem tailTrace_3810332 : CollatzResearch.WordTrace tailWord_3810332 prefixEnd_3810332 434784837601664731605913 := by
  unfold tailWord_3810332
  simp only [CollatzResearch.WordTrace]
  refine ⟨69487112615912695870812625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92649483487883594494416833 69487112615912695870812625)
  ·
    refine ⟨52115334461934521903109469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69487112615912695870812625 52115334461934521903109469)
    ·
      refine ⟨19543250423225445713666051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52115334461934521903109469 19543250423225445713666051)
      ·
        refine ⟨29314875634838168570499077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19543250423225445713666051 29314875634838168570499077)
        ·
          refine ⟨5496539181532156606968577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29314875634838168570499077 5496539181532156606968577)
          ·
            refine ⟨4122404386149117455226433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5496539181532156606968577 4122404386149117455226433)
            ·
              refine ⟨3091803289611838091419825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4122404386149117455226433 3091803289611838091419825)
              ·
                refine ⟨2318852467208878568564869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3091803289611838091419825 2318852467208878568564869)
                ·
                  refine ⟨434784837601664731605913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2318852467208878568564869 434784837601664731605913)
                  ·
                    rfl

theorem cell22_3810332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 2, 4].length) (baseStart_3810332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3810332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3810332 prefixEnd_3810332 := by exact prefixLift 3810332
  have htrace : WordTrace (prefixWord ++ tailWord_3810332) baseStart_3810332 baseEnd_3810332 := by
    simpa [prefixWord, tailWord_3810332, baseEnd_3810332] using wordTrace_append hprefix tailTrace_3810332
  have hstable : (prefixWord ++ tailWord_3810332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810332).length < 2 ^ (prefixWord ++ tailWord_3810332).sum := by decide
  have hdescent : baseEnd_3810332 < baseStart_3810332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810343 : List Nat := [1, 1, 7, 1, 1, 1, 3, 7]
def baseStart_3810343 : Nat := 118140960795 + 3810343 * 2 ^ 59
def prefixEnd_3810343 : Nat := 4983230072969 + 3 ^ 40 * 3810343 * 2
def baseEnd_3810343 : Nat := 144928697592199314754745

theorem tailTrace_3810343 : CollatzResearch.WordTrace tailWord_3810343 prefixEnd_3810343 144928697592199314754745 := by
  unfold tailWord_3810343
  simp only [CollatzResearch.WordTrace]
  refine ⟨138974626434785540620275683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92649750956523693746850455 138974626434785540620275683)
  ·
    refine ⟨208461939652178310930413525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138974626434785540620275683 208461939652178310930413525)
    ·
      refine ⟨4885826710597929162431567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 208461939652178310930413525 4885826710597929162431567)
      ·
        refine ⟨7328740065896893743647351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4885826710597929162431567 7328740065896893743647351)
        ·
          refine ⟨10993110098845340615471027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7328740065896893743647351 10993110098845340615471027)
          ·
            refine ⟨16489665148268010923206541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10993110098845340615471027 16489665148268010923206541)
            ·
              refine ⟨6183624430600504096202453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16489665148268010923206541 6183624430600504096202453)
              ·
                refine ⟨144928697592199314754745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6183624430600504096202453 144928697592199314754745)
                ·
                  rfl

theorem cell22_3810343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 7].length) (baseStart_3810343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3810343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3810343 prefixEnd_3810343 := by exact prefixLift 3810343
  have htrace : WordTrace (prefixWord ++ tailWord_3810343) baseStart_3810343 baseEnd_3810343 := by
    simpa [prefixWord, tailWord_3810343, baseEnd_3810343] using wordTrace_append hprefix tailTrace_3810343
  have hstable : (prefixWord ++ tailWord_3810343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810343).length < 2 ^ (prefixWord ++ tailWord_3810343).sum := by decide
  have hdescent : baseEnd_3810343 < baseStart_3810343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810375 : List Nat := [1, 1, 4, 1, 3, 2, 1, 5, 1, 3]
def baseStart_3810375 : Nat := 118140960795 + 3810375 * 2 ^ 59
def prefixEnd_3810375 : Nat := 4983230072969 + 3 ^ 40 * 3810375 * 2
def baseEnd_3810375 : Nat := 1304369232583756415992607

theorem tailTrace_3810375 : CollatzResearch.WordTrace tailWord_3810375 prefixEnd_3810375 1304369232583756415992607 := by
  unfold tailWord_3810375
  simp only [CollatzResearch.WordTrace]
  refine ⟨138975793570669610085440579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92650529047113073390293719 138975793570669610085440579)
  ·
    refine ⟨208463690356004415128160869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138975793570669610085440579 208463690356004415128160869)
    ·
      refine ⟨39086941941750827836530163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208463690356004415128160869 39086941941750827836530163)
      ·
        refine ⟨58630412912626241754795245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39086941941750827836530163 58630412912626241754795245)
        ·
          refine ⟨21986404842234840658048217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58630412912626241754795245 21986404842234840658048217)
          ·
            refine ⟨16489803631676130493536163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21986404842234840658048217 16489803631676130493536163)
            ·
              refine ⟨24734705447514195740304245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16489803631676130493536163 24734705447514195740304245)
              ·
                refine ⟨2318878635704455850653523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24734705447514195740304245 2318878635704455850653523)
                ·
                  refine ⟨3478317953556683775980285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2318878635704455850653523 3478317953556683775980285)
                  ·
                    refine ⟨1304369232583756415992607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3478317953556683775980285 1304369232583756415992607)
                    ·
                      rfl

theorem cell22_3810375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 5, 1, 3].length) (baseStart_3810375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3810375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3810375 prefixEnd_3810375 := by exact prefixLift 3810375
  have htrace : WordTrace (prefixWord ++ tailWord_3810375) baseStart_3810375 baseEnd_3810375 := by
    simpa [prefixWord, tailWord_3810375, baseEnd_3810375] using wordTrace_append hprefix tailTrace_3810375
  have hstable : (prefixWord ++ tailWord_3810375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810375).length < 2 ^ (prefixWord ++ tailWord_3810375).sum := by decide
  have hdescent : baseEnd_3810375 < baseStart_3810375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810388 : List Nat := [2, 4, 1, 1, 1, 1, 5, 2, 5]
def baseStart_3810388 : Nat := 118140960795 + 3810388 * 2 ^ 59
def prefixEnd_3810388 : Nat := 4983230072969 + 3 ^ 40 * 3810388 * 2
def baseEnd_3810388 : Nat := 434791227583142905139189

theorem tailTrace_3810388 : CollatzResearch.WordTrace tailWord_3810388 prefixEnd_3810388 434791227583142905139189 := by
  unfold tailWord_3810388
  simp only [CollatzResearch.WordTrace]
  refine ⟨69488133859811256652831909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92650845146415008870442545 69488133859811256652831909)
  ·
    refine ⟨13029025098714610622405983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69488133859811256652831909 13029025098714610622405983)
    ·
      refine ⟨19543537648071915933608975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13029025098714610622405983 19543537648071915933608975)
      ·
        refine ⟨29315306472107873900413463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19543537648071915933608975 29315306472107873900413463)
        ·
          refine ⟨43972959708161810850620195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29315306472107873900413463 43972959708161810850620195)
          ·
            refine ⟨65959439562242716275930293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43972959708161810850620195 65959439562242716275930293)
            ·
              refine ⟨6183697458960254650868465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65959439562242716275930293 6183697458960254650868465)
              ·
                refine ⟨4637773094220190988151349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6183697458960254650868465 4637773094220190988151349)
                ·
                  refine ⟨434791227583142905139189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4637773094220190988151349 434791227583142905139189)
                  ·
                    rfl

theorem cell22_3810388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_3810388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3810388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3810388 prefixEnd_3810388 := by exact prefixLift 3810388
  have htrace : WordTrace (prefixWord ++ tailWord_3810388) baseStart_3810388 baseEnd_3810388 := by
    simpa [prefixWord, tailWord_3810388, baseEnd_3810388] using wordTrace_append hprefix tailTrace_3810388
  have hstable : (prefixWord ++ tailWord_3810388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810388).length < 2 ^ (prefixWord ++ tailWord_3810388).sum := by decide
  have hdescent : baseEnd_3810388 < baseStart_3810388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810401 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 5, 4]
def baseStart_3810401 : Nat := 118140960795 + 3810401 * 2 ^ 59
def prefixEnd_3810401 : Nat := 4983230072969 + 3 ^ 40 * 3810401 * 2
def baseEnd_3810401 : Nat := 1304378132915101014842527

theorem tailTrace_3810401 : CollatzResearch.WordTrace tailWord_3810401 prefixEnd_3810401 1304378132915101014842527 := by
  unfold tailWord_3810401
  simp only [CollatzResearch.WordTrace]
  refine ⟨138976741868575416525887057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92651161245716944350591371 138976741868575416525887057)
  ·
    refine ⟨104232556401431562394415293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138976741868575416525887057 104232556401431562394415293)
    ·
      refine ⟨39087208650536835897905735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104232556401431562394415293 39087208650536835897905735)
      ·
        refine ⟨58630812975805253846858603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39087208650536835897905735 58630812975805253846858603)
        ·
          refine ⟨87946219463707880770287905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58630812975805253846858603 87946219463707880770287905)
          ·
            refine ⟨65959664597780910577715929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87946219463707880770287905 65959664597780910577715929)
            ·
              refine ⟨49469748448335682933286947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65959664597780910577715929 49469748448335682933286947)
              ·
                refine ⟨74204622672503524399930421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49469748448335682933286947 74204622672503524399930421)
                ·
                  refine ⟨6956683375547205412493477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74204622672503524399930421 6956683375547205412493477)
                  ·
                    refine ⟨1304378132915101014842527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6956683375547205412493477 1304378132915101014842527)
                    ·
                      rfl

theorem cell22_3810401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_3810401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3810401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3810401 prefixEnd_3810401 := by exact prefixLift 3810401
  have htrace : WordTrace (prefixWord ++ tailWord_3810401) baseStart_3810401 baseEnd_3810401 := by
    simpa [prefixWord, tailWord_3810401, baseEnd_3810401] using wordTrace_append hprefix tailTrace_3810401
  have hstable : (prefixWord ++ tailWord_3810401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810401).length < 2 ^ (prefixWord ++ tailWord_3810401).sum := by decide
  have hdescent : baseEnd_3810401 < baseStart_3810401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810416 : List Nat := [2, 1, 1, 1, 5, 1, 1, 4, 6]
def baseStart_3810416 : Nat := 118140960795 + 3810416 * 2 ^ 59
def prefixEnd_3810416 : Nat := 4983230072969 + 3 ^ 40 * 3810416 * 2
def baseEnd_3810416 : Nat := 434794422573881991905827

theorem tailTrace_3810416 : CollatzResearch.WordTrace tailWord_3810416 prefixEnd_3810416 434794422573881991905827 := by
  unfold tailWord_3810416
  simp only [CollatzResearch.WordTrace]
  refine ⟨69488644481760537043841551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92651525975680716058455401 69488644481760537043841551)
  ·
    refine ⟨104232966722640805565762327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69488644481760537043841551 104232966722640805565762327)
    ·
      refine ⟨156349450083961208348643491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104232966722640805565762327 156349450083961208348643491)
      ·
        refine ⟨234524175125941812522965237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156349450083961208348643491 234524175125941812522965237)
        ·
          refine ⟨21986641418057044924027991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 234524175125941812522965237 21986641418057044924027991)
          ·
            refine ⟨32979962127085567386041987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21986641418057044924027991 32979962127085567386041987)
            ·
              refine ⟨49469943190628351079062981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32979962127085567386041987 49469943190628351079062981)
              ·
                refine ⟨9275614348242815827324309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49469943190628351079062981 9275614348242815827324309)
                ·
                  refine ⟨434794422573881991905827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9275614348242815827324309 434794422573881991905827)
                  ·
                    rfl

theorem cell22_3810416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 6].length) (baseStart_3810416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3810416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3810416 prefixEnd_3810416 := by exact prefixLift 3810416
  have htrace : WordTrace (prefixWord ++ tailWord_3810416) baseStart_3810416 baseEnd_3810416 := by
    simpa [prefixWord, tailWord_3810416, baseEnd_3810416] using wordTrace_append hprefix tailTrace_3810416
  have hstable : (prefixWord ++ tailWord_3810416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810416).length < 2 ^ (prefixWord ++ tailWord_3810416).sum := by decide
  have hdescent : baseEnd_3810416 < baseStart_3810416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810450 : List Nat := [3, 2, 3, 1, 1, 4, 1, 1, 6]
def baseStart_3810450 : Nat := 118140960795 + 3810450 * 2 ^ 59
def prefixEnd_3810450 : Nat := 4983230072969 + 3 ^ 40 * 3810450 * 2
def baseEnd_3810450 : Nat := 434798302205493740122459

theorem tailTrace_3810450 : CollatzResearch.WordTrace tailWord_3810450 prefixEnd_3810450 434798302205493740122459 := by
  unfold tailWord_3810450
  simp only [CollatzResearch.WordTrace]
  refine ⟨34744632261349474473605201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92652352696931931929613869 34744632261349474473605201)
  ·
    refine ⟨26058474196012105855203901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34744632261349474473605201 26058474196012105855203901)
    ·
      refine ⟨9771927823504539695701463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26058474196012105855203901 9771927823504539695701463)
      ·
        refine ⟨14657891735256809543552195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9771927823504539695701463 14657891735256809543552195)
        ·
          refine ⟨21986837602885214315328293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14657891735256809543552195 21986837602885214315328293)
          ·
            refine ⟨4122532050540977684124055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21986837602885214315328293 4122532050540977684124055)
            ·
              refine ⟨6183798075811466526186083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4122532050540977684124055 6183798075811466526186083)
              ·
                refine ⟨9275697113717199789279125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6183798075811466526186083 9275697113717199789279125)
                ·
                  refine ⟨434798302205493740122459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9275697113717199789279125 434798302205493740122459)
                  ·
                    rfl

theorem cell22_3810450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_3810450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3810450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3810450 prefixEnd_3810450 := by exact prefixLift 3810450
  have htrace : WordTrace (prefixWord ++ tailWord_3810450) baseStart_3810450 baseEnd_3810450 := by
    simpa [prefixWord, tailWord_3810450, baseEnd_3810450] using wordTrace_append hprefix tailTrace_3810450
  have hstable : (prefixWord ++ tailWord_3810450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810450).length < 2 ^ (prefixWord ++ tailWord_3810450).sum := by decide
  have hdescent : baseEnd_3810450 < baseStart_3810450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810465 : List Nat := [1, 2, 3, 3, 1, 1, 3, 3, 2, 3]
def baseStart_3810465 : Nat := 118140960795 + 3810465 * 2 ^ 59
def prefixEnd_3810465 : Nat := 4983230072969 + 3 ^ 40 * 3810465 * 2
def baseEnd_3810465 : Nat := 1304400041423026181242331

theorem tailTrace_3810465 : CollatzResearch.WordTrace tailWord_3810465 prefixEnd_3810465 1304400041423026181242331 := by
  unfold tailWord_3810465
  simp only [CollatzResearch.WordTrace]
  refine ⟨138979076140343555456216849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92652717426895703637477899 138979076140343555456216849)
  ·
    refine ⟨104234307105257666592162637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138979076140343555456216849 104234307105257666592162637)
    ·
      refine ⟨39087865164471624972060989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104234307105257666592162637 39087865164471624972060989)
      ·
        refine ⟨14657949436676859364522871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39087865164471624972060989 14657949436676859364522871)
        ·
          refine ⟨21986924155015289046784307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14657949436676859364522871 21986924155015289046784307)
          ·
            refine ⟨32980386232522933570176461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21986924155015289046784307 32980386232522933570176461)
            ·
              refine ⟨12367644837196100088816173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32980386232522933570176461 12367644837196100088816173)
              ·
                refine ⟨4637866813948537533306065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12367644837196100088816173 4637866813948537533306065)
                ·
                  refine ⟨3478400110461403149979549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4637866813948537533306065 3478400110461403149979549)
                  ·
                    refine ⟨1304400041423026181242331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3478400110461403149979549 1304400041423026181242331)
                    ·
                      rfl

theorem cell22_3810465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_3810465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3810465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3810465 prefixEnd_3810465 := by exact prefixLift 3810465
  have htrace : WordTrace (prefixWord ++ tailWord_3810465) baseStart_3810465 baseEnd_3810465 := by
    simpa [prefixWord, tailWord_3810465, baseEnd_3810465] using wordTrace_append hprefix tailTrace_3810465
  have hstable : (prefixWord ++ tailWord_3810465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810465).length < 2 ^ (prefixWord ++ tailWord_3810465).sum := by decide
  have hdescent : baseEnd_3810465 < baseStart_3810465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810486 : List Nat := [5, 1, 3, 2, 1, 1, 3, 1, 1, 4]
def baseStart_3810486 : Nat := 118140960795 + 3810486 * 2 ^ 59
def prefixEnd_3810486 : Nat := 4983230072969 + 3 ^ 40 * 3810486 * 2
def baseEnd_3810486 : Nat := 1304407230152189126467267

theorem tailTrace_3810486 : CollatzResearch.WordTrace tailWord_3810486 prefixEnd_3810486 1304407230152189126467267 := by
  unfold tailWord_3810486
  simp only [CollatzResearch.WordTrace]
  refine ⟨8686240129579217252670707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92653228048844984028487541 8686240129579217252670707)
  ·
    refine ⟨13029360194368825879006061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8686240129579217252670707 13029360194368825879006061)
    ·
      refine ⟨4886010072888309704627273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13029360194368825879006061 4886010072888309704627273)
      ·
        refine ⟨3664507554666232278470455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4886010072888309704627273 3664507554666232278470455)
        ·
          refine ⟨5496761331999348417705683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3664507554666232278470455 5496761331999348417705683)
          ·
            refine ⟨8245141997999022626558525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5496761331999348417705683 8245141997999022626558525)
            ·
              refine ⟨3091928249249633484959447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8245141997999022626558525 3091928249249633484959447)
              ·
                refine ⟨4637892373874450227439171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3091928249249633484959447 4637892373874450227439171)
                ·
                  refine ⟨6956838560811675341158757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4637892373874450227439171 6956838560811675341158757)
                  ·
                    refine ⟨1304407230152189126467267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6956838560811675341158757 1304407230152189126467267)
                    ·
                      rfl

theorem cell22_3810486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_3810486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3810486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3810486 prefixEnd_3810486 := by exact prefixLift 3810486
  have htrace : WordTrace (prefixWord ++ tailWord_3810486) baseStart_3810486 baseEnd_3810486 := by
    simpa [prefixWord, tailWord_3810486, baseEnd_3810486] using wordTrace_append hprefix tailTrace_3810486
  have hstable : (prefixWord ++ tailWord_3810486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810486).length < 2 ^ (prefixWord ++ tailWord_3810486).sum := by decide
  have hdescent : baseEnd_3810486 < baseStart_3810486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810613 : List Nat := [1, 3, 3, 1, 2, 2, 10]
def baseStart_3810613 : Nat := 118140960795 + 3810613 * 2 ^ 59
def prefixEnd_3810613 : Nat := 4983230072969 + 3 ^ 40 * 3810613 * 2
def baseEnd_3810613 : Nat := 48312989068429745501551

theorem tailTrace_3810613 : CollatzResearch.WordTrace tailWord_3810613 prefixEnd_3810613 48312989068429745501551 := by
  unfold tailWord_3810613
  simp only [CollatzResearch.WordTrace]
  refine ⟨138984474143807376732604493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92656316095871584488402995 138984474143807376732604493)
  ·
    refine ⟨52119177803927766274726685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138984474143807376732604493 52119177803927766274726685)
    ·
      refine ⟨19544691676472912353022507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52119177803927766274726685 19544691676472912353022507)
      ·
        refine ⟨29317037514709368529533761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19544691676472912353022507 29317037514709368529533761)
        ·
          refine ⟨21987778136032026397150321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29317037514709368529533761 21987778136032026397150321)
          ·
            refine ⟨16490833602024019797862741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21987778136032026397150321 16490833602024019797862741)
            ·
              refine ⟨48312989068429745501551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16490833602024019797862741 48312989068429745501551)
              ·
                rfl

theorem cell22_3810613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 10].length) (baseStart_3810613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3810613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3810613 prefixEnd_3810613 := by exact prefixLift 3810613
  have htrace : WordTrace (prefixWord ++ tailWord_3810613) baseStart_3810613 baseEnd_3810613 := by
    simpa [prefixWord, tailWord_3810613, baseEnd_3810613] using wordTrace_append hprefix tailTrace_3810613
  have hstable : (prefixWord ++ tailWord_3810613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810613).length < 2 ^ (prefixWord ++ tailWord_3810613).sum := by decide
  have hdescent : baseEnd_3810613 < baseStart_3810613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810737 : List Nat := [1, 2, 2, 4, 1, 1, 1, 6, 4]
def baseStart_3810737 : Nat := 118140960795 + 3810737 * 2 ^ 59
def prefixEnd_3810737 : Nat := 4983230072969 + 3 ^ 40 * 3810737 * 2
def baseEnd_3810737 : Nat := 434831050860569379480499

theorem tailTrace_3810737 : CollatzResearch.WordTrace tailWord_3810737 prefixEnd_3810737 434831050860569379480499 := by
  unfold tailWord_3810737
  simp only [CollatzResearch.WordTrace]
  refine ⟨138988996795358145910118465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92659331196905430606745643 138988996795358145910118465)
  ·
    refine ⟨104241747596518609432588849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138988996795358145910118465 104241747596518609432588849)
    ·
      refine ⟨78181310697388957074441637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104241747596518609432588849 78181310697388957074441637)
      ·
        refine ⟨14658995755760429451457807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78181310697388957074441637 14658995755760429451457807)
        ·
          refine ⟨21988493633640644177186711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14658995755760429451457807 21988493633640644177186711)
          ·
            refine ⟨32982740450460966265780067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21988493633640644177186711 32982740450460966265780067)
            ·
              refine ⟨49474110675691449398670101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32982740450460966265780067 49474110675691449398670101)
              ·
                refine ⟨2319098937923036690562661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49474110675691449398670101 2319098937923036690562661)
                ·
                  refine ⟨434831050860569379480499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2319098937923036690562661 434831050860569379480499)
                  ·
                    rfl

theorem cell22_3810737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 6, 4].length) (baseStart_3810737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3810737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3810737 prefixEnd_3810737 := by exact prefixLift 3810737
  have htrace : WordTrace (prefixWord ++ tailWord_3810737) baseStart_3810737 baseEnd_3810737 := by
    simpa [prefixWord, tailWord_3810737, baseEnd_3810737] using wordTrace_append hprefix tailTrace_3810737
  have hstable : (prefixWord ++ tailWord_3810737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810737).length < 2 ^ (prefixWord ++ tailWord_3810737).sum := by decide
  have hdescent : baseEnd_3810737 < baseStart_3810737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810752 : List Nat := [2, 1, 1, 2, 3, 1, 2, 5, 2, 3]
def baseStart_3810752 : Nat := 118140960795 + 3810752 * 2 ^ 59
def prefixEnd_3810752 : Nat := 4983230072969 + 3 ^ 40 * 3810752 * 2
def baseEnd_3810752 : Nat := 1304498287388253099316451

theorem tailTrace_3810752 : CollatzResearch.WordTrace tailWord_3810752 prefixEnd_3810752 1304498287388253099316451 := by
  unfold tailWord_3810752
  simp only [CollatzResearch.WordTrace]
  refine ⟨69494771945151901735957255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92659695926869202314609673 69494771945151901735957255)
  ·
    refine ⟨104242157917727852603935883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69494771945151901735957255 104242157917727852603935883)
    ·
      refine ⟨156363236876591778905903825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104242157917727852603935883 156363236876591778905903825)
      ·
        refine ⟨117272427657443834179427869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156363236876591778905903825 117272427657443834179427869)
        ·
          refine ⟨43977160371541437817285451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117272427657443834179427869 43977160371541437817285451)
          ·
            refine ⟨65965740557312156725928177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43977160371541437817285451 65965740557312156725928177)
            ·
              refine ⟨49474305417984117544446133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65965740557312156725928177 49474305417984117544446133)
              ·
                refine ⟨4638216132936011019791825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49474305417984117544446133 4638216132936011019791825)
                ·
                  refine ⟨3478662099702008264843869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4638216132936011019791825 3478662099702008264843869)
                  ·
                    refine ⟨1304498287388253099316451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3478662099702008264843869 1304498287388253099316451)
                    ·
                      rfl

theorem cell22_3810752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 2, 3].length) (baseStart_3810752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3810752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3810752 prefixEnd_3810752 := by exact prefixLift 3810752
  have htrace : WordTrace (prefixWord ++ tailWord_3810752) baseStart_3810752 baseEnd_3810752 := by
    simpa [prefixWord, tailWord_3810752, baseEnd_3810752] using wordTrace_append hprefix tailTrace_3810752
  have hstable : (prefixWord ++ tailWord_3810752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810752).length < 2 ^ (prefixWord ++ tailWord_3810752).sum := by decide
  have hdescent : baseEnd_3810752 < baseStart_3810752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810848 : List Nat := [2, 1, 1, 6, 1, 1, 4, 2, 1, 3]
def baseStart_3810848 : Nat := 118140960795 + 3810848 * 2 ^ 59
def prefixEnd_3810848 : Nat := 4983230072969 + 3 ^ 40 * 3810848 * 2
def baseEnd_3810848 : Nat := 1304531150150140848916157

theorem tailTrace_3810848 : CollatzResearch.WordTrace tailWord_3810848 prefixEnd_3810848 1304531150150140848916157 := by
  unfold tailWord_3810848
  simp only [CollatzResearch.WordTrace]
  refine ⟨69496522648978005933704599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92662030198637341244939465 69496522648978005933704599)
  ·
    refine ⟨104244783973467008900556899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69496522648978005933704599 104244783973467008900556899)
    ·
      refine ⟨156367175960200513350835349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104244783973467008900556899 156367175960200513350835349)
      ·
        refine ⟨7329711373134399063320407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 156367175960200513350835349 7329711373134399063320407)
        ·
          refine ⟨10994567059701598594980611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7329711373134399063320407 10994567059701598594980611)
          ·
            refine ⟨16491850589552397892470917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10994567059701598594980611 16491850589552397892470917)
            ·
              refine ⟨3092221985541074604838297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16491850589552397892470917 3092221985541074604838297)
              ·
                refine ⟨2319166489155805953628723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3092221985541074604838297 2319166489155805953628723)
                ·
                  refine ⟨3478749733733708930443085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2319166489155805953628723 3478749733733708930443085)
                  ·
                    refine ⟨1304531150150140848916157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3478749733733708930443085 1304531150150140848916157)
                    ·
                      rfl

theorem cell22_3810848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 2, 1, 3].length) (baseStart_3810848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3810848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3810848 prefixEnd_3810848 := by exact prefixLift 3810848
  have htrace : WordTrace (prefixWord ++ tailWord_3810848) baseStart_3810848 baseEnd_3810848 := by
    simpa [prefixWord, tailWord_3810848, baseEnd_3810848] using wordTrace_append hprefix tailTrace_3810848
  have hstable : (prefixWord ++ tailWord_3810848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810848).length < 2 ^ (prefixWord ++ tailWord_3810848).sum := by decide
  have hdescent : baseEnd_3810848 < baseStart_3810848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810872 : List Nat := [2, 1, 2, 1, 4, 3, 1, 2, 6]
def baseStart_3810872 : Nat := 118140960795 + 3810872 * 2 ^ 59
def prefixEnd_3810872 : Nat := 4983230072969 + 3 ^ 40 * 3810872 * 2
def baseEnd_3810872 : Nat := 434846455280204262105361

theorem tailTrace_3810872 : CollatzResearch.WordTrace tailWord_3810872 prefixEnd_3810872 434846455280204262105361 := by
  unfold tailWord_3810872
  simp only [CollatzResearch.WordTrace]
  refine ⟨69496960324934531983141435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92662613766579375977521913 69496960324934531983141435)
  ·
    refine ⟨104245440487401797974712153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69496960324934531983141435 104245440487401797974712153)
    ·
      refine ⟨78184080365551348481034115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104245440487401797974712153 78184080365551348481034115)
      ·
        refine ⟨117276120548327022721551173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78184080365551348481034115 117276120548327022721551173)
        ·
          refine ⟨21989272602811316760290845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117276120548327022721551173 21989272602811316760290845)
          ·
            refine ⟨8245977226054243785109067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21989272602811316760290845 8245977226054243785109067)
            ·
              refine ⟨12368965839081365677663601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8245977226054243785109067 12368965839081365677663601)
              ·
                refine ⟨9276724379311024258247701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12368965839081365677663601 9276724379311024258247701)
                ·
                  refine ⟨434846455280204262105361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9276724379311024258247701 434846455280204262105361)
                  ·
                    rfl

theorem cell22_3810872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 6].length) (baseStart_3810872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3810872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3810872 prefixEnd_3810872 := by exact prefixLift 3810872
  have htrace : WordTrace (prefixWord ++ tailWord_3810872) baseStart_3810872 baseEnd_3810872 := by
    simpa [prefixWord, tailWord_3810872, baseEnd_3810872] using wordTrace_append hprefix tailTrace_3810872
  have hstable : (prefixWord ++ tailWord_3810872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810872).length < 2 ^ (prefixWord ++ tailWord_3810872).sum := by decide
  have hdescent : baseEnd_3810872 < baseStart_3810872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3810934 : List Nat := [5, 1, 1, 2, 2, 2, 1, 8]
def baseStart_3810934 : Nat := 118140960795 + 3810934 * 2 ^ 59
def prefixEnd_3810934 : Nat := 4983230072969 + 3 ^ 40 * 3810934 * 2
def baseEnd_3810934 : Nat := 144951176634185032362877

theorem tailTrace_3810934 : CollatzResearch.WordTrace tailWord_3810934 prefixEnd_3810934 144951176634185032362877 := by
  unfold tailWord_3810934
  simp only [CollatzResearch.WordTrace]
  refine ⟨8687261373477778034689991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92664121317096299036693237 8687261373477778034689991)
  ·
    refine ⟨13030892060216667052034987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8687261373477778034689991 13030892060216667052034987)
    ·
      refine ⟨19546338090325000578052481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13030892060216667052034987 19546338090325000578052481)
      ·
        refine ⟨14659753567743750433539361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19546338090325000578052481 14659753567743750433539361)
        ·
          refine ⟨10994815175807812825154521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14659753567743750433539361 10994815175807812825154521)
          ·
            refine ⟨8246111381855859618865891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10994815175807812825154521 8246111381855859618865891)
            ·
              refine ⟨12369167072783789428298837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8246111381855859618865891 12369167072783789428298837)
              ·
                refine ⟨144951176634185032362877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12369167072783789428298837 144951176634185032362877)
                ·
                  rfl

theorem cell22_3810934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_3810934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3810934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3810934 prefixEnd_3810934 := by exact prefixLift 3810934
  have htrace : WordTrace (prefixWord ++ tailWord_3810934) baseStart_3810934 baseEnd_3810934 := by
    simpa [prefixWord, tailWord_3810934, baseEnd_3810934] using wordTrace_append hprefix tailTrace_3810934
  have hstable : (prefixWord ++ tailWord_3810934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3810934).length < 2 ^ (prefixWord ++ tailWord_3810934).sum := by decide
  have hdescent : baseEnd_3810934 < baseStart_3810934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3810934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811039 : List Nat := [1, 1, 2, 3, 2, 2, 4, 1, 1, 5]
def baseStart_3811039 : Nat := 118140960795 + 3811039 * 2 ^ 59
def prefixEnd_3811039 : Nat := 4983230072969 + 3 ^ 40 * 3811039 * 2
def baseEnd_3811039 : Nat := 1304596533353480017390571

theorem tailTrace_3811039 : CollatzResearch.WordTrace tailWord_3811039 prefixEnd_3811039 1304596533353480017390571 := by
  unfold tailWord_3811039
  simp only [CollatzResearch.WordTrace]
  refine ⟨139000011640264051487612171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92666674426842700991741447 139000011640264051487612171)
  ·
    refine ⟨208500017460396077231418257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139000011640264051487612171 208500017460396077231418257)
    ·
      refine ⟨156375013095297057923563693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208500017460396077231418257 156375013095297057923563693)
      ·
        refine ⟨58640629910736396721336385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156375013095297057923563693 58640629910736396721336385)
        ·
          refine ⟨43980472433052297541002289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58640629910736396721336385 43980472433052297541002289)
          ·
            refine ⟨32985354324789223155751717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43980472433052297541002289 32985354324789223155751717)
            ·
              refine ⟨6184753935897979341703447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32985354324789223155751717 6184753935897979341703447)
              ·
                refine ⟨9277130903846969012555171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6184753935897979341703447 9277130903846969012555171)
                ·
                  refine ⟨13915696355770453518832757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9277130903846969012555171 13915696355770453518832757)
                  ·
                    refine ⟨1304596533353480017390571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13915696355770453518832757 1304596533353480017390571)
                    ·
                      rfl

theorem cell22_3811039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 5].length) (baseStart_3811039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3811039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3811039 prefixEnd_3811039 := by exact prefixLift 3811039
  have htrace : WordTrace (prefixWord ++ tailWord_3811039) baseStart_3811039 baseEnd_3811039 := by
    simpa [prefixWord, tailWord_3811039, baseEnd_3811039] using wordTrace_append hprefix tailTrace_3811039
  have hstable : (prefixWord ++ tailWord_3811039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811039).length < 2 ^ (prefixWord ++ tailWord_3811039).sum := by decide
  have hdescent : baseEnd_3811039 < baseStart_3811039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811052 : List Nat := [2, 2, 1, 1, 2, 2, 2, 10]
def baseStart_3811052 : Nat := 118140960795 + 3811052 * 2 ^ 59
def prefixEnd_3811052 : Nat := 4983230072969 + 3 ^ 40 * 3811052 * 2
def baseEnd_3811052 : Nat := 144955664835461368535059

theorem tailTrace_3811052 : CollatzResearch.WordTrace tailWord_3811052 prefixEnd_3811052 144955664835461368535059 := by
  unfold tailWord_3811052
  simp only [CollatzResearch.WordTrace]
  refine ⟨69500242894608477353917705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92666990526144636471890273 69500242894608477353917705)
  ·
    refine ⟨52125182170956358015438279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69500242894608477353917705 52125182170956358015438279)
    ·
      refine ⟨78187773256434537023157419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52125182170956358015438279 78187773256434537023157419)
      ·
        refine ⟨117281659884651805534736129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78187773256434537023157419 117281659884651805534736129)
        ·
          refine ⟨87961244913488854151052097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117281659884651805534736129 87961244913488854151052097)
          ·
            refine ⟨65970933685116640613289073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87961244913488854151052097 65970933685116640613289073)
            ·
              refine ⟨49478200263837480459966805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65970933685116640613289073 49478200263837480459966805)
              ·
                refine ⟨144955664835461368535059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49478200263837480459966805 144955664835461368535059)
                ·
                  rfl

theorem cell22_3811052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 10].length) (baseStart_3811052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3811052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3811052 prefixEnd_3811052 := by exact prefixLift 3811052
  have htrace : WordTrace (prefixWord ++ tailWord_3811052) baseStart_3811052 baseEnd_3811052 := by
    simpa [prefixWord, tailWord_3811052, baseEnd_3811052] using wordTrace_append hprefix tailTrace_3811052
  have hstable : (prefixWord ++ tailWord_3811052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811052).length < 2 ^ (prefixWord ++ tailWord_3811052).sum := by decide
  have hdescent : baseEnd_3811052 < baseStart_3811052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811054 : List Nat := [4, 1, 2, 1, 1, 2, 3, 1, 1, 6]
def baseStart_3811054 : Nat := 118140960795 + 3811054 * 2 ^ 59
def prefixEnd_3811054 : Nat := 4983230072969 + 3 ^ 40 * 3811054 * 2
def baseEnd_3811054 : Nat := 1304601668160024978265525

theorem tailTrace_3811054 : CollatzResearch.WordTrace tailWord_3811054 prefixEnd_3811054 1304601668160024978265525 := by
  unfold tailWord_3811054
  simp only [CollatzResearch.WordTrace]
  refine ⟨17375069841901213631176027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92667039156806472699605477 17375069841901213631176027)
  ·
    refine ⟨26062604762851820446764041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17375069841901213631176027 26062604762851820446764041)
    ·
      refine ⟨19546953572138865335073031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26062604762851820446764041 19546953572138865335073031)
      ·
        refine ⟨29320430358208298002609547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19546953572138865335073031 29320430358208298002609547)
        ·
          refine ⟨43980645537312447003914321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29320430358208298002609547 43980645537312447003914321)
          ·
            refine ⟨32985484152984335252935741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43980645537312447003914321 32985484152984335252935741)
            ·
              refine ⟨12369556557369125719850903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32985484152984335252935741 12369556557369125719850903)
              ·
                refine ⟨18554334836053688579776355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12369556557369125719850903 18554334836053688579776355)
                ·
                  refine ⟨27831502254080532869664533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18554334836053688579776355 27831502254080532869664533)
                  ·
                    refine ⟨1304601668160024978265525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27831502254080532869664533 1304601668160024978265525)
                    ·
                      rfl

theorem cell22_3811054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_3811054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3811054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3811054 prefixEnd_3811054 := by exact prefixLift 3811054
  have htrace : WordTrace (prefixWord ++ tailWord_3811054) baseStart_3811054 baseEnd_3811054 := by
    simpa [prefixWord, tailWord_3811054, baseEnd_3811054] using wordTrace_append hprefix tailTrace_3811054
  have hstable : (prefixWord ++ tailWord_3811054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811054).length < 2 ^ (prefixWord ++ tailWord_3811054).sum := by decide
  have hdescent : baseEnd_3811054 < baseStart_3811054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811060 : List Nat := [2, 6, 1, 1, 1, 2, 1, 3, 1, 4]
def baseStart_3811060 : Nat := 118140960795 + 3811060 * 2 ^ 59
def prefixEnd_3811060 : Nat := 4983230072969 + 3 ^ 40 * 3811060 * 2
def baseEnd_3811060 : Nat := 1304603722082642962615507

theorem tailTrace_3811060 : CollatzResearch.WordTrace tailWord_3811060 prefixEnd_3811060 1304603722082642962615507 := by
  unfold tailWord_3811060
  simp only [CollatzResearch.WordTrace]
  refine ⟨69500388786593986037063317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92667185048791981382751089 69500388786593986037063317)
  ·
    refine ⟨3257830724371593095487343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 69500388786593986037063317 3257830724371593095487343)
    ·
      refine ⟨4886746086557389643231015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3257830724371593095487343 4886746086557389643231015)
      ·
        refine ⟨7330119129836084464846523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4886746086557389643231015 7330119129836084464846523)
        ·
          refine ⟨10995178694754126697269785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7330119129836084464846523 10995178694754126697269785)
          ·
            refine ⟨8246384021065595022952339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10995178694754126697269785 8246384021065595022952339)
            ·
              refine ⟨12369576031598392534428509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8246384021065595022952339 12369576031598392534428509)
              ·
                refine ⟨4638591011849397200410691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12369576031598392534428509 4638591011849397200410691)
                ·
                  refine ⟨6957886517774095800616037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4638591011849397200410691 6957886517774095800616037)
                  ·
                    refine ⟨1304603722082642962615507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6957886517774095800616037 1304603722082642962615507)
                    ·
                      rfl

theorem cell22_3811060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_3811060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3811060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3811060 prefixEnd_3811060 := by exact prefixLift 3811060
  have htrace : WordTrace (prefixWord ++ tailWord_3811060) baseStart_3811060 baseEnd_3811060 := by
    simpa [prefixWord, tailWord_3811060, baseEnd_3811060] using wordTrace_append hprefix tailTrace_3811060
  have hstable : (prefixWord ++ tailWord_3811060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811060).length < 2 ^ (prefixWord ++ tailWord_3811060).sum := by decide
  have hdescent : baseEnd_3811060 < baseStart_3811060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811135 : List Nat := [1, 1, 2, 2, 7, 1, 1, 1, 3, 3]
def baseStart_3811135 : Nat := 118140960795 + 3811135 * 2 ^ 59
def prefixEnd_3811135 : Nat := 4983230072969 + 3 ^ 40 * 3811135 * 2
def baseEnd_3811135 : Nat := 1304629396115367766990277

theorem tailTrace_3811135 : CollatzResearch.WordTrace tailWord_3811135 prefixEnd_3811135 1304629396115367766990277 := by
  unfold tailWord_3811135
  simp only [CollatzResearch.WordTrace]
  refine ⟨139003513047916259883106859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92669008698610839922071239 139003513047916259883106859)
  ·
    refine ⟨208505269571874389824660289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139003513047916259883106859 208505269571874389824660289)
    ·
      refine ⟨156378952178905792368495217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208505269571874389824660289 156378952178905792368495217)
      ·
        refine ⟨117284214134179344276371413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156378952178905792368495217 117284214134179344276371413)
        ·
          refine ⟨2748848768769828381477455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 117284214134179344276371413 2748848768769828381477455)
          ·
            refine ⟨4123273153154742572216183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2748848768769828381477455 4123273153154742572216183)
            ·
              refine ⟨6184909729732113858324275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4123273153154742572216183 6184909729732113858324275)
              ·
                refine ⟨9277364594598170787486413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6184909729732113858324275 9277364594598170787486413)
                ·
                  refine ⟨3479011722974314045307405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9277364594598170787486413 3479011722974314045307405)
                  ·
                    refine ⟨1304629396115367766990277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3479011722974314045307405 1304629396115367766990277)
                    ·
                      rfl

theorem cell22_3811135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 3, 3].length) (baseStart_3811135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3811135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3811135 prefixEnd_3811135 := by exact prefixLift 3811135
  have htrace : WordTrace (prefixWord ++ tailWord_3811135) baseStart_3811135 baseEnd_3811135 := by
    simpa [prefixWord, tailWord_3811135, baseEnd_3811135] using wordTrace_append hprefix tailTrace_3811135
  have hstable : (prefixWord ++ tailWord_3811135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811135).length < 2 ^ (prefixWord ++ tailWord_3811135).sum := by decide
  have hdescent : baseEnd_3811135 < baseStart_3811135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811208 : List Nat := [2, 1, 3, 3, 3, 1, 2, 1, 1, 5]
def baseStart_3811208 : Nat := 118140960795 + 3811208 * 2 ^ 59
def prefixEnd_3811208 : Nat := 4983230072969 + 3 ^ 40 * 3811208 * 2
def baseEnd_3811208 : Nat := 1304654385507219909915053

theorem tailTrace_3811208 : CollatzResearch.WordTrace tailWord_3811208 prefixEnd_3811208 1304654385507219909915053 := by
  unfold tailWord_3811208
  simp only [CollatzResearch.WordTrace]
  refine ⟨69503087788325896675257139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92670783717767862233676185 69503087788325896675257139)
  ·
    refine ⟨104254631682488845012885709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69503087788325896675257139 104254631682488845012885709)
    ·
      refine ⟨39095486880933316879832141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104254631682488845012885709 39095486880933316879832141)
      ·
        refine ⟨14660807580349993829937053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39095486880933316879832141 14660807580349993829937053)
        ·
          refine ⟨5497802842631247686226395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14660807580349993829937053 5497802842631247686226395)
          ·
            refine ⟨8246704263946871529339593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5497802842631247686226395 8246704263946871529339593)
            ·
              refine ⟨6185028197960153647004695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8246704263946871529339593 6185028197960153647004695)
              ·
                refine ⟨9277542296940230470507043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6185028197960153647004695 9277542296940230470507043)
                ·
                  refine ⟨13916313445410345705760565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9277542296940230470507043 13916313445410345705760565)
                  ·
                    refine ⟨1304654385507219909915053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13916313445410345705760565 1304654385507219909915053)
                    ·
                      rfl

theorem cell22_3811208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_3811208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3811208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3811208 prefixEnd_3811208 := by exact prefixLift 3811208
  have htrace : WordTrace (prefixWord ++ tailWord_3811208) baseStart_3811208 baseEnd_3811208 := by
    simpa [prefixWord, tailWord_3811208, baseEnd_3811208] using wordTrace_append hprefix tailTrace_3811208
  have hstable : (prefixWord ++ tailWord_3811208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811208).length < 2 ^ (prefixWord ++ tailWord_3811208).sum := by decide
  have hdescent : baseEnd_3811208 < baseStart_3811208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811221 : List Nat := [1, 3, 2, 1, 1, 3, 5, 6]
def baseStart_3811221 : Nat := 118140960795 + 3811221 * 2 ^ 59
def prefixEnd_3811221 : Nat := 4983230072969 + 3 ^ 40 * 3811221 * 2
def baseEnd_3811221 : Nat := 144962092852543578815557

theorem tailTrace_3811221 : CollatzResearch.WordTrace tailWord_3811221 prefixEnd_3811221 144962092852543578815557 := by
  unfold tailWord_3811221
  simp only [CollatzResearch.WordTrace]
  refine ⟨139006649725604696570737517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92671099817069797713825011 139006649725604696570737517)
  ·
    refine ⟨52127493647101761214026569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139006649725604696570737517 52127493647101761214026569)
    ·
      refine ⟨39095620235326320910519927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52127493647101761214026569 39095620235326320910519927)
      ·
        refine ⟨58643430352989481365779891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39095620235326320910519927 58643430352989481365779891)
        ·
          refine ⟨87965145529484222048669837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58643430352989481365779891 87965145529484222048669837)
          ·
            refine ⟨32986929573556583268251189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87965145529484222048669837 32986929573556583268251189)
            ·
              refine ⟨3092524647520929681398549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32986929573556583268251189 3092524647520929681398549)
              ·
                refine ⟨144962092852543578815557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3092524647520929681398549 144962092852543578815557)
                ·
                  rfl

theorem cell22_3811221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 6].length) (baseStart_3811221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3811221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3811221 prefixEnd_3811221 := by exact prefixLift 3811221
  have htrace : WordTrace (prefixWord ++ tailWord_3811221) baseStart_3811221 baseEnd_3811221 := by
    simpa [prefixWord, tailWord_3811221, baseEnd_3811221] using wordTrace_append hprefix tailTrace_3811221
  have hstable : (prefixWord ++ tailWord_3811221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811221).length < 2 ^ (prefixWord ++ tailWord_3811221).sum := by decide
  have hdescent : baseEnd_3811221 < baseStart_3811221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811223 : List Nat := [1, 1, 3, 3, 1, 5, 1, 1, 2, 4]
def baseStart_3811223 : Nat := 118140960795 + 3811223 * 2 ^ 59
def prefixEnd_3811223 : Nat := 4983230072969 + 3 ^ 40 * 3811223 * 2
def baseEnd_3811223 : Nat := 1304659520313764870790007

theorem tailTrace_3811223 : CollatzResearch.WordTrace tailWord_3811223 prefixEnd_3811223 1304659520313764870790007 := by
  unfold tailWord_3811223
  simp only [CollatzResearch.WordTrace]
  refine ⟨139006722671597450912310323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92671148447731633941540215 139006722671597450912310323)
  ·
    refine ⟨208510084007396176368465485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139006722671597450912310323 208510084007396176368465485)
    ·
      refine ⟨78191281502773566138174557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208510084007396176368465485 78191281502773566138174557)
      ·
        refine ⟨29321730563540087301815459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78191281502773566138174557 29321730563540087301815459)
        ·
          refine ⟨43982595845310130952723189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29321730563540087301815459 43982595845310130952723189)
          ·
            refine ⟨4123368360497824776817799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43982595845310130952723189 4123368360497824776817799)
            ·
              refine ⟨6185052540746737165226699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4123368360497824776817799 6185052540746737165226699)
              ·
                refine ⟨9277578811120105747840049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6185052540746737165226699 9277578811120105747840049)
                ·
                  refine ⟨6958184108340079310880037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9277578811120105747840049 6958184108340079310880037)
                  ·
                    refine ⟨1304659520313764870790007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6958184108340079310880037 1304659520313764870790007)
                    ·
                      rfl

theorem cell22_3811223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 4].length) (baseStart_3811223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3811223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3811223 prefixEnd_3811223 := by exact prefixLift 3811223
  have htrace : WordTrace (prefixWord ++ tailWord_3811223) baseStart_3811223 baseEnd_3811223 := by
    simpa [prefixWord, tailWord_3811223, baseEnd_3811223] using wordTrace_append hprefix tailTrace_3811223
  have hstable : (prefixWord ++ tailWord_3811223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811223).length < 2 ^ (prefixWord ++ tailWord_3811223).sum := by decide
  have hdescent : baseEnd_3811223 < baseStart_3811223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811253 : List Nat := [1, 3, 3, 2, 1, 2, 1, 3, 3, 3]
def baseStart_3811253 : Nat := 118140960795 + 3811253 * 2 ^ 59
def prefixEnd_3811253 : Nat := 4983230072969 + 3 ^ 40 * 3811253 * 2
def baseEnd_3811253 : Nat := 1304669789926854792539915

theorem tailTrace_3811253 : CollatzResearch.WordTrace tailWord_3811253 prefixEnd_3811253 1304669789926854792539915 := by
  unfold tailWord_3811253
  simp only [CollatzResearch.WordTrace]
  refine ⟨139007816861488766035902413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92671877907659177357268275 139007816861488766035902413)
  ·
    refine ⟨52127931323058287263463405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139007816861488766035902413 52127931323058287263463405)
    ·
      refine ⟨19547974246146857723798777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52127931323058287263463405 19547974246146857723798777)
      ·
        refine ⟨14660980684610143292849083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19547974246146857723798777 14660980684610143292849083)
        ·
          refine ⟨21991471026915214939273625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14660980684610143292849083 21991471026915214939273625)
          ·
            refine ⟨16493603270186411204455219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21991471026915214939273625 16493603270186411204455219)
            ·
              refine ⟨24740404905279616806682829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16493603270186411204455219 24740404905279616806682829)
              ·
                refine ⟨9277651839479856302506061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24740404905279616806682829 9277651839479856302506061)
                ·
                  refine ⟨3479119439804946113439773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9277651839479856302506061 3479119439804946113439773)
                  ·
                    refine ⟨1304669789926854792539915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3479119439804946113439773 1304669789926854792539915)
                    ·
                      rfl

theorem cell22_3811253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_3811253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3811253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3811253 prefixEnd_3811253 := by exact prefixLift 3811253
  have htrace : WordTrace (prefixWord ++ tailWord_3811253) baseStart_3811253 baseEnd_3811253 := by
    simpa [prefixWord, tailWord_3811253, baseEnd_3811253] using wordTrace_append hprefix tailTrace_3811253
  have hstable : (prefixWord ++ tailWord_3811253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811253).length < 2 ^ (prefixWord ++ tailWord_3811253).sum := by decide
  have hdescent : baseEnd_3811253 < baseStart_3811253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811356 : List Nat := [2, 2, 3, 1, 3, 11]
def baseStart_3811356 : Nat := 118140960795 + 3811356 * 2 ^ 59
def prefixEnd_3811356 : Nat := 4983230072969 + 3 ^ 40 * 3811356 * 2
def baseEnd_3811356 : Nat := 16107469739898726632279

theorem tailTrace_3811356 : CollatzResearch.WordTrace tailWord_3811356 prefixEnd_3811356 16107469739898726632279 := by
  unfold tailWord_3811356
  simp only [CollatzResearch.WordTrace]
  refine ⟨69505786790057807313450961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92674382386743743084601281 69505786790057807313450961)
  ·
    refine ⟨52129340092543355485088221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69505786790057807313450961 52129340092543355485088221)
    ·
      refine ⟨19548502534703758306908083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52129340092543355485088221 19548502534703758306908083)
      ·
        refine ⟨29322753802055637460362125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19548502534703758306908083 29322753802055637460362125)
        ·
          refine ⟨10996032675770864047635797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29322753802055637460362125 10996032675770864047635797)
          ·
            refine ⟨16107469739898726632279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10996032675770864047635797 16107469739898726632279)
            ·
              rfl

theorem cell22_3811356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 11].length) (baseStart_3811356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3811356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3811356 prefixEnd_3811356 := by exact prefixLift 3811356
  have htrace : WordTrace (prefixWord ++ tailWord_3811356) baseStart_3811356 baseEnd_3811356 := by
    simpa [prefixWord, tailWord_3811356, baseEnd_3811356] using wordTrace_append hprefix tailTrace_3811356
  have hstable : (prefixWord ++ tailWord_3811356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811356).length < 2 ^ (prefixWord ++ tailWord_3811356).sum := by decide
  have hdescent : baseEnd_3811356 < baseStart_3811356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811386 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 4, 6]
def baseStart_3811386 : Nat := 118140960795 + 3811386 * 2 ^ 59
def prefixEnd_3811386 : Nat := 4983230072969 + 3 ^ 40 * 3811386 * 2
def baseEnd_3811386 : Nat := 1304715318544886778964507

theorem tailTrace_3811386 : CollatzResearch.WordTrace tailWord_3811386 prefixEnd_3811386 1304715318544886778964507 := by
  unfold tailWord_3811386
  simp only [CollatzResearch.WordTrace]
  refine ⟨34753166942501732437623503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92675111846671286500329341 34753166942501732437623503)
  ·
    refine ⟨52129750413752598656435255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34753166942501732437623503 52129750413752598656435255)
    ·
      refine ⟨78194625620628897984652883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52129750413752598656435255 78194625620628897984652883)
      ·
        refine ⟨117291938430943346976979325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78194625620628897984652883 117291938430943346976979325)
        ·
          refine ⟨43984476911603755116367247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117291938430943346976979325 43984476911603755116367247)
          ·
            refine ⟨65976715367405632674550871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43984476911603755116367247 65976715367405632674550871)
            ·
              refine ⟨98965073051108449011826307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65976715367405632674550871 98965073051108449011826307)
              ·
                refine ⟨148447609576662673517739461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98965073051108449011826307 148447609576662673517739461)
                ·
                  refine ⟨27833926795624251284576149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 148447609576662673517739461 27833926795624251284576149)
                  ·
                    refine ⟨1304715318544886778964507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27833926795624251284576149 1304715318544886778964507)
                    ·
                      rfl

theorem cell22_3811386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_3811386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3811386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3811386 prefixEnd_3811386 := by exact prefixLift 3811386
  have htrace : WordTrace (prefixWord ++ tailWord_3811386) baseStart_3811386 baseEnd_3811386 := by
    simpa [prefixWord, tailWord_3811386, baseEnd_3811386] using wordTrace_append hprefix tailTrace_3811386
  have hstable : (prefixWord ++ tailWord_3811386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811386).length < 2 ^ (prefixWord ++ tailWord_3811386).sum := by decide
  have hdescent : baseEnd_3811386 < baseStart_3811386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811401 : List Nat := [1, 2, 1, 1, 2, 2, 4, 2, 7]
def baseStart_3811401 : Nat := 118140960795 + 3811401 * 2 ^ 59
def prefixEnd_3811401 : Nat := 4983230072969 + 3 ^ 40 * 3811401 * 2
def baseEnd_3811401 : Nat := 434906817783810579946487

theorem tailTrace_3811401 : CollatzResearch.WordTrace tailWord_3811401 prefixEnd_3811401 434906817783810579946487 := by
  unfold tailWord_3811401
  simp only [CollatzResearch.WordTrace]
  refine ⟨139013214864952587312290057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92675476576635058208193371 139013214864952587312290057)
  ·
    refine ⟨104259911148714440484217543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139013214864952587312290057 104259911148714440484217543)
    ·
      refine ⟨156389866723071660726326315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104259911148714440484217543 156389866723071660726326315)
      ·
        refine ⟨234584800084607491089489473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156389866723071660726326315 234584800084607491089489473)
        ·
          refine ⟨175938600063455618317117105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234584800084607491089489473 175938600063455618317117105)
          ·
            refine ⟨131953950047591713737837829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175938600063455618317117105 131953950047591713737837829)
            ·
              refine ⟨24741365633923446325844593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131953950047591713737837829 24741365633923446325844593)
              ·
                refine ⟨18556024225442584744383445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24741365633923446325844593 18556024225442584744383445)
                ·
                  refine ⟨434906817783810579946487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18556024225442584744383445 434906817783810579946487)
                  ·
                    rfl

theorem cell22_3811401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 7].length) (baseStart_3811401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3811401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3811401 prefixEnd_3811401 := by exact prefixLift 3811401
  have htrace : WordTrace (prefixWord ++ tailWord_3811401) baseStart_3811401 baseEnd_3811401 := by
    simpa [prefixWord, tailWord_3811401, baseEnd_3811401] using wordTrace_append hprefix tailTrace_3811401
  have hstable : (prefixWord ++ tailWord_3811401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811401).length < 2 ^ (prefixWord ++ tailWord_3811401).sum := by decide
  have hdescent : baseEnd_3811401 < baseStart_3811401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811405 : List Nat := [1, 6, 1, 1, 1, 1, 1, 2, 5, 3]
def baseStart_3811405 : Nat := 118140960795 + 3811405 * 2 ^ 59
def prefixEnd_3811405 : Nat := 4983230072969 + 3 ^ 40 * 3811405 * 2
def baseEnd_3811405 : Nat := 1304721822633177062739449

theorem tailTrace_3811405 : CollatzResearch.WordTrace tailWord_3811405 prefixEnd_3811405 1304721822633177062739449 := by
  unfold tailWord_3811405
  simp only [CollatzResearch.WordTrace]
  refine ⟨139013360756938095995435669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92675573837958730663623779 139013360756938095995435669)
  ·
    refine ⟨6516251285481473249786047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 139013360756938095995435669 6516251285481473249786047)
    ·
      refine ⟨9774376928222209874679071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6516251285481473249786047 9774376928222209874679071)
      ·
        refine ⟨14661565392333314812018607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9774376928222209874679071 14661565392333314812018607)
        ·
          refine ⟨21992348088499972218027911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14661565392333314812018607 21992348088499972218027911)
          ·
            refine ⟨32988522132749958327041867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21992348088499972218027911 32988522132749958327041867)
            ·
              refine ⟨49482783199124937490562801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32988522132749958327041867 49482783199124937490562801)
              ·
                refine ⟨37112087399343703117922101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49482783199124937490562801 37112087399343703117922101)
                ·
                  refine ⟨3479258193688472167305197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37112087399343703117922101 3479258193688472167305197)
                  ·
                    refine ⟨1304721822633177062739449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3479258193688472167305197 1304721822633177062739449)
                    ·
                      rfl

theorem cell22_3811405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_3811405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3811405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3811405 prefixEnd_3811405 := by exact prefixLift 3811405
  have htrace : WordTrace (prefixWord ++ tailWord_3811405) baseStart_3811405 baseEnd_3811405 := by
    simpa [prefixWord, tailWord_3811405, baseEnd_3811405] using wordTrace_append hprefix tailTrace_3811405
  have hstable : (prefixWord ++ tailWord_3811405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811405).length < 2 ^ (prefixWord ++ tailWord_3811405).sum := by decide
  have hdescent : baseEnd_3811405 < baseStart_3811405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811486 : List Nat := [4, 3, 1, 1, 4, 1, 2, 1, 5]
def baseStart_3811486 : Nat := 118140960795 + 3811486 * 2 ^ 59
def prefixEnd_3811486 : Nat := 4983230072969 + 3 ^ 40 * 3811486 * 2
def baseEnd_3811486 : Nat := 434916516862839950488067

theorem tailTrace_3811486 : CollatzResearch.WordTrace tailWord_3811486 prefixEnd_3811486 434916516862839950488067 := by
  unfold tailWord_3811486
  simp only [CollatzResearch.WordTrace]
  refine ⟨17377039383705580853641789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92677543379763097886089541 17377039383705580853641789)
  ·
    refine ⟨6516389768889592820115671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17377039383705580853641789 6516389768889592820115671)
    ·
      refine ⟨9774584653334389230173507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6516389768889592820115671 9774584653334389230173507)
      ·
        refine ⟨14661876980001583845260261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9774584653334389230173507 14661876980001583845260261)
        ·
          refine ⟨2749101933750296970986299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14661876980001583845260261 2749101933750296970986299)
          ·
            refine ⟨4123652900625445456479449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2749101933750296970986299 4123652900625445456479449)
            ·
              refine ⟨3092739675469084092359587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4123652900625445456479449 3092739675469084092359587)
              ·
                refine ⟨4639109513203626138539381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3092739675469084092359587 4639109513203626138539381)
                ·
                  refine ⟨434916516862839950488067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4639109513203626138539381 434916516862839950488067)
                  ·
                    rfl

theorem cell22_3811486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_3811486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3811486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3811486 prefixEnd_3811486 := by exact prefixLift 3811486
  have htrace : WordTrace (prefixWord ++ tailWord_3811486) baseStart_3811486 baseEnd_3811486 := by
    simpa [prefixWord, tailWord_3811486, baseEnd_3811486] using wordTrace_append hprefix tailTrace_3811486
  have hstable : (prefixWord ++ tailWord_3811486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811486).length < 2 ^ (prefixWord ++ tailWord_3811486).sum := by decide
  have hdescent : baseEnd_3811486 < baseStart_3811486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811493 : List Nat := [1, 3, 1, 2, 1, 3, 1, 2, 4, 4]
def baseStart_3811493 : Nat := 118140960795 + 3811493 * 2 ^ 59
def prefixEnd_3811493 : Nat := 4983230072969 + 3 ^ 40 * 3811493 * 2
def baseEnd_3811493 : Nat := 1304751946831574166539179

theorem tailTrace_3811493 : CollatzResearch.WordTrace tailWord_3811493 prefixEnd_3811493 1304751946831574166539179 := by
  unfold tailWord_3811493
  simp only [CollatzResearch.WordTrace]
  refine ⟨139016570380619287024639133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92677713587079524683092755 139016570380619287024639133)
  ·
    refine ⟨52131213892732232634239675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139016570380619287024639133 52131213892732232634239675)
    ·
      refine ⟨78196820839098348951359513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52131213892732232634239675 78196820839098348951359513)
      ·
        refine ⟨58647615629323761713519635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78196820839098348951359513 58647615629323761713519635)
        ·
          refine ⟨87971423443985642570279453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58647615629323761713519635 87971423443985642570279453)
          ·
            refine ⟨32989283791494615963854795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87971423443985642570279453 32989283791494615963854795)
            ·
              refine ⟨49483925687241923945782193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32989283791494615963854795 49483925687241923945782193)
              ·
                refine ⟨37112944265431442959336645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49483925687241923945782193 37112944265431442959336645)
                ·
                  refine ⟨6958677049768395554875621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37112944265431442959336645 6958677049768395554875621)
                  ·
                    refine ⟨1304751946831574166539179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6958677049768395554875621 1304751946831574166539179)
                    ·
                      rfl

theorem cell22_3811493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_3811493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3811493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3811493 prefixEnd_3811493 := by exact prefixLift 3811493
  have htrace : WordTrace (prefixWord ++ tailWord_3811493) baseStart_3811493 baseEnd_3811493 := by
    simpa [prefixWord, tailWord_3811493, baseEnd_3811493] using wordTrace_append hprefix tailTrace_3811493
  have hstable : (prefixWord ++ tailWord_3811493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811493).length < 2 ^ (prefixWord ++ tailWord_3811493).sum := by decide
  have hdescent : baseEnd_3811493 < baseStart_3811493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811542 : List Nat := [5, 2, 1, 2, 1, 1, 3, 7]
def baseStart_3811542 : Nat := 118140960795 + 3811542 * 2 ^ 59
def prefixEnd_3811542 : Nat := 4983230072969 + 3 ^ 40 * 3811542 * 2
def baseEnd_3811542 : Nat := 144974302281439374673781

theorem tailTrace_3811542 : CollatzResearch.WordTrace tailWord_3811542 prefixEnd_3811542 144974302281439374673781 := by
  unfold tailWord_3811542
  simp only [CollatzResearch.WordTrace]
  refine ⟨8688647347340110524573305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92678905038294512262115253 8688647347340110524573305)
  ·
    refine ⟨6516485510505082893429979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8688647347340110524573305 6516485510505082893429979)
    ·
      refine ⟨9774728265757624340144969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6516485510505082893429979 9774728265757624340144969)
      ·
        refine ⟨7331046199318218255108727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9774728265757624340144969 7331046199318218255108727)
        ·
          refine ⟨10996569298977327382663091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7331046199318218255108727 10996569298977327382663091)
          ·
            refine ⟨16494853948465991073994637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10996569298977327382663091 16494853948465991073994637)
            ·
              refine ⟨6185570230674746652747989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16494853948465991073994637 6185570230674746652747989)
              ·
                refine ⟨144974302281439374673781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6185570230674746652747989 144974302281439374673781)
                ·
                  rfl

theorem cell22_3811542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_3811542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3811542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3811542 prefixEnd_3811542 := by exact prefixLift 3811542
  have htrace : WordTrace (prefixWord ++ tailWord_3811542) baseStart_3811542 baseEnd_3811542 := by
    simpa [prefixWord, tailWord_3811542, baseEnd_3811542] using wordTrace_append hprefix tailTrace_3811542
  have hstable : (prefixWord ++ tailWord_3811542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811542).length < 2 ^ (prefixWord ++ tailWord_3811542).sum := by decide
  have hdescent : baseEnd_3811542 < baseStart_3811542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811557 : List Nat := [1, 3, 1, 4, 2, 2, 1, 2, 3, 3]
def baseStart_3811557 : Nat := 118140960795 + 3811557 * 2 ^ 59
def prefixEnd_3811557 : Nat := 4983230072969 + 3 ^ 40 * 3811557 * 2
def baseEnd_3811557 : Nat := 1304773855339499332938983

theorem tailTrace_3811557 : CollatzResearch.WordTrace tailWord_3811557 prefixEnd_3811557 1304773855339499332938983 := by
  unfold tailWord_3811557
  simp only [CollatzResearch.WordTrace]
  refine ⟨139018904652387425954968925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92679269768258283969979283 139018904652387425954968925)
  ·
    refine ⟨52132089244645284733113347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139018904652387425954968925 52132089244645284733113347)
    ·
      refine ⟨78198133866967927099670021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52132089244645284733113347 78198133866967927099670021)
      ·
        refine ⟨14662150100056486331188129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78198133866967927099670021 14662150100056486331188129)
        ·
          refine ⟨10996612575042364748391097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14662150100056486331188129 10996612575042364748391097)
          ·
            refine ⟨8247459431281773561293323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10996612575042364748391097 8247459431281773561293323)
            ·
              refine ⟨12371189146922660341939985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8247459431281773561293323 12371189146922660341939985)
              ·
                refine ⟨9278391860191995256454989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12371189146922660341939985 9278391860191995256454989)
                ·
                  refine ⟨3479396947571998221170621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9278391860191995256454989 3479396947571998221170621)
                  ·
                    refine ⟨1304773855339499332938983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3479396947571998221170621 1304773855339499332938983)
                    ·
                      rfl

theorem cell22_3811557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 3, 3].length) (baseStart_3811557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3811557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3811557 prefixEnd_3811557 := by exact prefixLift 3811557
  have htrace : WordTrace (prefixWord ++ tailWord_3811557) baseStart_3811557 baseEnd_3811557 := by
    simpa [prefixWord, tailWord_3811557, baseEnd_3811557] using wordTrace_append hprefix tailTrace_3811557
  have hstable : (prefixWord ++ tailWord_3811557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811557).length < 2 ^ (prefixWord ++ tailWord_3811557).sum := by decide
  have hdescent : baseEnd_3811557 < baseStart_3811557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811574 : List Nat := [5, 1, 1, 1, 1, 1, 3, 5, 1, 3]
def baseStart_3811574 : Nat := 118140960795 + 3811574 * 2 ^ 59
def prefixEnd_3811574 : Nat := 4983230072969 + 3 ^ 40 * 3811574 * 2
def baseEnd_3811574 : Nat := 1304779674786916955263931

theorem tailTrace_3811574 : CollatzResearch.WordTrace tailWord_3811574 prefixEnd_3811574 1304779674786916955263931 := by
  unfold tailWord_3811574
  simp only [CollatzResearch.WordTrace]
  refine ⟨8688720293332864866146111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92679683128883891905558517 8688720293332864866146111)
  ·
    refine ⟨13033080439999297299219167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8688720293332864866146111 13033080439999297299219167)
    ·
      refine ⟨19549620659998945948828751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13033080439999297299219167 19549620659998945948828751)
      ·
        refine ⟨29324430989998418923243127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19549620659998945948828751 29324430989998418923243127)
        ·
          refine ⟨43986646484997628384864691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29324430989998418923243127 43986646484997628384864691)
          ·
            refine ⟨65979969727496442577297037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43986646484997628384864691 65979969727496442577297037)
            ·
              refine ⟨24742488647811165966486389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65979969727496442577297037 24742488647811165966486389)
              ·
                refine ⟨2319608310732296809358099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24742488647811165966486389 2319608310732296809358099)
                ·
                  refine ⟨3479412466098445214037149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2319608310732296809358099 3479412466098445214037149)
                  ·
                    refine ⟨1304779674786916955263931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3479412466098445214037149 1304779674786916955263931)
                    ·
                      rfl

theorem cell22_3811574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_3811574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3811574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3811574 prefixEnd_3811574 := by exact prefixLift 3811574
  have htrace : WordTrace (prefixWord ++ tailWord_3811574) baseStart_3811574 baseEnd_3811574 := by
    simpa [prefixWord, tailWord_3811574, baseEnd_3811574] using wordTrace_append hprefix tailTrace_3811574
  have hstable : (prefixWord ++ tailWord_3811574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811574).length < 2 ^ (prefixWord ++ tailWord_3811574).sum := by decide
  have hdescent : baseEnd_3811574 < baseStart_3811574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811615 : List Nat := [1, 1, 2, 4, 3, 1, 2, 2, 6]
def baseStart_3811615 : Nat := 118140960795 + 3811615 * 2 ^ 59
def prefixEnd_3811615 : Nat := 4983230072969 + 3 ^ 40 * 3811615 * 2
def baseEnd_3811615 : Nat := 434931236641602171662935

theorem tailTrace_3811615 : CollatzResearch.WordTrace tailWord_3811615 prefixEnd_3811615 434931236641602171662935 := by
  unfold tailWord_3811615
  simp only [CollatzResearch.WordTrace]
  refine ⟨139021020086177301860580299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92680680057451534573720199 139021020086177301860580299)
  ·
    refine ⟨208531530129265952790870449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139021020086177301860580299 208531530129265952790870449)
    ·
      refine ⟨156398647596949464593152837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208531530129265952790870449 156398647596949464593152837)
      ·
        refine ⟨29324746424428024611216157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156398647596949464593152837 29324746424428024611216157)
        ·
          refine ⟨10996779909160509229206059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29324746424428024611216157 10996779909160509229206059)
          ·
            refine ⟨16495169863740763843809089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10996779909160509229206059 16495169863740763843809089)
            ·
              refine ⟨12371377397805572882856817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16495169863740763843809089 12371377397805572882856817)
              ·
                refine ⟨9278533048354179662142613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12371377397805572882856817 9278533048354179662142613)
                ·
                  refine ⟨434931236641602171662935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9278533048354179662142613 434931236641602171662935)
                  ·
                    rfl

theorem cell22_3811615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 6].length) (baseStart_3811615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3811615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3811615 prefixEnd_3811615 := by exact prefixLift 3811615
  have htrace : WordTrace (prefixWord ++ tailWord_3811615) baseStart_3811615 baseEnd_3811615 := by
    simpa [prefixWord, tailWord_3811615, baseEnd_3811615] using wordTrace_append hprefix tailTrace_3811615
  have hstable : (prefixWord ++ tailWord_3811615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811615).length < 2 ^ (prefixWord ++ tailWord_3811615).sum := by decide
  have hdescent : baseEnd_3811615 < baseStart_3811615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811647 : List Nat := [1, 1, 2, 2, 4, 1, 2, 4, 2, 3]
def baseStart_3811647 : Nat := 118140960795 + 3811647 * 2 ^ 59
def prefixEnd_3811647 : Nat := 4983230072969 + 3 ^ 40 * 3811647 * 2
def baseEnd_3811647 : Nat := 1304804664178769098188707

theorem tailTrace_3811647 : CollatzResearch.WordTrace tailWord_3811647 prefixEnd_3811647 1304804664178769098188707 := by
  unfold tailWord_3811647
  simp only [CollatzResearch.WordTrace]
  refine ⟨139022187222061371325745195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92681458148040914217163463 139022187222061371325745195)
  ·
    refine ⟨208533280833092056988617793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139022187222061371325745195 208533280833092056988617793)
    ·
      refine ⟨156399960624819042741463345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208533280833092056988617793 156399960624819042741463345)
      ·
        refine ⟨117299970468614282056097509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156399960624819042741463345 117299970468614282056097509)
        ·
          refine ⟨21993744462865177885518283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117299970468614282056097509 21993744462865177885518283)
          ·
            refine ⟨32990616694297766828277425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21993744462865177885518283 32990616694297766828277425)
            ·
              refine ⟨24742962520723325121208069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32990616694297766828277425 24742962520723325121208069)
              ·
                refine ⟨4639305472635623460226513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24742962520723325121208069 4639305472635623460226513)
                ·
                  refine ⟨3479479104476717595169885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4639305472635623460226513 3479479104476717595169885)
                  ·
                    refine ⟨1304804664178769098188707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3479479104476717595169885 1304804664178769098188707)
                    ·
                      rfl

theorem cell22_3811647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 2, 3].length) (baseStart_3811647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3811647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3811647 prefixEnd_3811647 := by exact prefixLift 3811647
  have htrace : WordTrace (prefixWord ++ tailWord_3811647) baseStart_3811647 baseEnd_3811647 := by
    simpa [prefixWord, tailWord_3811647, baseEnd_3811647] using wordTrace_append hprefix tailTrace_3811647
  have hstable : (prefixWord ++ tailWord_3811647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811647).length < 2 ^ (prefixWord ++ tailWord_3811647).sum := by decide
  have hdescent : baseEnd_3811647 < baseStart_3811647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811649 : List Nat := [1, 2, 5, 2, 2, 2, 1, 1, 6]
def baseStart_3811649 : Nat := 118140960795 + 3811649 * 2 ^ 59
def prefixEnd_3811649 : Nat := 4983230072969 + 3 ^ 40 * 3811649 * 2
def baseEnd_3811649 : Nat := 434935116273213919879567

theorem tailTrace_3811649 : CollatzResearch.WordTrace tailWord_3811649 prefixEnd_3811649 434935116273213919879567 := by
  unfold tailWord_3811649
  simp only [CollatzResearch.WordTrace]
  refine ⟨139022260168054125667318001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92681506778702750444878667 139022260168054125667318001)
  ·
    refine ⟨104266695126040594250488501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139022260168054125667318001 104266695126040594250488501)
    ·
      refine ⟨9775002668066305710983297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104266695126040594250488501 9775002668066305710983297)
      ·
        refine ⟨7331252001049729283237473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9775002668066305710983297 7331252001049729283237473)
        ·
          refine ⟨5498439000787296962428105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7331252001049729283237473 5498439000787296962428105)
          ·
            refine ⟨4123829250590472721821079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5498439000787296962428105 4123829250590472721821079)
            ·
              refine ⟨6185743875885709082731619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4123829250590472721821079 6185743875885709082731619)
              ·
                refine ⟨9278615813828563624097429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6185743875885709082731619 9278615813828563624097429)
                ·
                  refine ⟨434935116273213919879567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9278615813828563624097429 434935116273213919879567)
                  ·
                    rfl

theorem cell22_3811649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 6].length) (baseStart_3811649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3811649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3811649 prefixEnd_3811649 := by exact prefixLift 3811649
  have htrace : WordTrace (prefixWord ++ tailWord_3811649) baseStart_3811649 baseEnd_3811649 := by
    simpa [prefixWord, tailWord_3811649, baseEnd_3811649] using wordTrace_append hprefix tailTrace_3811649
  have hstable : (prefixWord ++ tailWord_3811649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811649).length < 2 ^ (prefixWord ++ tailWord_3811649).sum := by decide
  have hdescent : baseEnd_3811649 < baseStart_3811649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811660 : List Nat := [2, 2, 1, 3, 2, 1, 4, 7]
def baseStart_3811660 : Nat := 118140960795 + 3811660 * 2 ^ 59
def prefixEnd_3811660 : Nat := 4983230072969 + 3 ^ 40 * 3811660 * 2
def baseEnd_3811660 : Nat := 144978790482715710845963

theorem tailTrace_3811660 : CollatzResearch.WordTrace tailWord_3811660 prefixEnd_3811660 144978790482715710845963 := by
  unfold tailWord_3811660
  simp only [CollatzResearch.WordTrace]
  refine ⟨69511330685507137272984217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92681774247342849697312289 69511330685507137272984217)
  ·
    refine ⟨52133498014130352954738163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69511330685507137272984217 52133498014130352954738163)
    ·
      refine ⟨78200247021195529432107245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52133498014130352954738163 78200247021195529432107245)
      ·
        refine ⟨29325092632948323537040217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78200247021195529432107245 29325092632948323537040217)
        ·
          refine ⟨21993819474711242652780163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29325092632948323537040217 21993819474711242652780163)
          ·
            refine ⟨32990729212066863979170245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21993819474711242652780163 32990729212066863979170245)
            ·
              refine ⟨6185761727262536996094421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32990729212066863979170245 6185761727262536996094421)
              ·
                refine ⟨144978790482715710845963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6185761727262536996094421 144978790482715710845963)
                ·
                  rfl

theorem cell22_3811660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 7].length) (baseStart_3811660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3811660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3811660 prefixEnd_3811660 := by exact prefixLift 3811660
  have htrace : WordTrace (prefixWord ++ tailWord_3811660) baseStart_3811660 baseEnd_3811660 := by
    simpa [prefixWord, tailWord_3811660, baseEnd_3811660] using wordTrace_append hprefix tailTrace_3811660
  have hstable : (prefixWord ++ tailWord_3811660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811660).length < 2 ^ (prefixWord ++ tailWord_3811660).sum := by decide
  have hdescent : baseEnd_3811660 < baseStart_3811660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811664 : List Nat := [2, 1, 1, 1, 1, 6, 4, 1, 2, 3]
def baseStart_3811664 : Nat := 118140960795 + 3811664 * 2 ^ 59
def prefixEnd_3811664 : Nat := 4983230072969 + 3 ^ 40 * 3811664 * 2
def baseEnd_3811664 : Nat := 1304810483626186720513655

theorem tailTrace_3811664 : CollatzResearch.WordTrace tailWord_3811664 prefixEnd_3811664 1304810483626186720513655 := by
  unfold tailWord_3811664
  simp only [CollatzResearch.WordTrace]
  refine ⟨69511403631499891614557023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92681871508666522152742697 69511403631499891614557023)
  ·
    refine ⟨104267105447249837421835535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69511403631499891614557023 104267105447249837421835535)
    ·
      refine ⟨156400658170874756132753303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104267105447249837421835535 156400658170874756132753303)
      ·
        refine ⟨234600987256312134199129955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156400658170874756132753303 234600987256312134199129955)
        ·
          refine ⟨351901480884468201298694933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234600987256312134199129955 351901480884468201298694933)
          ·
            refine ⟨16495381916459446935876325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 351901480884468201298694933 16495381916459446935876325)
            ·
              refine ⟨3092884109336146300476811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16495381916459446935876325 3092884109336146300476811)
              ·
                refine ⟨4639326164004219450715217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3092884109336146300476811 4639326164004219450715217)
                ·
                  refine ⟨3479494623003164588036413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4639326164004219450715217 3479494623003164588036413)
                  ·
                    refine ⟨1304810483626186720513655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3479494623003164588036413 1304810483626186720513655)
                    ·
                      rfl

theorem cell22_3811664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 2, 3].length) (baseStart_3811664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3811664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3811664 prefixEnd_3811664 := by exact prefixLift 3811664
  have htrace : WordTrace (prefixWord ++ tailWord_3811664) baseStart_3811664 baseEnd_3811664 := by
    simpa [prefixWord, tailWord_3811664, baseEnd_3811664] using wordTrace_append hprefix tailTrace_3811664
  have hstable : (prefixWord ++ tailWord_3811664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811664).length < 2 ^ (prefixWord ++ tailWord_3811664).sum := by decide
  have hdescent : baseEnd_3811664 < baseStart_3811664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811767 : List Nat := [1, 1, 3, 1, 3, 4, 2, 1, 6]
def baseStart_3811767 : Nat := 118140960795 + 3811767 * 2 ^ 59
def prefixEnd_3811767 : Nat := 4983230072969 + 3 ^ 40 * 3811767 * 2
def baseEnd_3811767 : Nat := 434948580877042928396113

theorem tailTrace_3811767 : CollatzResearch.WordTrace tailWord_3811767 prefixEnd_3811767 434948580877042928396113 := by
  unfold tailWord_3811767
  simp only [CollatzResearch.WordTrace]
  refine ⟨139026563981626631820113555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92684375987751087880075703 139026563981626631820113555)
  ·
    refine ⟨208539845972439947730170333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139026563981626631820113555 208539845972439947730170333)
    ·
      refine ⟨78202442239664980398813875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208539845972439947730170333 78202442239664980398813875)
      ·
        refine ⟨117303663359497470598220813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78202442239664980398813875 117303663359497470598220813)
        ·
          refine ⟨43988873759811551474332805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117303663359497470598220813 43988873759811551474332805)
          ·
            refine ⟨8247913829964665901437401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43988873759811551474332805 8247913829964665901437401)
            ·
              refine ⟨6185935372473499426078051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8247913829964665901437401 6185935372473499426078051)
              ·
                refine ⟨9278903058710249139117077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6185935372473499426078051 9278903058710249139117077)
                ·
                  refine ⟨434948580877042928396113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9278903058710249139117077 434948580877042928396113)
                  ·
                    rfl

theorem cell22_3811767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 6].length) (baseStart_3811767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3811767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3811767 prefixEnd_3811767 := by exact prefixLift 3811767
  have htrace : WordTrace (prefixWord ++ tailWord_3811767) baseStart_3811767 baseEnd_3811767 := by
    simpa [prefixWord, tailWord_3811767, baseEnd_3811767] using wordTrace_append hprefix tailTrace_3811767
  have hstable : (prefixWord ++ tailWord_3811767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811767).length < 2 ^ (prefixWord ++ tailWord_3811767).sum := by decide
  have hdescent : baseEnd_3811767 < baseStart_3811767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811797 : List Nat := [1, 3, 2, 3, 1, 2, 2, 1, 1, 6]
def baseStart_3811797 : Nat := 118140960795 + 3811797 * 2 ^ 59
def prefixEnd_3811797 : Nat := 4983230072969 + 3 ^ 40 * 3811797 * 2
def baseEnd_3811797 : Nat := 1304856012244218706938247

theorem tailTrace_3811797 : CollatzResearch.WordTrace tailWord_3811797 prefixEnd_3811797 1304856012244218706938247 := by
  unfold tailWord_3811797
  simp only [CollatzResearch.WordTrace]
  refine ⟨139027658171517946943705645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92685105447678631295803763 139027658171517946943705645)
  ·
    refine ⟨52135371814319230103889617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139027658171517946943705645 52135371814319230103889617)
    ·
      refine ⟨39101528860739422577917213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52135371814319230103889617 39101528860739422577917213)
      ·
        refine ⟨14663073322777283466718955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39101528860739422577917213 14663073322777283466718955)
        ·
          refine ⟨21994609984165925200078433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14663073322777283466718955 21994609984165925200078433)
          ·
            refine ⟨16495957488124443900058825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21994609984165925200078433 16495957488124443900058825)
            ·
              refine ⟨12371968116093332925044119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16495957488124443900058825 12371968116093332925044119)
              ·
                refine ⟨18557952174139999387566179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12371968116093332925044119 18557952174139999387566179)
                ·
                  refine ⟨27836928261209999081349269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18557952174139999387566179 27836928261209999081349269)
                  ·
                    refine ⟨1304856012244218706938247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27836928261209999081349269 1304856012244218706938247)
                    ·
                      rfl

theorem cell22_3811797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_3811797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3811797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3811797 prefixEnd_3811797 := by exact prefixLift 3811797
  have htrace : WordTrace (prefixWord ++ tailWord_3811797) baseStart_3811797 baseEnd_3811797 := by
    simpa [prefixWord, tailWord_3811797, baseEnd_3811797] using wordTrace_append hprefix tailTrace_3811797
  have hstable : (prefixWord ++ tailWord_3811797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811797).length < 2 ^ (prefixWord ++ tailWord_3811797).sum := by decide
  have hdescent : baseEnd_3811797 < baseStart_3811797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811861 : List Nat := [1, 3, 2, 1, 3, 1, 2, 5, 1, 3]
def baseStart_3811861 : Nat := 118140960795 + 3811861 * 2 ^ 59
def prefixEnd_3811861 : Nat := 4983230072969 + 3 ^ 40 * 3811861 * 2
def baseEnd_3811861 : Nat := 1304877920752143873338051

theorem tailTrace_3811861 : CollatzResearch.WordTrace tailWord_3811861 prefixEnd_3811861 1304877920752143873338051 := by
  unfold tailWord_3811861
  simp only [CollatzResearch.WordTrace]
  refine ⟨139029992443286085874035437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92686661628857390582690291 139029992443286085874035437)
  ·
    refine ⟨52136247166232282202763289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139029992443286085874035437 52136247166232282202763289)
    ·
      refine ⟨39102185374674211652072467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52136247166232282202763289 39102185374674211652072467)
      ·
        refine ⟨58653278062011317478108701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39102185374674211652072467 58653278062011317478108701)
        ·
          refine ⟨21994979273254244054290763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58653278062011317478108701 21994979273254244054290763)
          ·
            refine ⟨32992468909881366081436145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21994979273254244054290763 32992468909881366081436145)
            ·
              refine ⟨24744351682411024561077109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32992468909881366081436145 24744351682411024561077109)
              ·
                refine ⟨2319782970226033552600979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24744351682411024561077109 2319782970226033552600979)
                ·
                  refine ⟨3479674455339050328901469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2319782970226033552600979 3479674455339050328901469)
                  ·
                    refine ⟨1304877920752143873338051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3479674455339050328901469 1304877920752143873338051)
                    ·
                      rfl

theorem cell22_3811861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 5, 1, 3].length) (baseStart_3811861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3811861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3811861 prefixEnd_3811861 := by exact prefixLift 3811861
  have htrace : WordTrace (prefixWord ++ tailWord_3811861) baseStart_3811861 baseEnd_3811861 := by
    simpa [prefixWord, tailWord_3811861, baseEnd_3811861] using wordTrace_append hprefix tailTrace_3811861
  have hstable : (prefixWord ++ tailWord_3811861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811861).length < 2 ^ (prefixWord ++ tailWord_3811861).sum := by decide
  have hdescent : baseEnd_3811861 < baseStart_3811861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811919 : List Nat := [1, 1, 2, 1, 1, 2, 5, 5, 4]
def baseStart_3811919 : Nat := 118140960795 + 3811919 * 2 ^ 59
def prefixEnd_3811919 : Nat := 4983230072969 + 3 ^ 40 * 3811919 * 2
def baseEnd_3811919 : Nat := 434965925112483685129291

theorem tailTrace_3811919 : CollatzResearch.WordTrace tailWord_3811919 prefixEnd_3811919 434965925112483685129291 := by
  unfold tailWord_3811919
  simp only [CollatzResearch.WordTrace]
  refine ⟨139032107877075961779646811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92688071918050641186431207 139032107877075961779646811)
  ·
    refine ⟨208548161815613942669470217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139032107877075961779646811 208548161815613942669470217)
    ·
      refine ⟨156411121361710457002102663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208548161815613942669470217 156411121361710457002102663)
      ·
        refine ⟨234616682042565685503153995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156411121361710457002102663 234616682042565685503153995)
        ·
          refine ⟨351925023063848528254730993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234616682042565685503153995 351925023063848528254730993)
          ·
            refine ⟨263943767297886396191048245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351925023063848528254730993 263943767297886396191048245)
            ·
              refine ⟨24744728184176849642910773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 263943767297886396191048245 24744728184176849642910773)
              ·
                refine ⟨2319818267266579654022885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24744728184176849642910773 2319818267266579654022885)
                ·
                  refine ⟨434965925112483685129291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2319818267266579654022885 434965925112483685129291)
                  ·
                    rfl

theorem cell22_3811919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 5, 4].length) (baseStart_3811919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3811919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3811919 prefixEnd_3811919 := by exact prefixLift 3811919
  have htrace : WordTrace (prefixWord ++ tailWord_3811919) baseStart_3811919 baseEnd_3811919 := by
    simpa [prefixWord, tailWord_3811919, baseEnd_3811919] using wordTrace_append hprefix tailTrace_3811919
  have hstable : (prefixWord ++ tailWord_3811919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811919).length < 2 ^ (prefixWord ++ tailWord_3811919).sum := by decide
  have hdescent : baseEnd_3811919 < baseStart_3811919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811921 : List Nat := [1, 2, 2, 1, 3, 3, 4, 1, 1, 4]
def baseStart_3811921 : Nat := 118140960795 + 3811921 * 2 ^ 59
def prefixEnd_3811921 : Nat := 4983230072969 + 3 ^ 40 * 3811921 * 2
def baseEnd_3811921 : Nat := 1304898459978323716837867

theorem tailTrace_3811921 : CollatzResearch.WordTrace tailWord_3811921 prefixEnd_3811921 1304898459978323716837867 := by
  unfold tailWord_3811921
  simp only [CollatzResearch.WordTrace]
  refine ⟨139032180823068716121219617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92688120548712477414146411 139032180823068716121219617)
  ·
    refine ⟨104274135617301537090914713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139032180823068716121219617 104274135617301537090914713)
    ·
      refine ⟨78205601712976152818186035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104274135617301537090914713 78205601712976152818186035)
      ·
        refine ⟨117308402569464229227279053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78205601712976152818186035 117308402569464229227279053)
        ·
          refine ⟨43990650963549085960229645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117308402569464229227279053 43990650963549085960229645)
          ·
            refine ⟨16496494111330907235086117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43990650963549085960229645 16496494111330907235086117)
            ·
              refine ⟨3093092645874545106578647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16496494111330907235086117 3093092645874545106578647)
              ·
                refine ⟨4639638968811817659867971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3093092645874545106578647 4639638968811817659867971)
                ·
                  refine ⟨6959458453217726489801957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4639638968811817659867971 6959458453217726489801957)
                  ·
                    refine ⟨1304898459978323716837867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6959458453217726489801957 1304898459978323716837867)
                    ·
                      rfl

theorem cell22_3811921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 1, 4].length) (baseStart_3811921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3811921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3811921 prefixEnd_3811921 := by exact prefixLift 3811921
  have htrace : WordTrace (prefixWord ++ tailWord_3811921) baseStart_3811921 baseEnd_3811921 := by
    simpa [prefixWord, tailWord_3811921, baseEnd_3811921] using wordTrace_append hprefix tailTrace_3811921
  have hstable : (prefixWord ++ tailWord_3811921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811921).length < 2 ^ (prefixWord ++ tailWord_3811921).sum := by decide
  have hdescent : baseEnd_3811921 < baseStart_3811921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811949 : List Nat := [1, 5, 1, 1, 3, 1, 1, 2, 1, 6]
def baseStart_3811949 : Nat := 118140960795 + 3811949 * 2 ^ 59
def prefixEnd_3811949 : Nat := 4983230072969 + 3 ^ 40 * 3811949 * 2
def baseEnd_3811949 : Nat := 1304908044950540977137781

theorem tailTrace_3811949 : CollatzResearch.WordTrace tailWord_3811949 prefixEnd_3811949 1304908044950540977137781 := by
  unfold tailWord_3811949
  simp only [CollatzResearch.WordTrace]
  refine ⟨139033202066967276903238901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92688801377978184602159267 139033202066967276903238901)
  ·
    refine ⟨13034362693778182209678647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139033202066967276903238901 13034362693778182209678647)
    ·
      refine ⟨19551544040667273314517971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13034362693778182209678647 19551544040667273314517971)
      ·
        refine ⟨29327316061000909971776957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19551544040667273314517971 29327316061000909971776957)
        ·
          refine ⟨10997743522875341239416359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29327316061000909971776957 10997743522875341239416359)
          ·
            refine ⟨16496615284313011859124539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10997743522875341239416359 16496615284313011859124539)
            ·
              refine ⟨24744922926469517788686809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16496615284313011859124539 24744922926469517788686809)
              ·
                refine ⟨18558692194852138341515107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24744922926469517788686809 18558692194852138341515107)
                ·
                  refine ⟨27838038292278207512272661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18558692194852138341515107 27838038292278207512272661)
                  ·
                    refine ⟨1304908044950540977137781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27838038292278207512272661 1304908044950540977137781)
                    ·
                      rfl

theorem cell22_3811949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_3811949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3811949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3811949 prefixEnd_3811949 := by exact prefixLift 3811949
  have htrace : WordTrace (prefixWord ++ tailWord_3811949) baseStart_3811949 baseEnd_3811949 := by
    simpa [prefixWord, tailWord_3811949, baseEnd_3811949] using wordTrace_append hprefix tailTrace_3811949
  have hstable : (prefixWord ++ tailWord_3811949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811949).length < 2 ^ (prefixWord ++ tailWord_3811949).sum := by decide
  have hdescent : baseEnd_3811949 < baseStart_3811949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811964 : List Nat := [2, 2, 2, 1, 1, 2, 6, 6]
def baseStart_3811964 : Nat := 118140960795 + 3811964 * 2 ^ 59
def prefixEnd_3811964 : Nat := 4983230072969 + 3 ^ 40 * 3811964 * 2
def baseEnd_3811964 : Nat := 144990353306342882001415

theorem tailTrace_3811964 : CollatzResearch.WordTrace tailWord_3811964 prefixEnd_3811964 144990353306342882001415 := by
  unfold tailWord_3811964
  simp only [CollatzResearch.WordTrace]
  refine ⟨69516874580956467232517473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92689166107941956310023297 69516874580956467232517473)
  ·
    refine ⟨52137655935717350424388105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69516874580956467232517473 52137655935717350424388105)
    ·
      refine ⟨39103241951788012818291079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52137655935717350424388105 39103241951788012818291079)
      ·
        refine ⟨58654862927682019227436619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39103241951788012818291079 58654862927682019227436619)
        ·
          refine ⟨87982294391523028841154929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58654862927682019227436619 87982294391523028841154929)
          ·
            refine ⟨65986720793642271630866197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87982294391523028841154929 65986720793642271630866197)
            ·
              refine ⟨3093127537201981482696853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 65986720793642271630866197 3093127537201981482696853)
              ·
                refine ⟨144990353306342882001415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3093127537201981482696853 144990353306342882001415)
                ·
                  rfl

theorem cell22_3811964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 6].length) (baseStart_3811964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3811964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3811964 prefixEnd_3811964 := by exact prefixLift 3811964
  have htrace : WordTrace (prefixWord ++ tailWord_3811964) baseStart_3811964 baseEnd_3811964 := by
    simpa [prefixWord, tailWord_3811964, baseEnd_3811964] using wordTrace_append hprefix tailTrace_3811964
  have hstable : (prefixWord ++ tailWord_3811964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811964).length < 2 ^ (prefixWord ++ tailWord_3811964).sum := by decide
  have hdescent : baseEnd_3811964 < baseStart_3811964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3811977 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 1, 8]
def baseStart_3811977 : Nat := 118140960795 + 3811977 * 2 ^ 59
def prefixEnd_3811977 : Nat := 4983230072969 + 3 ^ 40 * 3811977 * 2
def baseEnd_3811977 : Nat := 1304917629922758237437695

theorem tailTrace_3811977 : CollatzResearch.WordTrace tailWord_3811977 prefixEnd_3811977 1304917629922758237437695 := by
  unfold tailWord_3811977
  simp only [CollatzResearch.WordTrace]
  refine ⟨139034223310865837685258185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92689482207243891790172123 139034223310865837685258185)
  ·
    refine ⟨104275667483149378263943639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139034223310865837685258185 104275667483149378263943639)
    ·
      refine ⟨156413501224724067395915459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104275667483149378263943639 156413501224724067395915459)
      ·
        refine ⟨234620251837086101093873189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156413501224724067395915459 234620251837086101093873189)
        ·
          refine ⟨43991297219453643955101223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234620251837086101093873189 43991297219453643955101223)
          ·
            refine ⟨65986945829180465932651835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43991297219453643955101223 65986945829180465932651835)
            ·
              refine ⟨98980418743770698898977753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65986945829180465932651835 98980418743770698898977753)
              ·
                refine ⟨74235314057828024174233315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98980418743770698898977753 74235314057828024174233315)
                ·
                  refine ⟨111352971086742036261349973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74235314057828024174233315 111352971086742036261349973)
                  ·
                    refine ⟨1304917629922758237437695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111352971086742036261349973 1304917629922758237437695)
                    ·
                      rfl

theorem cell22_3811977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 8].length) (baseStart_3811977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3811977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3811977 prefixEnd_3811977 := by exact prefixLift 3811977
  have htrace : WordTrace (prefixWord ++ tailWord_3811977) baseStart_3811977 baseEnd_3811977 := by
    simpa [prefixWord, tailWord_3811977, baseEnd_3811977] using wordTrace_append hprefix tailTrace_3811977
  have hstable : (prefixWord ++ tailWord_3811977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3811977).length < 2 ^ (prefixWord ++ tailWord_3811977).sum := by decide
  have hdescent : baseEnd_3811977 < baseStart_3811977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3811977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812086 : List Nat := [5, 1, 1, 1, 1, 2, 1, 4, 1, 5]
def baseStart_3812086 : Nat := 118140960795 + 3812086 * 2 ^ 59
def prefixEnd_3812086 : Nat := 4983230072969 + 3 ^ 40 * 3812086 * 2
def baseEnd_3812086 : Nat := 1304954942850318286462361

theorem tailTrace_3812086 : CollatzResearch.WordTrace tailWord_3812086 prefixEnd_3812086 1304954942850318286462361 := by
  unfold tailWord_3812086
  simp only [CollatzResearch.WordTrace]
  refine ⟨8689887429216934331311007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92692132578313966200650741 8689887429216934331311007)
  ·
    refine ⟨13034831143825401496966511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8689887429216934331311007 13034831143825401496966511)
    ·
      refine ⟨19552246715738102245449767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13034831143825401496966511 19552246715738102245449767)
      ·
        refine ⟨29328370073607153368174651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19552246715738102245449767 29328370073607153368174651)
        ·
          refine ⟨43992555110410730052261977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29328370073607153368174651 43992555110410730052261977)
          ·
            refine ⟨32994416332808047539196483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43992555110410730052261977 32994416332808047539196483)
            ·
              refine ⟨49491624499212071308794725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32994416332808047539196483 49491624499212071308794725)
              ·
                refine ⟨9279679593602263370399011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49491624499212071308794725 9279679593602263370399011)
                ·
                  refine ⟨13919519390403395055598517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9279679593602263370399011 13919519390403395055598517)
                  ·
                    refine ⟨1304954942850318286462361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13919519390403395055598517 1304954942850318286462361)
                    ·
                      rfl

theorem cell22_3812086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_3812086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3812086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3812086 prefixEnd_3812086 := by exact prefixLift 3812086
  have htrace : WordTrace (prefixWord ++ tailWord_3812086) baseStart_3812086 baseEnd_3812086 := by
    simpa [prefixWord, tailWord_3812086, baseEnd_3812086] using wordTrace_append hprefix tailTrace_3812086
  have hstable : (prefixWord ++ tailWord_3812086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812086).length < 2 ^ (prefixWord ++ tailWord_3812086).sum := by decide
  have hdescent : baseEnd_3812086 < baseStart_3812086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812103 : List Nat := [1, 1, 4, 4, 1, 2, 1, 1, 4, 3]
def baseStart_3812103 : Nat := 118140960795 + 3812103 * 2 ^ 59
def prefixEnd_3812103 : Nat := 4983230072969 + 3 ^ 40 * 3812103 * 2
def baseEnd_3812103 : Nat := 1304960762297735908787309

theorem tailTrace_3812103 : CollatzResearch.WordTrace tailWord_3812103 prefixEnd_3812103 1304960762297735908787309 := by
  unfold tailWord_3812103
  simp only [CollatzResearch.WordTrace]
  refine ⟨139038818908409361204344963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92692545938939574136229975 139038818908409361204344963)
  ·
    refine ⟨208558228362614041806517445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139038818908409361204344963 208558228362614041806517445)
    ·
      refine ⟨39104667817990132838722021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208558228362614041806517445 39104667817990132838722021)
      ·
        refine ⟨7332125215873149907260379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39104667817990132838722021 7332125215873149907260379)
        ·
          refine ⟨10998187823809724860890569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7332125215873149907260379 10998187823809724860890569)
          ·
            refine ⟨8248640867857293645667927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10998187823809724860890569 8248640867857293645667927)
            ·
              refine ⟨12372961301785940468501891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8248640867857293645667927 12372961301785940468501891)
              ·
                refine ⟨18559441952678910702752837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12372961301785940468501891 18559441952678910702752837)
                ·
                  refine ⟨3479895366127295756766157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18559441952678910702752837 3479895366127295756766157)
                  ·
                    refine ⟨1304960762297735908787309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3479895366127295756766157 1304960762297735908787309)
                    ·
                      rfl

theorem cell22_3812103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_3812103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3812103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3812103 prefixEnd_3812103 := by exact prefixLift 3812103
  have htrace : WordTrace (prefixWord ++ tailWord_3812103) baseStart_3812103 baseEnd_3812103 := by
    simpa [prefixWord, tailWord_3812103, baseEnd_3812103] using wordTrace_append hprefix tailTrace_3812103
  have hstable : (prefixWord ++ tailWord_3812103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812103).length < 2 ^ (prefixWord ++ tailWord_3812103).sum := by decide
  have hdescent : baseEnd_3812103 < baseStart_3812103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812150 : List Nat := [5, 1, 2, 2, 3, 1, 8]
def baseStart_3812150 : Nat := 118140960795 + 3812150 * 2 ^ 59
def prefixEnd_3812150 : Nat := 4983230072969 + 3 ^ 40 * 3812150 * 2
def baseEnd_3812150 : Nat := 48332475976231238994895

theorem tailTrace_3812150 : CollatzResearch.WordTrace tailWord_3812150 prefixEnd_3812150 48332475976231238994895 := by
  unfold tailWord_3812150
  simp only [CollatzResearch.WordTrace]
  refine ⟨8690033321202443014456619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92693688759492725487537269 8690033321202443014456619)
  ·
    refine ⟨13035049981803664521684929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8690033321202443014456619 13035049981803664521684929)
    ·
      refine ⟨9776287486352748391263697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13035049981803664521684929 9776287486352748391263697)
      ·
        refine ⟨7332215614764561293447773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9776287486352748391263697 7332215614764561293447773)
        ·
          refine ⟨2749580855536710485042915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7332215614764561293447773 2749580855536710485042915)
          ·
            refine ⟨4124371283305065727564373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2749580855536710485042915 4124371283305065727564373)
            ·
              refine ⟨48332475976231238994895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4124371283305065727564373 48332475976231238994895)
              ·
                rfl

theorem cell22_3812150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 8].length) (baseStart_3812150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3812150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3812150 prefixEnd_3812150 := by exact prefixLift 3812150
  have htrace : WordTrace (prefixWord ++ tailWord_3812150) baseStart_3812150 baseEnd_3812150 := by
    simpa [prefixWord, tailWord_3812150, baseEnd_3812150] using wordTrace_append hprefix tailTrace_3812150
  have hstable : (prefixWord ++ tailWord_3812150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812150).length < 2 ^ (prefixWord ++ tailWord_3812150).sum := by decide
  have hdescent : baseEnd_3812150 < baseStart_3812150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812191 : List Nat := [1, 1, 2, 3, 1, 3, 3, 1, 3, 4]
def baseStart_3812191 : Nat := 118140960795 + 3812191 * 2 ^ 59
def prefixEnd_3812191 : Nat := 4983230072969 + 3 ^ 40 * 3812191 * 2
def baseEnd_3812191 : Nat := 1304990886496133012587039

theorem tailTrace_3812191 : CollatzResearch.WordTrace tailWord_3812191 prefixEnd_3812191 1304990886496133012587039 := by
  unfold tailWord_3812191
  simp only [CollatzResearch.WordTrace]
  refine ⟨139042028532090552233548427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92694685688060368155698951 139042028532090552233548427)
  ·
    refine ⟨208563042798135828350322641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139042028532090552233548427 208563042798135828350322641)
    ·
      refine ⟨156422282098601871262741981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208563042798135828350322641 156422282098601871262741981)
      ·
        refine ⟨58658355786975701723528243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156422282098601871262741981 58658355786975701723528243)
        ·
          refine ⟨87987533680463552585292365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58658355786975701723528243 87987533680463552585292365)
          ·
            refine ⟨32995325130173832219484637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87987533680463552585292365 32995325130173832219484637)
            ·
              refine ⟨12373246923815187082306739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32995325130173832219484637 12373246923815187082306739)
              ·
                refine ⟨18559870385722780623460109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12373246923815187082306739 18559870385722780623460109)
                ·
                  refine ⟨6959951394646042733797541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18559870385722780623460109 6959951394646042733797541)
                  ·
                    refine ⟨1304990886496133012587039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6959951394646042733797541 1304990886496133012587039)
                    ·
                      rfl

theorem cell22_3812191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 4].length) (baseStart_3812191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3812191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3812191 prefixEnd_3812191 := by exact prefixLift 3812191
  have htrace : WordTrace (prefixWord ++ tailWord_3812191) baseStart_3812191 baseEnd_3812191 := by
    simpa [prefixWord, tailWord_3812191, baseEnd_3812191] using wordTrace_append hprefix tailTrace_3812191
  have hstable : (prefixWord ++ tailWord_3812191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812191).length < 2 ^ (prefixWord ++ tailWord_3812191).sum := by decide
  have hdescent : baseEnd_3812191 < baseStart_3812191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812236 : List Nat := [2, 2, 1, 2, 1, 2, 2, 2, 4, 4]
def baseStart_3812236 : Nat := 118140960795 + 3812236 * 2 ^ 59
def prefixEnd_3812236 : Nat := 4983230072969 + 3 ^ 40 * 3812236 * 2
def baseEnd_3812236 : Nat := 1305006290915767895211901

theorem tailTrace_3812236 : CollatzResearch.WordTrace tailWord_3812236 prefixEnd_3812236 1305006290915767895211901 := by
  unfold tailWord_3812236
  simp only [CollatzResearch.WordTrace]
  refine ⟨69521834908463762459468281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92695779877951683279291041 69521834908463762459468281)
  ·
    refine ⟨52141376181347821844601211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69521834908463762459468281 52141376181347821844601211)
    ·
      refine ⟨78212064272021732766901817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52141376181347821844601211 78212064272021732766901817)
      ·
        refine ⟨58659048204016299575176363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78212064272021732766901817 58659048204016299575176363)
        ·
          refine ⟨87988572306024449362764545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58659048204016299575176363 87988572306024449362764545)
          ·
            refine ⟨65991429229518337022073409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87988572306024449362764545 65991429229518337022073409)
            ·
              refine ⟨49493571922138752766555057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65991429229518337022073409 49493571922138752766555057)
              ·
                refine ⟨37120178941604064574916293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49493571922138752766555057 37120178941604064574916293)
                ·
                  refine ⟨6960033551550762107796805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37120178941604064574916293 6960033551550762107796805)
                  ·
                    refine ⟨1305006290915767895211901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6960033551550762107796805 1305006290915767895211901)
                    ·
                      rfl

theorem cell22_3812236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_3812236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3812236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3812236 prefixEnd_3812236 := by exact prefixLift 3812236
  have htrace : WordTrace (prefixWord ++ tailWord_3812236) baseStart_3812236 baseEnd_3812236 := by
    simpa [prefixWord, tailWord_3812236, baseEnd_3812236] using wordTrace_append hprefix tailTrace_3812236
  have hstable : (prefixWord ++ tailWord_3812236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812236).length < 2 ^ (prefixWord ++ tailWord_3812236).sum := by decide
  have hdescent : baseEnd_3812236 < baseStart_3812236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812311 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 4, 5]
def baseStart_3812311 : Nat := 118140960795 + 3812311 * 2 ^ 59
def prefixEnd_3812311 : Nat := 4983230072969 + 3 ^ 40 * 3812311 * 2
def baseEnd_3812311 : Nat := 1305031964948492699586671

theorem tailTrace_3812311 : CollatzResearch.WordTrace tailWord_3812311 prefixEnd_3812311 1305031964948492699586671 := by
  unfold tailWord_3812311
  simp only [CollatzResearch.WordTrace]
  refine ⟨139046405291655812727916787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92697603527770541818611191 139046405291655812727916787)
  ·
    refine ⟨208569607937483719091875181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139046405291655812727916787 208569607937483719091875181)
    ·
      refine ⟨78213602976556394659453193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208569607937483719091875181 78213602976556394659453193)
      ·
        refine ⟨58660202232417295994589895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78213602976556394659453193 58660202232417295994589895)
        ·
          refine ⟨87990303348625943991884843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58660202232417295994589895 87990303348625943991884843)
          ·
            refine ⟨131985455022938915987827265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87990303348625943991884843 131985455022938915987827265)
            ·
              refine ⟨98989091267204186990870449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131985455022938915987827265 98989091267204186990870449)
              ·
                refine ⟨74241818450403140243152837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98989091267204186990870449 74241818450403140243152837)
                ·
                  refine ⟨13920340959450588795591157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74241818450403140243152837 13920340959450588795591157)
                  ·
                    refine ⟨1305031964948492699586671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13920340959450588795591157 1305031964948492699586671)
                    ·
                      rfl

theorem cell22_3812311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_3812311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3812311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3812311 prefixEnd_3812311 := by exact prefixLift 3812311
  have htrace : WordTrace (prefixWord ++ tailWord_3812311) baseStart_3812311 baseEnd_3812311 := by
    simpa [prefixWord, tailWord_3812311, baseEnd_3812311] using wordTrace_append hprefix tailTrace_3812311
  have hstable : (prefixWord ++ tailWord_3812311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812311).length < 2 ^ (prefixWord ++ tailWord_3812311).sum := by decide
  have hdescent : baseEnd_3812311 < baseStart_3812311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812334 : List Nat := [4, 1, 2, 1, 5, 1, 1, 1, 3, 3]
def baseStart_3812334 : Nat := 118140960795 + 3812334 * 2 ^ 59
def prefixEnd_3812334 : Nat := 4983230072969 + 3 ^ 40 * 3812334 * 2
def baseEnd_3812334 : Nat := 1305039838318528306261601

theorem tailTrace_3812334 : CollatzResearch.WordTrace tailWord_3812334 prefixEnd_3812334 1305039838318528306261601 := by
  unfold tailWord_3812334
  simp only [CollatzResearch.WordTrace]
  refine ⟨17380905521321560957000507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92698162780381658437336037 17380905521321560957000507)
  ·
    refine ⟨26071358281982341435500761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17380905521321560957000507 26071358281982341435500761)
    ·
      refine ⟨19553518711486756076625571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26071358281982341435500761 19553518711486756076625571)
      ·
        refine ⟨29330278067230134114938357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19553518711486756076625571 29330278067230134114938357)
        ·
          refine ⟨2749713568802825073275471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29330278067230134114938357 2749713568802825073275471)
          ·
            refine ⟨4124570353204237609913207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2749713568802825073275471 4124570353204237609913207)
            ·
              refine ⟨6186855529806356414869811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4124570353204237609913207 6186855529806356414869811)
              ·
                refine ⟨9280283294709534622304717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6186855529806356414869811 9280283294709534622304717)
                ·
                  refine ⟨3480106235516075483364269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9280283294709534622304717 3480106235516075483364269)
                  ·
                    refine ⟨1305039838318528306261601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3480106235516075483364269 1305039838318528306261601)
                    ·
                      rfl

theorem cell22_3812334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_3812334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3812334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3812334 prefixEnd_3812334 := by exact prefixLift 3812334
  have htrace : WordTrace (prefixWord ++ tailWord_3812334) baseStart_3812334 baseEnd_3812334 := by
    simpa [prefixWord, tailWord_3812334, baseEnd_3812334] using wordTrace_append hprefix tailTrace_3812334
  have hstable : (prefixWord ++ tailWord_3812334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812334).length < 2 ^ (prefixWord ++ tailWord_3812334).sum := by decide
  have hdescent : baseEnd_3812334 < baseStart_3812334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812340 : List Nat := [2, 6, 2, 1, 1, 2, 2, 1, 2, 3]
def baseStart_3812340 : Nat := 118140960795 + 3812340 * 2 ^ 59
def prefixEnd_3812340 : Nat := 4983230072969 + 3 ^ 40 * 3812340 * 2
def baseEnd_3812340 : Nat := 1305041892241146290611583

theorem tailTrace_3812340 : CollatzResearch.WordTrace tailWord_3812340 prefixEnd_3812340 1305041892241146290611583 := by
  unfold tailWord_3812340
  simp only [CollatzResearch.WordTrace]
  refine ⟨69523731504275375340361237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92698308672367167120481649 69523731504275375340361237)
  ·
    refine ⟨3258924914262908219079433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 69523731504275375340361237 3258924914262908219079433)
    ·
      refine ⟨2444193685697181164309575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3258924914262908219079433 2444193685697181164309575)
      ·
        refine ⟨3666290528545771746464363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2444193685697181164309575 3666290528545771746464363)
        ·
          refine ⟨5499435792818657619696545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3666290528545771746464363 5499435792818657619696545)
          ·
            refine ⟨4124576844613993214772409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5499435792818657619696545 4124576844613993214772409)
            ·
              refine ⟨3093432633460494911079307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4124576844613993214772409 3093432633460494911079307)
              ·
                refine ⟨4640148950190742366618961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3093432633460494911079307 4640148950190742366618961)
                ·
                  refine ⟨3480111712643056774964221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4640148950190742366618961 3480111712643056774964221)
                  ·
                    refine ⟨1305041892241146290611583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3480111712643056774964221 1305041892241146290611583)
                    ·
                      rfl

theorem cell22_3812340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_3812340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3812340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3812340 prefixEnd_3812340 := by exact prefixLift 3812340
  have htrace : WordTrace (prefixWord ++ tailWord_3812340) baseStart_3812340 baseEnd_3812340 := by
    simpa [prefixWord, tailWord_3812340, baseEnd_3812340] using wordTrace_append hprefix tailTrace_3812340
  have hstable : (prefixWord ++ tailWord_3812340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812340).length < 2 ^ (prefixWord ++ tailWord_3812340).sum := by decide
  have hdescent : baseEnd_3812340 < baseStart_3812340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812360 : List Nat := [2, 1, 3, 2, 1, 3, 3, 2, 1, 4]
def baseStart_3812360 : Nat := 118140960795 + 3812360 * 2 ^ 59
def prefixEnd_3812360 : Nat := 4983230072969 + 3 ^ 40 * 3812360 * 2
def baseEnd_3812360 : Nat := 1305048738649872905111521

theorem tailTrace_3812360 : CollatzResearch.WordTrace tailWord_3812360 prefixEnd_3812360 1305048738649872905111521 := by
  unfold tailWord_3812360
  simp only [CollatzResearch.WordTrace]
  refine ⟨69524096234239147048225267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92698794978985529397633689 69524096234239147048225267)
  ·
    refine ⟨104286144351358720572337901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69524096234239147048225267 104286144351358720572337901)
    ·
      refine ⟨39107304131759520214626713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104286144351358720572337901 39107304131759520214626713)
      ·
        refine ⟨29330478098819640160970035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39107304131759520214626713 29330478098819640160970035)
        ·
          refine ⟨43995717148229460241455053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29330478098819640160970035 43995717148229460241455053)
          ·
            refine ⟨16498393930586047590545645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43995717148229460241455053 16498393930586047590545645)
            ·
              refine ⟨6186897723969767846454617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16498393930586047590545645 6186897723969767846454617)
              ·
                refine ⟨4640173292977325884840963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6186897723969767846454617 4640173292977325884840963)
                ·
                  refine ⟨6960259939465988827261445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4640173292977325884840963 6960259939465988827261445)
                  ·
                    refine ⟨1305048738649872905111521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6960259939465988827261445 1305048738649872905111521)
                    ·
                      rfl

theorem cell22_3812360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_3812360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3812360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3812360 prefixEnd_3812360 := by exact prefixLift 3812360
  have htrace : WordTrace (prefixWord ++ tailWord_3812360) baseStart_3812360 baseEnd_3812360 := by
    simpa [prefixWord, tailWord_3812360, baseEnd_3812360] using wordTrace_append hprefix tailTrace_3812360
  have hstable : (prefixWord ++ tailWord_3812360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812360).length < 2 ^ (prefixWord ++ tailWord_3812360).sum := by decide
  have hdescent : baseEnd_3812360 < baseStart_3812360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812373 : List Nat := [1, 3, 2, 1, 4, 1, 1, 1, 3, 5]
def baseStart_3812373 : Nat := 118140960795 + 3812373 * 2 ^ 59
def prefixEnd_3812373 : Nat := 4983230072969 + 3 ^ 40 * 3812373 * 2
def baseEnd_3812373 : Nat := 1305053188815545204536481

theorem tailTrace_3812373 : CollatzResearch.WordTrace tailWord_3812373 prefixEnd_3812373 1305053188815545204536481 := by
  unfold tailWord_3812373
  simp only [CollatzResearch.WordTrace]
  refine ⟨139048666617431197316673773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92699111078287464877782515 139048666617431197316673773)
  ·
    refine ⟨52143249981536698993752665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139048666617431197316673773 52143249981536698993752665)
    ·
      refine ⟨39107437486152524245314499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52143249981536698993752665 39107437486152524245314499)
      ·
        refine ⟨58661156229228786367971749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39107437486152524245314499 58661156229228786367971749)
        ·
          refine ⟨10998966792980397443994703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58661156229228786367971749 10998966792980397443994703)
          ·
            refine ⟨16498450189470596165992055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10998966792980397443994703 16498450189470596165992055)
            ·
              refine ⟨24747675284205894248988083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16498450189470596165992055 24747675284205894248988083)
              ·
                refine ⟨37121512926308841373482125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24747675284205894248988083 37121512926308841373482125)
                ·
                  refine ⟨13920567347365815515055797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37121512926308841373482125 13920567347365815515055797)
                  ·
                    refine ⟨1305053188815545204536481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13920567347365815515055797 1305053188815545204536481)
                    ·
                      rfl

theorem cell22_3812373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_3812373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3812373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3812373 prefixEnd_3812373 := by exact prefixLift 3812373
  have htrace : WordTrace (prefixWord ++ tailWord_3812373) baseStart_3812373 baseEnd_3812373 := by
    simpa [prefixWord, tailWord_3812373, baseEnd_3812373] using wordTrace_append hprefix tailTrace_3812373
  have hstable : (prefixWord ++ tailWord_3812373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812373).length < 2 ^ (prefixWord ++ tailWord_3812373).sum := by decide
  have hdescent : baseEnd_3812373 < baseStart_3812373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812422 : List Nat := [6, 1, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_3812422 : Nat := 118140960795 + 3812422 * 2 ^ 59
def prefixEnd_3812422 : Nat := 4983230072969 + 3 ^ 40 * 3812422 * 2
def baseEnd_3812422 : Nat := 1305069962516925410061331

theorem tailTrace_3812422 : CollatzResearch.WordTrace tailWord_3812422 prefixEnd_3812422 1305069962516925410061331 := by
  unfold tailWord_3812422
  simp only [CollatzResearch.WordTrace]
  refine ⟨4345326681070427458912735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 92700302529502452456805013 4345326681070427458912735)
  ·
    refine ⟨6517990021605641188369103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4345326681070427458912735 6517990021605641188369103)
    ·
      refine ⟨9776985032408461782553655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6517990021605641188369103 9776985032408461782553655)
      ·
        refine ⟨14665477548612692673830483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9776985032408461782553655 14665477548612692673830483)
        ·
          refine ⟨21998216322919039010745725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14665477548612692673830483 21998216322919039010745725)
          ·
            refine ⟨8249331121094639629029647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21998216322919039010745725 8249331121094639629029647)
            ·
              refine ⟨12373996681641959443544471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8249331121094639629029647 12373996681641959443544471)
              ·
                refine ⟨18560995022462939165316707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12373996681641959443544471 18560995022462939165316707)
                ·
                  refine ⟨27841492533694408747975061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18560995022462939165316707 27841492533694408747975061)
                  ·
                    refine ⟨1305069962516925410061331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27841492533694408747975061 1305069962516925410061331)
                    ·
                      rfl

theorem cell22_3812422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_3812422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3812422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3812422 prefixEnd_3812422 := by exact prefixLift 3812422
  have htrace : WordTrace (prefixWord ++ tailWord_3812422) baseStart_3812422 baseEnd_3812422 := by
    simpa [prefixWord, tailWord_3812422, baseEnd_3812422] using wordTrace_append hprefix tailTrace_3812422
  have hstable : (prefixWord ++ tailWord_3812422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812422).length < 2 ^ (prefixWord ++ tailWord_3812422).sum := by decide
  have hdescent : baseEnd_3812422 < baseStart_3812422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812448 : List Nat := [2, 1, 1, 3, 2, 2, 3, 1, 7]
def baseStart_3812448 : Nat := 118140960795 + 3812448 * 2 ^ 59
def prefixEnd_3812448 : Nat := 4983230072969 + 3 ^ 40 * 3812448 * 2
def baseEnd_3812448 : Nat := 435026287616090002970417

theorem tailTrace_3812448 : CollatzResearch.WordTrace tailWord_3812448 prefixEnd_3812448 435026287616090002970417 := by
  unfold tailWord_3812448
  simp only [CollatzResearch.WordTrace]
  refine ⟨69525701046079742562826999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92700934728106323417102665 69525701046079742562826999)
  ·
    refine ⟨104288551569119613844240499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69525701046079742562826999 104288551569119613844240499)
    ·
      refine ⟨156432827353679420766360749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104288551569119613844240499 156432827353679420766360749)
      ·
        refine ⟨58662310257629782787385281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156432827353679420766360749 58662310257629782787385281)
        ·
          refine ⟨43996732693222337090538961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58662310257629782787385281 43996732693222337090538961)
          ·
            refine ⟨32997549519916752817904221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43996732693222337090538961 32997549519916752817904221)
            ·
              refine ⟨12374081069968782306714083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32997549519916752817904221 12374081069968782306714083)
              ·
                refine ⟨18561121604953173460071125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12374081069968782306714083 18561121604953173460071125)
                ·
                  refine ⟨435026287616090002970417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18561121604953173460071125 435026287616090002970417)
                  ·
                    rfl

theorem cell22_3812448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 7].length) (baseStart_3812448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3812448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3812448 prefixEnd_3812448 := by exact prefixLift 3812448
  have htrace : WordTrace (prefixWord ++ tailWord_3812448) baseStart_3812448 baseEnd_3812448 := by
    simpa [prefixWord, tailWord_3812448, baseEnd_3812448] using wordTrace_append hprefix tailTrace_3812448
  have hstable : (prefixWord ++ tailWord_3812448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812448).length < 2 ^ (prefixWord ++ tailWord_3812448).sum := by decide
  have hdescent : baseEnd_3812448 < baseStart_3812448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812463 : List Nat := [1, 1, 2, 1, 3, 3, 1, 3, 2, 5]
def baseStart_3812463 : Nat := 118140960795 + 3812463 * 2 ^ 59
def prefixEnd_3812463 : Nat := 4983230072969 + 3 ^ 40 * 3812463 * 2
def baseEnd_3812463 : Nat := 1305083997654814969786205

theorem tailTrace_3812463 : CollatzResearch.WordTrace tailWord_3812463 prefixEnd_3812463 1305083997654814969786205 := by
  unfold tailWord_3812463
  simp only [CollatzResearch.WordTrace]
  refine ⟨139051949187105142687450043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92701299458070095124966695 139051949187105142687450043)
  ·
    refine ⟨208577923780657714031175065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139051949187105142687450043 208577923780657714031175065)
    ·
      refine ⟨156433442835493285523381299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208577923780657714031175065 156433442835493285523381299)
      ·
        refine ⟨234650164253239928285071949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156433442835493285523381299 234650164253239928285071949)
        ·
          refine ⟨87993811594964973106901981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234650164253239928285071949 87993811594964973106901981)
          ·
            refine ⟨32997679348111864915088243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87993811594964973106901981 32997679348111864915088243)
            ·
              refine ⟨49496519022167797372632365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32997679348111864915088243 49496519022167797372632365)
              ·
                refine ⟨18561194633312924014737137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49496519022167797372632365 18561194633312924014737137)
                ·
                  refine ⟨13920895974984693011052853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18561194633312924014737137 13920895974984693011052853)
                  ·
                    refine ⟨1305083997654814969786205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13920895974984693011052853 1305083997654814969786205)
                    ·
                      rfl

theorem cell22_3812463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 5].length) (baseStart_3812463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3812463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3812463 prefixEnd_3812463 := by exact prefixLift 3812463
  have htrace : WordTrace (prefixWord ++ tailWord_3812463) baseStart_3812463 baseEnd_3812463 := by
    simpa [prefixWord, tailWord_3812463, baseEnd_3812463] using wordTrace_append hprefix tailTrace_3812463
  have hstable : (prefixWord ++ tailWord_3812463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812463).length < 2 ^ (prefixWord ++ tailWord_3812463).sum := by decide
  have hdescent : baseEnd_3812463 < baseStart_3812463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812529 : List Nat := [1, 2, 2, 5, 1, 3, 1, 2, 1, 4]
def baseStart_3812529 : Nat := 118140960795 + 3812529 * 2 ^ 59
def prefixEnd_3812529 : Nat := 4983230072969 + 3 ^ 40 * 3812529 * 2
def baseEnd_3812529 : Nat := 1305106590803612797636003

theorem tailTrace_3812529 : CollatzResearch.WordTrace tailWord_3812529 prefixEnd_3812529 1305106590803612797636003 := by
  unfold tailWord_3812529
  simp only [CollatzResearch.WordTrace]
  refine ⟨139054356404866035959352641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92702904269910690639568427 139054356404866035959352641)
  ·
    refine ⟨104290767303649526969514481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139054356404866035959352641 104290767303649526969514481)
    ·
      refine ⟨78218075477737145227135861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104290767303649526969514481 78218075477737145227135861)
      ·
        refine ⟨7332944576037857365043987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78218075477737145227135861 7332944576037857365043987)
        ·
          refine ⟨10999416864056786047565981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7332944576037857365043987 10999416864056786047565981)
          ·
            refine ⟨4124781324021294767837243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10999416864056786047565981 4124781324021294767837243)
            ·
              refine ⟨6187171986031942151755865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4124781324021294767837243 6187171986031942151755865)
              ·
                refine ⟨4640378989523956613816899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6187171986031942151755865 4640378989523956613816899)
                ·
                  refine ⟨6960568484285934920725349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4640378989523956613816899 6960568484285934920725349)
                  ·
                    refine ⟨1305106590803612797636003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6960568484285934920725349 1305106590803612797636003)
                    ·
                      rfl

theorem cell22_3812529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 4].length) (baseStart_3812529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3812529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3812529 prefixEnd_3812529 := by exact prefixLift 3812529
  have htrace : WordTrace (prefixWord ++ tailWord_3812529) baseStart_3812529 baseEnd_3812529 := by
    simpa [prefixWord, tailWord_3812529, baseEnd_3812529] using wordTrace_append hprefix tailTrace_3812529
  have hstable : (prefixWord ++ tailWord_3812529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812529).length < 2 ^ (prefixWord ++ tailWord_3812529).sum := by decide
  have hdescent : baseEnd_3812529 < baseStart_3812529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812542 : List Nat := [4, 2, 1, 1, 3, 2, 1, 2, 1, 5]
def baseStart_3812542 : Nat := 118140960795 + 3812542 * 2 ^ 59
def prefixEnd_3812542 : Nat := 4983230072969 + 3 ^ 40 * 3812542 * 2
def baseEnd_3812542 : Nat := 1305111040969285097060963

theorem tailTrace_3812542 : CollatzResearch.WordTrace tailWord_3812542 prefixEnd_3812542 1305111040969285097060963 := by
  unfold tailWord_3812542
  simp only [CollatzResearch.WordTrace]
  refine ⟨17381853819227367397446985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92703220369212626119717253 17381853819227367397446985)
  ·
    refine ⟨13036390364420525548085239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17381853819227367397446985 13036390364420525548085239)
    ·
      refine ⟨19554585546630788322127859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13036390364420525548085239 19554585546630788322127859)
      ·
        refine ⟨29331878319946182483191789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19554585546630788322127859 29331878319946182483191789)
        ·
          refine ⟨10999454369979818431196921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29331878319946182483191789 10999454369979818431196921)
          ·
            refine ⟨8249590777484863823397691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10999454369979818431196921 8249590777484863823397691)
            ·
              refine ⟨12374386166227295735096537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8249590777484863823397691 12374386166227295735096537)
              ·
                refine ⟨9280789624670471801322403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12374386166227295735096537 9280789624670471801322403)
                ·
                  refine ⟨13921184437005707701983605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9280789624670471801322403 13921184437005707701983605)
                  ·
                    refine ⟨1305111040969285097060963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13921184437005707701983605 1305111040969285097060963)
                    ·
                      rfl

theorem cell22_3812542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_3812542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3812542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3812542 prefixEnd_3812542 := by exact prefixLift 3812542
  have htrace : WordTrace (prefixWord ++ tailWord_3812542) baseStart_3812542 baseEnd_3812542 := by
    simpa [prefixWord, tailWord_3812542, baseEnd_3812542] using wordTrace_append hprefix tailTrace_3812542
  have hstable : (prefixWord ++ tailWord_3812542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812542).length < 2 ^ (prefixWord ++ tailWord_3812542).sum := by decide
  have hdescent : baseEnd_3812542 < baseStart_3812542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812553 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 4, 7]
def baseStart_3812553 : Nat := 118140960795 + 3812553 * 2 ^ 59
def prefixEnd_3812553 : Nat := 4983230072969 + 3 ^ 40 * 3812553 * 2
def baseEnd_3812553 : Nat := 1305114806494084735035929

theorem tailTrace_3812553 : CollatzResearch.WordTrace tailWord_3812553 prefixEnd_3812553 1305114806494084735035929 := by
  unfold tailWord_3812553
  simp only [CollatzResearch.WordTrace]
  refine ⟨139055231756779088058226313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92703487837852725372150875 139055231756779088058226313)
  ·
    refine ⟨104291423817584316043669735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139055231756779088058226313 104291423817584316043669735)
    ·
      refine ⟨156437135726376474065504603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104291423817584316043669735 156437135726376474065504603)
      ·
        refine ⟨234655703589564711098256905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156437135726376474065504603 234655703589564711098256905)
        ·
          refine ⟨175991777692173533323692679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234655703589564711098256905 175991777692173533323692679)
          ·
            refine ⟨263987666538260299985539019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175991777692173533323692679 263987666538260299985539019)
            ·
              refine ⟨395981499807390449978308529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263987666538260299985539019 395981499807390449978308529)
              ·
                refine ⟨296986124855542837483731397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 395981499807390449978308529 296986124855542837483731397)
                ·
                  refine ⟨55684898410414282028199637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 296986124855542837483731397 55684898410414282028199637)
                  ·
                    refine ⟨1305114806494084735035929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55684898410414282028199637 1305114806494084735035929)
                    ·
                      rfl

theorem cell22_3812553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 7].length) (baseStart_3812553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3812553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3812553 prefixEnd_3812553 := by exact prefixLift 3812553
  have htrace : WordTrace (prefixWord ++ tailWord_3812553) baseStart_3812553 baseEnd_3812553 := by
    simpa [prefixWord, tailWord_3812553, baseEnd_3812553] using wordTrace_append hprefix tailTrace_3812553
  have hstable : (prefixWord ++ tailWord_3812553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812553).length < 2 ^ (prefixWord ++ tailWord_3812553).sum := by decide
  have hdescent : baseEnd_3812553 < baseStart_3812553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812587 : List Nat := [1, 1, 1, 1, 2, 7, 1, 2, 3, 3]
def baseStart_3812587 : Nat := 118140960795 + 3812587 * 2 ^ 59
def prefixEnd_3812587 : Nat := 4983230072969 + 3 ^ 40 * 3812587 * 2
def baseEnd_3812587 : Nat := 1305126445388919979685825

theorem tailTrace_3812587 : CollatzResearch.WordTrace tailWord_3812587 prefixEnd_3812587 1305126445388919979685825 := by
  unfold tailWord_3812587
  simp only [CollatzResearch.WordTrace]
  refine ⟨139056471838655911864964015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92704314559103941243309343 139056471838655911864964015)
  ·
    refine ⟨208584707757983867797446023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139056471838655911864964015 208584707757983867797446023)
    ·
      refine ⟨312877061636975801696169035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208584707757983867797446023 312877061636975801696169035)
      ·
        refine ⟨469315592455463702544253553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312877061636975801696169035 469315592455463702544253553)
        ·
          refine ⟨351986694341597776908190165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469315592455463702544253553 351986694341597776908190165)
          ·
            refine ⟨8249688148631197896285707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 351986694341597776908190165 8249688148631197896285707)
            ·
              refine ⟨12374532222946796844428561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8249688148631197896285707 12374532222946796844428561)
              ·
                refine ⟨9280899167210097633321421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12374532222946796844428561 9280899167210097633321421)
                ·
                  refine ⟨3480337187703786612495533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9280899167210097633321421 3480337187703786612495533)
                  ·
                    refine ⟨1305126445388919979685825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3480337187703786612495533 1305126445388919979685825)
                    ·
                      rfl

theorem cell22_3812587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 3, 3].length) (baseStart_3812587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3812587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3812587 prefixEnd_3812587 := by exact prefixLift 3812587
  have htrace : WordTrace (prefixWord ++ tailWord_3812587) baseStart_3812587 baseEnd_3812587 := by
    simpa [prefixWord, tailWord_3812587, baseEnd_3812587] using wordTrace_append hprefix tailTrace_3812587
  have hstable : (prefixWord ++ tailWord_3812587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812587).length < 2 ^ (prefixWord ++ tailWord_3812587).sum := by decide
  have hdescent : baseEnd_3812587 < baseStart_3812587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812634 : List Nat := [3, 1, 1, 3, 3, 2, 3, 1, 5]
def baseStart_3812634 : Nat := 118140960795 + 3812634 * 2 ^ 59
def prefixEnd_3812634 : Nat := 4983230072969 + 3 ^ 40 * 3812634 * 2
def baseEnd_3812634 : Nat := 435047511483142507920227

theorem tailTrace_3812634 : CollatzResearch.WordTrace tailWord_3812634 prefixEnd_3812634 435047511483142507920227 := by
  unfold tailWord_3812634
  simp only [CollatzResearch.WordTrace]
  refine ⟨34764546517371409722981239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92705457379657092594616637 34764546517371409722981239)
  ·
    refine ⟨52146819776057114584471859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34764546517371409722981239 52146819776057114584471859)
    ·
      refine ⟨78220229664085671876707789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52146819776057114584471859 78220229664085671876707789)
      ·
        refine ⟨29332586124032126953765421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78220229664085671876707789 29332586124032126953765421)
        ·
          refine ⟨10999719796512047607662033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29332586124032126953765421 10999719796512047607662033)
          ·
            refine ⟨8249789847384035705746525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10999719796512047607662033 8249789847384035705746525)
            ·
              refine ⟨3093671192769013389654947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8249789847384035705746525 3093671192769013389654947)
              ·
                refine ⟨4640506789153520084482421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3093671192769013389654947 4640506789153520084482421)
                ·
                  refine ⟨435047511483142507920227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4640506789153520084482421 435047511483142507920227)
                  ·
                    rfl

theorem cell22_3812634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 5].length) (baseStart_3812634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3812634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3812634 prefixEnd_3812634 := by exact prefixLift 3812634
  have htrace : WordTrace (prefixWord ++ tailWord_3812634) baseStart_3812634 baseEnd_3812634 := by
    simpa [prefixWord, tailWord_3812634, baseEnd_3812634] using wordTrace_append hprefix tailTrace_3812634
  have hstable : (prefixWord ++ tailWord_3812634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812634).length < 2 ^ (prefixWord ++ tailWord_3812634).sum := by decide
  have hdescent : baseEnd_3812634 < baseStart_3812634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812685 : List Nat := [1, 6, 1, 3, 2, 1, 2, 1, 5]
def baseStart_3812685 : Nat := 118140960795 + 3812685 * 2 ^ 59
def prefixEnd_3812685 : Nat := 4983230072969 + 3 ^ 40 * 3812685 * 2
def baseEnd_3812685 : Nat := 435053330930560130245175

theorem tailTrace_3812685 : CollatzResearch.WordTrace tailWord_3812685 prefixEnd_3812685 435053330930560130245175 := by
  unfold tailWord_3812685
  simp only [CollatzResearch.WordTrace]
  refine ⟨139060046192300874602031509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92706697461533916401354339 139060046192300874602031509)
  ·
    refine ⟨6518439665264103496970227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 139060046192300874602031509 6518439665264103496970227)
    ·
      refine ⟨9777659497896155245455341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6518439665264103496970227 9777659497896155245455341)
      ·
        refine ⟨3666622311711058217045753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9777659497896155245455341 3666622311711058217045753)
        ·
          refine ⟨2749966733783293662784315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3666622311711058217045753 2749966733783293662784315)
          ·
            refine ⟨4124950100674940494176473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2749966733783293662784315 4124950100674940494176473)
            ·
              refine ⟨3093712575506205370632355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4124950100674940494176473 3093712575506205370632355)
              ·
                refine ⟨4640568863259308055948533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3093712575506205370632355 4640568863259308055948533)
                ·
                  refine ⟨435053330930560130245175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4640568863259308055948533 435053330930560130245175)
                  ·
                    rfl

theorem cell22_3812685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_3812685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3812685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3812685 prefixEnd_3812685 := by exact prefixLift 3812685
  have htrace : WordTrace (prefixWord ++ tailWord_3812685) baseStart_3812685 baseEnd_3812685 := by
    simpa [prefixWord, tailWord_3812685, baseEnd_3812685] using wordTrace_append hprefix tailTrace_3812685
  have hstable : (prefixWord ++ tailWord_3812685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812685).length < 2 ^ (prefixWord ++ tailWord_3812685).sum := by decide
  have hdescent : baseEnd_3812685 < baseStart_3812685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812692 : List Nat := [2, 4, 1, 1, 2, 1, 1, 2, 4, 4]
def baseStart_3812692 : Nat := 118140960795 + 3812692 * 2 ^ 59
def prefixEnd_3812692 : Nat := 4983230072969 + 3 ^ 40 * 3812692 * 2
def baseEnd_3812692 : Nat := 1305162389034734705810503

theorem tailTrace_3812692 : CollatzResearch.WordTrace tailWord_3812692 prefixEnd_3812692 1305162389034734705810503 := by
  unfold tailWord_3812692
  simp only [CollatzResearch.WordTrace]
  refine ⟨69530150751637757398768165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92706867668850343198357553 69530150751637757398768165)
  ·
    refine ⟨13036903265932079512269031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69530150751637757398768165 13036903265932079512269031)
    ·
      refine ⟨19555354898898119268403547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13036903265932079512269031 19555354898898119268403547)
      ·
        refine ⟨29333032348347178902605321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19555354898898119268403547 29333032348347178902605321)
        ·
          refine ⟨21999774261260384176953991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29333032348347178902605321 21999774261260384176953991)
          ·
            refine ⟨32999661391890576265430987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21999774261260384176953991 32999661391890576265430987)
            ·
              refine ⟨49499492087835864398146481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32999661391890576265430987 49499492087835864398146481)
              ·
                refine ⟨37124619065876898298609861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49499492087835864398146481 37124619065876898298609861)
                ·
                  refine ⟨6960866074851918430989349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37124619065876898298609861 6960866074851918430989349)
                  ·
                    refine ⟨1305162389034734705810503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6960866074851918430989349 1305162389034734705810503)
                    ·
                      rfl

theorem cell22_3812692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_3812692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3812692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3812692 prefixEnd_3812692 := by exact prefixLift 3812692
  have htrace : WordTrace (prefixWord ++ tailWord_3812692) baseStart_3812692 baseEnd_3812692 := by
    simpa [prefixWord, tailWord_3812692, baseEnd_3812692] using wordTrace_append hprefix tailTrace_3812692
  have hstable : (prefixWord ++ tailWord_3812692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812692).length < 2 ^ (prefixWord ++ tailWord_3812692).sum := by decide
  have hdescent : baseEnd_3812692 < baseStart_3812692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812705 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 2, 7]
def baseStart_3812705 : Nat := 118140960795 + 3812705 * 2 ^ 59
def prefixEnd_3812705 : Nat := 4983230072969 + 3 ^ 40 * 3812705 * 2
def baseEnd_3812705 : Nat := 1305166839200407005235463

theorem tailTrace_3812705 : CollatzResearch.WordTrace tailWord_3812705 prefixEnd_3812705 1305166839200407005235463 := by
  unfold tailWord_3812705
  simp only [CollatzResearch.WordTrace]
  refine ⟨139060775652228418017759569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92707183768152278678506379 139060775652228418017759569)
  ·
    refine ⟨104295581739171313513319677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139060775652228418017759569 104295581739171313513319677)
    ·
      refine ⟨39110843152189242567494879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104295581739171313513319677 39110843152189242567494879)
      ·
        refine ⟨58666264728283863851242319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39110843152189242567494879 58666264728283863851242319)
        ·
          refine ⟨87999397092425795776863479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58666264728283863851242319 87999397092425795776863479)
          ·
            refine ⟨131999095638638693665295219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87999397092425795776863479 131999095638638693665295219)
            ·
              refine ⟨197998643457958040497942829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131999095638638693665295219 197998643457958040497942829)
              ·
                refine ⟨74249491296734265186728561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197998643457958040497942829 74249491296734265186728561)
                ·
                  refine ⟨55687118472550698890046421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74249491296734265186728561 55687118472550698890046421)
                  ·
                    refine ⟨1305166839200407005235463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55687118472550698890046421 1305166839200407005235463)
                    ·
                      rfl

theorem cell22_3812705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_3812705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3812705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3812705 prefixEnd_3812705 := by exact prefixLift 3812705
  have htrace : WordTrace (prefixWord ++ tailWord_3812705) baseStart_3812705 baseEnd_3812705 := by
    simpa [prefixWord, tailWord_3812705, baseEnd_3812705] using wordTrace_append hprefix tailTrace_3812705
  have hstable : (prefixWord ++ tailWord_3812705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812705).length < 2 ^ (prefixWord ++ tailWord_3812705).sum := by decide
  have hdescent : baseEnd_3812705 < baseStart_3812705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812756 : List Nat := [2, 4, 2, 1, 2, 2, 1, 2, 3, 3]
def baseStart_3812756 : Nat := 118140960795 + 3812756 * 2 ^ 59
def prefixEnd_3812756 : Nat := 4983230072969 + 3 ^ 40 * 3812756 * 2
def baseEnd_3812756 : Nat := 1305184297542659872210307

theorem tailTrace_3812756 : CollatzResearch.WordTrace tailWord_3812756 prefixEnd_3812756 1305184297542659872210307 := by
  unfold tailWord_3812756
  simp only [CollatzResearch.WordTrace]
  refine ⟨69531317887521826863933061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92708423850029102485244081 69531317887521826863933061)
  ·
    refine ⟨13037122103910342536987449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69531317887521826863933061 13037122103910342536987449)
    ·
      refine ⟨9777841577932756902740587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13037122103910342536987449 9777841577932756902740587)
      ·
        refine ⟨14666762366899135354110881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9777841577932756902740587 14666762366899135354110881)
        ·
          refine ⟨11000071775174351515583161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14666762366899135354110881 11000071775174351515583161)
          ·
            refine ⟨8250053831380763636687371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11000071775174351515583161 8250053831380763636687371)
            ·
              refine ⟨12375080747071145455031057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8250053831380763636687371 12375080747071145455031057)
              ·
                refine ⟨9281310560303359091273293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12375080747071145455031057 9281310560303359091273293)
                ·
                  refine ⟨3480491460113759659227485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9281310560303359091273293 3480491460113759659227485)
                  ·
                    refine ⟨1305184297542659872210307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3480491460113759659227485 1305184297542659872210307)
                    ·
                      rfl

theorem cell22_3812756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_3812756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3812756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3812756 prefixEnd_3812756 := by exact prefixLift 3812756
  have htrace : WordTrace (prefixWord ++ tailWord_3812756) baseStart_3812756 baseEnd_3812756 := by
    simpa [prefixWord, tailWord_3812756, baseEnd_3812756] using wordTrace_append hprefix tailTrace_3812756
  have hstable : (prefixWord ++ tailWord_3812756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812756).length < 2 ^ (prefixWord ++ tailWord_3812756).sum := by decide
  have hdescent : baseEnd_3812756 < baseStart_3812756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812846 : List Nat := [4, 1, 2, 1, 2, 1, 2, 4, 2, 3]
def baseStart_3812846 : Nat := 118140960795 + 3812846 * 2 ^ 59
def prefixEnd_3812846 : Nat := 4983230072969 + 3 ^ 40 * 3812846 * 2
def baseEnd_3812846 : Nat := 1305215106381929637460031

theorem tailTrace_3812846 : CollatzResearch.WordTrace tailWord_3812846 prefixEnd_3812846 1305215106381929637460031 := by
  unfold tailWord_3812846
  simp only [CollatzResearch.WordTrace]
  refine ⟨17383239793089699887330299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92710612229811732732428261 17383239793089699887330299)
  ·
    refine ⟨26074859689634549830995449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17383239793089699887330299 26074859689634549830995449)
    ·
      refine ⟨19556144767225912373246587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26074859689634549830995449 19556144767225912373246587)
      ·
        refine ⟨29334217150838868559869881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19556144767225912373246587 29334217150838868559869881)
        ·
          refine ⟨22000662863129151419902411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29334217150838868559869881 22000662863129151419902411)
          ·
            refine ⟨33000994294693727129853617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22000662863129151419902411 33000994294693727129853617)
            ·
              refine ⟨24750745721020295347390213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33000994294693727129853617 24750745721020295347390213)
              ·
                refine ⟨4640764822691305377635665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24750745721020295347390213 4640764822691305377635665)
                ·
                  refine ⟨3480573617018479033226749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4640764822691305377635665 3480573617018479033226749)
                  ·
                    refine ⟨1305215106381929637460031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3480573617018479033226749 1305215106381929637460031)
                    ·
                      rfl

theorem cell22_3812846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_3812846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3812846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3812846 prefixEnd_3812846 := by exact prefixLift 3812846
  have htrace : WordTrace (prefixWord ++ tailWord_3812846) baseStart_3812846 baseEnd_3812846 := by
    simpa [prefixWord, tailWord_3812846, baseEnd_3812846] using wordTrace_append hprefix tailTrace_3812846
  have hstable : (prefixWord ++ tailWord_3812846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812846).length < 2 ^ (prefixWord ++ tailWord_3812846).sum := by decide
  have hdescent : baseEnd_3812846 < baseStart_3812846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812919 : List Nat := [1, 1, 3, 1, 2, 5, 1, 1, 2, 5]
def baseStart_3812919 : Nat := 118140960795 + 3812919 * 2 ^ 59
def prefixEnd_3812919 : Nat := 4983230072969 + 3 ^ 40 * 3812919 * 2
def baseEnd_3812919 : Nat := 1305240095773781780384807

theorem tailTrace_3812919 : CollatzResearch.WordTrace tailWord_3812919 prefixEnd_3812919 1305240095773781780384807 := by
  unfold tailWord_3812919
  simp only [CollatzResearch.WordTrace]
  refine ⟨139068580873453132566049811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92712387248968755044033207 139068580873453132566049811)
  ·
    refine ⟨208602871310179698849074717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139068580873453132566049811 208602871310179698849074717)
    ·
      refine ⟨78226076741317387068403019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208602871310179698849074717 78226076741317387068403019)
      ·
        refine ⟨117339115111976080602604529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78226076741317387068403019 117339115111976080602604529)
        ·
          refine ⟨88004336333982060451953397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117339115111976080602604529 88004336333982060451953397)
          ·
            refine ⟨8250406531310818167370631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88004336333982060451953397 8250406531310818167370631)
            ·
              refine ⟨12375609796966227251055947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8250406531310818167370631 12375609796966227251055947)
              ·
                refine ⟨18563414695449340876583921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12375609796966227251055947 18563414695449340876583921)
                ·
                  refine ⟨13922561021587005657437941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18563414695449340876583921 13922561021587005657437941)
                  ·
                    refine ⟨1305240095773781780384807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13922561021587005657437941 1305240095773781780384807)
                    ·
                      rfl

theorem cell22_3812919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_3812919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3812919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3812919 prefixEnd_3812919 := by exact prefixLift 3812919
  have htrace : WordTrace (prefixWord ++ tailWord_3812919) baseStart_3812919 baseEnd_3812919 := by
    simpa [prefixWord, tailWord_3812919, baseEnd_3812919] using wordTrace_append hprefix tailTrace_3812919
  have hstable : (prefixWord ++ tailWord_3812919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812919).length < 2 ^ (prefixWord ++ tailWord_3812919).sum := by decide
  have hdescent : baseEnd_3812919 < baseStart_3812919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3812951 : List Nat := [1, 1, 3, 2, 2, 4, 1, 3, 1, 4]
def baseStart_3812951 : Nat := 118140960795 + 3812951 * 2 ^ 59
def prefixEnd_3812951 : Nat := 4983230072969 + 3 ^ 40 * 3812951 * 2
def baseEnd_3812951 : Nat := 1305251050027744363584709

theorem tailTrace_3812951 : CollatzResearch.WordTrace tailWord_3812951 prefixEnd_3812951 1305251050027744363584709 := by
  unfold tailWord_3812951
  simp only [CollatzResearch.WordTrace]
  refine ⟨139069748009337202031214707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92713165339558134687476471 139069748009337202031214707)
  ·
    refine ⟨208604622014005803046822061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139069748009337202031214707 208604622014005803046822061)
    ·
      refine ⟨78226733255252176142558273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208604622014005803046822061 78226733255252176142558273)
      ·
        refine ⟨58670049941439132106918705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78226733255252176142558273 58670049941439132106918705)
        ·
          refine ⟨44002537456079349080189029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58670049941439132106918705 44002537456079349080189029)
          ·
            refine ⟨8250475773014877952535443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44002537456079349080189029 8250475773014877952535443)
            ·
              refine ⟨12375713659522316928803165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8250475773014877952535443 12375713659522316928803165)
              ·
                refine ⟨4640892622320868848301187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12375713659522316928803165 4640892622320868848301187)
                ·
                  refine ⟨6961338933481303272451781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4640892622320868848301187 6961338933481303272451781)
                  ·
                    refine ⟨1305251050027744363584709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6961338933481303272451781 1305251050027744363584709)
                    ·
                      rfl

theorem cell22_3812951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 4].length) (baseStart_3812951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3812951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3812951 prefixEnd_3812951 := by exact prefixLift 3812951
  have htrace : WordTrace (prefixWord ++ tailWord_3812951) baseStart_3812951 baseEnd_3812951 := by
    simpa [prefixWord, tailWord_3812951, baseEnd_3812951] using wordTrace_append hprefix tailTrace_3812951
  have hstable : (prefixWord ++ tailWord_3812951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3812951).length < 2 ^ (prefixWord ++ tailWord_3812951).sum := by decide
  have hdescent : baseEnd_3812951 < baseStart_3812951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3812951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813060 : List Nat := [2, 3, 3, 1, 1, 1, 2, 5, 1, 3]
def baseStart_3813060 : Nat := 118140960795 + 3813060 * 2 ^ 59
def prefixEnd_3813060 : Nat := 4983230072969 + 3 ^ 40 * 3813060 * 2
def baseEnd_3813060 : Nat := 1305288362955304412609375

theorem tailTrace_3813060 : CollatzResearch.WordTrace tailWord_3813060 prefixEnd_3813060 1305288362955304412609375 := by
  unfold tailWord_3813060
  simp only [CollatzResearch.WordTrace]
  refine ⟨69536861782971156823466317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92715815710628209097955089 69536861782971156823466317)
  ·
    refine ⟨26076323168614183808799869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69536861782971156823466317 26076323168614183808799869)
    ·
      refine ⟨9778621188230318928299951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26076323168614183808799869 9778621188230318928299951)
      ·
        refine ⟨14667931782345478392449927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9778621188230318928299951 14667931782345478392449927)
        ·
          refine ⟨22001897673518217588674891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14667931782345478392449927 22001897673518217588674891)
          ·
            refine ⟨33002846510277326383012337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22001897673518217588674891 33002846510277326383012337)
            ·
              refine ⟨24752134882707994787259253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33002846510277326383012337 24752134882707994787259253)
              ·
                refine ⟨2320512645253874511305555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24752134882707994787259253 2320512645253874511305555)
                ·
                  refine ⟨3480768967880811766958333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2320512645253874511305555 3480768967880811766958333)
                  ·
                    refine ⟨1305288362955304412609375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3480768967880811766958333 1305288362955304412609375)
                    ·
                      rfl

theorem cell22_3813060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_3813060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3813060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3813060 prefixEnd_3813060 := by exact prefixLift 3813060
  have htrace : WordTrace (prefixWord ++ tailWord_3813060) baseStart_3813060 baseEnd_3813060 := by
    simpa [prefixWord, tailWord_3813060, baseEnd_3813060] using wordTrace_append hprefix tailTrace_3813060
  have hstable : (prefixWord ++ tailWord_3813060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813060).length < 2 ^ (prefixWord ++ tailWord_3813060).sum := by decide
  have hdescent : baseEnd_3813060 < baseStart_3813060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813101 : List Nat := [1, 5, 1, 2, 1, 2, 1, 1, 8]
def baseStart_3813101 : Nat := 118140960795 + 3813101 * 2 ^ 59
def prefixEnd_3813101 : Nat := 4983230072969 + 3 ^ 40 * 3813101 * 2
def baseEnd_3813101 : Nat := 435100799364397990778083

theorem tailTrace_3813101 : CollatzResearch.WordTrace tailWord_3813101 prefixEnd_3813101 435100799364397990778083 := by
  unfold tailWord_3813101
  simp only [CollatzResearch.WordTrace]
  refine ⟨139075218958793777649175157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92716812639195851766116771 139075218958793777649175157)
  ·
    refine ⟨13038301777386916654610171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139075218958793777649175157 13038301777386916654610171)
    ·
      refine ⟨19557452666080374981915257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13038301777386916654610171 19557452666080374981915257)
      ·
        refine ⟨14668089499560281236436443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19557452666080374981915257 14668089499560281236436443)
        ·
          refine ⟨22002134249340421854654665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14668089499560281236436443 22002134249340421854654665)
          ·
            refine ⟨16501600687005316390990999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22002134249340421854654665 16501600687005316390990999)
            ·
              refine ⟨24752401030507974586486499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16501600687005316390990999 24752401030507974586486499)
              ·
                refine ⟨37128601545761961879729749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24752401030507974586486499 37128601545761961879729749)
                ·
                  refine ⟨435100799364397990778083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37128601545761961879729749 435100799364397990778083)
                  ·
                    rfl

theorem cell22_3813101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_3813101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3813101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3813101 prefixEnd_3813101 := by exact prefixLift 3813101
  have htrace : WordTrace (prefixWord ++ tailWord_3813101) baseStart_3813101 baseEnd_3813101 := by
    simpa [prefixWord, tailWord_3813101, baseEnd_3813101] using wordTrace_append hprefix tailTrace_3813101
  have hstable : (prefixWord ++ tailWord_3813101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813101).length < 2 ^ (prefixWord ++ tailWord_3813101).sum := by decide
  have hdescent : baseEnd_3813101 < baseStart_3813101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813116 : List Nat := [2, 2, 2, 1, 3, 1, 1, 4, 1, 5]
def baseStart_3813116 : Nat := 118140960795 + 3813116 * 2 ^ 59
def prefixEnd_3813116 : Nat := 4983230072969 + 3 ^ 40 * 3813116 * 2
def baseEnd_3813116 : Nat := 1305307532899738933209203

theorem tailTrace_3813116 : CollatzResearch.WordTrace tailWord_3813116 prefixEnd_3813116 1305307532899738933209203 := by
  unfold tailWord_3813116
  simp only [CollatzResearch.WordTrace]
  refine ⟨69537883026869717605485601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92717177369159623473980801 69537883026869717605485601)
  ·
    refine ⟨52153412270152288204114201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69537883026869717605485601 52153412270152288204114201)
    ·
      refine ⟨39115059202614216153085651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52153412270152288204114201 39115059202614216153085651)
      ·
        refine ⟨58672588803921324229628477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39115059202614216153085651 58672588803921324229628477)
        ·
          refine ⟨22002220801470496586110679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58672588803921324229628477 22002220801470496586110679)
          ·
            refine ⟨33003331202205744879166019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22002220801470496586110679 33003331202205744879166019)
            ·
              refine ⟨49504996803308617318749029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33003331202205744879166019 49504996803308617318749029)
              ·
                refine ⟨9282186900620365747265443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49504996803308617318749029 9282186900620365747265443)
                ·
                  refine ⟨13923280350930548620898165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9282186900620365747265443 13923280350930548620898165)
                  ·
                    refine ⟨1305307532899738933209203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13923280350930548620898165 1305307532899738933209203)
                    ·
                      rfl

theorem cell22_3813116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_3813116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3813116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3813116 prefixEnd_3813116 := by exact prefixLift 3813116
  have htrace : WordTrace (prefixWord ++ tailWord_3813116) baseStart_3813116 baseEnd_3813116 := by
    simpa [prefixWord, tailWord_3813116, baseEnd_3813116] using wordTrace_append hprefix tailTrace_3813116
  have hstable : (prefixWord ++ tailWord_3813116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813116).length < 2 ^ (prefixWord ++ tailWord_3813116).sum := by decide
  have hdescent : baseEnd_3813116 < baseStart_3813116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813131 : List Nat := [1, 1, 1, 1, 5, 1, 2, 4, 2, 4]
def baseStart_3813131 : Nat := 118140960795 + 3813131 * 2 ^ 59
def prefixEnd_3813131 : Nat := 4983230072969 + 3 ^ 40 * 3813131 * 2
def baseEnd_3813131 : Nat := 1305312667706283894084157

theorem tailTrace_3813131 : CollatzResearch.WordTrace tailWord_3813131 prefixEnd_3813131 1305312667706283894084157 := by
  unfold tailWord_3813131
  simp only [CollatzResearch.WordTrace]
  refine ⟨139076313148685092772767247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92717542099123395181844831 139076313148685092772767247)
  ·
    refine ⟨208614469723027639159150871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139076313148685092772767247 208614469723027639159150871)
    ·
      refine ⟨312921704584541458738726307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208614469723027639159150871 312921704584541458738726307)
      ·
        refine ⟨469382556876812188108089461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312921704584541458738726307 469382556876812188108089461)
        ·
          refine ⟨44004614707201142635133387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 469382556876812188108089461 44004614707201142635133387)
          ·
            refine ⟨66006922060801713952700081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44004614707201142635133387 66006922060801713952700081)
            ·
              refine ⟨49505191545601285464525061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66006922060801713952700081 49505191545601285464525061)
              ·
                refine ⟨9282223414800241024598449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49505191545601285464525061 9282223414800241024598449)
                ·
                  refine ⟨6961667561100180768448837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9282223414800241024598449 6961667561100180768448837)
                  ·
                    refine ⟨1305312667706283894084157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6961667561100180768448837 1305312667706283894084157)
                    ·
                      rfl

theorem cell22_3813131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 4].length) (baseStart_3813131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3813131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3813131 prefixEnd_3813131 := by exact prefixLift 3813131
  have htrace : WordTrace (prefixWord ++ tailWord_3813131) baseStart_3813131 baseEnd_3813131 := by
    simpa [prefixWord, tailWord_3813131, baseEnd_3813131] using wordTrace_append hprefix tailTrace_3813131
  have hstable : (prefixWord ++ tailWord_3813131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813131).length < 2 ^ (prefixWord ++ tailWord_3813131).sum := by decide
  have hdescent : baseEnd_3813131 < baseStart_3813131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813191 : List Nat := [1, 1, 4, 1, 2, 1, 4, 1, 7]
def baseStart_3813191 : Nat := 118140960795 + 3813191 * 2 ^ 59
def prefixEnd_3813191 : Nat := 4983230072969 + 3 ^ 40 * 3813191 * 2
def baseEnd_3813191 : Nat := 435111068977487912527991

theorem tailTrace_3813191 : CollatzResearch.WordTrace tailWord_3813191 prefixEnd_3813191 435111068977487912527991 := by
  unfold tailWord_3813191
  simp only [CollatzResearch.WordTrace]
  refine ⟨139078501528467723019951427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92719001018978482013300951 139078501528467723019951427)
  ·
    refine ⟨208617752292701584529927141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139078501528467723019951427 208617752292701584529927141)
    ·
      refine ⟨39115828554881547099361339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208617752292701584529927141 39115828554881547099361339)
      ·
        refine ⟨58673742832322320649042009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39115828554881547099361339 58673742832322320649042009)
        ·
          refine ⟨44005307124241740486781507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58673742832322320649042009 44005307124241740486781507)
          ·
            refine ⟨66007960686362610730172261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44005307124241740486781507 66007960686362610730172261)
            ·
              refine ⟨12376492628692989511907299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66007960686362610730172261 12376492628692989511907299)
              ·
                refine ⟨18564738943039484267860949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12376492628692989511907299 18564738943039484267860949)
                ·
                  refine ⟨435111068977487912527991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18564738943039484267860949 435111068977487912527991)
                  ·
                    rfl

theorem cell22_3813191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 7].length) (baseStart_3813191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3813191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3813191 prefixEnd_3813191 := by exact prefixLift 3813191
  have htrace : WordTrace (prefixWord ++ tailWord_3813191) baseStart_3813191 baseEnd_3813191 := by
    simpa [prefixWord, tailWord_3813191, baseEnd_3813191] using wordTrace_append hprefix tailTrace_3813191
  have hstable : (prefixWord ++ tailWord_3813191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813191).length < 2 ^ (prefixWord ++ tailWord_3813191).sum := by decide
  have hdescent : baseEnd_3813191 < baseStart_3813191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813246 : List Nat := [4, 2, 3, 1, 1, 1, 4, 2, 1, 3]
def baseStart_3813246 : Nat := 118140960795 + 3813246 * 2 ^ 59
def prefixEnd_3813246 : Nat := 4983230072969 + 3 ^ 40 * 3813246 * 2
def baseEnd_3813246 : Nat := 1305352034556461927458805

theorem tailTrace_3813246 : CollatzResearch.WordTrace tailWord_3813246 prefixEnd_3813246 1305352034556461927458805 := by
  unfold tailWord_3813246
  simp only [CollatzResearch.WordTrace]
  refine ⟨17385063442908558426650449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92720338362178978275469061 17385063442908558426650449)
  ·
    refine ⟨13038797582181418819987837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17385063442908558426650449 13038797582181418819987837)
    ·
      refine ⟨4889549093318032057495439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13038797582181418819987837 4889549093318032057495439)
      ·
        refine ⟨7334323639977048086243159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4889549093318032057495439 7334323639977048086243159)
        ·
          refine ⟨11001485459965572129364739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7334323639977048086243159 11001485459965572129364739)
          ·
            refine ⟨16502228189948358194047109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11001485459965572129364739 16502228189948358194047109)
            ·
              refine ⟨3094167785615317161383833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16502228189948358194047109 3094167785615317161383833)
              ·
                refine ⟨2320625839211487871037875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3094167785615317161383833 2320625839211487871037875)
                ·
                  refine ⟨3480938758817231806556813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2320625839211487871037875 3480938758817231806556813)
                  ·
                    refine ⟨1305352034556461927458805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3480938758817231806556813 1305352034556461927458805)
                    ·
                      rfl

theorem cell22_3813246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_3813246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3813246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3813246 prefixEnd_3813246 := by exact prefixLift 3813246
  have htrace : WordTrace (prefixWord ++ tailWord_3813246) baseStart_3813246 baseEnd_3813246 := by
    simpa [prefixWord, tailWord_3813246, baseEnd_3813246] using wordTrace_append hprefix tailTrace_3813246
  have hstable : (prefixWord ++ tailWord_3813246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813246).length < 2 ^ (prefixWord ++ tailWord_3813246).sum := by decide
  have hdescent : baseEnd_3813246 < baseStart_3813246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813287 : List Nat := [1, 1, 6, 1, 2, 2, 2, 3, 4]
def baseStart_3813287 : Nat := 118140960795 + 3813287 * 2 ^ 59
def prefixEnd_3813287 : Nat := 4983230072969 + 3 ^ 40 * 3813287 * 2
def baseEnd_3813287 : Nat := 435122023231450495727893

theorem tailTrace_3813287 : CollatzResearch.WordTrace tailWord_3813287 prefixEnd_3813287 435122023231450495727893 := by
  unfold tailWord_3813287
  simp only [CollatzResearch.WordTrace]
  refine ⟨139082002936119931415446115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92721335290746620943630743 139082002936119931415446115)
  ·
    refine ⟨208623004404179897123169173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139082002936119931415446115 208623004404179897123169173)
    ·
      refine ⟨9779203331445932677648555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 208623004404179897123169173 9779203331445932677648555)
      ·
        refine ⟨14668804997168899016472833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9779203331445932677648555 14668804997168899016472833)
        ·
          refine ⟨11001603747876674262354625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14668804997168899016472833 11001603747876674262354625)
          ·
            refine ⟨8251202810907505696765969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11001603747876674262354625 8251202810907505696765969)
            ·
              refine ⟨6188402108180629272574477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8251202810907505696765969 6188402108180629272574477)
              ·
                refine ⟨2320650790567735977215429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6188402108180629272574477 2320650790567735977215429)
                ·
                  refine ⟨435122023231450495727893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2320650790567735977215429 435122023231450495727893)
                  ·
                    rfl

theorem cell22_3813287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 3, 4].length) (baseStart_3813287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3813287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3813287 prefixEnd_3813287 := by exact prefixLift 3813287
  have htrace : WordTrace (prefixWord ++ tailWord_3813287) baseStart_3813287 baseEnd_3813287 := by
    simpa [prefixWord, tailWord_3813287, baseEnd_3813287] using wordTrace_append hprefix tailTrace_3813287
  have hstable : (prefixWord ++ tailWord_3813287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813287).length < 2 ^ (prefixWord ++ tailWord_3813287).sum := by decide
  have hdescent : baseEnd_3813287 < baseStart_3813287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813296 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 3, 9]
def baseStart_3813296 : Nat := 118140960795 + 3813296 * 2 ^ 59
def prefixEnd_3813296 : Nat := 4983230072969 + 3 ^ 40 * 3813296 * 2
def baseEnd_3813296 : Nat := 1305369150578278463708651

theorem tailTrace_3813296 : CollatzResearch.WordTrace tailWord_3813296 prefixEnd_3813296 1305369150578278463708651 := by
  unfold tailWord_3813296
  simp only [CollatzResearch.WordTrace]
  refine ⟨69541165596543662976261871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92721554128724883968349161 69541165596543662976261871)
  ·
    refine ⟨104311748394815494464392807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69541165596543662976261871 104311748394815494464392807)
    ·
      refine ⟨156467622592223241696589211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104311748394815494464392807 156467622592223241696589211)
      ·
        refine ⟨234701433888334862544883817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156467622592223241696589211 234701433888334862544883817)
        ·
          refine ⟨176026075416251146908662863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234701433888334862544883817 176026075416251146908662863)
          ·
            refine ⟨264039113124376720362994295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176026075416251146908662863 264039113124376720362994295)
            ·
              refine ⟨396058669686565080544491443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264039113124376720362994295 396058669686565080544491443)
              ·
                refine ⟨594088004529847620816737165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 396058669686565080544491443 594088004529847620816737165)
                ·
                  refine ⟨222783001698692857806276437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 594088004529847620816737165 222783001698692857806276437)
                  ·
                    refine ⟨1305369150578278463708651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 222783001698692857806276437 1305369150578278463708651)
                    ·
                      rfl

theorem cell22_3813296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 9].length) (baseStart_3813296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3813296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3813296 prefixEnd_3813296 := by exact prefixLift 3813296
  have htrace : WordTrace (prefixWord ++ tailWord_3813296) baseStart_3813296 baseEnd_3813296 := by
    simpa [prefixWord, tailWord_3813296, baseEnd_3813296] using wordTrace_append hprefix tailTrace_3813296
  have hstable : (prefixWord ++ tailWord_3813296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813296).length < 2 ^ (prefixWord ++ tailWord_3813296).sum := by decide
  have hdescent : baseEnd_3813296 < baseStart_3813296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813343 : List Nat := [1, 1, 2, 3, 4, 1, 1, 2, 7]
def baseStart_3813343 : Nat := 118140960795 + 3813343 * 2 ^ 59
def prefixEnd_3813343 : Nat := 4983230072969 + 3 ^ 40 * 3813343 * 2
def baseEnd_3813343 : Nat := 435128413212928669261169

theorem tailTrace_3813343 : CollatzResearch.WordTrace tailWord_3813343 prefixEnd_3813343 435128413212928669261169 := by
  unfold tailWord_3813343
  simp only [CollatzResearch.WordTrace]
  refine ⟨139084045423917052979484683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92722696949278035319656455 139084045423917052979484683)
  ·
    refine ⟨208626068135875579469227025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139084045423917052979484683 208626068135875579469227025)
    ·
      refine ⟨156469551101906684601920269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208626068135875579469227025 156469551101906684601920269)
      ·
        refine ⟨58676081663215006725720101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156469551101906684601920269 58676081663215006725720101)
        ·
          refine ⟨11001765311852813761072519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58676081663215006725720101 11001765311852813761072519)
          ·
            refine ⟨16502647967779220641608779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11001765311852813761072519 16502647967779220641608779)
            ·
              refine ⟨24753971951668830962413169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16502647967779220641608779 24753971951668830962413169)
              ·
                refine ⟨18565478963751623221809877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24753971951668830962413169 18565478963751623221809877)
                ·
                  refine ⟨435128413212928669261169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18565478963751623221809877 435128413212928669261169)
                  ·
                    rfl

theorem cell22_3813343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 7].length) (baseStart_3813343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3813343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3813343 prefixEnd_3813343 := by exact prefixLift 3813343
  have htrace : WordTrace (prefixWord ++ tailWord_3813343) baseStart_3813343 baseEnd_3813343 := by
    simpa [prefixWord, tailWord_3813343, baseEnd_3813343] using wordTrace_append hprefix tailTrace_3813343
  have hstable : (prefixWord ++ tailWord_3813343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813343).length < 2 ^ (prefixWord ++ tailWord_3813343).sum := by decide
  have hdescent : baseEnd_3813343 < baseStart_3813343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813388 : List Nat := [2, 2, 1, 2, 3, 1, 2, 1, 8]
def baseStart_3813388 : Nat := 118140960795 + 3813388 * 2 ^ 59
def prefixEnd_3813388 : Nat := 4983230072969 + 3 ^ 40 * 3813388 * 2
def baseEnd_3813388 : Nat := 435133548019473630136123

theorem tailTrace_3813388 : CollatzResearch.WordTrace tailWord_3813388 prefixEnd_3813388 435133548019473630136123 := by
  unfold tailWord_3813388
  simp only [CollatzResearch.WordTrace]
  refine ⟨69542843354377012832436409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92723791139169350443248545 69542843354377012832436409)
  ·
    refine ⟨52157132515782759624327307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69542843354377012832436409 52157132515782759624327307)
    ·
      refine ⟨78235698773674139436490961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52157132515782759624327307 78235698773674139436490961)
      ·
        refine ⟨58676774080255604577368221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78235698773674139436490961 58676774080255604577368221)
        ·
          refine ⟨22003790280095851716513083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58676774080255604577368221 22003790280095851716513083)
          ·
            refine ⟨33005685420143777574769625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22003790280095851716513083 33005685420143777574769625)
            ·
              refine ⟨24754264065107833181077219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33005685420143777574769625 24754264065107833181077219)
              ·
                refine ⟨37131396097661749771615829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24754264065107833181077219 37131396097661749771615829)
                ·
                  refine ⟨435133548019473630136123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37131396097661749771615829 435133548019473630136123)
                  ·
                    rfl

theorem cell22_3813388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 8].length) (baseStart_3813388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3813388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3813388 prefixEnd_3813388 := by exact prefixLift 3813388
  have htrace : WordTrace (prefixWord ++ tailWord_3813388) baseStart_3813388 baseEnd_3813388 := by
    simpa [prefixWord, tailWord_3813388, baseEnd_3813388] using wordTrace_append hprefix tailTrace_3813388
  have hstable : (prefixWord ++ tailWord_3813388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813388).length < 2 ^ (prefixWord ++ tailWord_3813388).sum := by decide
  have hdescent : baseEnd_3813388 < baseStart_3813388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813390 : List Nat := [4, 1, 1, 2, 2, 1, 3, 1, 3, 4]
def baseStart_3813390 : Nat := 118140960795 + 3813390 * 2 ^ 59
def prefixEnd_3813390 : Nat := 4983230072969 + 3 ^ 40 * 3813390 * 2
def baseEnd_3813390 : Nat := 1305401328699293551858363

theorem tailTrace_3813390 : CollatzResearch.WordTrace tailWord_3813390 prefixEnd_3813390 1305401328699293551858363 := by
  unfold tailWord_3813390
  simp only [CollatzResearch.WordTrace]
  refine ⟨17385719956843347500805703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92723839769831186670963749 17385719956843347500805703)
  ·
    refine ⟨26078579935265021251208555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17385719956843347500805703 26078579935265021251208555)
    ·
      refine ⟨39117869902897531876812833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26078579935265021251208555 39117869902897531876812833)
      ·
        refine ⟨29338402427173148907609625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39117869902897531876812833 29338402427173148907609625)
        ·
          refine ⟨22003801820379861680707219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29338402427173148907609625 22003801820379861680707219)
          ·
            refine ⟨33005702730569792521060829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22003801820379861680707219 33005702730569792521060829)
            ·
              refine ⟨12377138523963672195397811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33005702730569792521060829 12377138523963672195397811)
              ·
                refine ⟨18565707785945508293096717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12377138523963672195397811 18565707785945508293096717)
                ·
                  refine ⟨6962140419729565609911269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18565707785945508293096717 6962140419729565609911269)
                  ·
                    refine ⟨1305401328699293551858363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6962140419729565609911269 1305401328699293551858363)
                    ·
                      rfl

theorem cell22_3813390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_3813390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3813390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3813390 prefixEnd_3813390 := by exact prefixLift 3813390
  have htrace : WordTrace (prefixWord ++ tailWord_3813390) baseStart_3813390 baseEnd_3813390 := by
    simpa [prefixWord, tailWord_3813390, baseEnd_3813390] using wordTrace_append hprefix tailTrace_3813390
  have hstable : (prefixWord ++ tailWord_3813390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813390).length < 2 ^ (prefixWord ++ tailWord_3813390).sum := by decide
  have hdescent : baseEnd_3813390 < baseStart_3813390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813407 : List Nat := [1, 1, 2, 4, 1, 2, 5, 1, 1, 4]
def baseStart_3813407 : Nat := 118140960795 + 3813407 * 2 ^ 59
def prefixEnd_3813407 : Nat := 4983230072969 + 3 ^ 40 * 3813407 * 2
def baseEnd_3813407 : Nat := 1305407148146711174183311

theorem tailTrace_3813407 : CollatzResearch.WordTrace tailWord_3813407 prefixEnd_3813407 1305407148146711174183311 := by
  unfold tailWord_3813407
  simp only [CollatzResearch.WordTrace]
  refine ⟨139086379695685191909814475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92724253130456794606542983 139086379695685191909814475)
  ·
    refine ⟨208629569543527787864721713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139086379695685191909814475 208629569543527787864721713)
    ·
      refine ⟨156472177157645840898541285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208629569543527787864721713 156472177157645840898541285)
      ·
        refine ⟨29338533217058595168476491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156472177157645840898541285 29338533217058595168476491)
        ·
          refine ⟨44007799825587892752714737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29338533217058595168476491 44007799825587892752714737)
          ·
            refine ⟨33005849869190919564536053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44007799825587892752714737 33005849869190919564536053)
            ·
              refine ⟨3094298425236648709175255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33005849869190919564536053 3094298425236648709175255)
              ·
                refine ⟨4641447637854973063762883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3094298425236648709175255 4641447637854973063762883)
                ·
                  refine ⟨6962171456782459595644325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4641447637854973063762883 6962171456782459595644325)
                  ·
                    refine ⟨1305407148146711174183311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6962171456782459595644325 1305407148146711174183311)
                    ·
                      rfl

theorem cell22_3813407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 1, 1, 4].length) (baseStart_3813407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3813407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3813407 prefixEnd_3813407 := by exact prefixLift 3813407
  have htrace : WordTrace (prefixWord ++ tailWord_3813407) baseStart_3813407 baseEnd_3813407 := by
    simpa [prefixWord, tailWord_3813407, baseEnd_3813407] using wordTrace_append hprefix tailTrace_3813407
  have hstable : (prefixWord ++ tailWord_3813407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813407).length < 2 ^ (prefixWord ++ tailWord_3813407).sum := by decide
  have hdescent : baseEnd_3813407 < baseStart_3813407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813415 : List Nat := [1, 1, 7, 1, 3, 1, 2, 2, 1, 3]
def baseStart_3813415 : Nat := 118140960795 + 3813415 * 2 ^ 59
def prefixEnd_3813415 : Nat := 4983230072969 + 3 ^ 40 * 3813415 * 2
def baseEnd_3813415 : Nat := 1305409886710201819983287

theorem tailTrace_3813415 : CollatzResearch.WordTrace tailWord_3813415 prefixEnd_3813415 1305409886710201819983287 := by
  unfold tailWord_3813415
  simp only [CollatzResearch.WordTrace]
  refine ⟨139086671479656209276105699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92724447653104139517403799 139086671479656209276105699)
  ·
    refine ⟨208630007219484313914158549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139086671479656209276105699 208630007219484313914158549)
    ·
      refine ⟨4889765794206663607363091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 208630007219484313914158549 4889765794206663607363091)
      ·
        refine ⟨7334648691309995411044637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4889765794206663607363091 7334648691309995411044637)
        ·
          refine ⟨2750493259241248279141739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7334648691309995411044637 2750493259241248279141739)
          ·
            refine ⟨4125739888861872418712609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2750493259241248279141739 4125739888861872418712609)
            ·
              refine ⟨3094304916646404314034457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4125739888861872418712609 3094304916646404314034457)
              ·
                refine ⟨2320728687484803235525843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3094304916646404314034457 2320728687484803235525843)
                ·
                  refine ⟨3481093031227204853288765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2320728687484803235525843 3481093031227204853288765)
                  ·
                    refine ⟨1305409886710201819983287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3481093031227204853288765 1305409886710201819983287)
                    ·
                      rfl

theorem cell22_3813415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_3813415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3813415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3813415 prefixEnd_3813415 := by exact prefixLift 3813415
  have htrace : WordTrace (prefixWord ++ tailWord_3813415) baseStart_3813415 baseEnd_3813415 := by
    simpa [prefixWord, tailWord_3813415, baseEnd_3813415] using wordTrace_append hprefix tailTrace_3813415
  have hstable : (prefixWord ++ tailWord_3813415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813415).length < 2 ^ (prefixWord ++ tailWord_3813415).sum := by decide
  have hdescent : baseEnd_3813415 < baseStart_3813415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813437 : List Nat := [1, 4, 1, 3, 1, 1, 1, 5, 2, 3]
def baseStart_3813437 : Nat := 118140960795 + 3813437 * 2 ^ 59
def prefixEnd_3813437 : Nat := 4983230072969 + 3 ^ 40 * 3813437 * 2
def baseEnd_3813437 : Nat := 1305417417759801095933219

theorem tailTrace_3813437 : CollatzResearch.WordTrace tailWord_3813437 prefixEnd_3813437 1305417417759801095933219 := by
  unfold tailWord_3813437
  simp only [CollatzResearch.WordTrace]
  refine ⟨139087473885576507033406565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92724982590384338022271043 139087473885576507033406565)
  ·
    refine ⟨26078901353545595068763731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139087473885576507033406565 26078901353545595068763731)
    ·
      refine ⟨39118352030318392603145597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26078901353545595068763731 39118352030318392603145597)
      ·
        refine ⟨14669382011369397226179599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39118352030318392603145597 14669382011369397226179599)
        ·
          refine ⟨22004073017054095839269399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14669382011369397226179599 22004073017054095839269399)
          ·
            refine ⟨33006109525581143758904099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22004073017054095839269399 33006109525581143758904099)
            ·
              refine ⟨49509164288371715638356149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33006109525581143758904099 49509164288371715638356149)
              ·
                refine ⟨4641484152034848341095889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49509164288371715638356149 4641484152034848341095889)
                ·
                  refine ⟨3481113114026136255821917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4641484152034848341095889 3481113114026136255821917)
                  ·
                    refine ⟨1305417417759801095933219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3481113114026136255821917 1305417417759801095933219)
                    ·
                      rfl

theorem cell22_3813437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_3813437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3813437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3813437 prefixEnd_3813437 := by exact prefixLift 3813437
  have htrace : WordTrace (prefixWord ++ tailWord_3813437) baseStart_3813437 baseEnd_3813437 := by
    simpa [prefixWord, tailWord_3813437, baseEnd_3813437] using wordTrace_append hprefix tailTrace_3813437
  have hstable : (prefixWord ++ tailWord_3813437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813437).length < 2 ^ (prefixWord ++ tailWord_3813437).sum := by decide
  have hdescent : baseEnd_3813437 < baseStart_3813437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813448 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 1, 9]
def baseStart_3813448 : Nat := 118140960795 + 3813448 * 2 ^ 59
def prefixEnd_3813448 : Nat := 4983230072969 + 3 ^ 40 * 3813448 * 2
def baseEnd_3813448 : Nat := 1305421183284600733908185

theorem tailTrace_3813448 : CollatzResearch.WordTrace tailWord_3813448 prefixEnd_3813448 1305421183284600733908185 := by
  unfold tailWord_3813448
  simp only [CollatzResearch.WordTrace]
  refine ⟨69543937544268327956028499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92725250059024437274704665 69543937544268327956028499)
  ·
    refine ⟨104315906316402491934042749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69543937544268327956028499 104315906316402491934042749)
    ·
      refine ⟨39118464868650934475266031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104315906316402491934042749 39118464868650934475266031)
      ·
        refine ⟨58677697302976401712899047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39118464868650934475266031 58677697302976401712899047)
        ·
          refine ⟨88016545954464602569348571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58677697302976401712899047 88016545954464602569348571)
          ·
            refine ⟨132024818931696903854022857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88016545954464602569348571 132024818931696903854022857)
            ·
              refine ⟨99018614198772677890517143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132024818931696903854022857 99018614198772677890517143)
              ·
                refine ⟨148527921298159016835775715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99018614198772677890517143 148527921298159016835775715)
                ·
                  refine ⟨222791881947238525253663573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148527921298159016835775715 222791881947238525253663573)
                  ·
                    refine ⟨1305421183284600733908185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 222791881947238525253663573 1305421183284600733908185)
                    ·
                      rfl

theorem cell22_3813448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_3813448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3813448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3813448 prefixEnd_3813448 := by exact prefixLift 3813448
  have htrace : WordTrace (prefixWord ++ tailWord_3813448) baseStart_3813448 baseEnd_3813448 := by
    simpa [prefixWord, tailWord_3813448, baseEnd_3813448] using wordTrace_append hprefix tailTrace_3813448
  have hstable : (prefixWord ++ tailWord_3813448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813448).length < 2 ^ (prefixWord ++ tailWord_3813448).sum := by decide
  have hdescent : baseEnd_3813448 < baseStart_3813448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813465 : List Nat := [1, 2, 1, 2, 2, 1, 3, 2, 5, 3]
def baseStart_3813465 : Nat := 118140960795 + 3813465 * 2 ^ 59
def prefixEnd_3813465 : Nat := 4983230072969 + 3 ^ 40 * 3813465 * 2
def baseEnd_3813465 : Nat := 1305427002732018356233133

theorem tailTrace_3813465 : CollatzResearch.WordTrace tailWord_3813465 prefixEnd_3813465 1305427002732018356233133 := by
  unfold tailWord_3813465
  simp only [CollatzResearch.WordTrace]
  refine ⟨139088495129475067815425849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92725663419650045210283899 139088495129475067815425849)
  ·
    refine ⟨104316371347106300861569387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139088495129475067815425849 104316371347106300861569387)
    ·
      refine ⟨156474557020659451292354081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104316371347106300861569387 156474557020659451292354081)
      ·
        refine ⟨117355917765494588469265561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156474557020659451292354081 117355917765494588469265561)
        ·
          refine ⟨88016938324120941351949171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117355917765494588469265561 88016938324120941351949171)
          ·
            refine ⟨132025407486181412027923757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88016938324120941351949171 132025407486181412027923757)
            ·
              refine ⟨49509527807318029510471409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132025407486181412027923757 49509527807318029510471409)
              ·
                refine ⟨37132145855488522132853557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49509527807318029510471409 37132145855488522132853557)
                ·
                  refine ⟨3481138673952048949955021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37132145855488522132853557 3481138673952048949955021)
                  ·
                    refine ⟨1305427002732018356233133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3481138673952048949955021 1305427002732018356233133)
                    ·
                      rfl

theorem cell22_3813465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 5, 3].length) (baseStart_3813465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3813465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3813465 prefixEnd_3813465 := by exact prefixLift 3813465
  have htrace : WordTrace (prefixWord ++ tailWord_3813465) baseStart_3813465 baseEnd_3813465 := by
    simpa [prefixWord, tailWord_3813465, baseEnd_3813465] using wordTrace_append hprefix tailTrace_3813465
  have hstable : (prefixWord ++ tailWord_3813465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813465).length < 2 ^ (prefixWord ++ tailWord_3813465).sum := by decide
  have hdescent : baseEnd_3813465 < baseStart_3813465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813555 : List Nat := [1, 1, 1, 2, 3, 2, 1, 5, 1, 5]
def baseStart_3813555 : Nat := 118140960795 + 3813555 * 2 ^ 59
def prefixEnd_3813555 : Nat := 4983230072969 + 3 ^ 40 * 3813555 * 2
def baseEnd_3813555 : Nat := 1305457811571288121482857

theorem tailTrace_3813555 : CollatzResearch.WordTrace tailWord_3813555 prefixEnd_3813555 1305457811571288121482857 := by
  unfold tailWord_3813555
  simp only [CollatzResearch.WordTrace]
  refine ⟨139091777699149013186202119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92727851799432675457468079 139091777699149013186202119)
  ·
    refine ⟨208637666548723519779303179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139091777699149013186202119 208637666548723519779303179)
    ·
      refine ⟨312956499823085279668954769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208637666548723519779303179 312956499823085279668954769)
      ·
        refine ⟨234717374867313959751716077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312956499823085279668954769 234717374867313959751716077)
        ·
          refine ⟨88019015575242734906893529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234717374867313959751716077 88019015575242734906893529)
          ·
            refine ⟨66014261681432051180170147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88019015575242734906893529 66014261681432051180170147)
            ·
              refine ⟨99021392522148076770255221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66014261681432051180170147 99021392522148076770255221)
              ·
                refine ⟨9283255548951382197211427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99021392522148076770255221 9283255548951382197211427)
                ·
                  refine ⟨13924883323427073295817141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9283255548951382197211427 13924883323427073295817141)
                  ·
                    refine ⟨1305457811571288121482857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13924883323427073295817141 1305457811571288121482857)
                    ·
                      rfl

theorem cell22_3813555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 5].length) (baseStart_3813555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3813555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3813555 prefixEnd_3813555 := by exact prefixLift 3813555
  have htrace : WordTrace (prefixWord ++ tailWord_3813555) baseStart_3813555 baseEnd_3813555 := by
    simpa [prefixWord, tailWord_3813555, baseEnd_3813555] using wordTrace_append hprefix tailTrace_3813555
  have hstable : (prefixWord ++ tailWord_3813555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813555).length < 2 ^ (prefixWord ++ tailWord_3813555).sum := by decide
  have hdescent : baseEnd_3813555 < baseStart_3813555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813559 : List Nat := [1, 1, 3, 1, 4, 4, 1, 2, 1, 4]
def baseStart_3813559 : Nat := 118140960795 + 3813559 * 2 ^ 59
def prefixEnd_3813559 : Nat := 4983230072969 + 3 ^ 40 * 3813559 * 2
def baseEnd_3813559 : Nat := 1305459180853033444382845

theorem tailTrace_3813559 : CollatzResearch.WordTrace tailWord_3813559 prefixEnd_3813559 1305459180853033444382845 := by
  unfold tailWord_3813559
  simp only [CollatzResearch.WordTrace]
  refine ⟨139091923591134521869347731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92727949060756347912898487 139091923591134521869347731)
  ·
    refine ⟨208637885386701782804021597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139091923591134521869347731 208637885386701782804021597)
    ·
      refine ⟨78239207020013168551508099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208637885386701782804021597 78239207020013168551508099)
      ·
        refine ⟨117358810530019752827262149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78239207020013168551508099 117358810530019752827262149)
        ·
          refine ⟨22004776974378703655111653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117358810530019752827262149 22004776974378703655111653)
          ·
            refine ⟨4125895682696006935333435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22004776974378703655111653 4125895682696006935333435)
            ·
              refine ⟨6188843524044010403000153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4125895682696006935333435 6188843524044010403000153)
              ·
                refine ⟨4641632643033007802250115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6188843524044010403000153 4641632643033007802250115)
                ·
                  refine ⟨6962448964549511703375173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4641632643033007802250115 6962448964549511703375173)
                  ·
                    refine ⟨1305459180853033444382845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6962448964549511703375173 1305459180853033444382845)
                    ·
                      rfl

theorem cell22_3813559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 4].length) (baseStart_3813559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3813559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3813559 prefixEnd_3813559 := by exact prefixLift 3813559
  have htrace : WordTrace (prefixWord ++ tailWord_3813559) baseStart_3813559 baseEnd_3813559 := by
    simpa [prefixWord, tailWord_3813559, baseEnd_3813559] using wordTrace_append hprefix tailTrace_3813559
  have hstable : (prefixWord ++ tailWord_3813559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813559).length < 2 ^ (prefixWord ++ tailWord_3813559).sum := by decide
  have hdescent : baseEnd_3813559 < baseStart_3813559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813572 : List Nat := [2, 3, 3, 1, 2, 1, 1, 1, 3, 5]
def baseStart_3813572 : Nat := 118140960795 + 3813572 * 2 ^ 59
def prefixEnd_3813572 : Nat := 4983230072969 + 3 ^ 40 * 3813572 * 2
def baseEnd_3813572 : Nat := 1305463631018705743807805

theorem tailTrace_3813572 : CollatzResearch.WordTrace tailWord_3813572 prefixEnd_3813572 1305463631018705743807805 := by
  unfold tailWord_3813572
  simp only [CollatzResearch.WordTrace]
  refine ⟨69546198870043712544785485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92728265160058283393047313 69546198870043712544785485)
  ·
    refine ⟨26079824576266392204294557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69546198870043712544785485 26079824576266392204294557)
    ·
      refine ⟨9779934216099897076610459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26079824576266392204294557 9779934216099897076610459)
      ·
        refine ⟨14669901324149845614915689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9779934216099897076610459 14669901324149845614915689)
        ·
          refine ⟨11002425993112384211186767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14669901324149845614915689 11002425993112384211186767)
          ·
            refine ⟨16503638989668576316780151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11002425993112384211186767 16503638989668576316780151)
            ·
              refine ⟨24755458484502864475170227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16503638989668576316780151 24755458484502864475170227)
              ·
                refine ⟨37133187726754296712755341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24755458484502864475170227 37133187726754296712755341)
                ·
                  refine ⟨13924945397532861267283253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37133187726754296712755341 13924945397532861267283253)
                  ·
                    refine ⟨1305463631018705743807805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13924945397532861267283253 1305463631018705743807805)
                    ·
                      rfl

theorem cell22_3813572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_3813572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3813572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3813572 prefixEnd_3813572 := by exact prefixLift 3813572
  have htrace : WordTrace (prefixWord ++ tailWord_3813572) baseStart_3813572 baseEnd_3813572 := by
    simpa [prefixWord, tailWord_3813572, baseEnd_3813572] using wordTrace_append hprefix tailTrace_3813572
  have hstable : (prefixWord ++ tailWord_3813572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813572).length < 2 ^ (prefixWord ++ tailWord_3813572).sum := by decide
  have hdescent : baseEnd_3813572 < baseStart_3813572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813617 : List Nat := [1, 2, 2, 2, 2, 1, 3, 1, 5, 3]
def baseStart_3813617 : Nat := 118140960795 + 3813617 * 2 ^ 59
def prefixEnd_3813617 : Nat := 4983230072969 + 3 ^ 40 * 3813617 * 2
def baseEnd_3813617 : Nat := 1305479035438340626432667

theorem tailTrace_3813617 : CollatzResearch.WordTrace tailWord_3813617 prefixEnd_3813617 1305479035438340626432667 := by
  unfold tailWord_3813617
  simp only [CollatzResearch.WordTrace]
  refine ⟨139094039024924397774959105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92729359349949598516639403 139094039024924397774959105)
  ·
    refine ⟨104320529268693298331219329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139094039024924397774959105 104320529268693298331219329)
    ·
      refine ⟨78240396951519973748414497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104320529268693298331219329 78240396951519973748414497)
      ·
        refine ⟨58680297713639980311310873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78240396951519973748414497 58680297713639980311310873)
        ·
          refine ⟨44010223285229985233483155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58680297713639980311310873 44010223285229985233483155)
          ·
            refine ⟨66015334927844977850224733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44010223285229985233483155 66015334927844977850224733)
            ·
              refine ⟨24755750597941866693834275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66015334927844977850224733 24755750597941866693834275)
              ·
                refine ⟨37133625896912800040751413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24755750597941866693834275 37133625896912800040751413)
                ·
                  refine ⟨3481277427835575003820445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37133625896912800040751413 3481277427835575003820445)
                  ·
                    refine ⟨1305479035438340626432667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3481277427835575003820445 1305479035438340626432667)
                    ·
                      rfl

theorem cell22_3813617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 5, 3].length) (baseStart_3813617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3813617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3813617 prefixEnd_3813617 := by exact prefixLift 3813617
  have htrace : WordTrace (prefixWord ++ tailWord_3813617) baseStart_3813617 baseEnd_3813617 := by
    simpa [prefixWord, tailWord_3813617, baseEnd_3813617] using wordTrace_append hprefix tailTrace_3813617
  have hstable : (prefixWord ++ tailWord_3813617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813617).length < 2 ^ (prefixWord ++ tailWord_3813617).sum := by decide
  have hdescent : baseEnd_3813617 < baseStart_3813617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813722 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 6, 4]
def baseStart_3813722 : Nat := 118140960795 + 3813722 * 2 ^ 59
def prefixEnd_3813722 : Nat := 4983230072969 + 3 ^ 40 * 3813722 * 2
def baseEnd_3813722 : Nat := 1305514979084155352557345

theorem tailTrace_3813722 : CollatzResearch.WordTrace tailWord_3813722 prefixEnd_3813722 1305514979084155352557345 := by
  unfold tailWord_3813722
  simp only [CollatzResearch.WordTrace]
  refine ⟨34774467172386000176882855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92731912459696000471687613 34774467172386000176882855)
  ·
    refine ⟨52161700758579000265324283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34774467172386000176882855 52161700758579000265324283)
    ·
      refine ⟨78242551137868500397986425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52161700758579000265324283 78242551137868500397986425)
      ·
        refine ⟨58681913353401375298489819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78242551137868500397986425 58681913353401375298489819)
        ·
          refine ⟨88022870030102062947734729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58681913353401375298489819 88022870030102062947734729)
          ·
            refine ⟨66017152522576547210801047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88022870030102062947734729 66017152522576547210801047)
            ·
              refine ⟨99025728783864820816201571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66017152522576547210801047 99025728783864820816201571)
              ·
                refine ⟨148538593175797231224302357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99025728783864820816201571 148538593175797231224302357)
                ·
                  refine ⟨6962746555115495213639173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 148538593175797231224302357 6962746555115495213639173)
                  ·
                    refine ⟨1305514979084155352557345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6962746555115495213639173 1305514979084155352557345)
                    ·
                      rfl

theorem cell22_3813722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_3813722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3813722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3813722 prefixEnd_3813722 := by exact prefixLift 3813722
  have htrace : WordTrace (prefixWord ++ tailWord_3813722) baseStart_3813722 baseEnd_3813722 := by
    simpa [prefixWord, tailWord_3813722, baseEnd_3813722] using wordTrace_append hprefix tailTrace_3813722
  have hstable : (prefixWord ++ tailWord_3813722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813722).length < 2 ^ (prefixWord ++ tailWord_3813722).sum := by decide
  have hdescent : baseEnd_3813722 < baseStart_3813722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813728 : List Nat := [2, 1, 1, 3, 6, 1, 1, 2, 1, 4]
def baseStart_3813728 : Nat := 118140960795 + 3813728 * 2 ^ 59
def prefixEnd_3813728 : Nat := 4983230072969 + 3 ^ 40 * 3813728 * 2
def baseEnd_3813728 : Nat := 1305517033006773336907327

theorem tailTrace_3813728 : CollatzResearch.WordTrace tailWord_3813728 prefixEnd_3813728 1305517033006773336907327 := by
  unfold tailWord_3813728
  simp only [CollatzResearch.WordTrace]
  refine ⟨69549043763761131866124919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92732058351681509154833225 69549043763761131866124919)
  ·
    refine ⟨104323565645641697799187379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69549043763761131866124919 104323565645641697799187379)
    ·
      refine ⟨156485348468462546698781069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104323565645641697799187379 156485348468462546698781069)
      ·
        refine ⟨58682005675673455012042901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156485348468462546698781069 58682005675673455012042901)
        ·
          refine ⟨2750719016047193203689511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 58682005675673455012042901 2750719016047193203689511)
          ·
            refine ⟨4126078524070789805534267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2750719016047193203689511 4126078524070789805534267)
            ·
              refine ⟨6189117786106184708301401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4126078524070789805534267 6189117786106184708301401)
              ·
                refine ⟨4641838339579638531226051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6189117786106184708301401 4641838339579638531226051)
                ·
                  refine ⟨6962757509369457796839077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4641838339579638531226051 6962757509369457796839077)
                  ·
                    refine ⟨1305517033006773336907327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6962757509369457796839077 1305517033006773336907327)
                    ·
                      rfl

theorem cell22_3813728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 1, 4].length) (baseStart_3813728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3813728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3813728 prefixEnd_3813728 := by exact prefixLift 3813728
  have htrace : WordTrace (prefixWord ++ tailWord_3813728) baseStart_3813728 baseEnd_3813728 := by
    simpa [prefixWord, tailWord_3813728, baseEnd_3813728] using wordTrace_append hprefix tailTrace_3813728
  have hstable : (prefixWord ++ tailWord_3813728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813728).length < 2 ^ (prefixWord ++ tailWord_3813728).sum := by decide
  have hdescent : baseEnd_3813728 < baseStart_3813728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813767 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 1, 8]
def baseStart_3813767 : Nat := 118140960795 + 3813767 * 2 ^ 59
def prefixEnd_3813767 : Nat := 4983230072969 + 3 ^ 40 * 3813767 * 2
def baseEnd_3813767 : Nat := 1305530383503790235182207

theorem tailTrace_3813767 : CollatzResearch.WordTrace tailWord_3813767 prefixEnd_3813767 1305530383503790235182207 := by
  unfold tailWord_3813767
  simp only [CollatzResearch.WordTrace]
  refine ⟨139099509974380973392919555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92733006649587315595279703 139099509974380973392919555)
  ·
    refine ⟨208649264961571460089379333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139099509974380973392919555 208649264961571460089379333)
    ·
      refine ⟨39121737180294648766758625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208649264961571460089379333 39121737180294648766758625)
      ·
        refine ⟨29341302885220986575068969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39121737180294648766758625 29341302885220986575068969)
        ·
          refine ⟨22005977163915739931301727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29341302885220986575068969 22005977163915739931301727)
          ·
            refine ⟨33008965745873609896952591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22005977163915739931301727 33008965745873609896952591)
            ·
              refine ⟨49513448618810414845428887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33008965745873609896952591 49513448618810414845428887)
              ·
                refine ⟨74270172928215622268143331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49513448618810414845428887 74270172928215622268143331)
                ·
                  refine ⟨111405259392323433402214997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74270172928215622268143331 111405259392323433402214997)
                  ·
                    refine ⟨1305530383503790235182207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111405259392323433402214997 1305530383503790235182207)
                    ·
                      rfl

theorem cell22_3813767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_3813767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3813767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3813767 prefixEnd_3813767 := by exact prefixLift 3813767
  have htrace : WordTrace (prefixWord ++ tailWord_3813767) baseStart_3813767 baseEnd_3813767 := by
    simpa [prefixWord, tailWord_3813767, baseEnd_3813767] using wordTrace_append hprefix tailTrace_3813767
  have hstable : (prefixWord ++ tailWord_3813767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813767).length < 2 ^ (prefixWord ++ tailWord_3813767).sum := by decide
  have hdescent : baseEnd_3813767 < baseStart_3813767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813786 : List Nat := [3, 1, 1, 4, 1, 3, 1, 2, 3, 3]
def baseStart_3813786 : Nat := 118140960795 + 3813786 * 2 ^ 59
def prefixEnd_3813786 : Nat := 4983230072969 + 3 ^ 40 * 3813786 * 2
def baseEnd_3813786 : Nat := 1305536887592080518957149

theorem tailTrace_3813786 : CollatzResearch.WordTrace tailWord_3813786 prefixEnd_3813786 1305536887592080518957149 := by
  unfold tailWord_3813786
  simp only [CollatzResearch.WordTrace]
  refine ⟨34775050740328034909465303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92733468640874759758574141 34775050740328034909465303)
  ·
    refine ⟨52162576110492052364197955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34775050740328034909465303 52162576110492052364197955)
    ·
      refine ⟨78243864165738078546296933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52162576110492052364197955 78243864165738078546296933)
      ·
        refine ⟨14670724531075889727430675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78243864165738078546296933 14670724531075889727430675)
        ·
          refine ⟨22006086796613834591146013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14670724531075889727430675 22006086796613834591146013)
          ·
            refine ⟨8252282548730187971679755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22006086796613834591146013 8252282548730187971679755)
            ·
              refine ⟨12378423823095281957519633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8252282548730187971679755 12378423823095281957519633)
              ·
                refine ⟨9283817867321461468139725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12378423823095281957519633 9283817867321461468139725)
                ·
                  refine ⟨3481431700245548050552397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9283817867321461468139725 3481431700245548050552397)
                  ·
                    refine ⟨1305536887592080518957149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3481431700245548050552397 1305536887592080518957149)
                    ·
                      rfl

theorem cell22_3813786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 3, 3].length) (baseStart_3813786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3813786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3813786 prefixEnd_3813786 := by exact prefixLift 3813786
  have htrace : WordTrace (prefixWord ++ tailWord_3813786) baseStart_3813786 baseEnd_3813786 := by
    simpa [prefixWord, tailWord_3813786, baseEnd_3813786] using wordTrace_append hprefix tailTrace_3813786
  have hstable : (prefixWord ++ tailWord_3813786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813786).length < 2 ^ (prefixWord ++ tailWord_3813786).sum := by decide
  have hdescent : baseEnd_3813786 < baseStart_3813786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813797 : List Nat := [1, 3, 1, 2, 1, 1, 3, 2, 1, 7]
def baseStart_3813797 : Nat := 118140960795 + 3813797 * 2 ^ 59
def prefixEnd_3813797 : Nat := 4983230072969 + 3 ^ 40 * 3813797 * 2
def baseEnd_3813797 : Nat := 1305540653116880156932115

theorem tailTrace_3813797 : CollatzResearch.WordTrace tailWord_3813797 prefixEnd_3813797 1305540653116880156932115 := by
  unfold tailWord_3813797
  simp only [CollatzResearch.WordTrace]
  refine ⟨139100604164272288516511645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92733736109514859011007763 139100604164272288516511645)
  ·
    refine ⟨52162726561602108193691867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139100604164272288516511645 52162726561602108193691867)
    ·
      refine ⟨78244089842403162290537801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52162726561602108193691867 78244089842403162290537801)
      ·
        refine ⟨58683067381802371717903351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78244089842403162290537801 58683067381802371717903351)
        ·
          refine ⟨88024601072703557576855027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58683067381802371717903351 88024601072703557576855027)
          ·
            refine ⟨132036901609055336365282541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88024601072703557576855027 132036901609055336365282541)
            ·
              refine ⟨49513838103395751136980953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132036901609055336365282541 49513838103395751136980953)
              ·
                refine ⟨37135378577546813352735715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49513838103395751136980953 37135378577546813352735715)
                ·
                  refine ⟨55703067866320220029103573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37135378577546813352735715 55703067866320220029103573)
                  ·
                    refine ⟨1305540653116880156932115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55703067866320220029103573 1305540653116880156932115)
                    ·
                      rfl

theorem cell22_3813797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_3813797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3813797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3813797 prefixEnd_3813797 := by exact prefixLift 3813797
  have htrace : WordTrace (prefixWord ++ tailWord_3813797) baseStart_3813797 baseEnd_3813797 := by
    simpa [prefixWord, tailWord_3813797, baseEnd_3813797] using wordTrace_append hprefix tailTrace_3813797
  have hstable : (prefixWord ++ tailWord_3813797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813797).length < 2 ^ (prefixWord ++ tailWord_3813797).sum := by decide
  have hdescent : baseEnd_3813797 < baseStart_3813797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813889 : List Nat := [1, 2, 4, 1, 3, 1, 1, 9]
def baseStart_3813889 : Nat := 118140960795 + 3813889 * 2 ^ 59
def prefixEnd_3813889 : Nat := 4983230072969 + 3 ^ 40 * 3813889 * 2
def baseEnd_3813889 : Nat := 145063571844113620403537

theorem tailTrace_3813889 : CollatzResearch.WordTrace tailWord_3813889 prefixEnd_3813889 145063571844113620403537 := by
  unfold tailWord_3813889
  simp only [CollatzResearch.WordTrace]
  refine ⟨139103959679938988228860721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92735973119959325485907147 139103959679938988228860721)
  ·
    refine ⟨104327969759954241171645541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139103959679938988228860721 104327969759954241171645541)
    ·
      refine ⟨19561494329991420219683539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104327969759954241171645541 19561494329991420219683539)
      ·
        refine ⟨29342241494987130329525309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19561494329991420219683539 29342241494987130329525309)
        ·
          refine ⟨11003340560620173873571991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29342241494987130329525309 11003340560620173873571991)
          ·
            refine ⟨16505010840930260810357987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11003340560620173873571991 16505010840930260810357987)
            ·
              refine ⟨24757516261395391215536981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16505010840930260810357987 24757516261395391215536981)
              ·
                refine ⟨145063571844113620403537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24757516261395391215536981 145063571844113620403537)
                ·
                  rfl

theorem cell22_3813889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 9].length) (baseStart_3813889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3813889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3813889 prefixEnd_3813889 := by exact prefixLift 3813889
  have htrace : WordTrace (prefixWord ++ tailWord_3813889) baseStart_3813889 baseEnd_3813889 := by
    simpa [prefixWord, tailWord_3813889, baseEnd_3813889] using wordTrace_append hprefix tailTrace_3813889
  have hstable : (prefixWord ++ tailWord_3813889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813889).length < 2 ^ (prefixWord ++ tailWord_3813889).sum := by decide
  have hdescent : baseEnd_3813889 < baseStart_3813889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813893 : List Nat := [1, 3, 1, 1, 2, 2, 6, 1, 2, 3]
def baseStart_3813893 : Nat := 118140960795 + 3813893 * 2 ^ 59
def prefixEnd_3813893 : Nat := 4983230072969 + 3 ^ 40 * 3813893 * 2
def baseEnd_3813893 : Nat := 1305573515878767906531821

theorem tailTrace_3813893 : CollatzResearch.WordTrace tailWord_3813893 prefixEnd_3813893 1305573515878767906531821 := by
  unfold tailWord_3813893
  simp only [CollatzResearch.WordTrace]
  refine ⟨139104105571924496912006333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92736070381282997941337555 139104105571924496912006333)
  ·
    refine ⟨52164039589471686342002375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139104105571924496912006333 52164039589471686342002375)
    ·
      refine ⟨78246059384207529513003563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52164039589471686342002375 78246059384207529513003563)
      ·
        refine ⟨117369089076311294269505345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78246059384207529513003563 117369089076311294269505345)
        ·
          refine ⟨88026816807233470702129009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117369089076311294269505345 88026816807233470702129009)
          ·
            refine ⟨66020112605425103026596757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88026816807233470702129009 66020112605425103026596757)
            ·
              refine ⟨3094692778379301704371723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66020112605425103026596757 3094692778379301704371723)
              ·
                refine ⟨4642039167568952556557585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3094692778379301704371723 4642039167568952556557585)
                ·
                  refine ⟨3481529375676714417418189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4642039167568952556557585 3481529375676714417418189)
                  ·
                    refine ⟨1305573515878767906531821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3481529375676714417418189 1305573515878767906531821)
                    ·
                      rfl

theorem cell22_3813893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 2, 3].length) (baseStart_3813893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3813893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3813893 prefixEnd_3813893 := by exact prefixLift 3813893
  have htrace : WordTrace (prefixWord ++ tailWord_3813893) baseStart_3813893 baseEnd_3813893 := by
    simpa [prefixWord, tailWord_3813893, baseEnd_3813893] using wordTrace_append hprefix tailTrace_3813893
  have hstable : (prefixWord ++ tailWord_3813893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813893).length < 2 ^ (prefixWord ++ tailWord_3813893).sum := by decide
  have hdescent : baseEnd_3813893 < baseStart_3813893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813908 : List Nat := [2, 4, 3, 1, 1, 1, 1, 3, 2, 4]
def baseStart_3813908 : Nat := 118140960795 + 3813908 * 2 ^ 59
def prefixEnd_3813908 : Nat := 4983230072969 + 3 ^ 40 * 3813908 * 2
def baseEnd_3813908 : Nat := 1305578650685312867406775

theorem tailTrace_3813908 : CollatzResearch.WordTrace tailWord_3813908 prefixEnd_3813908 1305578650685312867406775 := by
  unfold tailWord_3813908
  simp only [CollatzResearch.WordTrace]
  refine ⟨69552326333435077236901189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92736435111246769649201585 69552326333435077236901189)
  ·
    refine ⟨13041061187519076981918973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69552326333435077236901189 13041061187519076981918973)
    ·
      refine ⟨4890397945319653868219615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13041061187519076981918973 4890397945319653868219615)
      ·
        refine ⟨7335596917979480802329423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4890397945319653868219615 7335596917979480802329423)
        ·
          refine ⟨11003395376969221203494135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7335596917979480802329423 11003395376969221203494135)
          ·
            refine ⟨16505093065453831805241203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11003395376969221203494135 16505093065453831805241203)
            ·
              refine ⟨24757639598180747707861805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16505093065453831805241203 24757639598180747707861805)
              ·
                refine ⟨9284114849317780390448177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24757639598180747707861805 9284114849317780390448177)
                ·
                  refine ⟨6963086136988335292836133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9284114849317780390448177 6963086136988335292836133)
                  ·
                    refine ⟨1305578650685312867406775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6963086136988335292836133 1305578650685312867406775)
                    ·
                      rfl

theorem cell22_3813908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_3813908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3813908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3813908 prefixEnd_3813908 := by exact prefixLift 3813908
  have htrace : WordTrace (prefixWord ++ tailWord_3813908) baseStart_3813908 baseEnd_3813908 := by
    simpa [prefixWord, tailWord_3813908, baseEnd_3813908] using wordTrace_append hprefix tailTrace_3813908
  have hstable : (prefixWord ++ tailWord_3813908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813908).length < 2 ^ (prefixWord ++ tailWord_3813908).sum := by decide
  have hdescent : baseEnd_3813908 < baseStart_3813908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813927 : List Nat := [1, 1, 7, 2, 1, 1, 2, 2, 2, 3]
def baseStart_3813927 : Nat := 118140960795 + 3813927 * 2 ^ 59
def prefixEnd_3813927 : Nat := 4983230072969 + 3 ^ 40 * 3813927 * 2
def baseEnd_3813927 : Nat := 1305585154773603151181717

theorem tailTrace_3813927 : CollatzResearch.WordTrace tailWord_3813927 prefixEnd_3813927 1305585154773603151181717 := by
  unfold tailWord_3813927
  simp only [CollatzResearch.WordTrace]
  refine ⟨139105345653801320718744035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92736897102534213812496023 139105345653801320718744035)
  ·
    refine ⟨208658018480701981078116053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139105345653801320718744035 208658018480701981078116053)
    ·
      refine ⟨4890422308141452681518345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 208658018480701981078116053 4890422308141452681518345)
      ·
        refine ⟨3667816731106089511138759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4890422308141452681518345 3667816731106089511138759)
        ·
          refine ⟨5501725096659134266708139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3667816731106089511138759 5501725096659134266708139)
          ·
            refine ⟨8252587644988701400062209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5501725096659134266708139 8252587644988701400062209)
            ·
              refine ⟨6189440733741526050046657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8252587644988701400062209 6189440733741526050046657)
              ·
                refine ⟨4642080550306144537534993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6189440733741526050046657 4642080550306144537534993)
                ·
                  refine ⟨3481560412729608403151245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4642080550306144537534993 3481560412729608403151245)
                  ·
                    refine ⟨1305585154773603151181717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3481560412729608403151245 1305585154773603151181717)
                    ·
                      rfl

theorem cell22_3813927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_3813927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3813927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3813927 prefixEnd_3813927 := by exact prefixLift 3813927
  have htrace : WordTrace (prefixWord ++ tailWord_3813927) baseStart_3813927 baseEnd_3813927 := by
    simpa [prefixWord, tailWord_3813927, baseEnd_3813927] using wordTrace_append hprefix tailTrace_3813927
  have hstable : (prefixWord ++ tailWord_3813927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813927).length < 2 ^ (prefixWord ++ tailWord_3813927).sum := by decide
  have hdescent : baseEnd_3813927 < baseStart_3813927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3813940 : List Nat := [2, 5, 1, 3, 1, 2, 1, 7]
def baseStart_3813940 : Nat := 118140960795 + 3813940 * 2 ^ 59
def prefixEnd_3813940 : Nat := 4983230072969 + 3 ^ 40 * 3813940 * 2
def baseEnd_3813940 : Nat := 145065511659919494511853

theorem tailTrace_3813940 : CollatzResearch.WordTrace tailWord_3813940 prefixEnd_3813940 145065511659919494511853 := by
  unfold tailWord_3813940
  simp only [CollatzResearch.WordTrace]
  refine ⟨69552909901377111969483637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92737213201836149292644849 69552909901377111969483637)
  ·
    refine ⟨6520585303254104247139091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69552909901377111969483637 6520585303254104247139091)
    ·
      refine ⟨9780877954881156370708637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6520585303254104247139091 9780877954881156370708637)
      ·
        refine ⟨3667829233080433639015739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9780877954881156370708637 3667829233080433639015739)
        ·
          refine ⟨5501743849620650458523609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3667829233080433639015739 5501743849620650458523609)
          ·
            refine ⟨4126307887215487843892707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5501743849620650458523609 4126307887215487843892707)
            ·
              refine ⟨6189461830823231765839061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4126307887215487843892707 6189461830823231765839061)
              ·
                refine ⟨145065511659919494511853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6189461830823231765839061 145065511659919494511853)
                ·
                  rfl

theorem cell22_3813940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 7].length) (baseStart_3813940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3813940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3813940 prefixEnd_3813940 := by exact prefixLift 3813940
  have htrace : WordTrace (prefixWord ++ tailWord_3813940) baseStart_3813940 baseEnd_3813940 := by
    simpa [prefixWord, tailWord_3813940, baseEnd_3813940] using wordTrace_append hprefix tailTrace_3813940
  have hstable : (prefixWord ++ tailWord_3813940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3813940).length < 2 ^ (prefixWord ++ tailWord_3813940).sum := by decide
  have hdescent : baseEnd_3813940 < baseStart_3813940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3813940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814062 : List Nat := [4, 1, 4, 1, 1, 2, 1, 3, 2, 3]
def baseStart_3814062 : Nat := 118140960795 + 3814062 * 2 ^ 59
def prefixEnd_3814062 : Nat := 4983230072969 + 3 ^ 40 * 3814062 * 2
def baseEnd_3814062 : Nat := 1305631368032507799056303

theorem tailTrace_3814062 : CollatzResearch.WordTrace tailWord_3814062 prefixEnd_3814062 1305631368032507799056303 := by
  unfold tailWord_3814062
  simp only [CollatzResearch.WordTrace]
  refine ⟨17388783688539029846863555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92740179672208159183272293 17388783688539029846863555)
  ·
    refine ⟨26083175532808544770295333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17388783688539029846863555 26083175532808544770295333)
    ·
      refine ⟨4890595412401602144430375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26083175532808544770295333 4890595412401602144430375)
      ·
        refine ⟨7335893118602403216645563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4890595412401602144430375 7335893118602403216645563)
        ·
          refine ⟨11003839677903604824968345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7335893118602403216645563 11003839677903604824968345)
          ·
            refine ⟨8252879758427703618726259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11003839677903604824968345 8252879758427703618726259)
            ·
              refine ⟨12379319637641555428089389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8252879758427703618726259 12379319637641555428089389)
              ·
                refine ⟨4642244864115583285533521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12379319637641555428089389 4642244864115583285533521)
                ·
                  refine ⟨3481683648086687464150141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4642244864115583285533521 3481683648086687464150141)
                  ·
                    refine ⟨1305631368032507799056303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3481683648086687464150141 1305631368032507799056303)
                    ·
                      rfl

theorem cell22_3814062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_3814062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3814062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3814062 prefixEnd_3814062 := by exact prefixLift 3814062
  have htrace : WordTrace (prefixWord ++ tailWord_3814062) baseStart_3814062 baseEnd_3814062 := by
    simpa [prefixWord, tailWord_3814062, baseEnd_3814062] using wordTrace_append hprefix tailTrace_3814062
  have hstable : (prefixWord ++ tailWord_3814062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814062).length < 2 ^ (prefixWord ++ tailWord_3814062).sum := by decide
  have hdescent : baseEnd_3814062 < baseStart_3814062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814103 : List Nat := [1, 1, 3, 2, 1, 5, 2, 2, 5]
def baseStart_3814103 : Nat := 118140960795 + 3814103 * 2 ^ 59
def prefixEnd_3814103 : Nat := 4983230072969 + 3 ^ 40 * 3814103 * 2
def baseEnd_3814103 : Nat := 435215134390132452927059

theorem tailTrace_3814103 : CollatzResearch.WordTrace tailWord_3814103 prefixEnd_3814103 435215134390132452927059 := by
  unfold tailWord_3814103
  simp only [CollatzResearch.WordTrace]
  refine ⟨139111764901163702777150963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92741176600775801851433975 139111764901163702777150963)
  ·
    refine ⟨208667647351745554165726445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139111764901163702777150963 208667647351745554165726445)
    ·
      refine ⟨78250367756904582812147417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208667647351745554165726445 78250367756904582812147417)
      ·
        refine ⟨58687775817678437109110563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78250367756904582812147417 58687775817678437109110563)
        ·
          refine ⟨88031663726517655663665845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58687775817678437109110563 88031663726517655663665845)
          ·
            refine ⟨8252968474361030218468673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88031663726517655663665845 8252968474361030218468673)
            ·
              refine ⟨6189726355770772663851505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8252968474361030218468673 6189726355770772663851505)
              ·
                refine ⟨4642294766828079497888629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6189726355770772663851505 4642294766828079497888629)
                ·
                  refine ⟨435215134390132452927059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4642294766828079497888629 435215134390132452927059)
                  ·
                    rfl

theorem cell22_3814103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 5].length) (baseStart_3814103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3814103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3814103 prefixEnd_3814103 := by exact prefixLift 3814103
  have htrace : WordTrace (prefixWord ++ tailWord_3814103) baseStart_3814103 baseEnd_3814103 := by
    simpa [prefixWord, tailWord_3814103, baseEnd_3814103] using wordTrace_append hprefix tailTrace_3814103
  have hstable : (prefixWord ++ tailWord_3814103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814103).length < 2 ^ (prefixWord ++ tailWord_3814103).sum := by decide
  have hdescent : baseEnd_3814103 < baseStart_3814103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814163 : List Nat := [1, 1, 1, 2, 1, 3, 5, 1, 4, 3]
def baseStart_3814163 : Nat := 118140960795 + 3814163 * 2 ^ 59
def prefixEnd_3814163 : Nat := 4983230072969 + 3 ^ 40 * 3814163 * 2
def baseEnd_3814163 : Nat := 1305665942396577202280993

theorem tailTrace_3814163 : CollatzResearch.WordTrace tailWord_3814163 prefixEnd_3814163 1305665942396577202280993 := by
  unfold tailWord_3814163
  simp only [CollatzResearch.WordTrace]
  refine ⟨139113953280946333024335143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92742635520630888682890095 139113953280946333024335143)
  ·
    refine ⟨208670929921419499536502715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139113953280946333024335143 208670929921419499536502715)
    ·
      refine ⟨313006394882129249304754073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208670929921419499536502715 313006394882129249304754073)
      ·
        refine ⟨234754796161596936978565555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313006394882129249304754073 234754796161596936978565555)
        ·
          refine ⟨352132194242395405467848333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234754796161596936978565555 352132194242395405467848333)
          ·
            refine ⟨132049572840898277050443125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 352132194242395405467848333 132049572840898277050443125)
            ·
              refine ⟨12379647453834213473479043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132049572840898277050443125 12379647453834213473479043)
              ·
                refine ⟨18569471180751320210218565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12379647453834213473479043 18569471180751320210218565)
                ·
                  refine ⟨3481775846390872539415981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18569471180751320210218565 3481775846390872539415981)
                  ·
                    refine ⟨1305665942396577202280993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3481775846390872539415981 1305665942396577202280993)
                    ·
                      rfl

theorem cell22_3814163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 4, 3].length) (baseStart_3814163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3814163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3814163 prefixEnd_3814163 := by exact prefixLift 3814163
  have htrace : WordTrace (prefixWord ++ tailWord_3814163) baseStart_3814163 baseEnd_3814163 := by
    simpa [prefixWord, tailWord_3814163, baseEnd_3814163] using wordTrace_append hprefix tailTrace_3814163
  have hstable : (prefixWord ++ tailWord_3814163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814163).length < 2 ^ (prefixWord ++ tailWord_3814163).sum := by decide
  have hdescent : baseEnd_3814163 < baseStart_3814163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814178 : List Nat := [3, 3, 1, 1, 2, 2, 1, 2, 1, 6]
def baseStart_3814178 : Nat := 118140960795 + 3814178 * 2 ^ 59
def prefixEnd_3814178 : Nat := 4983230072969 + 3 ^ 40 * 3814178 * 2
def baseEnd_3814178 : Nat := 1305671077203122163155947

theorem tailTrace_3814178 : CollatzResearch.WordTrace tailWord_3814178 prefixEnd_3814178 1305671077203122163155947 := by
  unfold tailWord_3814178
  simp only [CollatzResearch.WordTrace]
  refine ⟨34778625093972997646532797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92743000250594660390754125 34778625093972997646532797)
  ·
    refine ⟨13041984410239874117449799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34778625093972997646532797 13041984410239874117449799)
    ·
      refine ⟨19562976615359811176174699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13041984410239874117449799 19562976615359811176174699)
      ·
        refine ⟨29344464923039716764262049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19562976615359811176174699 29344464923039716764262049)
        ·
          refine ⟨22008348692279787573196537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29344464923039716764262049 22008348692279787573196537)
          ·
            refine ⟨16506261519209840679897403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22008348692279787573196537 16506261519209840679897403)
            ·
              refine ⟨24759392278814761019846105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16506261519209840679897403 24759392278814761019846105)
              ·
                refine ⟨18569544209111070764884579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24759392278814761019846105 18569544209111070764884579)
                ·
                  refine ⟨27854316313666606147326869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18569544209111070764884579 27854316313666606147326869)
                  ·
                    refine ⟨1305671077203122163155947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27854316313666606147326869 1305671077203122163155947)
                    ·
                      rfl

theorem cell22_3814178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_3814178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3814178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3814178 prefixEnd_3814178 := by exact prefixLift 3814178
  have htrace : WordTrace (prefixWord ++ tailWord_3814178) baseStart_3814178 baseEnd_3814178 := by
    simpa [prefixWord, tailWord_3814178, baseEnd_3814178] using wordTrace_append hprefix tailTrace_3814178
  have hstable : (prefixWord ++ tailWord_3814178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814178).length < 2 ^ (prefixWord ++ tailWord_3814178).sum := by decide
  have hdescent : baseEnd_3814178 < baseStart_3814178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814208 : List Nat := [2, 1, 1, 2, 2, 1, 1, 4, 5, 3]
def baseStart_3814208 : Nat := 118140960795 + 3814208 * 2 ^ 59
def prefixEnd_3814208 : Nat := 4983230072969 + 3 ^ 40 * 3814208 * 2
def baseEnd_3814208 : Nat := 1305681346816212084905855

theorem tailTrace_3814208 : CollatzResearch.WordTrace tailWord_3814208 prefixEnd_3814208 1305681346816212084905855 := by
  unfold tailWord_3814208
  simp only [CollatzResearch.WordTrace]
  refine ⟨69557797282891652854861639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92743729710522203806482185 69557797282891652854861639)
  ·
    refine ⟨104336695924337479282292459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69557797282891652854861639 104336695924337479282292459)
    ·
      refine ⟨156505043886506218923438689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104336695924337479282292459 156505043886506218923438689)
      ·
        refine ⟨117378782914879664192579017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156505043886506218923438689 117378782914879664192579017)
        ·
          refine ⟨88034087186159748144434263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117378782914879664192579017 88034087186159748144434263)
          ·
            refine ⟨132051130779239622216651395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88034087186159748144434263 132051130779239622216651395)
            ·
              refine ⟨198076696168859433324977093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132051130779239622216651395 198076696168859433324977093)
              ·
                refine ⟨37139380531661143748433205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198076696168859433324977093 37139380531661143748433205)
                ·
                  refine ⟨3481816924843232226415613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37139380531661143748433205 3481816924843232226415613)
                  ·
                    refine ⟨1305681346816212084905855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3481816924843232226415613 1305681346816212084905855)
                    ·
                      rfl

theorem cell22_3814208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 5, 3].length) (baseStart_3814208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3814208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3814208 prefixEnd_3814208 := by exact prefixLift 3814208
  have htrace : WordTrace (prefixWord ++ tailWord_3814208) baseStart_3814208 baseEnd_3814208 := by
    simpa [prefixWord, tailWord_3814208, baseEnd_3814208] using wordTrace_append hprefix tailTrace_3814208
  have hstable : (prefixWord ++ tailWord_3814208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814208).length < 2 ^ (prefixWord ++ tailWord_3814208).sum := by decide
  have hdescent : baseEnd_3814208 < baseStart_3814208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814253 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 4, 5]
def baseStart_3814253 : Nat := 118140960795 + 3814253 * 2 ^ 59
def prefixEnd_3814253 : Nat := 4983230072969 + 3 ^ 40 * 3814253 * 2
def baseEnd_3814253 : Nat := 1305696751235846967530717

theorem tailTrace_3814253 : CollatzResearch.WordTrace tailWord_3814253 prefixEnd_3814253 1305696751235846967530717 := by
  unfold tailWord_3814253
  simp only [CollatzResearch.WordTrace]
  refine ⟨139117235850620278395111413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92744823900413518930074275 139117235850620278395111413)
  ·
    refine ⟨13042240860995651099541695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139117235850620278395111413 13042240860995651099541695)
    ·
      refine ⟨19563361291493476649312543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13042240860995651099541695 19563361291493476649312543)
      ·
        refine ⟨29345041937240214973968815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19563361291493476649312543 29345041937240214973968815)
        ·
          refine ⟨44017562905860322460953223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29345041937240214973968815 44017562905860322460953223)
          ·
            refine ⟨66026344358790483691429835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44017562905860322460953223 66026344358790483691429835)
            ·
              refine ⟨99039516538185725537144753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66026344358790483691429835 99039516538185725537144753)
              ·
                refine ⟨74279637403639294152858565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99039516538185725537144753 74279637403639294152858565)
                ·
                  refine ⟨13927432013182367653660981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74279637403639294152858565 13927432013182367653660981)
                  ·
                    refine ⟨1305696751235846967530717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13927432013182367653660981 1305696751235846967530717)
                    ·
                      rfl

theorem cell22_3814253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_3814253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3814253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3814253 prefixEnd_3814253 := by exact prefixLift 3814253
  have htrace : WordTrace (prefixWord ++ tailWord_3814253) baseStart_3814253 baseEnd_3814253 := by
    simpa [prefixWord, tailWord_3814253, baseEnd_3814253] using wordTrace_append hprefix tailTrace_3814253
  have hstable : (prefixWord ++ tailWord_3814253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814253).length < 2 ^ (prefixWord ++ tailWord_3814253).sum := by decide
  have hdescent : baseEnd_3814253 < baseStart_3814253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814313 : List Nat := [1, 2, 1, 1, 1, 1, 7, 1, 1, 6]
def baseStart_3814313 : Nat := 118140960795 + 3814313 * 2 ^ 59
def prefixEnd_3814313 : Nat := 4983230072969 + 3 ^ 40 * 3814313 * 2
def baseEnd_3814313 : Nat := 1305717290462026811030533

theorem tailTrace_3814313 : CollatzResearch.WordTrace tailWord_3814313 prefixEnd_3814313 1305717290462026811030533 := by
  unfold tailWord_3814313
  simp only [CollatzResearch.WordTrace]
  refine ⟨139119424230402908642295593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92746282820268605761530395 139119424230402908642295593)
  ·
    refine ⟨104339568172802181481721695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139119424230402908642295593 104339568172802181481721695)
    ·
      refine ⟨156509352259203272222582543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104339568172802181481721695 156509352259203272222582543)
      ·
        refine ⟨234764028388804908333873815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156509352259203272222582543 234764028388804908333873815)
        ·
          refine ⟨352146042583207362500810723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234764028388804908333873815 352146042583207362500810723)
          ·
            refine ⟨528219063874811043751216085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352146042583207362500810723 528219063874811043751216085)
            ·
              refine ⟨12380134309565883837919127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 528219063874811043751216085 12380134309565883837919127)
              ·
                refine ⟨18570201464348825756878691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12380134309565883837919127 18570201464348825756878691)
                ·
                  refine ⟨27855302196523238635318037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18570201464348825756878691 27855302196523238635318037)
                  ·
                    refine ⟨1305717290462026811030533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27855302196523238635318037 1305717290462026811030533)
                    ·
                      rfl

theorem cell22_3814313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 6].length) (baseStart_3814313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3814313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3814313 prefixEnd_3814313 := by exact prefixLift 3814313
  have htrace : WordTrace (prefixWord ++ tailWord_3814313) baseStart_3814313 baseEnd_3814313 := by
    simpa [prefixWord, tailWord_3814313, baseEnd_3814313] using wordTrace_append hprefix tailTrace_3814313
  have hstable : (prefixWord ++ tailWord_3814313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814313).length < 2 ^ (prefixWord ++ tailWord_3814313).sum := by decide
  have hdescent : baseEnd_3814313 < baseStart_3814313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814328 : List Nat := [2, 1, 2, 1, 2, 5, 9]
def baseStart_3814328 : Nat := 118140960795 + 3814328 * 2 ^ 59
def prefixEnd_3814328 : Nat := 4983230072969 + 3 ^ 40 * 3814328 * 2
def baseEnd_3814328 : Nat := 48360089824761917477981

theorem tailTrace_3814328 : CollatzResearch.WordTrace tailWord_3814328 prefixEnd_3814328 48360089824761917477981 := by
  unfold tailWord_3814328
  simp only [CollatzResearch.WordTrace]
  refine ⟨69559985662674283102045819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92746647550232377469394425 69559985662674283102045819)
  ·
    refine ⟨104339978494011424653068729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69559985662674283102045819 104339978494011424653068729)
    ·
      refine ⟨78254983870508568489801547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104339978494011424653068729 78254983870508568489801547)
      ·
        refine ⟨117382475805762852734702321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78254983870508568489801547 117382475805762852734702321)
        ·
          refine ⟨88036856854322139551026741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117382475805762852734702321 88036856854322139551026741)
          ·
            refine ⟨8253455330092700582908757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88036856854322139551026741 8253455330092700582908757)
            ·
              refine ⟨48360089824761917477981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8253455330092700582908757 48360089824761917477981)
              ·
                rfl

theorem cell22_3814328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 9].length) (baseStart_3814328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3814328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3814328 prefixEnd_3814328 := by exact prefixLift 3814328
  have htrace : WordTrace (prefixWord ++ tailWord_3814328) baseStart_3814328 baseEnd_3814328 := by
    simpa [prefixWord, tailWord_3814328, baseEnd_3814328] using wordTrace_append hprefix tailTrace_3814328
  have hstable : (prefixWord ++ tailWord_3814328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814328).length < 2 ^ (prefixWord ++ tailWord_3814328).sum := by decide
  have hdescent : baseEnd_3814328 < baseStart_3814328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814362 : List Nat := [3, 1, 1, 2, 4, 3, 2, 6]
def baseStart_3814362 : Nat := 118140960795 + 3814362 * 2 ^ 59
def prefixEnd_3814362 : Nat := 4983230072969 + 3 ^ 40 * 3814362 * 2
def baseEnd_3814362 : Nat := 145081562684823001839487

theorem tailTrace_3814362 : CollatzResearch.WordTrace tailWord_3814362 prefixEnd_3814362 145081562684823001839487 := by
  unfold tailWord_3814362
  simp only [CollatzResearch.WordTrace]
  refine ⟨34780302851806347502707335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92747474271483593340552893 34780302851806347502707335)
  ·
    refine ⟨52170454277709521254061003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34780302851806347502707335 52170454277709521254061003)
    ·
      refine ⟨78255681416564281881091505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52170454277709521254061003 78255681416564281881091505)
      ·
        refine ⟨58691761062423211410818629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78255681416564281881091505 58691761062423211410818629)
        ·
          refine ⟨11004705199204352139528493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58691761062423211410818629 11004705199204352139528493)
          ·
            refine ⟨4126764449701632052323185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11004705199204352139528493 4126764449701632052323185)
            ·
              refine ⟨3095073337276224039242389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4126764449701632052323185 3095073337276224039242389)
              ·
                refine ⟨145081562684823001839487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3095073337276224039242389 145081562684823001839487)
                ·
                  rfl

theorem cell22_3814362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 6].length) (baseStart_3814362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3814362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3814362 prefixEnd_3814362 := by exact prefixLift 3814362
  have htrace : WordTrace (prefixWord ++ tailWord_3814362) baseStart_3814362 baseEnd_3814362 := by
    simpa [prefixWord, tailWord_3814362, baseEnd_3814362] using wordTrace_append hprefix tailTrace_3814362
  have hstable : (prefixWord ++ tailWord_3814362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814362).length < 2 ^ (prefixWord ++ tailWord_3814362).sum := by decide
  have hdescent : baseEnd_3814362 < baseStart_3814362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814403 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 1, 10]
def baseStart_3814403 : Nat := 118140960795 + 3814403 * 2 ^ 59
def prefixEnd_3814403 : Nat := 4983230072969 + 3 ^ 40 * 3814403 * 2
def baseEnd_3814403 : Nat := 1305748099301296576280257

theorem tailTrace_3814403 : CollatzResearch.WordTrace tailWord_3814403 prefixEnd_3814403 1305748099301296576280257 := by
  unfold tailWord_3814403
  simp only [CollatzResearch.WordTrace]
  refine ⟨139122706800076854013071863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92748471200051236008714575 139122706800076854013071863)
  ·
    refine ⟨208684060200115281019607795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139122706800076854013071863 208684060200115281019607795)
    ·
      refine ⟨313026090300172921529411693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208684060200115281019607795 313026090300172921529411693)
      ·
        refine ⟨117384783862564845573529385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313026090300172921529411693 117384783862564845573529385)
        ·
          refine ⟨88038587896923634180147039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117384783862564845573529385 88038587896923634180147039)
          ·
            refine ⟨132057881845385451270220559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88038587896923634180147039 132057881845385451270220559)
            ·
              refine ⟨198086822768078176905330839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132057881845385451270220559 198086822768078176905330839)
              ·
                refine ⟨297130234152117265357996259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198086822768078176905330839 297130234152117265357996259)
                ·
                  refine ⟨445695351228175898036994389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297130234152117265357996259 445695351228175898036994389)
                  ·
                    refine ⟨1305748099301296576280257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 445695351228175898036994389 1305748099301296576280257)
                    ·
                      rfl

theorem cell22_3814403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 10].length) (baseStart_3814403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3814403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3814403 prefixEnd_3814403 := by exact prefixLift 3814403
  have htrace : WordTrace (prefixWord ++ tailWord_3814403) baseStart_3814403 baseEnd_3814403 := by
    simpa [prefixWord, tailWord_3814403, baseEnd_3814403] using wordTrace_append hprefix tailTrace_3814403
  have hstable : (prefixWord ++ tailWord_3814403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814403).length < 2 ^ (prefixWord ++ tailWord_3814403).sum := by decide
  have hdescent : baseEnd_3814403 < baseStart_3814403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814450 : List Nat := [3, 2, 1, 1, 2, 2, 1, 2, 3, 5]
def baseStart_3814450 : Nat := 118140960795 + 3814450 * 2 ^ 59
def prefixEnd_3814450 : Nat := 4983230072969 + 3 ^ 40 * 3814450 * 2
def baseEnd_3814450 : Nat := 1305764188361804120355113

theorem tailTrace_3814450 : CollatzResearch.WordTrace tailWord_3814450 prefixEnd_3814450 1305764188361804120355113 := by
  unfold tailWord_3814450
  simp only [CollatzResearch.WordTrace]
  refine ⟨34781105257726645260008201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92749614020604387360021869 34781105257726645260008201)
  ·
    refine ⟨26085828943294983945006151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34781105257726645260008201 26085828943294983945006151)
    ·
      refine ⟨39128743414942475917509227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26085828943294983945006151 39128743414942475917509227)
      ·
        refine ⟨58693115122413713876263841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39128743414942475917509227 58693115122413713876263841)
        ·
          refine ⟨44019836341810285407197881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58693115122413713876263841 44019836341810285407197881)
          ·
            refine ⟨33014877256357714055398411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44019836341810285407197881 33014877256357714055398411)
            ·
              refine ⟨49522315884536571083097617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33014877256357714055398411 49522315884536571083097617)
              ·
                refine ⟨37141736913402428312323213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49522315884536571083097617 37141736913402428312323213)
                ·
                  refine ⟨13928151342525910617121205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37141736913402428312323213 13928151342525910617121205)
                  ·
                    refine ⟨1305764188361804120355113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13928151342525910617121205 1305764188361804120355113)
                    ·
                      rfl

theorem cell22_3814450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_3814450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3814450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3814450 prefixEnd_3814450 := by exact prefixLift 3814450
  have htrace : WordTrace (prefixWord ++ tailWord_3814450) baseStart_3814450 baseEnd_3814450 := by
    simpa [prefixWord, tailWord_3814450, baseEnd_3814450] using wordTrace_append hprefix tailTrace_3814450
  have hstable : (prefixWord ++ tailWord_3814450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814450).length < 2 ^ (prefixWord ++ tailWord_3814450).sum := by decide
  have hdescent : baseEnd_3814450 < baseStart_3814450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814467 : List Nat := [1, 1, 1, 3, 1, 2, 3, 5, 2, 3]
def baseStart_3814467 : Nat := 118140960795 + 3814467 * 2 ^ 59
def prefixEnd_3814467 : Nat := 4983230072969 + 3 ^ 40 * 3814467 * 2
def baseEnd_3814467 : Nat := 1305770007809221742680061

theorem tailTrace_3814467 : CollatzResearch.WordTrace tailWord_3814467 prefixEnd_3814467 1305770007809221742680061 := by
  unfold tailWord_3814467
  simp only [CollatzResearch.WordTrace]
  refine ⟨139125041071844992943401655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92750027381229995295601103 139125041071844992943401655)
  ·
    refine ⟨208687561607767489415102483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139125041071844992943401655 208687561607767489415102483)
    ·
      refine ⟨313031342411651234122653725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208687561607767489415102483 313031342411651234122653725)
      ·
        refine ⟨117386753404369212795995147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313031342411651234122653725 117386753404369212795995147)
        ·
          refine ⟨176080130106553819193992721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117386753404369212795995147 176080130106553819193992721)
          ·
            refine ⟨132060097579915364395494541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176080130106553819193992721 132060097579915364395494541)
            ·
              refine ⟨49522536592468261648310453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132060097579915364395494541 49522536592468261648310453)
              ·
                refine ⟨4642737805543899529529105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49522536592468261648310453 4642737805543899529529105)
                ·
                  refine ⟨3482053354157924647146829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4642737805543899529529105 3482053354157924647146829)
                  ·
                    refine ⟨1305770007809221742680061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3482053354157924647146829 1305770007809221742680061)
                    ·
                      rfl

theorem cell22_3814467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 2, 3].length) (baseStart_3814467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3814467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3814467 prefixEnd_3814467 := by exact prefixLift 3814467
  have htrace : WordTrace (prefixWord ++ tailWord_3814467) baseStart_3814467 baseEnd_3814467 := by
    simpa [prefixWord, tailWord_3814467, baseEnd_3814467] using wordTrace_append hprefix tailTrace_3814467
  have hstable : (prefixWord ++ tailWord_3814467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814467).length < 2 ^ (prefixWord ++ tailWord_3814467).sum := by decide
  have hdescent : baseEnd_3814467 < baseStart_3814467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814482 : List Nat := [3, 2, 2, 1, 3, 2, 1, 1, 1, 6]
def baseStart_3814482 : Nat := 118140960795 + 3814482 * 2 ^ 59
def prefixEnd_3814482 : Nat := 4983230072969 + 3 ^ 40 * 3814482 * 2
def baseEnd_3814482 : Nat := 1305775142615766703555015

theorem tailTrace_3814482 : CollatzResearch.WordTrace tailWord_3814482 prefixEnd_3814482 1305775142615766703555015 := by
  unfold tailWord_3814482
  simp only [CollatzResearch.WordTrace]
  refine ⟨34781397041697662626299425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92750392111193767003465133 34781397041697662626299425)
  ·
    refine ⟨26086047781273246969724569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34781397041697662626299425 26086047781273246969724569)
    ·
      refine ⟨19564535835954935227293427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26086047781273246969724569 19564535835954935227293427)
      ·
        refine ⟨29346803753932402840940141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19564535835954935227293427 29346803753932402840940141)
        ·
          refine ⟨11005051407724651065352553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29346803753932402840940141 11005051407724651065352553)
          ·
            refine ⟨8253788555793488299014415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11005051407724651065352553 8253788555793488299014415)
            ·
              refine ⟨12380682833690232448521623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8253788555793488299014415 12380682833690232448521623)
              ·
                refine ⟨18571024250535348672782435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12380682833690232448521623 18571024250535348672782435)
                ·
                  refine ⟨27856536375803023009173653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18571024250535348672782435 27856536375803023009173653)
                  ·
                    refine ⟨1305775142615766703555015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27856536375803023009173653 1305775142615766703555015)
                    ·
                      rfl

theorem cell22_3814482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_3814482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3814482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3814482 prefixEnd_3814482 := by exact prefixLift 3814482
  have htrace : WordTrace (prefixWord ++ tailWord_3814482) baseStart_3814482 baseEnd_3814482 := by
    simpa [prefixWord, tailWord_3814482, baseEnd_3814482] using wordTrace_append hprefix tailTrace_3814482
  have hstable : (prefixWord ++ tailWord_3814482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814482).length < 2 ^ (prefixWord ++ tailWord_3814482).sum := by decide
  have hdescent : baseEnd_3814482 < baseStart_3814482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814529 : List Nat := [1, 2, 4, 2, 2, 1, 2, 2, 3, 3]
def baseStart_3814529 : Nat := 118140960795 + 3814529 * 2 ^ 59
def prefixEnd_3814529 : Nat := 4983230072969 + 3 ^ 40 * 3814529 * 2
def baseEnd_3814529 : Nat := 1305791231676274247629871

theorem tailTrace_3814529 : CollatzResearch.WordTrace tailWord_3814529 prefixEnd_3814529 1305791231676274247629871 := by
  unfold tailWord_3814529
  simp only [CollatzResearch.WordTrace]
  refine ⟨139127302397620377532158641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92751534931746918354772427 139127302397620377532158641)
  ·
    refine ⟨104345476798215283149118981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139127302397620377532158641 104345476798215283149118981)
    ·
      refine ⟨19564776899665365590459809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104345476798215283149118981 19564776899665365590459809)
      ·
        refine ⟨14673582674749024192844857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19564776899665365590459809 14673582674749024192844857)
        ·
          refine ⟨11005187006061768144633643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14673582674749024192844857 11005187006061768144633643)
          ·
            refine ⟨16507780509092652216950465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11005187006061768144633643 16507780509092652216950465)
            ·
              refine ⟨12380835381819489162712849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16507780509092652216950465 12380835381819489162712849)
              ·
                refine ⟨9285626536364616872034637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12380835381819489162712849 9285626536364616872034637)
                ·
                  refine ⟨3482109951136731327012989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9285626536364616872034637 3482109951136731327012989)
                  ·
                    refine ⟨1305791231676274247629871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3482109951136731327012989 1305791231676274247629871)
                    ·
                      rfl

theorem cell22_3814529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_3814529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3814529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3814529 prefixEnd_3814529 := by exact prefixLift 3814529
  have htrace : WordTrace (prefixWord ++ tailWord_3814529) baseStart_3814529 baseEnd_3814529 := by
    simpa [prefixWord, tailWord_3814529, baseEnd_3814529] using wordTrace_append hprefix tailTrace_3814529
  have hstable : (prefixWord ++ tailWord_3814529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814529).length < 2 ^ (prefixWord ++ tailWord_3814529).sum := by decide
  have hdescent : baseEnd_3814529 < baseStart_3814529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814540 : List Nat := [2, 2, 1, 2, 1, 1, 1, 4, 1, 7]
def baseStart_3814540 : Nat := 118140960795 + 3814540 * 2 ^ 59
def prefixEnd_3814540 : Nat := 4983230072969 + 3 ^ 40 * 3814540 * 2
def baseEnd_3814540 : Nat := 1305794997201073885604837

theorem tailTrace_3814540 : CollatzResearch.WordTrace tailWord_3814540 prefixEnd_3814540 1305794997201073885604837 := by
  unfold tailWord_3814540
  simp only [CollatzResearch.WordTrace]
  refine ⟨69563851800290263205404537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92751802400387017607206049 69563851800290263205404537)
  ·
    refine ⟨52172888850217697404053403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69563851800290263205404537 52172888850217697404053403)
    ·
      refine ⟨78259333275326546106080105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52172888850217697404053403 78259333275326546106080105)
      ·
        refine ⟨58694499956494909579560079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78259333275326546106080105 58694499956494909579560079)
        ·
          refine ⟨88041749934742364369340119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58694499956494909579560079 88041749934742364369340119)
          ·
            refine ⟨132062624902113546554010179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88041749934742364369340119 132062624902113546554010179)
            ·
              refine ⟨198093937353170319831015269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132062624902113546554010179 198093937353170319831015269)
              ·
                refine ⟨37142613253719434968315363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198093937353170319831015269 37142613253719434968315363)
                ·
                  refine ⟨55713919880579152452473045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37142613253719434968315363 55713919880579152452473045)
                  ·
                    refine ⟨1305794997201073885604837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55713919880579152452473045 1305794997201073885604837)
                    ·
                      rfl

theorem cell22_3814540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_3814540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3814540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3814540 prefixEnd_3814540 := by exact prefixLift 3814540
  have htrace : WordTrace (prefixWord ++ tailWord_3814540) baseStart_3814540 baseEnd_3814540 := by
    simpa [prefixWord, tailWord_3814540, baseEnd_3814540] using wordTrace_append hprefix tailTrace_3814540
  have hstable : (prefixWord ++ tailWord_3814540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814540).length < 2 ^ (prefixWord ++ tailWord_3814540).sum := by decide
  have hdescent : baseEnd_3814540 < baseStart_3814540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814542 : List Nat := [4, 1, 1, 3, 2, 1, 1, 2, 7]
def baseStart_3814542 : Nat := 118140960795 + 3814542 * 2 ^ 59
def prefixEnd_3814542 : Nat := 4983230072969 + 3 ^ 40 * 3814542 * 2
def baseEnd_3814542 : Nat := 435265227280648849018277

theorem tailTrace_3814542 : CollatzResearch.WordTrace tailWord_3814542 prefixEnd_3814542 435265227280648849018277 := by
  unfold tailWord_3814542
  simp only [CollatzResearch.WordTrace]
  refine ⟨17390972068321660094047735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92751851031048853834921253 17390972068321660094047735)
  ·
    refine ⟨26086458102482490141071603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17390972068321660094047735 26086458102482490141071603)
    ·
      refine ⟨39129687153723735211607405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26086458102482490141071603 39129687153723735211607405)
      ·
        refine ⟨14673632682646400704352777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39129687153723735211607405 14673632682646400704352777)
        ·
          refine ⟨11005224511984800528264583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14673632682646400704352777 11005224511984800528264583)
          ·
            refine ⟨16507836767977200792396875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11005224511984800528264583 16507836767977200792396875)
            ·
              refine ⟨24761755151965801188595313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16507836767977200792396875 24761755151965801188595313)
              ·
                refine ⟨18571316363974350891446485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24761755151965801188595313 18571316363974350891446485)
                ·
                  refine ⟨435265227280648849018277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18571316363974350891446485 435265227280648849018277)
                  ·
                    rfl

theorem cell22_3814542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_3814542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3814542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3814542 prefixEnd_3814542 := by exact prefixLift 3814542
  have htrace : WordTrace (prefixWord ++ tailWord_3814542) baseStart_3814542 baseEnd_3814542 := by
    simpa [prefixWord, tailWord_3814542, baseEnd_3814542] using wordTrace_append hprefix tailTrace_3814542
  have hstable : (prefixWord ++ tailWord_3814542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814542).length < 2 ^ (prefixWord ++ tailWord_3814542).sum := by decide
  have hdescent : baseEnd_3814542 < baseStart_3814542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814589 : List Nat := [1, 4, 1, 2, 1, 1, 5, 2, 1, 4]
def baseStart_3814589 : Nat := 118140960795 + 3814589 * 2 ^ 59
def prefixEnd_3814589 : Nat := 4983230072969 + 3 ^ 40 * 3814589 * 2
def baseEnd_3814589 : Nat := 1305811770902454091129687

theorem tailTrace_3814589 : CollatzResearch.WordTrace tailWord_3814589 prefixEnd_3814589 1305811770902454091129687 := by
  unfold tailWord_3814589
  simp only [CollatzResearch.WordTrace]
  refine ⟨139129490777403007779342821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92752993851602005186228547 139129490777403007779342821)
  ·
    refine ⟨26086779520763063958626779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139129490777403007779342821 26086779520763063958626779)
    ·
      refine ⟨39130169281144595937940169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26086779520763063958626779 39130169281144595937940169)
      ·
        refine ⟨29347626960858446953455127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39130169281144595937940169 29347626960858446953455127)
        ·
          refine ⟨44021440441287670430182691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29347626960858446953455127 44021440441287670430182691)
          ·
            refine ⟨66032160661931505645274037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44021440441287670430182691 66032160661931505645274037)
            ·
              refine ⟨6190515062056078654244441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66032160661931505645274037 6190515062056078654244441)
              ·
                refine ⟨4642886296542058990683331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6190515062056078654244441 4642886296542058990683331)
                ·
                  refine ⟨6964329444813088486024997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4642886296542058990683331 6964329444813088486024997)
                  ·
                    refine ⟨1305811770902454091129687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6964329444813088486024997 1305811770902454091129687)
                    ·
                      rfl

theorem cell22_3814589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_3814589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3814589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3814589 prefixEnd_3814589 := by exact prefixLift 3814589
  have htrace : WordTrace (prefixWord ++ tailWord_3814589) baseStart_3814589 baseEnd_3814589 := by
    simpa [prefixWord, tailWord_3814589, baseEnd_3814589] using wordTrace_append hprefix tailTrace_3814589
  have hstable : (prefixWord ++ tailWord_3814589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814589).length < 2 ^ (prefixWord ++ tailWord_3814589).sum := by decide
  have hdescent : baseEnd_3814589 < baseStart_3814589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814602 : List Nat := [3, 1, 2, 1, 3, 2, 1, 1, 3, 5]
def baseStart_3814602 : Nat := 118140960795 + 3814602 * 2 ^ 59
def prefixEnd_3814602 : Nat := 4983230072969 + 3 ^ 40 * 3814602 * 2
def baseEnd_3814602 : Nat := 1305816221068126390554647

theorem tailTrace_3814602 : CollatzResearch.WordTrace tailWord_3814602 prefixEnd_3814602 1305816221068126390554647 := by
  unfold tailWord_3814602
  simp only [CollatzResearch.WordTrace]
  refine ⟨34782491231588977749891515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92753309950903940666377373 34782491231588977749891515)
  ·
    refine ⟨52173736847383466624837273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34782491231588977749891515 52173736847383466624837273)
    ·
      refine ⟨39130302635537599968627955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52173736847383466624837273 39130302635537599968627955)
      ·
        refine ⟨58695453953306399952941933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39130302635537599968627955 58695453953306399952941933)
        ·
          refine ⟨22010795232489899982353225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58695453953306399952941933 22010795232489899982353225)
          ·
            refine ⟨16508096424367424986764919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22010795232489899982353225 16508096424367424986764919)
            ·
              refine ⟨24762144636551137480147379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16508096424367424986764919 24762144636551137480147379)
              ·
                refine ⟨37143216954826706220221069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24762144636551137480147379 37143216954826706220221069)
                ·
                  refine ⟨13928706358060014832582901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37143216954826706220221069 13928706358060014832582901)
                  ·
                    refine ⟨1305816221068126390554647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13928706358060014832582901 1305816221068126390554647)
                    ·
                      rfl

theorem cell22_3814602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_3814602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3814602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3814602 prefixEnd_3814602 := by exact prefixLift 3814602
  have htrace : WordTrace (prefixWord ++ tailWord_3814602) baseStart_3814602 baseEnd_3814602 := by
    simpa [prefixWord, tailWord_3814602, baseEnd_3814602] using wordTrace_append hprefix tailTrace_3814602
  have hstable : (prefixWord ++ tailWord_3814602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814602).length < 2 ^ (prefixWord ++ tailWord_3814602).sum := by decide
  have hdescent : baseEnd_3814602 < baseStart_3814602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814614 : List Nat := [5, 2, 1, 2, 3, 1, 2, 2, 1, 3]
def baseStart_3814614 : Nat := 118140960795 + 3814614 * 2 ^ 59
def prefixEnd_3814614 : Nat := 4983230072969 + 3 ^ 40 * 3814614 * 2
def baseEnd_3814614 : Nat := 1305820328913362359254611

theorem tailTrace_3814614 : CollatzResearch.WordTrace tailWord_3814614 prefixEnd_3814614 1305820328913362359254611 := by
  unfold tailWord_3814614
  simp only [CollatzResearch.WordTrace]
  refine ⟨8695650162644527315562681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92753601734874958032668597 8695650162644527315562681)
  ·
    refine ⟨6521737621983395486672011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8695650162644527315562681 6521737621983395486672011)
    ·
      refine ⟨9782606432975093230008017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6521737621983395486672011 9782606432975093230008017)
      ·
        refine ⟨7336954824731319922506013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9782606432975093230008017 7336954824731319922506013)
        ·
          refine ⟨2751358059274244970939755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7336954824731319922506013 2751358059274244970939755)
          ·
            refine ⟨4127037088911367456409633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2751358059274244970939755 4127037088911367456409633)
            ·
              refine ⟨3095277816683525592307225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4127037088911367456409633 3095277816683525592307225)
              ·
                refine ⟨2321458362512644194230419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3095277816683525592307225 2321458362512644194230419)
                ·
                  refine ⟨3482187543768966291345629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2321458362512644194230419 3482187543768966291345629)
                  ·
                    refine ⟨1305820328913362359254611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3482187543768966291345629 1305820328913362359254611)
                    ·
                      rfl

theorem cell22_3814614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_3814614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3814614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3814614 prefixEnd_3814614 := by exact prefixLift 3814614
  have htrace : WordTrace (prefixWord ++ tailWord_3814614) baseStart_3814614 baseEnd_3814614 := by
    simpa [prefixWord, tailWord_3814614, baseEnd_3814614] using wordTrace_append hprefix tailTrace_3814614
  have hstable : (prefixWord ++ tailWord_3814614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814614).length < 2 ^ (prefixWord ++ tailWord_3814614).sum := by decide
  have hdescent : baseEnd_3814614 < baseStart_3814614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814767 : List Nat := [1, 1, 2, 1, 3, 1, 3, 10]
def baseStart_3814767 : Nat := 118140960795 + 3814767 * 2 ^ 59
def prefixEnd_3814767 : Nat := 4983230072969 + 3 ^ 40 * 3814767 * 2
def baseEnd_3814767 : Nat := 145096967104457884464349

theorem tailTrace_3814767 : CollatzResearch.WordTrace tailWord_3814767 prefixEnd_3814767 145096967104457884464349 := by
  unfold tailWord_3814767
  simp only [CollatzResearch.WordTrace]
  refine ⟨139135982970758144179322555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92757321980505429452881703 139135982970758144179322555)
  ·
    refine ⟨208703974456137216268983833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139135982970758144179322555 208703974456137216268983833)
    ·
      refine ⟨156527980842102912201737875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208703974456137216268983833 156527980842102912201737875)
      ·
        refine ⟨234791971263154368302606813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156527980842102912201737875 234791971263154368302606813)
        ·
          refine ⟨88046989223682888113477555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234791971263154368302606813 88046989223682888113477555)
          ·
            refine ⟨132070483835524332170216333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88046989223682888113477555 132070483835524332170216333)
            ·
              refine ⟨49526431438321624563831125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132070483835524332170216333 49526431438321624563831125)
              ·
                refine ⟨145096967104457884464349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49526431438321624563831125 145096967104457884464349)
                ·
                  rfl

theorem cell22_3814767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 10].length) (baseStart_3814767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3814767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3814767 prefixEnd_3814767 := by exact prefixLift 3814767
  have htrace : WordTrace (prefixWord ++ tailWord_3814767) baseStart_3814767 baseEnd_3814767 := by
    simpa [prefixWord, tailWord_3814767, baseEnd_3814767] using wordTrace_append hprefix tailTrace_3814767
  have hstable : (prefixWord ++ tailWord_3814767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814767).length < 2 ^ (prefixWord ++ tailWord_3814767).sum := by decide
  have hdescent : baseEnd_3814767 < baseStart_3814767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814769 : List Nat := [1, 2, 2, 2, 1, 2, 3, 3, 2, 4]
def baseStart_3814769 : Nat := 118140960795 + 3814769 * 2 ^ 59
def prefixEnd_3814769 : Nat := 4983230072969 + 3 ^ 40 * 3814769 * 2
def baseEnd_3814769 : Nat := 1305873388580993621629135

theorem tailTrace_3814769 : CollatzResearch.WordTrace tailWord_3814769 prefixEnd_3814769 1305873388580993621629135 := by
  unfold tailWord_3814769
  simp only [CollatzResearch.WordTrace]
  refine ⟨139136055916750898520895361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92757370611167265680596907 139136055916750898520895361)
  ·
    refine ⟨104352041937563173890671521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139136055916750898520895361 104352041937563173890671521)
    ·
      refine ⟨78264031453172380418003641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104352041937563173890671521 78264031453172380418003641)
      ·
        refine ⟨58698023589879285313502731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78264031453172380418003641 58698023589879285313502731)
        ·
          refine ⟨88047035384818927970254097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58698023589879285313502731 88047035384818927970254097)
          ·
            refine ⟨66035276538614195977690573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88047035384818927970254097 66035276538614195977690573)
            ·
              refine ⟨24763228701980323491633965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66035276538614195977690573 24763228701980323491633965)
              ·
                refine ⟨9286210763242621309362737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24763228701980323491633965 9286210763242621309362737)
                ·
                  refine ⟨6964658072431965982022053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9286210763242621309362737 6964658072431965982022053)
                  ·
                    refine ⟨1305873388580993621629135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6964658072431965982022053 1305873388580993621629135)
                    ·
                      rfl

theorem cell22_3814769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_3814769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3814769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3814769 prefixEnd_3814769 := by exact prefixLift 3814769
  have htrace : WordTrace (prefixWord ++ tailWord_3814769) baseStart_3814769 baseEnd_3814769 := by
    simpa [prefixWord, tailWord_3814769, baseEnd_3814769] using wordTrace_append hprefix tailTrace_3814769
  have hstable : (prefixWord ++ tailWord_3814769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814769).length < 2 ^ (prefixWord ++ tailWord_3814769).sum := by decide
  have hdescent : baseEnd_3814769 < baseStart_3814769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814788 : List Nat := [2, 3, 2, 1, 1, 4, 2, 2, 2, 3]
def baseStart_3814788 : Nat := 118140960795 + 3814788 * 2 ^ 59
def prefixEnd_3814788 : Nat := 4983230072969 + 3 ^ 40 * 3814788 * 2
def baseEnd_3814788 : Nat := 1305879892669283905404077

theorem tailTrace_3814788 : CollatzResearch.WordTrace tailWord_3814788 prefixEnd_3814788 1305879892669283905404077 := by
  unfold tailWord_3814788
  simp only [CollatzResearch.WordTrace]
  refine ⟨69568374451841032382918509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92757832602454709843891345 69568374451841032382918509)
  ·
    refine ⟨26088140419440387143594441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69568374451841032382918509 26088140419440387143594441)
    ·
      refine ⟨19566105314580290357695831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26088140419440387143594441 19566105314580290357695831)
      ·
        refine ⟨29349157971870435536543747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19566105314580290357695831 29349157971870435536543747)
        ·
          refine ⟨44023736957805653304815621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29349157971870435536543747 44023736957805653304815621)
          ·
            refine ⟨8254450679588559994652929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44023736957805653304815621 8254450679588559994652929)
            ·
              refine ⟨6190838009691419995989697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8254450679588559994652929 6190838009691419995989697)
              ·
                refine ⟨4643128507268564996992273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6190838009691419995989697 4643128507268564996992273)
                ·
                  refine ⟨3482346380451423747744205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4643128507268564996992273 3482346380451423747744205)
                  ·
                    refine ⟨1305879892669283905404077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3482346380451423747744205 1305879892669283905404077)
                    ·
                      rfl

theorem cell22_3814788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_3814788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3814788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3814788 prefixEnd_3814788 := by exact prefixLift 3814788
  have htrace : WordTrace (prefixWord ++ tailWord_3814788) baseStart_3814788 baseEnd_3814788 := by
    simpa [prefixWord, tailWord_3814788, baseEnd_3814788] using wordTrace_append hprefix tailTrace_3814788
  have hstable : (prefixWord ++ tailWord_3814788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814788).length < 2 ^ (prefixWord ++ tailWord_3814788).sum := by decide
  have hdescent : baseEnd_3814788 < baseStart_3814788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814816 : List Nat := [2, 1, 1, 4, 1, 2, 3, 2, 3, 3]
def baseStart_3814816 : Nat := 118140960795 + 3814816 * 2 ^ 59
def prefixEnd_3814816 : Nat := 4983230072969 + 3 ^ 40 * 3814816 * 2
def baseEnd_3814816 : Nat := 1305889477641501165703991

theorem tailTrace_3814816 : CollatzResearch.WordTrace tailWord_3814816 prefixEnd_3814816 1305889477641501165703991 := by
  unfold tailWord_3814816
  simp only [CollatzResearch.WordTrace]
  refine ⟨69568885073790312773928151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92758513431720417031904201 69568885073790312773928151)
  ·
    refine ⟨104353327610685469160892227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69568885073790312773928151 104353327610685469160892227)
    ·
      refine ⟨156529991416028203741338341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104353327610685469160892227 156529991416028203741338341)
      ·
        refine ⟨29349373390505288201500939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156529991416028203741338341 29349373390505288201500939)
        ·
          refine ⟨44024060085757932302251409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29349373390505288201500939 44024060085757932302251409)
          ·
            refine ⟨33018045064318449226688557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44024060085757932302251409 33018045064318449226688557)
            ·
              refine ⟨12381766899119418460008209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33018045064318449226688557 12381766899119418460008209)
              ·
                refine ⟨9286325174339563845006157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12381766899119418460008209 9286325174339563845006157)
                ·
                  refine ⟨3482371940377336441877309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9286325174339563845006157 3482371940377336441877309)
                  ·
                    refine ⟨1305889477641501165703991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3482371940377336441877309 1305889477641501165703991)
                    ·
                      rfl

theorem cell22_3814816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 3, 3].length) (baseStart_3814816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3814816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3814816 prefixEnd_3814816 := by exact prefixLift 3814816
  have htrace : WordTrace (prefixWord ++ tailWord_3814816) baseStart_3814816 baseEnd_3814816 := by
    simpa [prefixWord, tailWord_3814816, baseEnd_3814816] using wordTrace_append hprefix tailTrace_3814816
  have hstable : (prefixWord ++ tailWord_3814816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814816).length < 2 ^ (prefixWord ++ tailWord_3814816).sum := by decide
  have hdescent : baseEnd_3814816 < baseStart_3814816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814859 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 5, 4]
def baseStart_3814859 : Nat := 118140960795 + 3814859 * 2 ^ 59
def prefixEnd_3814859 : Nat := 4983230072969 + 3 ^ 40 * 3814859 * 2
def baseEnd_3814859 : Nat := 1305904197420263386878859

theorem tailTrace_3814859 : CollatzResearch.WordTrace tailWord_3814859 prefixEnd_3814859 1305904197420263386878859 := by
  unfold tailWord_3814859
  simp only [CollatzResearch.WordTrace]
  refine ⟨139139338486424843891671631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92759558990949895927781087 139139338486424843891671631)
  ·
    refine ⟨208709007729637265837507447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139139338486424843891671631 208709007729637265837507447)
    ·
      refine ⟨313063511594455898756261171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208709007729637265837507447 313063511594455898756261171)
      ·
        refine ⟨469595267391683848134391757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313063511594455898756261171 469595267391683848134391757)
        ·
          refine ⟨176098225271881443050396909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 469595267391683848134391757 176098225271881443050396909)
          ·
            refine ⟨66036834476955541143898841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176098225271881443050396909 66036834476955541143898841)
            ·
              refine ⟨49527625857716655857924131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66036834476955541143898841 49527625857716655857924131)
              ·
                refine ⟨74291438786574983786886197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49527625857716655857924131 74291438786574983786886197)
                ·
                  refine ⟨6964822386241404730020581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74291438786574983786886197 6964822386241404730020581)
                  ·
                    refine ⟨1305904197420263386878859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6964822386241404730020581 1305904197420263386878859)
                    ·
                      rfl

theorem cell22_3814859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 4].length) (baseStart_3814859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3814859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3814859 prefixEnd_3814859 := by exact prefixLift 3814859
  have htrace : WordTrace (prefixWord ++ tailWord_3814859) baseStart_3814859 baseEnd_3814859 := by
    simpa [prefixWord, tailWord_3814859, baseEnd_3814859] using wordTrace_append hprefix tailTrace_3814859
  have hstable : (prefixWord ++ tailWord_3814859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814859).length < 2 ^ (prefixWord ++ tailWord_3814859).sum := by decide
  have hdescent : baseEnd_3814859 < baseStart_3814859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814891 : List Nat := [1, 1, 1, 1, 2, 3, 2, 7, 4]
def baseStart_3814891 : Nat := 118140960795 + 3814891 * 2 ^ 59
def prefixEnd_3814891 : Nat := 4983230072969 + 3 ^ 40 * 3814891 * 2
def baseEnd_3814891 : Nat := 435305050558075323359587

theorem tailTrace_3814891 : CollatzResearch.WordTrace tailWord_3814891 prefixEnd_3814891 435305050558075323359587 := by
  unfold tailWord_3814891
  simp only [CollatzResearch.WordTrace]
  refine ⟨139140505622308913356836527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92760337081539275571224351 139140505622308913356836527)
  ·
    refine ⟨208710758433463370035254791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139140505622308913356836527 208710758433463370035254791)
    ·
      refine ⟨313066137650195055052882187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208710758433463370035254791 313066137650195055052882187)
      ·
        refine ⟨469599206475292582579323281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313066137650195055052882187 469599206475292582579323281)
        ·
          refine ⟨352199404856469436934492461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469599206475292582579323281 352199404856469436934492461)
          ·
            refine ⟨132074776821176038850434673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 352199404856469436934492461 132074776821176038850434673)
            ·
              refine ⟨99056082615882029137826005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132074776821176038850434673 99056082615882029137826005)
              ·
                refine ⟨2321626936309735057917797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 99056082615882029137826005 2321626936309735057917797)
                ·
                  refine ⟨435305050558075323359587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2321626936309735057917797 435305050558075323359587)
                  ·
                    rfl

theorem cell22_3814891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 7, 4].length) (baseStart_3814891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3814891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3814891 prefixEnd_3814891 := by exact prefixLift 3814891
  have htrace : WordTrace (prefixWord ++ tailWord_3814891) baseStart_3814891 baseEnd_3814891 := by
    simpa [prefixWord, tailWord_3814891, baseEnd_3814891] using wordTrace_append hprefix tailTrace_3814891
  have hstable : (prefixWord ++ tailWord_3814891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814891).length < 2 ^ (prefixWord ++ tailWord_3814891).sum := by decide
  have hdescent : baseEnd_3814891 < baseStart_3814891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814906 : List Nat := [3, 1, 1, 1, 1, 2, 3, 3, 4, 3]
def baseStart_3814906 : Nat := 118140960795 + 3814906 * 2 ^ 59
def prefixEnd_3814906 : Nat := 4983230072969 + 3 ^ 40 * 3814906 * 2
def baseEnd_3814906 : Nat := 1305920286480770930953715

theorem tailTrace_3814906 : CollatzResearch.WordTrace tailWord_3814906 prefixEnd_3814906 1305920286480770930953715 := by
  unfold tailWord_3814906
  simp only [CollatzResearch.WordTrace]
  refine ⟨34785263179313642729658143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92760701811503047279088381 34785263179313642729658143)
  ·
    refine ⟨52177894768970464094487215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34785263179313642729658143 52177894768970464094487215)
    ·
      refine ⟨78266842153455696141730823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52177894768970464094487215 78266842153455696141730823)
      ·
        refine ⟨117400263230183544212596235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78266842153455696141730823 117400263230183544212596235)
        ·
          refine ⟨176100394845275316318894353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117400263230183544212596235 176100394845275316318894353)
          ·
            refine ⟨132075296133956487239170765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176100394845275316318894353 132075296133956487239170765)
            ·
              refine ⟨49528236050233682714689037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132075296133956487239170765 49528236050233682714689037)
              ·
                refine ⟨18573088518837631018008389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49528236050233682714689037 18573088518837631018008389)
                ·
                  refine ⟨3482454097282055815876573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18573088518837631018008389 3482454097282055815876573)
                  ·
                    refine ⟨1305920286480770930953715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3482454097282055815876573 1305920286480770930953715)
                    ·
                      rfl

theorem cell22_3814906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 4, 3].length) (baseStart_3814906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3814906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3814906 prefixEnd_3814906 := by exact prefixLift 3814906
  have htrace : WordTrace (prefixWord ++ tailWord_3814906) baseStart_3814906 baseEnd_3814906 := by
    simpa [prefixWord, tailWord_3814906, baseEnd_3814906] using wordTrace_append hprefix tailTrace_3814906
  have hstable : (prefixWord ++ tailWord_3814906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814906).length < 2 ^ (prefixWord ++ tailWord_3814906).sum := by decide
  have hdescent : baseEnd_3814906 < baseStart_3814906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814981 : List Nat := [1, 3, 1, 1, 1, 4, 1, 5, 5]
def baseStart_3814981 : Nat := 118140960795 + 3814981 * 2 ^ 59
def prefixEnd_3814981 : Nat := 4983230072969 + 3 ^ 40 * 3814981 * 2
def baseEnd_3814981 : Nat := 435315320171165245109495

theorem tailTrace_3814981 : CollatzResearch.WordTrace tailWord_3814981 prefixEnd_3814981 435315320171165245109495 := by
  unfold tailWord_3814981
  simp only [CollatzResearch.WordTrace]
  refine ⟨139143788191982858727612797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92762525461321905818408531 139143788191982858727612797)
  ·
    refine ⟨52178920571993572022854799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139143788191982858727612797 52178920571993572022854799)
    ·
      refine ⟨78268380857990358034282199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52178920571993572022854799 78268380857990358034282199)
      ·
        refine ⟨117402571286985537051423299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78268380857990358034282199 117402571286985537051423299)
        ·
          refine ⟨176103856930478305577134949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117402571286985537051423299 176103856930478305577134949)
          ·
            refine ⟨33019473174464682295712803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176103856930478305577134949 33019473174464682295712803)
            ·
              refine ⟨49529209761697023443569205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33019473174464682295712803 49529209761697023443569205)
              ·
                refine ⟨4643363415159095947834613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49529209761697023443569205 4643363415159095947834613)
                ·
                  refine ⟨435315320171165245109495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4643363415159095947834613 435315320171165245109495)
                  ·
                    rfl

theorem cell22_3814981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 5].length) (baseStart_3814981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3814981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3814981 prefixEnd_3814981 := by exact prefixLift 3814981
  have htrace : WordTrace (prefixWord ++ tailWord_3814981) baseStart_3814981 baseEnd_3814981 := by
    simpa [prefixWord, tailWord_3814981, baseEnd_3814981] using wordTrace_append hprefix tailTrace_3814981
  have hstable : (prefixWord ++ tailWord_3814981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814981).length < 2 ^ (prefixWord ++ tailWord_3814981).sum := by decide
  have hdescent : baseEnd_3814981 < baseStart_3814981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3814996 : List Nat := [2, 4, 1, 1, 1, 2, 1, 2, 1, 7]
def baseStart_3814996 : Nat := 118140960795 + 3814996 * 2 ^ 59
def prefixEnd_3814996 : Nat := 4983230072969 + 3 ^ 40 * 3814996 * 2
def baseEnd_3814996 : Nat := 1305951095320040696203439

theorem tailTrace_3814996 : CollatzResearch.WordTrace tailWord_3814996 prefixEnd_3814996 1305951095320040696203439 := by
  unfold tailWord_3814996
  simp only [CollatzResearch.WordTrace]
  refine ⟨69572167643464258144704421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92762890191285677526272561 69572167643464258144704421)
  ·
    refine ⟨13044781433149548402132079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69572167643464258144704421 13044781433149548402132079)
    ·
      refine ⟨19567172149724322603198119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13044781433149548402132079 19567172149724322603198119)
      ·
        refine ⟨29350758224586483904797179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19567172149724322603198119 29350758224586483904797179)
        ·
          refine ⟨44026137336879725857195769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29350758224586483904797179 44026137336879725857195769)
          ·
            refine ⟨33019603002659794392896827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44026137336879725857195769 33019603002659794392896827)
            ·
              refine ⟨49529404503989691589345241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33019603002659794392896827 49529404503989691589345241)
              ·
                refine ⟨37147053377992268692008931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49529404503989691589345241 37147053377992268692008931)
                ·
                  refine ⟨55720580066988403038013397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37147053377992268692008931 55720580066988403038013397)
                  ·
                    refine ⟨1305951095320040696203439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55720580066988403038013397 1305951095320040696203439)
                    ·
                      rfl

theorem cell22_3814996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_3814996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3814996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3814996 prefixEnd_3814996 := by exact prefixLift 3814996
  have htrace : WordTrace (prefixWord ++ tailWord_3814996) baseStart_3814996 baseEnd_3814996 := by
    simpa [prefixWord, tailWord_3814996, baseEnd_3814996] using wordTrace_append hprefix tailTrace_3814996
  have hstable : (prefixWord ++ tailWord_3814996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3814996).length < 2 ^ (prefixWord ++ tailWord_3814996).sum := by decide
  have hdescent : baseEnd_3814996 < baseStart_3814996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3814996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815056 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 6, 4]
def baseStart_3815056 : Nat := 118140960795 + 3815056 * 2 ^ 59
def prefixEnd_3815056 : Nat := 4983230072969 + 3 ^ 40 * 3815056 * 2
def baseEnd_3815056 : Nat := 1305971634546220539703255

theorem tailTrace_3815056 : CollatzResearch.WordTrace tailWord_3815056 prefixEnd_3815056 1305971634546220539703255 := by
  unfold tailWord_3815056
  simp only [CollatzResearch.WordTrace]
  refine ⟨69573261833355573268296511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92764349111140764357728681 69573261833355573268296511)
  ·
    refine ⟨104359892750033359902444767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69573261833355573268296511 104359892750033359902444767)
    ·
      refine ⟨156539839125050039853667151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104359892750033359902444767 156539839125050039853667151)
      ·
        refine ⟨234809758687575059780500727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156539839125050039853667151 234809758687575059780500727)
        ·
          refine ⟨352214638031362589670751091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234809758687575059780500727 352214638031362589670751091)
          ·
            refine ⟨528321957047043884506126637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352214638031362589670751091 528321957047043884506126637)
            ·
              refine ⟨198120733892641456689797489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 528321957047043884506126637 198120733892641456689797489)
              ·
                refine ⟨148590550419481092517348117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198120733892641456689797489 148590550419481092517348117)
                ·
                  refine ⟨6965182050913176211750693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 148590550419481092517348117 6965182050913176211750693)
                  ·
                    refine ⟨1305971634546220539703255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6965182050913176211750693 1305971634546220539703255)
                    ·
                      rfl

theorem cell22_3815056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 6, 4].length) (baseStart_3815056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3815056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3815056 prefixEnd_3815056 := by exact prefixLift 3815056
  have htrace : WordTrace (prefixWord ++ tailWord_3815056) baseStart_3815056 baseEnd_3815056 := by
    simpa [prefixWord, tailWord_3815056, baseEnd_3815056] using wordTrace_append hprefix tailTrace_3815056
  have hstable : (prefixWord ++ tailWord_3815056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815056).length < 2 ^ (prefixWord ++ tailWord_3815056).sum := by decide
  have hdescent : baseEnd_3815056 < baseStart_3815056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815073 : List Nat := [1, 2, 3, 3, 2, 1, 1, 1, 4, 4]
def baseStart_3815073 : Nat := 118140960795 + 3815073 * 2 ^ 59
def prefixEnd_3815073 : Nat := 4983230072969 + 3 ^ 40 * 3815073 * 2
def baseEnd_3815073 : Nat := 1305977453993638162028203

theorem tailTrace_3815073 : CollatzResearch.WordTrace tailWord_3815073 prefixEnd_3815073 1305977453993638162028203 := by
  unfold tailWord_3815073
  simp only [CollatzResearch.WordTrace]
  refine ⟨139147143707649558439961873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92764762471766372293307915 139147143707649558439961873)
  ·
    refine ⟨104360357780737168829971405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139147143707649558439961873 104360357780737168829971405)
    ·
      refine ⟨39135134167776438311239277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104360357780737168829971405 39135134167776438311239277)
      ·
        refine ⟨14675675312916164366714729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39135134167776438311239277 14675675312916164366714729)
        ·
          refine ⟨11006756484687123275036047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14675675312916164366714729 11006756484687123275036047)
          ·
            refine ⟨16510134727030684912554071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11006756484687123275036047 16510134727030684912554071)
            ·
              refine ⟨24765202090546027368831107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16510134727030684912554071 24765202090546027368831107)
              ·
                refine ⟨37147803135819041053246661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24765202090546027368831107 37147803135819041053246661)
                ·
                  refine ⟨6965213087966070197483749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37147803135819041053246661 6965213087966070197483749)
                  ·
                    refine ⟨1305977453993638162028203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6965213087966070197483749 1305977453993638162028203)
                    ·
                      rfl

theorem cell22_3815073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_3815073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3815073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3815073 prefixEnd_3815073 := by exact prefixLift 3815073
  have htrace : WordTrace (prefixWord ++ tailWord_3815073) baseStart_3815073 baseEnd_3815073 := by
    simpa [prefixWord, tailWord_3815073, baseEnd_3815073] using wordTrace_append hprefix tailTrace_3815073
  have hstable : (prefixWord ++ tailWord_3815073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815073).length < 2 ^ (prefixWord ++ tailWord_3815073).sum := by decide
  have hdescent : baseEnd_3815073 < baseStart_3815073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815103 : List Nat := [1, 1, 2, 2, 2, 3, 2, 1, 5, 3]
def baseStart_3815103 : Nat := 118140960795 + 3815103 * 2 ^ 59
def prefixEnd_3815103 : Nat := 4983230072969 + 3 ^ 40 * 3815103 * 2
def baseEnd_3815103 : Nat := 1305987723606728083778111

theorem tailTrace_3815103 : CollatzResearch.WordTrace tailWord_3815103 prefixEnd_3815103 1305987723606728083778111 := by
  unfold tailWord_3815103
  simp only [CollatzResearch.WordTrace]
  refine ⟨139148237897540873563553963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92765491931693915709035975 139148237897540873563553963)
  ·
    refine ⟨208722356846311310345330945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139148237897540873563553963 208722356846311310345330945)
    ·
      refine ⟨156541767634733482758998209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208722356846311310345330945 156541767634733482758998209)
      ·
        refine ⟨117406325726050112069248657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156541767634733482758998209 117406325726050112069248657)
        ·
          refine ⟨88054744294537584051936493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117406325726050112069248657 88054744294537584051936493)
          ·
            refine ⟨33020529110451594019476185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88054744294537584051936493 33020529110451594019476185)
            ·
              refine ⟨24765396832838695514607139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33020529110451594019476185 24765396832838695514607139)
              ·
                refine ⟨37148095249258043271910709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24765396832838695514607139 37148095249258043271910709)
                ·
                  refine ⟨3482633929617941556741629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37148095249258043271910709 3482633929617941556741629)
                  ·
                    refine ⟨1305987723606728083778111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3482633929617941556741629 1305987723606728083778111)
                    ·
                      rfl

theorem cell22_3815103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 5, 3].length) (baseStart_3815103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3815103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3815103 prefixEnd_3815103 := by exact prefixLift 3815103
  have htrace : WordTrace (prefixWord ++ tailWord_3815103) baseStart_3815103 baseEnd_3815103 := by
    simpa [prefixWord, tailWord_3815103, baseEnd_3815103] using wordTrace_append hprefix tailTrace_3815103
  have hstable : (prefixWord ++ tailWord_3815103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815103).length < 2 ^ (prefixWord ++ tailWord_3815103).sum := by decide
  have hdescent : baseEnd_3815103 < baseStart_3815103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815126 : List Nat := [5, 2, 1, 3, 1, 1, 2, 2, 2, 3]
def baseStart_3815126 : Nat := 118140960795 + 3815126 * 2 ^ 59
def prefixEnd_3815126 : Nat := 4983230072969 + 3 ^ 40 * 3815126 * 2
def baseEnd_3815126 : Nat := 1305995596976763690453041

theorem tailTrace_3815126 : CollatzResearch.WordTrace tailWord_3815126 prefixEnd_3815126 1305995596976763690453041 := by
  unfold tailWord_3815126
  simp only [CollatzResearch.WordTrace]
  refine ⟨8696817298528596780727577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92766051184305032327760821 8696817298528596780727577)
  ·
    refine ⟨6522612973896447585545683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8696817298528596780727577 6522612973896447585545683)
    ·
      refine ⟨9783919460844671378318525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6522612973896447585545683 9783919460844671378318525)
      ·
        refine ⟨3668969797816751766869447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9783919460844671378318525 3668969797816751766869447)
        ·
          refine ⟨5503454696725127650304171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3668969797816751766869447 5503454696725127650304171)
          ·
            refine ⟨8255182045087691475456257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5503454696725127650304171 8255182045087691475456257)
            ·
              refine ⟨6191386533815768606592193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8255182045087691475456257 6191386533815768606592193)
              ·
                refine ⟨4643539900361826454944145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6191386533815768606592193 4643539900361826454944145)
                ·
                  refine ⟨3482654925271369841208109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4643539900361826454944145 3482654925271369841208109)
                  ·
                    refine ⟨1305995596976763690453041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3482654925271369841208109 1305995596976763690453041)
                    ·
                      rfl

theorem cell22_3815126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_3815126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3815126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3815126 prefixEnd_3815126 := by exact prefixLift 3815126
  have htrace : WordTrace (prefixWord ++ tailWord_3815126) baseStart_3815126 baseEnd_3815126 := by
    simpa [prefixWord, tailWord_3815126, baseEnd_3815126] using wordTrace_append hprefix tailTrace_3815126
  have hstable : (prefixWord ++ tailWord_3815126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815126).length < 2 ^ (prefixWord ++ tailWord_3815126).sum := by decide
  have hdescent : baseEnd_3815126 < baseStart_3815126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815214 : List Nat := [4, 1, 3, 2, 2, 1, 2, 2, 1, 4]
def baseStart_3815214 : Nat := 118140960795 + 3815214 * 2 ^ 59
def prefixEnd_3815214 : Nat := 4983230072969 + 3 ^ 40 * 3815214 * 2
def baseEnd_3815214 : Nat := 1306025721175160794252771

theorem tailTrace_3815214 : CollatzResearch.WordTrace tailWord_3815214 prefixEnd_3815214 1306025721175160794252771 := by
  unfold tailWord_3815214
  simp only [CollatzResearch.WordTrace]
  refine ⟨17394035800017342440105587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92768190933425826347229797 17394035800017342440105587)
  ·
    refine ⟨26091053700026013660158381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17394035800017342440105587 26091053700026013660158381)
    ·
      refine ⟨9784145137509755122559393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26091053700026013660158381 9784145137509755122559393)
      ·
        refine ⟨7338108853132316341919545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9784145137509755122559393 7338108853132316341919545)
        ·
          refine ⟨5503581639849237256439659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7338108853132316341919545 5503581639849237256439659)
          ·
            refine ⟨8255372459773855884659489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5503581639849237256439659 8255372459773855884659489)
            ·
              refine ⟨6191529344830391913494617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8255372459773855884659489 6191529344830391913494617)
              ·
                refine ⟨4643647008622793935120963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6191529344830391913494617 4643647008622793935120963)
                ·
                  refine ⟨6965470512934190902681445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4643647008622793935120963 6965470512934190902681445)
                  ·
                    refine ⟨1306025721175160794252771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6965470512934190902681445 1306025721175160794252771)
                    ·
                      rfl

theorem cell22_3815214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_3815214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3815214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3815214 prefixEnd_3815214 := by exact prefixLift 3815214
  have htrace : WordTrace (prefixWord ++ tailWord_3815214) baseStart_3815214 baseEnd_3815214 := by
    simpa [prefixWord, tailWord_3815214, baseEnd_3815214] using wordTrace_append hprefix tailTrace_3815214
  have hstable : (prefixWord ++ tailWord_3815214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815214).length < 2 ^ (prefixWord ++ tailWord_3815214).sum := by decide
  have hdescent : baseEnd_3815214 < baseStart_3815214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815229 : List Nat := [1, 4, 1, 4, 1, 3, 1, 3, 4]
def baseStart_3815229 : Nat := 118140960795 + 3815229 * 2 ^ 59
def prefixEnd_3815229 : Nat := 4983230072969 + 3 ^ 40 * 3815229 * 2
def baseEnd_3815229 : Nat := 435343618660568585042575

theorem tailTrace_3815229 : CollatzResearch.WordTrace tailWord_3815229 prefixEnd_3815229 435343618660568585042575 := by
  unfold tailWord_3815229
  simp only [CollatzResearch.WordTrace]
  refine ⟨139152833495084397082640741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92768555663389598055093827 139152833495084397082640741)
  ·
    refine ⟨26091156280328324452995139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139152833495084397082640741 26091156280328324452995139)
    ·
      refine ⟨39136734420492486679492709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26091156280328324452995139 39136734420492486679492709)
      ·
        refine ⟨7338137703842341252404883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39136734420492486679492709 7338137703842341252404883)
        ·
          refine ⟨11007206555763511878607325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7338137703842341252404883 11007206555763511878607325)
          ·
            refine ⟨4127702458411316954477747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11007206555763511878607325 4127702458411316954477747)
            ·
              refine ⟨6191553687616975431716621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4127702458411316954477747 6191553687616975431716621)
              ·
                refine ⟨2321832632856365786893733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6191553687616975431716621 2321832632856365786893733)
                ·
                  refine ⟨435343618660568585042575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2321832632856365786893733 435343618660568585042575)
                  ·
                    rfl

theorem cell22_3815229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_3815229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3815229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3815229 prefixEnd_3815229 := by exact prefixLift 3815229
  have htrace : WordTrace (prefixWord ++ tailWord_3815229) baseStart_3815229 baseEnd_3815229 := by
    simpa [prefixWord, tailWord_3815229, baseEnd_3815229] using wordTrace_append hprefix tailTrace_3815229
  have hstable : (prefixWord ++ tailWord_3815229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815229).length < 2 ^ (prefixWord ++ tailWord_3815229).sum := by decide
  have hdescent : baseEnd_3815229 < baseStart_3815229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815283 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 4, 5]
def baseStart_3815283 : Nat := 118140960795 + 3815283 * 2 ^ 59
def prefixEnd_3815283 : Nat := 4983230072969 + 3 ^ 40 * 3815283 * 2
def baseEnd_3815283 : Nat := 1306049341285267614277559

theorem tailTrace_3815283 : CollatzResearch.WordTrace tailWord_3815283 prefixEnd_3815283 1306049341285267614277559 := by
  unfold tailWord_3815283
  simp only [CollatzResearch.WordTrace]
  refine ⟨139154803036888764305106503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92769868691259176203404335 139154803036888764305106503)
  ·
    refine ⟨208732204555333146457659755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139154803036888764305106503 208732204555333146457659755)
    ·
      refine ⟨313098306832999719686489633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208732204555333146457659755 313098306832999719686489633)
      ·
        refine ⟨234823730124749789764867225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313098306832999719686489633 234823730124749789764867225)
        ·
          refine ⟨176117797593562342323650419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234823730124749789764867225 176117797593562342323650419)
          ·
            refine ⟨264176696390343513485475629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176117797593562342323650419 264176696390343513485475629)
            ·
              refine ⟨99066261146378817557053361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264176696390343513485475629 99066261146378817557053361)
              ·
                refine ⟨74299695859784113167790021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99066261146378817557053361 74299695859784113167790021)
                ·
                  refine ⟨13931192973709521218960629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74299695859784113167790021 13931192973709521218960629)
                  ·
                    refine ⟨1306049341285267614277559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13931192973709521218960629 1306049341285267614277559)
                    ·
                      rfl

theorem cell22_3815283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 5].length) (baseStart_3815283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3815283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3815283 prefixEnd_3815283 := by exact prefixLift 3815283
  have htrace : WordTrace (prefixWord ++ tailWord_3815283) baseStart_3815283 baseEnd_3815283 := by
    simpa [prefixWord, tailWord_3815283, baseEnd_3815283] using wordTrace_append hprefix tailTrace_3815283
  have hstable : (prefixWord ++ tailWord_3815283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815283).length < 2 ^ (prefixWord ++ tailWord_3815283).sum := by decide
  have hdescent : baseEnd_3815283 < baseStart_3815283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815306 : List Nat := [3, 1, 2, 4, 2, 1, 1, 4, 1, 3]
def baseStart_3815306 : Nat := 118140960795 + 3815306 * 2 ^ 59
def prefixEnd_3815306 : Nat := 4983230072969 + 3 ^ 40 * 3815306 * 2
def baseEnd_3815306 : Nat := 1306057214655303220952489

theorem tailTrace_3815306 : CollatzResearch.WordTrace tailWord_3815306 prefixEnd_3815306 1306057214655303220952489 := by
  unfold tailWord_3815306
  simp only [CollatzResearch.WordTrace]
  refine ⟨34788910478951359808298443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92770427943870292822129181 34788910478951359808298443)
  ·
    refine ⟨52183365718427039712447665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34788910478951359808298443 52183365718427039712447665)
    ·
      refine ⟨39137524288820279784335749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52183365718427039712447665 39137524288820279784335749)
      ·
        refine ⟨7338285804153802459562953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39137524288820279784335749 7338285804153802459562953)
        ·
          refine ⟨5503714353115351844672215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7338285804153802459562953 5503714353115351844672215)
          ·
            refine ⟨8255571529673027767008323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5503714353115351844672215 8255571529673027767008323)
            ·
              refine ⟨12383357294509541650512485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8255571529673027767008323 12383357294509541650512485)
              ·
                refine ⟨2321879492720539059471091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12383357294509541650512485 2321879492720539059471091)
                ·
                  refine ⟨3482819239080808589206637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2321879492720539059471091 3482819239080808589206637)
                  ·
                    refine ⟨1306057214655303220952489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3482819239080808589206637 1306057214655303220952489)
                    ·
                      rfl

theorem cell22_3815306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 4, 1, 3].length) (baseStart_3815306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3815306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3815306 prefixEnd_3815306 := by exact prefixLift 3815306
  have htrace : WordTrace (prefixWord ++ tailWord_3815306) baseStart_3815306 baseEnd_3815306 := by
    simpa [prefixWord, tailWord_3815306, baseEnd_3815306] using wordTrace_append hprefix tailTrace_3815306
  have hstable : (prefixWord ++ tailWord_3815306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815306).length < 2 ^ (prefixWord ++ tailWord_3815306).sum := by decide
  have hdescent : baseEnd_3815306 < baseStart_3815306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815347 : List Nat := [1, 1, 1, 2, 3, 1, 6, 3, 4]
def baseStart_3815347 : Nat := 118140960795 + 3815347 * 2 ^ 59
def prefixEnd_3815347 : Nat := 4983230072969 + 3 ^ 40 * 3815347 * 2
def baseEnd_3815347 : Nat := 435357083264397593559121

theorem tailTrace_3815347 : CollatzResearch.WordTrace tailWord_3815347 prefixEnd_3815347 435357083264397593559121 := by
  unfold tailWord_3815347
  simp only [CollatzResearch.WordTrace]
  refine ⟨139157137308656903235436295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92771424872437935490290863 139157137308656903235436295)
  ·
    refine ⟨208735705962985354853154443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139157137308656903235436295 208735705962985354853154443)
    ·
      refine ⟨313103558944478032279731665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208735705962985354853154443 313103558944478032279731665)
      ·
        refine ⟨234827669208358524209798749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313103558944478032279731665 234827669208358524209798749)
        ·
          refine ⟨88060375953134446578674531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234827669208358524209798749 88060375953134446578674531)
          ·
            refine ⟨132090563929701669868011797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88060375953134446578674531 132090563929701669868011797)
            ·
              refine ⟨6191745184204765775063053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 132090563929701669868011797 6191745184204765775063053)
              ·
                refine ⟨2321904444076787165648645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6191745184204765775063053 2321904444076787165648645)
                ·
                  refine ⟨435357083264397593559121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2321904444076787165648645 435357083264397593559121)
                  ·
                    rfl

theorem cell22_3815347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 3, 4].length) (baseStart_3815347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3815347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3815347 prefixEnd_3815347 := by exact prefixLift 3815347
  have htrace : WordTrace (prefixWord ++ tailWord_3815347) baseStart_3815347 baseEnd_3815347 := by
    simpa [prefixWord, tailWord_3815347, baseEnd_3815347] using wordTrace_append hprefix tailTrace_3815347
  have hstable : (prefixWord ++ tailWord_3815347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815347).length < 2 ^ (prefixWord ++ tailWord_3815347).sum := by decide
  have hdescent : baseEnd_3815347 < baseStart_3815347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815349 : List Nat := [1, 3, 3, 2, 1, 2, 4, 1, 1, 4]
def baseStart_3815349 : Nat := 118140960795 + 3815349 * 2 ^ 59
def prefixEnd_3815349 : Nat := 4983230072969 + 3 ^ 40 * 3815349 * 2
def baseEnd_3815349 : Nat := 1306071934434065442127357

theorem tailTrace_3815349 : CollatzResearch.WordTrace tailWord_3815349 prefixEnd_3815349 1306071934434065442127357 := by
  unfold tailWord_3815349
  simp only [CollatzResearch.WordTrace]
  refine ⟨139157210254649657577009101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92771473503099771718006067 139157210254649657577009101)
  ·
    refine ⟨52183953845493621591378413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139157210254649657577009101 52183953845493621591378413)
    ·
      refine ⟨19568982692060108096766905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52183953845493621591378413 19568982692060108096766905)
      ·
        refine ⟨14676737019045081072575179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19568982692060108096766905 14676737019045081072575179)
        ·
          refine ⟨22015105528567621608862769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14676737019045081072575179 22015105528567621608862769)
          ·
            refine ⟨16511329146425716206647077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22015105528567621608862769 16511329146425716206647077)
            ·
              refine ⟨3095874214954821788746327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16511329146425716206647077 3095874214954821788746327)
              ·
                refine ⟨4643811322432232683119491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3095874214954821788746327 4643811322432232683119491)
                ·
                  refine ⟨6965716983648349024679237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4643811322432232683119491 6965716983648349024679237)
                  ·
                    refine ⟨1306071934434065442127357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6965716983648349024679237 1306071934434065442127357)
                    ·
                      rfl

theorem cell22_3815349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_3815349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3815349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3815349 prefixEnd_3815349 := by exact prefixLift 3815349
  have htrace : WordTrace (prefixWord ++ tailWord_3815349) baseStart_3815349 baseEnd_3815349 := by
    simpa [prefixWord, tailWord_3815349, baseEnd_3815349] using wordTrace_append hprefix tailTrace_3815349
  have hstable : (prefixWord ++ tailWord_3815349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815349).length < 2 ^ (prefixWord ++ tailWord_3815349).sum := by decide
  have hdescent : baseEnd_3815349 < baseStart_3815349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815360 : List Nat := [2, 1, 1, 2, 3, 2, 2, 1, 4, 4]
def baseStart_3815360 : Nat := 118140960795 + 3815360 * 2 ^ 59
def prefixEnd_3815360 : Nat := 4983230072969 + 3 ^ 40 * 3815360 * 2
def baseEnd_3815360 : Nat := 1306075699958865080102323

theorem tailTrace_3815360 : CollatzResearch.WordTrace tailWord_3815360 prefixEnd_3815360 1306075699958865080102323 := by
  unfold tailWord_3815360
  simp only [CollatzResearch.WordTrace]
  refine ⟨69578805728804903227829767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92771740971739870970439689 69578805728804903227829767)
  ·
    refine ⟨104368208593207354841744651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69578805728804903227829767 104368208593207354841744651)
    ·
      refine ⟨156552312889811032262616977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104368208593207354841744651 156552312889811032262616977)
      ·
        refine ⟨117414234667358274196962733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156552312889811032262616977 117414234667358274196962733)
        ·
          refine ⟨44030338000259352823861025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117414234667358274196962733 44030338000259352823861025)
          ·
            refine ⟨33022753500194514617895769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44030338000259352823861025 33022753500194514617895769)
            ·
              refine ⟨24767065125145885963421827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33022753500194514617895769 24767065125145885963421827)
              ·
                refine ⟨37150597687718828945132741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24767065125145885963421827 37150597687718828945132741)
                ·
                  refine ⟨6965737066447280427212389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37150597687718828945132741 6965737066447280427212389)
                  ·
                    refine ⟨1306075699958865080102323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6965737066447280427212389 1306075699958865080102323)
                    ·
                      rfl

theorem cell22_3815360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 4, 4].length) (baseStart_3815360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3815360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3815360 prefixEnd_3815360 := by exact prefixLift 3815360
  have htrace : WordTrace (prefixWord ++ tailWord_3815360) baseStart_3815360 baseEnd_3815360 := by
    simpa [prefixWord, tailWord_3815360, baseEnd_3815360] using wordTrace_append hprefix tailTrace_3815360
  have hstable : (prefixWord ++ tailWord_3815360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815360).length < 2 ^ (prefixWord ++ tailWord_3815360).sum := by decide
  have hdescent : baseEnd_3815360 < baseStart_3815360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815420 : List Nat := [2, 2, 2, 1, 2, 2, 1, 3, 7]
def baseStart_3815420 : Nat := 118140960795 + 3815420 * 2 ^ 59
def prefixEnd_3815420 : Nat := 4983230072969 + 3 ^ 40 * 3815420 * 2
def baseEnd_3815420 : Nat := 435365413061681641200713

theorem tailTrace_3815420 : CollatzResearch.WordTrace tailWord_3815420 prefixEnd_3815420 435365413061681641200713 := by
  unfold tailWord_3815420
  simp only [CollatzResearch.WordTrace]
  refine ⟨69579899918696218351421857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92773199891594957801895809 69579899918696218351421857)
  ·
    refine ⟨52184924939022163763566393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69579899918696218351421857 52184924939022163763566393)
    ·
      refine ⟨39138693704266622822674795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52184924939022163763566393 39138693704266622822674795)
      ·
        refine ⟨58708040556399934234012193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39138693704266622822674795 58708040556399934234012193)
        ·
          refine ⟨44031030417299950675509145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58708040556399934234012193 44031030417299950675509145)
          ·
            refine ⟨33023272812974963006631859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44031030417299950675509145 33023272812974963006631859)
            ·
              refine ⟨49534909219462444509947789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33023272812974963006631859 49534909219462444509947789)
              ·
                refine ⟨18575590957298416691230421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49534909219462444509947789 18575590957298416691230421)
                ·
                  refine ⟨435365413061681641200713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18575590957298416691230421 435365413061681641200713)
                  ·
                    rfl

theorem cell22_3815420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 7].length) (baseStart_3815420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3815420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3815420 prefixEnd_3815420 := by exact prefixLift 3815420
  have htrace : WordTrace (prefixWord ++ tailWord_3815420) baseStart_3815420 baseEnd_3815420 := by
    simpa [prefixWord, tailWord_3815420, baseEnd_3815420] using wordTrace_append hprefix tailTrace_3815420
  have hstable : (prefixWord ++ tailWord_3815420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815420).length < 2 ^ (prefixWord ++ tailWord_3815420).sum := by decide
  have hdescent : baseEnd_3815420 < baseStart_3815420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815435 : List Nat := [1, 1, 1, 1, 6, 1, 2, 1, 1, 7]
def baseStart_3815435 : Nat := 118140960795 + 3815435 * 2 ^ 59
def prefixEnd_3815435 : Nat := 4983230072969 + 3 ^ 40 * 3815435 * 2
def baseEnd_3815435 : Nat := 1306101373991589884477093

theorem tailTrace_3815435 : CollatzResearch.WordTrace tailWord_3815435 prefixEnd_3815435 1306101373991589884477093 := by
  unfold tailWord_3815435
  simp only [CollatzResearch.WordTrace]
  refine ⟨139160346932338094264639759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92773564621558729509759839 139160346932338094264639759)
  ·
    refine ⟨208740520398507141396959639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139160346932338094264639759 208740520398507141396959639)
    ·
      refine ⟨313110780597760712095439459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208740520398507141396959639 313110780597760712095439459)
      ·
        refine ⟨469666170896641068143159189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313110780597760712095439459 469666170896641068143159189)
        ·
          refine ⟨22015601760780050069210587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 469666170896641068143159189 22015601760780050069210587)
          ·
            refine ⟨33023402641170075103815881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22015601760780050069210587 33023402641170075103815881)
            ·
              refine ⟨24767551980877556327861911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33023402641170075103815881 24767551980877556327861911)
              ·
                refine ⟨37151327971316334491792867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24767551980877556327861911 37151327971316334491792867)
                ·
                  refine ⟨55726991956974501737689301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37151327971316334491792867 55726991956974501737689301)
                  ·
                    refine ⟨1306101373991589884477093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55726991956974501737689301 1306101373991589884477093)
                    ·
                      rfl

theorem cell22_3815435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 7].length) (baseStart_3815435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3815435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3815435 prefixEnd_3815435 := by exact prefixLift 3815435
  have htrace : WordTrace (prefixWord ++ tailWord_3815435) baseStart_3815435 baseEnd_3815435 := by
    simpa [prefixWord, tailWord_3815435, baseEnd_3815435] using wordTrace_append hprefix tailTrace_3815435
  have hstable : (prefixWord ++ tailWord_3815435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815435).length < 2 ^ (prefixWord ++ tailWord_3815435).sum := by decide
  have hdescent : baseEnd_3815435 < baseStart_3815435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815497 : List Nat := [1, 2, 1, 1, 2, 2, 6, 1, 1, 5]
def baseStart_3815497 : Nat := 118140960795 + 3815497 * 2 ^ 59
def prefixEnd_3815497 : Nat := 4983230072969 + 3 ^ 40 * 3815497 * 2
def baseEnd_3815497 : Nat := 1306122597858642389426903

theorem tailTrace_3815497 : CollatzResearch.WordTrace tailWord_3815497 prefixEnd_3815497 1306122597858642389426903 := by
  unfold tailWord_3815497
  simp only [CollatzResearch.WordTrace]
  refine ⟨139162608258113478853396745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92775072172075652568931163 139162608258113478853396745)
  ·
    refine ⟨104371956193585109140047559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139162608258113478853396745 104371956193585109140047559)
    ·
      refine ⟨156557934290377663710071339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104371956193585109140047559 156557934290377663710071339)
      ·
        refine ⟨234836901435566495565107009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156557934290377663710071339 234836901435566495565107009)
        ·
          refine ⟨176127676076674871673830257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234836901435566495565107009 176127676076674871673830257)
          ·
            refine ⟨132095757057506153755372693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176127676076674871673830257 132095757057506153755372693)
            ·
              refine ⟨6191988612070600957283095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 132095757057506153755372693 6191988612070600957283095)
              ·
                refine ⟨9287982918105901435924643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6191988612070600957283095 9287982918105901435924643)
                ·
                  refine ⟨13931974377158852153886965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9287982918105901435924643 13931974377158852153886965)
                  ·
                    refine ⟨1306122597858642389426903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13931974377158852153886965 1306122597858642389426903)
                    ·
                      rfl

theorem cell22_3815497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 5].length) (baseStart_3815497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3815497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3815497 prefixEnd_3815497 := by exact prefixLift 3815497
  have htrace : WordTrace (prefixWord ++ tailWord_3815497) baseStart_3815497 baseEnd_3815497 := by
    simpa [prefixWord, tailWord_3815497, baseEnd_3815497] using wordTrace_append hprefix tailTrace_3815497
  have hstable : (prefixWord ++ tailWord_3815497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815497).length < 2 ^ (prefixWord ++ tailWord_3815497).sum := by decide
  have hdescent : baseEnd_3815497 < baseStart_3815497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815512 : List Nat := [2, 1, 2, 2, 1, 5, 1, 1, 1, 6]
def baseStart_3815512 : Nat := 118140960795 + 3815512 * 2 ^ 59
def prefixEnd_3815512 : Nat := 4983230072969 + 3 ^ 40 * 3815512 * 2
def baseEnd_3815512 : Nat := 1306127732665187350301857

theorem tailTrace_3815512 : CollatzResearch.WordTrace tailWord_3815512 prefixEnd_3815512 1306127732665187350301857 := by
  unfold tailWord_3815512
  simp only [CollatzResearch.WordTrace]
  refine ⟨69581577676529568207596395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92775436902039424276795193 69581577676529568207596395)
  ·
    refine ⟨104372366514794352311394593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69581577676529568207596395 104372366514794352311394593)
    ·
      refine ⟨78279274886095764233545945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104372366514794352311394593 78279274886095764233545945)
      ·
        refine ⟨58709456164571823175159459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78279274886095764233545945 58709456164571823175159459)
        ·
          refine ⟨88064184246857734762739189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58709456164571823175159459 88064184246857734762739189)
          ·
            refine ⟨8256017273142912634006799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88064184246857734762739189 8256017273142912634006799)
            ·
              refine ⟨12384025909714368951010199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8256017273142912634006799 12384025909714368951010199)
              ·
                refine ⟨18576038864571553426515299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12384025909714368951010199 18576038864571553426515299)
                ·
                  refine ⟨27864058296857330139772949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18576038864571553426515299 27864058296857330139772949)
                  ·
                    refine ⟨1306127732665187350301857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27864058296857330139772949 1306127732665187350301857)
                    ·
                      rfl

theorem cell22_3815512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_3815512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3815512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3815512 prefixEnd_3815512 := by exact prefixLift 3815512
  have htrace : WordTrace (prefixWord ++ tailWord_3815512) baseStart_3815512 baseEnd_3815512 := by
    simpa [prefixWord, tailWord_3815512, baseEnd_3815512] using wordTrace_append hprefix tailTrace_3815512
  have hstable : (prefixWord ++ tailWord_3815512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815512).length < 2 ^ (prefixWord ++ tailWord_3815512).sum := by decide
  have hdescent : baseEnd_3815512 < baseStart_3815512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815516 : List Nat := [2, 2, 4, 1, 1, 3, 2, 3, 4]
def baseStart_3815516 : Nat := 118140960795 + 3815516 * 2 ^ 59
def prefixEnd_3815516 : Nat := 4983230072969 + 3 ^ 40 * 3815516 * 2
def baseEnd_3815516 : Nat := 435376367315644224400615

theorem tailTrace_3815516 : CollatzResearch.WordTrace tailWord_3815516 prefixEnd_3815516 435376367315644224400615 := by
  unfold tailWord_3815516
  simp only [CollatzResearch.WordTrace]
  refine ⟨69581650622522322549169201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92775534163363096732225601 69581650622522322549169201)
  ·
    refine ⟨52186237966891741911876901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69581650622522322549169201 52186237966891741911876901)
    ·
      refine ⟨9784919618792201608476919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52186237966891741911876901 9784919618792201608476919)
      ·
        refine ⟨14677379428188302412715379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9784919618792201608476919 14677379428188302412715379)
        ·
          refine ⟨22016069142282453619073069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14677379428188302412715379 22016069142282453619073069)
          ·
            refine ⟨8256025928355920107152401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22016069142282453619073069 8256025928355920107152401)
            ·
              refine ⟨6192019446266940080364301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8256025928355920107152401 6192019446266940080364301)
              ·
                refine ⟨2322007292350102530136613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6192019446266940080364301 2322007292350102530136613)
                ·
                  refine ⟨435376367315644224400615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2322007292350102530136613 435376367315644224400615)
                  ·
                    rfl

theorem cell22_3815516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 3, 4].length) (baseStart_3815516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3815516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3815516 prefixEnd_3815516 := by exact prefixLift 3815516
  have htrace : WordTrace (prefixWord ++ tailWord_3815516) baseStart_3815516 baseEnd_3815516 := by
    simpa [prefixWord, tailWord_3815516, baseEnd_3815516] using wordTrace_append hprefix tailTrace_3815516
  have hstable : (prefixWord ++ tailWord_3815516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815516).length < 2 ^ (prefixWord ++ tailWord_3815516).sum := by decide
  have hdescent : baseEnd_3815516 < baseStart_3815516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815559 : List Nat := [1, 1, 4, 2, 1, 1, 4, 2, 3, 3]
def baseStart_3815559 : Nat := 118140960795 + 3815559 * 2 ^ 59
def prefixEnd_3815559 : Nat := 4983230072969 + 3 ^ 40 * 3815559 * 2
def baseEnd_3815559 : Nat := 1306143821725694894376713

theorem tailTrace_3815559 : CollatzResearch.WordTrace tailWord_3815559 prefixEnd_3815559 1306143821725694894376713 := by
  unfold tailWord_3815559
  simp only [CollatzResearch.WordTrace]
  refine ⟨139164869583888863442153731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92776579722592575628102487 139164869583888863442153731)
  ·
    refine ⟨208747304375833295163230597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139164869583888863442153731 208747304375833295163230597)
    ·
      refine ⟨39140119570468742843105737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208747304375833295163230597 39140119570468742843105737)
      ·
        refine ⟨29355089677851557132329303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39140119570468742843105737 29355089677851557132329303)
        ·
          refine ⟨44032634516777335698493955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29355089677851557132329303 44032634516777335698493955)
          ·
            refine ⟨66048951775166003547740933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44032634516777335698493955 66048951775166003547740933)
            ·
              refine ⟨12384178457843625665201425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66048951775166003547740933 12384178457843625665201425)
              ·
                refine ⟨9288133843382719248901069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12384178457843625665201425 9288133843382719248901069)
                ·
                  refine ⟨3483050191268519718337901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9288133843382719248901069 3483050191268519718337901)
                  ·
                    refine ⟨1306143821725694894376713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3483050191268519718337901 1306143821725694894376713)
                    ·
                      rfl

theorem cell22_3815559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_3815559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3815559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3815559 prefixEnd_3815559 := by exact prefixLift 3815559
  have htrace : WordTrace (prefixWord ++ tailWord_3815559) baseStart_3815559 baseEnd_3815559 := by
    simpa [prefixWord, tailWord_3815559, baseEnd_3815559] using wordTrace_append hprefix tailTrace_3815559
  have hstable : (prefixWord ++ tailWord_3815559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815559).length < 2 ^ (prefixWord ++ tailWord_3815559).sum := by decide
  have hdescent : baseEnd_3815559 < baseStart_3815559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815644 : List Nat := [2, 2, 5, 2, 1, 2, 2, 2, 1, 3]
def baseStart_3815644 : Nat := 118140960795 + 3815644 * 2 ^ 59
def prefixEnd_3815644 : Nat := 4983230072969 + 3 ^ 40 * 3815644 * 2
def baseEnd_3815644 : Nat := 1306172918962783006001453

theorem tailTrace_3815644 : CollatzResearch.WordTrace tailWord_3815644 prefixEnd_3815644 1306172918962783006001453 := by
  unfold tailWord_3815644
  simp only [CollatzResearch.WordTrace]
  refine ⟨69583984894290461479498993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92778646525720615305998657 69583984894290461479498993)
  ·
    refine ⟨52187988670717846109624245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69583984894290461479498993 52187988670717846109624245)
    ·
      refine ⟨4892623937879798072777273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52187988670717846109624245 4892623937879798072777273)
      ·
        refine ⟨3669467953409848554582955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4892623937879798072777273 3669467953409848554582955)
        ·
          refine ⟨5504201930114772831874433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3669467953409848554582955 5504201930114772831874433)
          ·
            refine ⟨4128151447586079623905825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5504201930114772831874433 4128151447586079623905825)
            ·
              refine ⟨3096113585689559717929369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4128151447586079623905825 3096113585689559717929369)
              ·
                refine ⟨2322085189267169788447027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3096113585689559717929369 2322085189267169788447027)
                ·
                  refine ⟨3483127783900754682670541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2322085189267169788447027 3483127783900754682670541)
                  ·
                    refine ⟨1306172918962783006001453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3483127783900754682670541 1306172918962783006001453)
                    ·
                      rfl

theorem cell22_3815644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_3815644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3815644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3815644 prefixEnd_3815644 := by exact prefixLift 3815644
  have htrace : WordTrace (prefixWord ++ tailWord_3815644) baseStart_3815644 baseEnd_3815644 := by
    simpa [prefixWord, tailWord_3815644, baseEnd_3815644] using wordTrace_append hprefix tailTrace_3815644
  have hstable : (prefixWord ++ tailWord_3815644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815644).length < 2 ^ (prefixWord ++ tailWord_3815644).sum := by decide
  have hdescent : baseEnd_3815644 < baseStart_3815644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815647 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 3, 6]
def baseStart_3815647 : Nat := 118140960795 + 3815647 * 2 ^ 59
def prefixEnd_3815647 : Nat := 4983230072969 + 3 ^ 40 * 3815647 * 2
def baseEnd_3815647 : Nat := 1306173945924091998176443

theorem tailTrace_3815647 : CollatzResearch.WordTrace tailWord_3815647 prefixEnd_3815647 1306173945924091998176443 := by
  unfold tailWord_3815647
  simp only [CollatzResearch.WordTrace]
  refine ⟨139168079207570054471357195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92778719471713369647571463 139168079207570054471357195)
  ·
    refine ⟨208752118811355081707035793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139168079207570054471357195 208752118811355081707035793)
    ·
      refine ⟨156564089108516311280276845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208752118811355081707035793 156564089108516311280276845)
      ·
        refine ⟨58711533415693616730103817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156564089108516311280276845 58711533415693616730103817)
        ·
          refine ⟨44033650061770212547577863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58711533415693616730103817 44033650061770212547577863)
          ·
            refine ⟨66050475092655318821366795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44033650061770212547577863 66050475092655318821366795)
            ·
              refine ⟨99075712638982978232050193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66050475092655318821366795 99075712638982978232050193)
              ·
                refine ⟨74306784479237233674037645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99075712638982978232050193 74306784479237233674037645)
                ·
                  refine ⟨27865044179713962627764117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74306784479237233674037645 27865044179713962627764117)
                  ·
                    refine ⟨1306173945924091998176443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27865044179713962627764117 1306173945924091998176443)
                    ·
                      rfl

theorem cell22_3815647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 6].length) (baseStart_3815647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3815647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3815647 prefixEnd_3815647 := by exact prefixLift 3815647
  have htrace : WordTrace (prefixWord ++ tailWord_3815647) baseStart_3815647 baseEnd_3815647 := by
    simpa [prefixWord, tailWord_3815647, baseEnd_3815647] using wordTrace_append hprefix tailTrace_3815647
  have hstable : (prefixWord ++ tailWord_3815647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815647).length < 2 ^ (prefixWord ++ tailWord_3815647).sum := by decide
  have hdescent : baseEnd_3815647 < baseStart_3815647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815666 : List Nat := [3, 2, 1, 3, 2, 2, 2, 1, 1, 5]
def baseStart_3815666 : Nat := 118140960795 + 3815666 * 2 ^ 59
def prefixEnd_3815666 : Nat := 4983230072969 + 3 ^ 40 * 3815666 * 2
def baseEnd_3815666 : Nat := 1306180450012382281951385

theorem tailTrace_3815666 : CollatzResearch.WordTrace tailWord_3815666 prefixEnd_3815666 1306180450012382281951385 := by
  unfold tailWord_3815666
  simp only [CollatzResearch.WordTrace]
  refine ⟨34792193048625305179074713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92779181463000813810865901 34792193048625305179074713)
  ·
    refine ⟨26094144786468978884306035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34792193048625305179074713 26094144786468978884306035)
    ·
      refine ⟨39141217179703468326459053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26094144786468978884306035 39141217179703468326459053)
      ·
        refine ⟨14677956442388800622422145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39141217179703468326459053 14677956442388800622422145)
        ·
          refine ⟨11008467331791600466816609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14677956442388800622422145 11008467331791600466816609)
          ·
            refine ⟨8256350498843700350112457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11008467331791600466816609 8256350498843700350112457)
            ·
              refine ⟨6192262874132775262584343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8256350498843700350112457 6192262874132775262584343)
              ·
                refine ⟨9288394311199162893876515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6192262874132775262584343 9288394311199162893876515)
                ·
                  refine ⟨13932591466798744340814773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9288394311199162893876515 13932591466798744340814773)
                  ·
                    refine ⟨1306180450012382281951385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13932591466798744340814773 1306180450012382281951385)
                    ·
                      rfl

theorem cell22_3815666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_3815666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3815666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3815666 prefixEnd_3815666 := by exact prefixLift 3815666
  have htrace : WordTrace (prefixWord ++ tailWord_3815666) baseStart_3815666 baseEnd_3815666 := by
    simpa [prefixWord, tailWord_3815666, baseEnd_3815666] using wordTrace_append hprefix tailTrace_3815666
  have hstable : (prefixWord ++ tailWord_3815666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815666).length < 2 ^ (prefixWord ++ tailWord_3815666).sum := by decide
  have hdescent : baseEnd_3815666 < baseStart_3815666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815679 : List Nat := [1, 1, 2, 2, 1, 4, 5, 6]
def baseStart_3815679 : Nat := 118140960795 + 3815679 * 2 ^ 59
def prefixEnd_3815679 : Nat := 4983230072969 + 3 ^ 40 * 3815679 * 2
def baseEnd_3815679 : Nat := 145131655575339397930705

theorem tailTrace_3815679 : CollatzResearch.WordTrace tailWord_3815679 prefixEnd_3815679 145131655575339397930705 := by
  unfold tailWord_3815679
  simp only [CollatzResearch.WordTrace]
  refine ⟨139169246343454123936522091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92779497562302749291014727 139169246343454123936522091)
  ·
    refine ⟨208753869515181185904783137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139169246343454123936522091 208753869515181185904783137)
    ·
      refine ⟨156565402136385889428587353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208753869515181185904783137 156565402136385889428587353)
      ·
        refine ⟨117424051602289417071440515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156565402136385889428587353 117424051602289417071440515)
        ·
          refine ⟨176136077403434125607160773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117424051602289417071440515 176136077403434125607160773)
          ·
            refine ⟨33025514513143898551342645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176136077403434125607160773 33025514513143898551342645)
            ·
              refine ⟨3096141985607240489188373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33025514513143898551342645 3096141985607240489188373)
              ·
                refine ⟨145131655575339397930705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3096141985607240489188373 145131655575339397930705)
                ·
                  rfl

theorem cell22_3815679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 6].length) (baseStart_3815679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3815679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3815679 prefixEnd_3815679 := by exact prefixLift 3815679
  have htrace : WordTrace (prefixWord ++ tailWord_3815679) baseStart_3815679 baseEnd_3815679 := by
    simpa [prefixWord, tailWord_3815679, baseEnd_3815679] using wordTrace_append hprefix tailTrace_3815679
  have hstable : (prefixWord ++ tailWord_3815679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815679).length < 2 ^ (prefixWord ++ tailWord_3815679).sum := by decide
  have hdescent : baseEnd_3815679 < baseStart_3815679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815687 : List Nat := [1, 1, 4, 5, 2, 1, 2, 1, 1, 4]
def baseStart_3815687 : Nat := 118140960795 + 3815687 * 2 ^ 59
def prefixEnd_3815687 : Nat := 4983230072969 + 3 ^ 40 * 3815687 * 2
def baseEnd_3815687 : Nat := 1306187638741545227176321

theorem tailTrace_3815687 : CollatzResearch.WordTrace tailWord_3815687 prefixEnd_3815687 1306187638741545227176321 := by
  unfold tailWord_3815687
  simp only [CollatzResearch.WordTrace]
  refine ⟨139169538127425141302813315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92779692084950094201875543 139169538127425141302813315)
  ·
    refine ⟨208754307191137711954219973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139169538127425141302813315 208754307191137711954219973)
    ·
      refine ⟨39141432598338320991416245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208754307191137711954219973 39141432598338320991416245)
      ·
        refine ⟨3669509306094217592945273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39141432598338320991416245 3669509306094217592945273)
        ·
          refine ⟨2752131979570663194708955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3669509306094217592945273 2752131979570663194708955)
          ·
            refine ⟨4128197969355994792063433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2752131979570663194708955 4128197969355994792063433)
            ·
              refine ⟨3096148477016996094047575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4128197969355994792063433 3096148477016996094047575)
              ·
                refine ⟨4644222715525494141071363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3096148477016996094047575 4644222715525494141071363)
                ·
                  refine ⟨6966334073288241211607045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4644222715525494141071363 6966334073288241211607045)
                  ·
                    refine ⟨1306187638741545227176321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6966334073288241211607045 1306187638741545227176321)
                    ·
                      rfl

theorem cell22_3815687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 1, 4].length) (baseStart_3815687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3815687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3815687 prefixEnd_3815687 := by exact prefixLift 3815687
  have htrace : WordTrace (prefixWord ++ tailWord_3815687) baseStart_3815687 baseEnd_3815687 := by
    simpa [prefixWord, tailWord_3815687, baseEnd_3815687] using wordTrace_append hprefix tailTrace_3815687
  have hstable : (prefixWord ++ tailWord_3815687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815687).length < 2 ^ (prefixWord ++ tailWord_3815687).sum := by decide
  have hdescent : baseEnd_3815687 < baseStart_3815687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815711 : List Nat := [1, 1, 2, 4, 3, 1, 1, 3, 3, 3]
def baseStart_3815711 : Nat := 118140960795 + 3815711 * 2 ^ 59
def prefixEnd_3815711 : Nat := 4983230072969 + 3 ^ 40 * 3815711 * 2
def baseEnd_3815711 : Nat := 1306195854432017164576247

theorem tailTrace_3815711 : CollatzResearch.WordTrace tailWord_3815711 prefixEnd_3815711 1306195854432017164576247 := by
  unfold tailWord_3815711
  simp only [CollatzResearch.WordTrace]
  refine ⟨139170413479338193401686987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92780275652892128934457991 139170413479338193401686987)
  ·
    refine ⟨208755620219007290102530481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139170413479338193401686987 208755620219007290102530481)
    ·
      refine ⟨156566715164255467576897861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208755620219007290102530481 156566715164255467576897861)
      ·
        refine ⟨29356259093297900170668349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156566715164255467576897861 29356259093297900170668349)
        ·
          refine ⟨11008597159986712564000631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29356259093297900170668349 11008597159986712564000631)
          ·
            refine ⟨16512895739980068846000947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11008597159986712564000631 16512895739980068846000947)
            ·
              refine ⟨24769343609970103269001421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16512895739980068846000947 24769343609970103269001421)
              ·
                refine ⟨9288503853738788725875533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24769343609970103269001421 9288503853738788725875533)
                ·
                  refine ⟨3483188945152045772203325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9288503853738788725875533 3483188945152045772203325)
                  ·
                    refine ⟨1306195854432017164576247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3483188945152045772203325 1306195854432017164576247)
                    ·
                      rfl

theorem cell22_3815711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 3, 3].length) (baseStart_3815711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3815711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3815711 prefixEnd_3815711 := by exact prefixLift 3815711
  have htrace : WordTrace (prefixWord ++ tailWord_3815711) baseStart_3815711 baseEnd_3815711 := by
    simpa [prefixWord, tailWord_3815711, baseEnd_3815711] using wordTrace_append hprefix tailTrace_3815711
  have hstable : (prefixWord ++ tailWord_3815711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815711).length < 2 ^ (prefixWord ++ tailWord_3815711).sum := by decide
  have hdescent : baseEnd_3815711 < baseStart_3815711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815724 : List Nat := [2, 2, 1, 1, 1, 3, 2, 5, 5]
def baseStart_3815724 : Nat := 118140960795 + 3815724 * 2 ^ 59
def prefixEnd_3815724 : Nat := 4983230072969 + 3 ^ 40 * 3815724 * 2
def baseEnd_3815724 : Nat := 435400101532563154667069

theorem tailTrace_3815724 : CollatzResearch.WordTrace tailWord_3815724 prefixEnd_3815724 435400101532563154667069 := by
  unfold tailWord_3815724
  simp only [CollatzResearch.WordTrace]
  refine ⟨69585443814145548310955113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92780591752194064414606817 69585443814145548310955113)
  ·
    refine ⟨52189082860609161233216335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69585443814145548310955113 52189082860609161233216335)
    ·
      refine ⟨78283624290913741849824503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52189082860609161233216335 78283624290913741849824503)
      ·
        refine ⟨117425436436370612774736755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78283624290913741849824503 117425436436370612774736755)
        ·
          refine ⟨176138154654555919162105133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117425436436370612774736755 176138154654555919162105133)
          ·
            refine ⟨66051807995458469685789425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176138154654555919162105133 66051807995458469685789425)
            ·
              refine ⟨49538855996593852264342069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66051807995458469685789425 49538855996593852264342069)
              ·
                refine ⟨4644267749680673649782069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49538855996593852264342069 4644267749680673649782069)
                ·
                  refine ⟨435400101532563154667069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4644267749680673649782069 435400101532563154667069)
                  ·
                    rfl

theorem cell22_3815724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 5].length) (baseStart_3815724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3815724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3815724 prefixEnd_3815724 := by exact prefixLift 3815724
  have htrace : WordTrace (prefixWord ++ tailWord_3815724) baseStart_3815724 baseEnd_3815724 := by
    simpa [prefixWord, tailWord_3815724, baseEnd_3815724] using wordTrace_append hprefix tailTrace_3815724
  have hstable : (prefixWord ++ tailWord_3815724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815724).length < 2 ^ (prefixWord ++ tailWord_3815724).sum := by decide
  have hdescent : baseEnd_3815724 < baseStart_3815724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815754 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 7, 4]
def baseStart_3815754 : Nat := 118140960795 + 3815754 * 2 ^ 59
def prefixEnd_3815754 : Nat := 4983230072969 + 3 ^ 40 * 3815754 * 2
def baseEnd_3815754 : Nat := 1306210574210779385751115

theorem tailTrace_3815754 : CollatzResearch.WordTrace tailWord_3815754 prefixEnd_3815754 1306210574210779385751115 := by
  unfold tailWord_3815754
  simp only [CollatzResearch.WordTrace]
  refine ⟨34792995454545602936375579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92781321212121607830334877 34792995454545602936375579)
  ·
    refine ⟨52189493181818404404563369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34792995454545602936375579 52189493181818404404563369)
    ·
      refine ⟨39142119886363803303422527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52189493181818404404563369 39142119886363803303422527)
      ·
        refine ⟨58713179829545704955133791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39142119886363803303422527 58713179829545704955133791)
        ·
          refine ⟨88069769744318557432700687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58713179829545704955133791 88069769744318557432700687)
          ·
            refine ⟨132104654616477836149051031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88069769744318557432700687 132104654616477836149051031)
            ·
              refine ⟨198156981924716754223576547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132104654616477836149051031 198156981924716754223576547)
              ·
                refine ⟨297235472887075131335364821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198156981924716754223576547 297235472887075131335364821)
                ·
                  refine ⟨6966456395790823390672613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 297235472887075131335364821 6966456395790823390672613)
                  ·
                    refine ⟨1306210574210779385751115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6966456395790823390672613 1306210574210779385751115)
                    ·
                      rfl

theorem cell22_3815754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_3815754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3815754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3815754 prefixEnd_3815754 := by exact prefixLift 3815754
  have htrace : WordTrace (prefixWord ++ tailWord_3815754) baseStart_3815754 baseEnd_3815754 := by
    simpa [prefixWord, tailWord_3815754, baseEnd_3815754] using wordTrace_append hprefix tailTrace_3815754
  have hstable : (prefixWord ++ tailWord_3815754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815754).length < 2 ^ (prefixWord ++ tailWord_3815754).sum := by decide
  have hdescent : baseEnd_3815754 < baseStart_3815754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815816 : List Nat := [2, 1, 3, 3, 1, 1, 1, 4, 2, 4]
def baseStart_3815816 : Nat := 118140960795 + 3815816 * 2 ^ 59
def prefixEnd_3815816 : Nat := 4983230072969 + 3 ^ 40 * 3815816 * 2
def baseEnd_3815816 : Nat := 1306231798077831890700925

theorem tailTrace_3815816 : CollatzResearch.WordTrace tailWord_3815816 prefixEnd_3815816 1306231798077831890700925 := by
  unfold tailWord_3815816
  simp only [CollatzResearch.WordTrace]
  refine ⟨69587121571978898167129651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92782828762638530889506201 69587121571978898167129651)
  ·
    refine ⟨104380682357968347250694477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69587121571978898167129651 104380682357968347250694477)
    ·
      refine ⟨39142755884238130219010429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104380682357968347250694477 39142755884238130219010429)
      ·
        refine ⟨14678533456589298832128911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39142755884238130219010429 14678533456589298832128911)
        ·
          refine ⟨22017800184883948248193367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14678533456589298832128911 22017800184883948248193367)
          ·
            refine ⟨33026700277325922372290051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22017800184883948248193367 33026700277325922372290051)
            ·
              refine ⟨49540050415988883558435077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33026700277325922372290051 49540050415988883558435077)
              ·
                refine ⟨9288759452997915667206577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49540050415988883558435077 9288759452997915667206577)
                ·
                  refine ⟨6966569589748436750404933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9288759452997915667206577 6966569589748436750404933)
                  ·
                    refine ⟨1306231798077831890700925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6966569589748436750404933 1306231798077831890700925)
                    ·
                      rfl

theorem cell22_3815816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_3815816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3815816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3815816 prefixEnd_3815816 := by exact prefixLift 3815816
  have htrace : WordTrace (prefixWord ++ tailWord_3815816) baseStart_3815816 baseEnd_3815816 := by
    simpa [prefixWord, tailWord_3815816, baseEnd_3815816] using wordTrace_append hprefix tailTrace_3815816
  have hstable : (prefixWord ++ tailWord_3815816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815816).length < 2 ^ (prefixWord ++ tailWord_3815816).sum := by decide
  have hdescent : baseEnd_3815816 < baseStart_3815816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815820 : List Nat := [2, 2, 1, 2, 1, 6, 2, 2, 4]
def baseStart_3815820 : Nat := 118140960795 + 3815820 * 2 ^ 59
def prefixEnd_3815820 : Nat := 4983230072969 + 3 ^ 40 * 3815820 * 2
def baseEnd_3815820 : Nat := 435411055786525737866971

theorem tailTrace_3815820 : CollatzResearch.WordTrace tailWord_3815820 prefixEnd_3815820 435411055786525737866971 := by
  unfold tailWord_3815820
  simp only [CollatzResearch.WordTrace]
  refine ⟨69587194517971652508702457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92782926023962203344936609 69587194517971652508702457)
  ·
    refine ⟨52190395888478739381526843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69587194517971652508702457 52190395888478739381526843)
    ·
      refine ⟨78285593832718109072290265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52190395888478739381526843 78285593832718109072290265)
      ·
        refine ⟨58714195374538581804217699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78285593832718109072290265 58714195374538581804217699)
        ·
          refine ⟨88071293061807872706326549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58714195374538581804217699 88071293061807872706326549)
          ·
            refine ⟨4128341862272244033109057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 88071293061807872706326549 4128341862272244033109057)
            ·
              refine ⟨3096256396704183024831793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4128341862272244033109057 3096256396704183024831793)
              ·
                refine ⟨2322192297528137268623845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3096256396704183024831793 2322192297528137268623845)
                ·
                  refine ⟨435411055786525737866971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2322192297528137268623845 435411055786525737866971)
                  ·
                    rfl

theorem cell22_3815820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 2, 4].length) (baseStart_3815820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3815820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3815820 prefixEnd_3815820 := by exact prefixLift 3815820
  have htrace : WordTrace (prefixWord ++ tailWord_3815820) baseStart_3815820 baseEnd_3815820 := by
    simpa [prefixWord, tailWord_3815820, baseEnd_3815820] using wordTrace_append hprefix tailTrace_3815820
  have hstable : (prefixWord ++ tailWord_3815820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815820).length < 2 ^ (prefixWord ++ tailWord_3815820).sum := by decide
  have hdescent : baseEnd_3815820 < baseStart_3815820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815829 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 2, 7]
def baseStart_3815829 : Nat := 118140960795 + 3815829 * 2 ^ 59
def prefixEnd_3815829 : Nat := 4983230072969 + 3 ^ 40 * 3815829 * 2
def baseEnd_3815829 : Nat := 1306236248243504190125885

theorem tailTrace_3815829 : CollatzResearch.WordTrace tailWord_3815829 prefixEnd_3815829 1306236248243504190125885 := by
  unfold tailWord_3815829
  simp only [CollatzResearch.WordTrace]
  refine ⟨139174717292910699554482541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92783144861940466369655027 139174717292910699554482541)
  ·
    refine ⟨52190518984841512332930953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139174717292910699554482541 52190518984841512332930953)
    ·
      refine ⟨39142889238631134249698215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52190518984841512332930953 39142889238631134249698215)
      ·
        refine ⟨58714333857946701374547323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39142889238631134249698215 58714333857946701374547323)
        ·
          refine ⟨88071500786920052061820985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58714333857946701374547323 88071500786920052061820985)
          ·
            refine ⟨66053625590190039046365739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88071500786920052061820985 66053625590190039046365739)
            ·
              refine ⟨99080438385285058569548609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66053625590190039046365739 99080438385285058569548609)
              ·
                refine ⟨74310328788963793927161457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99080438385285058569548609 74310328788963793927161457)
                ·
                  refine ⟨55732746591722845445371093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74310328788963793927161457 55732746591722845445371093)
                  ·
                    refine ⟨1306236248243504190125885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55732746591722845445371093 1306236248243504190125885)
                    ·
                      rfl

theorem cell22_3815829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_3815829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3815829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3815829 prefixEnd_3815829 := by exact prefixLift 3815829
  have htrace : WordTrace (prefixWord ++ tailWord_3815829) baseStart_3815829 baseEnd_3815829 := by
    simpa [prefixWord, tailWord_3815829, baseEnd_3815829] using wordTrace_append hprefix tailTrace_3815829
  have hstable : (prefixWord ++ tailWord_3815829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815829).length < 2 ^ (prefixWord ++ tailWord_3815829).sum := by decide
  have hdescent : baseEnd_3815829 < baseStart_3815829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3815880 : List Nat := [2, 1, 3, 1, 3, 2, 2, 4, 1, 3]
def baseStart_3815880 : Nat := 118140960795 + 3815880 * 2 ^ 59
def prefixEnd_3815880 : Nat := 4983230072969 + 3 ^ 40 * 3815880 * 2
def baseEnd_3815880 : Nat := 1306253706585757057100729

theorem tailTrace_3815880 : CollatzResearch.WordTrace tailWord_3815880 prefixEnd_3815880 1306253706585757057100729 := by
  unfold tailWord_3815880
  simp only [CollatzResearch.WordTrace]
  refine ⟨69588288707862967632294547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92784384943817290176392729 69588288707862967632294547)
  ·
    refine ⟨104382433061794451448441821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69588288707862967632294547 104382433061794451448441821)
    ·
      refine ⟨39143412398172919293165683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104382433061794451448441821 39143412398172919293165683)
      ·
        refine ⟨58715118597259378939748525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39143412398172919293165683 58715118597259378939748525)
        ·
          refine ⟨22018169473972267102405697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58715118597259378939748525 22018169473972267102405697)
          ·
            refine ⟨16513627105479200326804273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22018169473972267102405697 16513627105479200326804273)
            ·
              refine ⟨12385220329109400245103205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16513627105479200326804273 12385220329109400245103205)
              ·
                refine ⟨2322228811708012545956851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12385220329109400245103205 2322228811708012545956851)
                ·
                  refine ⟨3483343217562018818935277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2322228811708012545956851 3483343217562018818935277)
                  ·
                    refine ⟨1306253706585757057100729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3483343217562018818935277 1306253706585757057100729)
                    ·
                      rfl

theorem cell22_3815880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 4, 1, 3].length) (baseStart_3815880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3815880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3815880 prefixEnd_3815880 := by exact prefixLift 3815880
  have htrace : WordTrace (prefixWord ++ tailWord_3815880) baseStart_3815880 baseEnd_3815880 := by
    simpa [prefixWord, tailWord_3815880, baseEnd_3815880] using wordTrace_append hprefix tailTrace_3815880
  have hstable : (prefixWord ++ tailWord_3815880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3815880).length < 2 ^ (prefixWord ++ tailWord_3815880).sum := by decide
  have hdescent : baseEnd_3815880 < baseStart_3815880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3815880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816004 : List Nat := [2, 3, 5, 1, 1, 1, 2, 1, 1, 5]
def baseStart_3816004 : Nat := 118140960795 + 3816004 * 2 ^ 59
def prefixEnd_3816004 : Nat := 4983230072969 + 3 ^ 40 * 3816004 * 2
def baseEnd_3816004 : Nat := 1306296154319862067000349

theorem tailTrace_3816004 : CollatzResearch.WordTrace tailWord_3816004 prefixEnd_3816004 1306296154319862067000349 := by
  unfold tailWord_3816004
  simp only [CollatzResearch.WordTrace]
  refine ⟨69590550033638352221051533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92787400044851136294735377 69590550033638352221051533)
  ·
    refine ⟨26096456262614382082894325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69590550033638352221051533 26096456262614382082894325)
    ·
      refine ⟨2446542774620098320271343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26096456262614382082894325 2446542774620098320271343)
      ·
        refine ⟨3669814161930147480407015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2446542774620098320271343 3669814161930147480407015)
        ·
          refine ⟨5504721242895221220610523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3669814161930147480407015 5504721242895221220610523)
          ·
            refine ⟨8257081864342831830915785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5504721242895221220610523 8257081864342831830915785)
            ·
              refine ⟨6192811398257123873186839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8257081864342831830915785 6192811398257123873186839)
              ·
                refine ⟨9289217097385685809780259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6192811398257123873186839 9289217097385685809780259)
                ·
                  refine ⟨13933825646078528714670389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9289217097385685809780259 13933825646078528714670389)
                  ·
                    refine ⟨1306296154319862067000349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13933825646078528714670389 1306296154319862067000349)
                    ·
                      rfl

theorem cell22_3816004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_3816004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3816004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3816004 prefixEnd_3816004 := by exact prefixLift 3816004
  have htrace : WordTrace (prefixWord ++ tailWord_3816004) baseStart_3816004 baseEnd_3816004 := by
    simpa [prefixWord, tailWord_3816004, baseEnd_3816004] using wordTrace_append hprefix tailTrace_3816004
  have hstable : (prefixWord ++ tailWord_3816004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816004).length < 2 ^ (prefixWord ++ tailWord_3816004).sum := by decide
  have hdescent : baseEnd_3816004 < baseStart_3816004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816045 : List Nat := [1, 5, 1, 1, 3, 1, 3, 2, 5]
def baseStart_3816045 : Nat := 118140960795 + 3816045 * 2 ^ 59
def prefixEnd_3816045 : Nat := 4983230072969 + 3 ^ 40 * 3816045 * 2
def baseEnd_3816045 : Nat := 435436729819250542241741

theorem tailTrace_3816045 : CollatzResearch.WordTrace tailWord_3816045 prefixEnd_3816045 435436729819250542241741 := by
  unfold tailWord_3816045
  simp only [CollatzResearch.WordTrace]
  refine ⟨139182595460128168444345589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92788396973418778962897059 139182595460128168444345589)
  ·
    refine ⟨13048368324387015791657399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139182595460128168444345589 13048368324387015791657399)
    ·
      refine ⟨19572552486580523687486099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13048368324387015791657399 19572552486580523687486099)
      ·
        refine ⟨29358828729870785531229149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19572552486580523687486099 29358828729870785531229149)
        ·
          refine ⟨11009560773701544574210931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29358828729870785531229149 11009560773701544574210931)
          ·
            refine ⟨16514341160552316861316397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11009560773701544574210931 16514341160552316861316397)
            ·
              refine ⟨6192877935207118822993649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16514341160552316861316397 6192877935207118822993649)
              ·
                refine ⟨4644658451405339117245237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6192877935207118822993649 4644658451405339117245237)
                ·
                  refine ⟨435436729819250542241741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4644658451405339117245237 435436729819250542241741)
                  ·
                    rfl

theorem cell22_3816045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_3816045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3816045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3816045 prefixEnd_3816045 := by exact prefixLift 3816045
  have htrace : WordTrace (prefixWord ++ tailWord_3816045) baseStart_3816045 baseEnd_3816045 := by
    simpa [prefixWord, tailWord_3816045, baseEnd_3816045] using wordTrace_append hprefix tailTrace_3816045
  have hstable : (prefixWord ++ tailWord_3816045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816045).length < 2 ^ (prefixWord ++ tailWord_3816045).sum := by decide
  have hdescent : baseEnd_3816045 < baseStart_3816045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816056 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 10]
def baseStart_3816056 : Nat := 118140960795 + 3816056 * 2 ^ 59
def prefixEnd_3816056 : Nat := 4983230072969 + 3 ^ 40 * 3816056 * 2
def baseEnd_3816056 : Nat := 435437984994183754900063

theorem tailTrace_3816056 : CollatzResearch.WordTrace tailWord_3816056 prefixEnd_3816056 435437984994183754900063 := by
  unfold tailWord_3816056
  simp only [CollatzResearch.WordTrace]
  refine ⟨69591498331544158661498011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92788664442058878215330681 69591498331544158661498011)
  ·
    refine ⟨104387247497316237992247017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69591498331544158661498011 104387247497316237992247017)
    ·
      refine ⟨78290435622987178494185263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104387247497316237992247017 78290435622987178494185263)
      ·
        refine ⟨117435653434480767741277895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78290435622987178494185263 117435653434480767741277895)
        ·
          refine ⟨176153480151721151611916843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117435653434480767741277895 176153480151721151611916843)
          ·
            refine ⟨264230220227581727417875265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176153480151721151611916843 264230220227581727417875265)
            ·
              refine ⟨198172665170686295563406449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264230220227581727417875265 198172665170686295563406449)
              ·
                refine ⟨148629498878014721672554837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198172665170686295563406449 148629498878014721672554837)
                ·
                  refine ⟨435437984994183754900063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 148629498878014721672554837 435437984994183754900063)
                  ·
                    rfl

theorem cell22_3816056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 10].length) (baseStart_3816056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3816056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3816056 prefixEnd_3816056 := by exact prefixLift 3816056
  have htrace : WordTrace (prefixWord ++ tailWord_3816056) baseStart_3816056 baseEnd_3816056 := by
    simpa [prefixWord, tailWord_3816056, baseEnd_3816056] using wordTrace_append hprefix tailTrace_3816056
  have hstable : (prefixWord ++ tailWord_3816056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816056).length < 2 ^ (prefixWord ++ tailWord_3816056).sum := by decide
  have hdescent : baseEnd_3816056 < baseStart_3816056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816088 : List Nat := [2, 1, 2, 4, 1, 1, 2, 1, 3, 5]
def baseStart_3816088 : Nat := 118140960795 + 3816088 * 2 ^ 59
def prefixEnd_3816088 : Nat := 4983230072969 + 3 ^ 40 * 3816088 * 2
def baseEnd_3816088 : Nat := 1306324909236513847900091

theorem tailTrace_3816088 : CollatzResearch.WordTrace tailWord_3816088 prefixEnd_3816088 1306324909236513847900091 := by
  unfold tailWord_3816088
  simp only [CollatzResearch.WordTrace]
  refine ⟨69592081899486193394080459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92789442532648257858773945 69592081899486193394080459)
  ·
    refine ⟨104388122849229290091120689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69592081899486193394080459 104388122849229290091120689)
    ·
      refine ⟨78291092136921967568340517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104388122849229290091120689 78291092136921967568340517)
      ·
        refine ⟨14679579775672868919063847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78291092136921967568340517 14679579775672868919063847)
        ·
          refine ⟨22019369663509303378595771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14679579775672868919063847 22019369663509303378595771)
          ·
            refine ⟨33029054495263955067893657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22019369663509303378595771 33029054495263955067893657)
            ·
              refine ⟨24771790871447966300920243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33029054495263955067893657 24771790871447966300920243)
              ·
                refine ⟨37157686307171949451380365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24771790871447966300920243 37157686307171949451380365)
                ·
                  refine ⟨13934132365189481044267637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37157686307171949451380365 13934132365189481044267637)
                  ·
                    refine ⟨1306324909236513847900091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13934132365189481044267637 1306324909236513847900091)
                    ·
                      rfl

theorem cell22_3816088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_3816088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3816088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3816088 prefixEnd_3816088 := by exact prefixLift 3816088
  have htrace : WordTrace (prefixWord ++ tailWord_3816088) baseStart_3816088 baseEnd_3816088 := by
    simpa [prefixWord, tailWord_3816088, baseEnd_3816088] using wordTrace_append hprefix tailTrace_3816088
  have hstable : (prefixWord ++ tailWord_3816088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816088).length < 2 ^ (prefixWord ++ tailWord_3816088).sum := by decide
  have hdescent : baseEnd_3816088 < baseStart_3816088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816225 : List Nat := [1, 2, 3, 2, 1, 2, 4, 1, 6]
def baseStart_3816225 : Nat := 118140960795 + 3816225 * 2 ^ 59
def prefixEnd_3816225 : Nat := 4983230072969 + 3 ^ 40 * 3816225 * 2
def baseEnd_3816225 : Nat := 435457269045430385741557

theorem tailTrace_3816225 : CollatzResearch.WordTrace tailWord_3816225 prefixEnd_3816225 435457269045430385741557 := by
  unfold tailWord_3816225
  simp only [CollatzResearch.WordTrace]
  refine ⟨139189160599476059185898129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92792773732984039457265419 139189160599476059185898129)
  ·
    refine ⟨104391870449607044389423597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139189160599476059185898129 104391870449607044389423597)
    ·
      refine ⟨39146951418602641646033849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104391870449607044389423597 39146951418602641646033849)
      ·
        refine ⟨29360213563951981234525387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39146951418602641646033849 29360213563951981234525387)
        ·
          refine ⟨44040320345927971851788081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29360213563951981234525387 44040320345927971851788081)
          ·
            refine ⟨33030240259445978888841061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44040320345927971851788081 33030240259445978888841061)
            ·
              refine ⟨6193170048646121041657699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33030240259445978888841061 6193170048646121041657699)
              ·
                refine ⟨9289755072969181562486549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6193170048646121041657699 9289755072969181562486549)
                ·
                  refine ⟨435457269045430385741557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9289755072969181562486549 435457269045430385741557)
                  ·
                    rfl

theorem cell22_3816225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 6].length) (baseStart_3816225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3816225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3816225 prefixEnd_3816225 := by exact prefixLift 3816225
  have htrace : WordTrace (prefixWord ++ tailWord_3816225) baseStart_3816225 baseEnd_3816225 := by
    simpa [prefixWord, tailWord_3816225, baseEnd_3816225] using wordTrace_append hprefix tailTrace_3816225
  have hstable : (prefixWord ++ tailWord_3816225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816225).length < 2 ^ (prefixWord ++ tailWord_3816225).sum := by decide
  have hdescent : baseEnd_3816225 < baseStart_3816225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816255 : List Nat := [1, 1, 2, 2, 5, 1, 2, 1, 1, 6]
def baseStart_3816255 : Nat := 118140960795 + 3816255 * 2 ^ 59
def prefixEnd_3816255 : Nat := 4983230072969 + 3 ^ 40 * 3816255 * 2
def baseEnd_3816255 : Nat := 1306382076749381078974579

theorem tailTrace_3816255 : CollatzResearch.WordTrace tailWord_3816255 prefixEnd_3816255 1306382076749381078974579 := by
  unfold tailWord_3816255
  simp only [CollatzResearch.WordTrace]
  refine ⟨139190254789367374309490219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92793503192911582872993479 139190254789367374309490219)
  ·
    refine ⟨208785382184051061464235329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139190254789367374309490219 208785382184051061464235329)
    ·
      refine ⟨156589036638038296098176497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208785382184051061464235329 156589036638038296098176497)
      ·
        refine ⟨117441777478528722073632373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156589036638038296098176497 117441777478528722073632373)
        ·
          refine ⟨11010166638612067694403035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117441777478528722073632373 11010166638612067694403035)
          ·
            refine ⟨16515249957918101541604553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11010166638612067694403035 16515249957918101541604553)
            ·
              refine ⟨12386437468438576156203415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16515249957918101541604553 12386437468438576156203415)
              ·
                refine ⟨18579656202657864234305123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12386437468438576156203415 18579656202657864234305123)
                ·
                  refine ⟨27869484303986796351457685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18579656202657864234305123 27869484303986796351457685)
                  ·
                    refine ⟨1306382076749381078974579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27869484303986796351457685 1306382076749381078974579)
                    ·
                      rfl

theorem cell22_3816255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 6].length) (baseStart_3816255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3816255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3816255 prefixEnd_3816255 := by exact prefixLift 3816255
  have htrace : WordTrace (prefixWord ++ tailWord_3816255) baseStart_3816255 baseEnd_3816255 := by
    simpa [prefixWord, tailWord_3816255, baseEnd_3816255] using wordTrace_append hprefix tailTrace_3816255
  have hstable : (prefixWord ++ tailWord_3816255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816255).length < 2 ^ (prefixWord ++ tailWord_3816255).sum := by decide
  have hdescent : baseEnd_3816255 < baseStart_3816255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816276 : List Nat := [2, 4, 1, 1, 4, 1, 3, 2, 4]
def baseStart_3816276 : Nat := 118140960795 + 3816276 * 2 ^ 59
def prefixEnd_3816276 : Nat := 4983230072969 + 3 ^ 40 * 3816276 * 2
def baseEnd_3816276 : Nat := 435463088492848008066505

theorem tailTrace_3816276 : CollatzResearch.WordTrace tailWord_3816276 prefixEnd_3816276 435463088492848008066505 := by
  unfold tailWord_3816276
  simp only [CollatzResearch.WordTrace]
  refine ⟨69595510361145647448002341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92794013814860863264003121 69595510361145647448002341)
  ·
    refine ⟨13049158192714808896500439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69595510361145647448002341 13049158192714808896500439)
    ·
      refine ⟨19573737289072213344750659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13049158192714808896500439 19573737289072213344750659)
      ·
        refine ⟨29360605933608320017125989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19573737289072213344750659 29360605933608320017125989)
        ·
          refine ⟨5505113612551560003211123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29360605933608320017125989 5505113612551560003211123)
          ·
            refine ⟨8257670418827340004816685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5505113612551560003211123 8257670418827340004816685)
            ·
              refine ⟨3096626407060252501806257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8257670418827340004816685 3096626407060252501806257)
              ·
                refine ⟨2322469805295189376354693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3096626407060252501806257 2322469805295189376354693)
                ·
                  refine ⟨435463088492848008066505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2322469805295189376354693 435463088492848008066505)
                  ·
                    rfl

theorem cell22_3816276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_3816276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3816276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3816276 prefixEnd_3816276 := by exact prefixLift 3816276
  have htrace : WordTrace (prefixWord ++ tailWord_3816276) baseStart_3816276 baseEnd_3816276 := by
    simpa [prefixWord, tailWord_3816276, baseEnd_3816276] using wordTrace_append hprefix tailTrace_3816276
  have hstable : (prefixWord ++ tailWord_3816276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816276).length < 2 ^ (prefixWord ++ tailWord_3816276).sum := by decide
  have hdescent : baseEnd_3816276 < baseStart_3816276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816291 : List Nat := [1, 1, 1, 5, 3, 3, 2, 1, 2, 3]
def baseStart_3816291 : Nat := 118140960795 + 3816291 * 2 ^ 59
def prefixEnd_3816291 : Nat := 4983230072969 + 3 ^ 40 * 3816291 * 2
def baseEnd_3816291 : Nat := 1306394400285088985074469

theorem tailTrace_3816291 : CollatzResearch.WordTrace tailWord_3816291 prefixEnd_3816291 1306394400285088985074469 := by
  unfold tailWord_3816291
  simp only [CollatzResearch.WordTrace]
  refine ⟨139191567817236952457800727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92794378544824634971867151 139191567817236952457800727)
  ·
    refine ⟨208787351725855428686701091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139191567817236952457800727 208787351725855428686701091)
    ·
      refine ⟨313181027588783143030051637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208787351725855428686701091 313181027588783143030051637)
      ·
        refine ⟨29360721336448419659067341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 313181027588783143030051637 29360721336448419659067341)
        ·
          refine ⟨11010270501168157372150253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29360721336448419659067341 11010270501168157372150253)
          ·
            refine ⟨4128851437938059014556345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11010270501168157372150253 4128851437938059014556345)
            ·
              refine ⟨3096638578453544260917259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4128851437938059014556345 3096638578453544260917259)
              ·
                refine ⟨4644957867680316391375889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3096638578453544260917259 4644957867680316391375889)
                ·
                  refine ⟨3483718400760237293531917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4644957867680316391375889 3483718400760237293531917)
                  ·
                    refine ⟨1306394400285088985074469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3483718400760237293531917 1306394400285088985074469)
                    ·
                      rfl

theorem cell22_3816291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 2, 3].length) (baseStart_3816291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3816291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3816291 prefixEnd_3816291 := by exact prefixLift 3816291
  have htrace : WordTrace (prefixWord ++ tailWord_3816291) baseStart_3816291 baseEnd_3816291 := by
    simpa [prefixWord, tailWord_3816291, baseEnd_3816291] using wordTrace_append hprefix tailTrace_3816291
  have hstable : (prefixWord ++ tailWord_3816291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816291).length < 2 ^ (prefixWord ++ tailWord_3816291).sum := by decide
  have hdescent : baseEnd_3816291 < baseStart_3816291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816409 : List Nat := [1, 2, 1, 2, 5, 3, 1, 1, 1, 5]
def baseStart_3816409 : Nat := 118140960795 + 3816409 * 2 ^ 59
def prefixEnd_3816409 : Nat := 4983230072969 + 3 ^ 40 * 3816409 * 2
def baseEnd_3816409 : Nat := 1306434794096576010624107

theorem tailTrace_3816409 : CollatzResearch.WordTrace tailWord_3816409 prefixEnd_3816409 1306434794096576010624107 := by
  unfold tailWord_3816409
  simp only [CollatzResearch.WordTrace]
  refine ⟨139195871630809458610596281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92797247753872972407064187 139195871630809458610596281)
  ·
    refine ⟨104396903723107093957947211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139195871630809458610596281 104396903723107093957947211)
    ·
      refine ⟨156595355584660640936920817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104396903723107093957947211 156595355584660640936920817)
      ·
        refine ⟨117446516688495480702690613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156595355584660640936920817 117446516688495480702690613)
        ·
          refine ⟨11010610939546451315877245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117446516688495480702690613 11010610939546451315877245)
          ·
            refine ⟨4128979102329919243453967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11010610939546451315877245 4128979102329919243453967)
            ·
              refine ⟨6193468653494878865180951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4128979102329919243453967 6193468653494878865180951)
              ·
                refine ⟨9290202980242318297771427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6193468653494878865180951 9290202980242318297771427)
                ·
                  refine ⟨13935304470363477446657141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9290202980242318297771427 13935304470363477446657141)
                  ·
                    refine ⟨1306434794096576010624107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13935304470363477446657141 1306434794096576010624107)
                    ·
                      rfl

theorem cell22_3816409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 5].length) (baseStart_3816409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3816409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3816409 prefixEnd_3816409 := by exact prefixLift 3816409
  have htrace : WordTrace (prefixWord ++ tailWord_3816409) baseStart_3816409 baseEnd_3816409 := by
    simpa [prefixWord, tailWord_3816409, baseEnd_3816409] using wordTrace_append hprefix tailTrace_3816409
  have hstable : (prefixWord ++ tailWord_3816409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816409).length < 2 ^ (prefixWord ++ tailWord_3816409).sum := by decide
  have hdescent : baseEnd_3816409 < baseStart_3816409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816435 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 3, 8]
def baseStart_3816435 : Nat := 118140960795 + 3816435 * 2 ^ 59
def prefixEnd_3816435 : Nat := 4983230072969 + 3 ^ 40 * 3816435 * 2
def baseEnd_3816435 : Nat := 1306443694427920609474027

theorem tailTrace_3816435 : CollatzResearch.WordTrace tailWord_3816435 prefixEnd_3816435 1306443694427920609474027 := by
  unfold tailWord_3816435
  simp only [CollatzResearch.WordTrace]
  refine ⟨139196819928715265051042759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92797879952476843367361839 139196819928715265051042759)
  ·
    refine ⟨208795229893072897576564139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139196819928715265051042759 208795229893072897576564139)
    ·
      refine ⟨313192844839609346364846209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208795229893072897576564139 313192844839609346364846209)
      ·
        refine ⟨234894633629707009773634657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313192844839609346364846209 234894633629707009773634657)
        ·
          refine ⟨176170975222280257330225993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234894633629707009773634657 176170975222280257330225993)
          ·
            refine ⟨132128231416710192997669495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176170975222280257330225993 132128231416710192997669495)
            ·
              refine ⟨198192347125065289496504243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132128231416710192997669495 198192347125065289496504243)
              ·
                refine ⟨297288520687597934244756365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198192347125065289496504243 297288520687597934244756365)
                ·
                  refine ⟨111483195257849225341783637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 297288520687597934244756365 111483195257849225341783637)
                  ·
                    refine ⟨1306443694427920609474027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111483195257849225341783637 1306443694427920609474027)
                    ·
                      rfl

theorem cell22_3816435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 8].length) (baseStart_3816435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3816435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3816435 prefixEnd_3816435 := by exact prefixLift 3816435
  have htrace : WordTrace (prefixWord ++ tailWord_3816435) baseStart_3816435 baseEnd_3816435 := by
    simpa [prefixWord, tailWord_3816435, baseEnd_3816435] using wordTrace_append hprefix tailTrace_3816435
  have hstable : (prefixWord ++ tailWord_3816435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816435).length < 2 ^ (prefixWord ++ tailWord_3816435).sum := by decide
  have hdescent : baseEnd_3816435 < baseStart_3816435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816505 : List Nat := [1, 2, 1, 5, 2, 3, 2, 2, 1, 3]
def baseStart_3816505 : Nat := 118140960795 + 3816505 * 2 ^ 59
def prefixEnd_3816505 : Nat := 4983230072969 + 3 ^ 40 * 3816505 * 2
def baseEnd_3816505 : Nat := 1306467656858463760223813

theorem tailTrace_3816505 : CollatzResearch.WordTrace tailWord_3816505 prefixEnd_3816505 1306467656858463760223813 := by
  unfold tailWord_3816505
  simp only [CollatzResearch.WordTrace]
  refine ⟨139199373038461667006090969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92799582025641111337393979 139199373038461667006090969)
  ·
    refine ⟨104399529778846250254568227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139199373038461667006090969 104399529778846250254568227)
    ·
      refine ⟨156599294668269375381852341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104399529778846250254568227 156599294668269375381852341)
      ·
        refine ⟨14681183875150253942048657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156599294668269375381852341 14681183875150253942048657)
        ·
          refine ⟨11010887906362690456536493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14681183875150253942048657 11010887906362690456536493)
          ·
            refine ⟨4129082964886008921201185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11010887906362690456536493 4129082964886008921201185)
            ·
              refine ⟨3096812223664506690900889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4129082964886008921201185 3096812223664506690900889)
              ·
                refine ⟨2322609167748380018175667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3096812223664506690900889 2322609167748380018175667)
                ·
                  refine ⟨3483913751622570027263501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2322609167748380018175667 3483913751622570027263501)
                  ·
                    refine ⟨1306467656858463760223813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3483913751622570027263501 1306467656858463760223813)
                    ·
                      rfl

theorem cell22_3816505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 2, 1, 3].length) (baseStart_3816505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3816505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3816505 prefixEnd_3816505 := by exact prefixLift 3816505
  have htrace : WordTrace (prefixWord ++ tailWord_3816505) baseStart_3816505 baseEnd_3816505 := by
    simpa [prefixWord, tailWord_3816505, baseEnd_3816505] using wordTrace_append hprefix tailTrace_3816505
  have hstable : (prefixWord ++ tailWord_3816505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816505).length < 2 ^ (prefixWord ++ tailWord_3816505).sum := by decide
  have hdescent : baseEnd_3816505 < baseStart_3816505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816512 : List Nat := [2, 1, 1, 2, 2, 3, 2, 3, 6]
def baseStart_3816512 : Nat := 118140960795 + 3816512 * 2 ^ 59
def prefixEnd_3816512 : Nat := 4983230072969 + 3 ^ 40 * 3816512 * 2
def baseEnd_3816512 : Nat := 435490017700506025099597

theorem tailTrace_3816512 : CollatzResearch.WordTrace tailWord_3816512 prefixEnd_3816512 435490017700506025099597 := by
  unfold tailWord_3816512
  simp only [CollatzResearch.WordTrace]
  refine ⟨69599814174718153600797895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92799752232957538134397193 69599814174718153600797895)
  ·
    refine ⟨104399721262077230401196843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69599814174718153600797895 104399721262077230401196843)
    ·
      refine ⟨156599581893115845601795265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104399721262077230401196843 156599581893115845601795265)
      ·
        refine ⟨117449686419836884201346449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156599581893115845601795265 117449686419836884201346449)
        ·
          refine ⟨88087264814877663151009837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117449686419836884201346449 88087264814877663151009837)
          ·
            refine ⟨33032724305579123681628689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88087264814877663151009837 33032724305579123681628689)
            ·
              refine ⟨24774543229184342761221517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33032724305579123681628689 24774543229184342761221517)
              ·
                refine ⟨9290453710944128535458069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24774543229184342761221517 9290453710944128535458069)
                ·
                  refine ⟨435490017700506025099597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9290453710944128535458069 435490017700506025099597)
                  ·
                    rfl

theorem cell22_3816512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 6].length) (baseStart_3816512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3816512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3816512 prefixEnd_3816512 := by exact prefixLift 3816512
  have htrace : WordTrace (prefixWord ++ tailWord_3816512) baseStart_3816512 baseEnd_3816512 := by
    simpa [prefixWord, tailWord_3816512, baseEnd_3816512] using wordTrace_append hprefix tailTrace_3816512
  have hstable : (prefixWord ++ tailWord_3816512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816512).length < 2 ^ (prefixWord ++ tailWord_3816512).sum := by decide
  have hdescent : baseEnd_3816512 < baseStart_3816512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816544 : List Nat := [2, 1, 1, 3, 2, 2, 2, 2, 4, 3]
def baseStart_3816544 : Nat := 118140960795 + 3816544 * 2 ^ 59
def prefixEnd_3816544 : Nat := 4983230072969 + 3 ^ 40 * 3816544 * 2
def baseEnd_3816544 : Nat := 1306481007355480658498693

theorem tailTrace_3816544 : CollatzResearch.WordTrace tailWord_3816544 prefixEnd_3816544 1306481007355480658498693 := by
  unfold tailWord_3816544
  simp only [CollatzResearch.WordTrace]
  refine ⟨69600397742660188333380343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92800530323546917777840457 69600397742660188333380343)
  ·
    refine ⟨104400596613990282500070515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69600397742660188333380343 104400596613990282500070515)
    ·
      refine ⟨156600894920985423750105773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104400596613990282500070515 156600894920985423750105773)
      ·
        refine ⟨58725335595369533906289665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156600894920985423750105773 58725335595369533906289665)
        ·
          refine ⟨44044001696527150429717249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58725335595369533906289665 44044001696527150429717249)
          ·
            refine ⟨33033001272395362822287937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44044001696527150429717249 33033001272395362822287937)
            ·
              refine ⟨24774750954296522116715953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33033001272395362822287937 24774750954296522116715953)
              ·
                refine ⟨18581063215722391587536965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24774750954296522116715953 18581063215722391587536965)
                ·
                  refine ⟨3483949352947948422663181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18581063215722391587536965 3483949352947948422663181)
                  ·
                    refine ⟨1306481007355480658498693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3483949352947948422663181 1306481007355480658498693)
                    ·
                      rfl

theorem cell22_3816544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 4, 3].length) (baseStart_3816544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3816544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3816544 prefixEnd_3816544 := by exact prefixLift 3816544
  have htrace : WordTrace (prefixWord ++ tailWord_3816544) baseStart_3816544 baseEnd_3816544 := by
    simpa [prefixWord, tailWord_3816544, baseEnd_3816544] using wordTrace_append hprefix tailTrace_3816544
  have hstable : (prefixWord ++ tailWord_3816544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816544).length < 2 ^ (prefixWord ++ tailWord_3816544).sum := by decide
  have hdescent : baseEnd_3816544 < baseStart_3816544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816587 : List Nat := [1, 1, 1, 1, 4, 1, 1, 4, 2, 6]
def baseStart_3816587 : Nat := 118140960795 + 3816587 * 2 ^ 59
def prefixEnd_3816587 : Nat := 4983230072969 + 3 ^ 40 * 3816587 * 2
def baseEnd_3816587 : Nat := 1306495727134242879673561

theorem tailTrace_3816587 : CollatzResearch.WordTrace tailWord_3816587 prefixEnd_3816587 1306495727134242879673561 := by
  unfold tailWord_3816587
  simp only [CollatzResearch.WordTrace]
  refine ⟨139202363824164595010576015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92801575882776396673717343 139202363824164595010576015)
  ·
    refine ⟨208803545736246892515864023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139202363824164595010576015 208803545736246892515864023)
    ·
      refine ⟨313205318604370338773796035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208803545736246892515864023 313205318604370338773796035)
      ·
        refine ⟨469807977906555508160694053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313205318604370338773796035 469807977906555508160694053)
        ·
          refine ⟨88088995857479157780130135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 469807977906555508160694053 88088995857479157780130135)
          ·
            refine ⟨132133493786218736670195203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88088995857479157780130135 132133493786218736670195203)
            ·
              refine ⟨198200240679328105005292805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132133493786218736670195203 198200240679328105005292805)
              ·
                refine ⟨37162545127374019688492401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198200240679328105005292805 37162545127374019688492401)
                ·
                  refine ⟨27871908845530514766369301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37162545127374019688492401 27871908845530514766369301)
                  ·
                    refine ⟨1306495727134242879673561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27871908845530514766369301 1306495727134242879673561)
                    ·
                      rfl

theorem cell22_3816587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 6].length) (baseStart_3816587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3816587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3816587 prefixEnd_3816587 := by exact prefixLift 3816587
  have htrace : WordTrace (prefixWord ++ tailWord_3816587) baseStart_3816587 baseEnd_3816587 := by
    simpa [prefixWord, tailWord_3816587, baseEnd_3816587] using wordTrace_append hprefix tailTrace_3816587
  have hstable : (prefixWord ++ tailWord_3816587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816587).length < 2 ^ (prefixWord ++ tailWord_3816587).sum := by decide
  have hdescent : baseEnd_3816587 < baseStart_3816587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816617 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 5, 7]
def baseStart_3816617 : Nat := 118140960795 + 3816617 * 2 ^ 59
def prefixEnd_3816617 : Nat := 4983230072969 + 3 ^ 40 * 3816617 * 2
def baseEnd_3816617 : Nat := 1306505996747332801423469

theorem tailTrace_3816617 : CollatzResearch.WordTrace tailWord_3816617 prefixEnd_3816617 1306505996747332801423469 := by
  unfold tailWord_3816617
  simp only [CollatzResearch.WordTrace]
  refine ⟨139203458014055910134168105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92802305342703940089445403 139203458014055910134168105)
  ·
    refine ⟨104402593510541932600626079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139203458014055910134168105 104402593510541932600626079)
    ·
      refine ⟨156603890265812898900939119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104402593510541932600626079 156603890265812898900939119)
      ·
        refine ⟨234905835398719348351408679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156603890265812898900939119 234905835398719348351408679)
        ·
          refine ⟨352358753098079022527113019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234905835398719348351408679 352358753098079022527113019)
          ·
            refine ⟨528538129647118533790669529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352358753098079022527113019 528538129647118533790669529)
            ·
              refine ⟨396403597235338900343002147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 528538129647118533790669529 396403597235338900343002147)
              ·
                refine ⟨594605395853008350514503221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 396403597235338900343002147 594605395853008350514503221)
                ·
                  refine ⟨55744255861219532860734677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 594605395853008350514503221 55744255861219532860734677)
                  ·
                    refine ⟨1306505996747332801423469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55744255861219532860734677 1306505996747332801423469)
                    ·
                      rfl

theorem cell22_3816617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 7].length) (baseStart_3816617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3816617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3816617 prefixEnd_3816617 := by exact prefixLift 3816617
  have htrace : WordTrace (prefixWord ++ tailWord_3816617) baseStart_3816617 baseEnd_3816617 := by
    simpa [prefixWord, tailWord_3816617, baseEnd_3816617] using wordTrace_append hprefix tailTrace_3816617
  have hstable : (prefixWord ++ tailWord_3816617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816617).length < 2 ^ (prefixWord ++ tailWord_3816617).sum := by decide
  have hdescent : baseEnd_3816617 < baseStart_3816617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816636 : List Nat := [2, 2, 2, 3, 2, 2, 1, 3, 5]
def baseStart_3816636 : Nat := 118140960795 + 3816636 * 2 ^ 59
def prefixEnd_3816636 : Nat := 4983230072969 + 3 ^ 40 * 3816636 * 2
def baseEnd_3816636 : Nat := 435504166945207695066137

theorem tailTrace_3816636 : CollatzResearch.WordTrace tailWord_3816636 prefixEnd_3816636 435504166945207695066137 := by
  unfold tailWord_3816636
  simp only [CollatzResearch.WordTrace]
  refine ⟨69602075500493538189554881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92802767333991384252739841 69602075500493538189554881)
  ·
    refine ⟨52201556625370153642166161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69602075500493538189554881 52201556625370153642166161)
    ·
      refine ⟨39151167469027615231624621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52201556625370153642166161 39151167469027615231624621)
      ·
        refine ⟨14681687800885355711859233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39151167469027615231624621 14681687800885355711859233)
        ·
          refine ⟨11011265850664016783894425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14681687800885355711859233 11011265850664016783894425)
          ·
            refine ⟨8258449387998012587920819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11011265850664016783894425 8258449387998012587920819)
            ·
              refine ⟨12387674081997018881881229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8258449387998012587920819 12387674081997018881881229)
              ·
                refine ⟨4645377780748882080705461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12387674081997018881881229 4645377780748882080705461)
                ·
                  refine ⟨435504166945207695066137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4645377780748882080705461 435504166945207695066137)
                  ·
                    rfl

theorem cell22_3816636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 5].length) (baseStart_3816636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3816636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3816636 prefixEnd_3816636 := by exact prefixLift 3816636
  have htrace : WordTrace (prefixWord ++ tailWord_3816636) baseStart_3816636 baseEnd_3816636 := by
    simpa [prefixWord, tailWord_3816636, baseEnd_3816636] using wordTrace_append hprefix tailTrace_3816636
  have hstable : (prefixWord ++ tailWord_3816636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816636).length < 2 ^ (prefixWord ++ tailWord_3816636).sum := by decide
  have hdescent : baseEnd_3816636 < baseStart_3816636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
