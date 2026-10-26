import V185TrunkScan19Chunk004

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_50562 : List Nat := [3, 4, 2, 1, 1, 1, 4, 3]
def baseStart_50562 : Nat := 118140960795 + 50562 * 2 ^ 59
def prefixEnd_50562 : Nat := 4983230072969 + 3 ^ 40 * 50562 * 2
def baseEnd_50562 : Nat := 15385249690510464973319

theorem tailTrace_50562 : CollatzResearch.WordTrace tailWord_50562 prefixEnd_50562 15385249690510464973319 := by
  unfold tailWord_50562
  simp only [CollatzResearch.WordTrace]
  refine ⟨461036910707496036804485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1229431761886656098145293 461036910707496036804485)
  ·
    refine ⟨86444420757655506900841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 461036910707496036804485 86444420757655506900841)
    ·
      refine ⟨64833315568241630175631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86444420757655506900841 64833315568241630175631)
      ·
        refine ⟨97249973352362445263447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64833315568241630175631 97249973352362445263447)
        ·
          refine ⟨145874960028543667895171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97249973352362445263447 145874960028543667895171)
          ·
            refine ⟨218812440042815501842757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145874960028543667895171 218812440042815501842757)
            ·
              refine ⟨41027332508027906595517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 218812440042815501842757 41027332508027906595517)
              ·
                refine ⟨15385249690510464973319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41027332508027906595517 15385249690510464973319)
                ·
                  rfl

theorem cell19_50562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_50562 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_50562 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_50562 prefixEnd_50562 := by exact prefixLift 50562
  have htrace : WordTrace (prefixWord ++ tailWord_50562) baseStart_50562 baseEnd_50562 := by
    simpa [prefixWord, tailWord_50562, baseEnd_50562] using wordTrace_append hprefix tailTrace_50562
  have hstable : (prefixWord ++ tailWord_50562).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50562).length < 2 ^ (prefixWord ++ tailWord_50562).sum := by decide
  have hdescent : baseEnd_50562 < baseStart_50562 := by decide
  rcases family_descends (prefixWord ++ tailWord_50562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50564 : List Nat := [2, 3, 2, 1, 1, 5, 2, 3]
def baseStart_50564 : Nat := 118140960795 + 50564 * 2 ^ 59
def prefixEnd_50564 : Nat := 4983230072969 + 3 ^ 40 * 50564 * 2
def baseEnd_50564 : Nat := 15385858260175052928869

theorem tailTrace_50564 : CollatzResearch.WordTrace tailWord_50564 prefixEnd_50564 15385858260175052928869 := by
  unfold tailWord_50564
  simp only [CollatzResearch.WordTrace]
  refine ⟨922110294411369244395373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1229480392548492325860497 922110294411369244395373)
  ·
    refine ⟨345791360404263466648265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 922110294411369244395373 345791360404263466648265)
    ·
      refine ⟨259343520303197599986199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345791360404263466648265 259343520303197599986199)
      ·
        refine ⟨389015280454796399979299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259343520303197599986199 389015280454796399979299)
        ·
          refine ⟨583522920682194599968949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389015280454796399979299 583522920682194599968949)
          ·
            refine ⟨54705273813955743747089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 583522920682194599968949 54705273813955743747089)
            ·
              refine ⟨41028955360466807810317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54705273813955743747089 41028955360466807810317)
              ·
                refine ⟨15385858260175052928869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41028955360466807810317 15385858260175052928869)
                ·
                  rfl

theorem cell19_50564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 3].length) (baseStart_50564 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_50564 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_50564 prefixEnd_50564 := by exact prefixLift 50564
  have htrace : WordTrace (prefixWord ++ tailWord_50564) baseStart_50564 baseEnd_50564 := by
    simpa [prefixWord, tailWord_50564, baseEnd_50564] using wordTrace_append hprefix tailTrace_50564
  have hstable : (prefixWord ++ tailWord_50564).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50564).length < 2 ^ (prefixWord ++ tailWord_50564).sum := by decide
  have hdescent : baseEnd_50564 < baseStart_50564 := by decide
  rcases family_descends (prefixWord ++ tailWord_50564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50644 : List Nat := [2, 4, 1, 2, 10]
def baseStart_50644 : Nat := 118140960795 + 50644 * 2 ^ 59
def prefixEnd_50644 : Nat := 4983230072969 + 3 ^ 40 * 50644 * 2
def baseEnd_50644 : Nat := 570748186916984116699

theorem tailTrace_50644 : CollatzResearch.WordTrace tailWord_50644 prefixEnd_50644 570748186916984116699 := by
  unfold tailWord_50644
  simp only [CollatzResearch.WordTrace]
  refine ⟨923569214266456075851493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1231425619021941434468657 923569214266456075851493)
  ·
    refine ⟨173169227674960514222155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 923569214266456075851493 173169227674960514222155)
    ·
      refine ⟨259753841512440771333233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173169227674960514222155 259753841512440771333233)
      ·
        refine ⟨194815381134330578499925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259753841512440771333233 194815381134330578499925)
        ·
          refine ⟨570748186916984116699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 194815381134330578499925 570748186916984116699)
          ·
            rfl

theorem cell19_50644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 10].length) (baseStart_50644 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_50644 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_50644 prefixEnd_50644 := by exact prefixLift 50644
  have htrace : WordTrace (prefixWord ++ tailWord_50644) baseStart_50644 baseEnd_50644 := by
    simpa [prefixWord, tailWord_50644, baseEnd_50644] using wordTrace_append hprefix tailTrace_50644
  have hstable : (prefixWord ++ tailWord_50644).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50644).length < 2 ^ (prefixWord ++ tailWord_50644).sum := by decide
  have hdescent : baseEnd_50644 < baseStart_50644 := by decide
  rcases family_descends (prefixWord ++ tailWord_50644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50661 : List Nat := [1, 3, 1, 5, 1, 1, 3, 4]
def baseStart_50661 : Nat := 118140960795 + 50661 * 2 ^ 59
def prefixEnd_50661 : Nat := 4983230072969 + 3 ^ 40 * 50661 * 2
def baseEnd_50661 : Nat := 15415373888907568773049

theorem tailTrace_50661 : CollatzResearch.WordTrace tailWord_50661 prefixEnd_50661 15415373888907568773049 := by
  unfold tailWord_50661
  simp only [CollatzResearch.WordTrace]
  refine ⟨1847758469471324055071837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1231838979647549370047891 1847758469471324055071837)
  ·
    refine ⟨692909426051746520651939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1847758469471324055071837 692909426051746520651939)
    ·
      refine ⟨1039364139077619780977909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 692909426051746520651939 1039364139077619780977909)
      ·
        refine ⟨97440388038526854466679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1039364139077619780977909 97440388038526854466679)
        ·
          refine ⟨146160582057790281700019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97440388038526854466679 146160582057790281700019)
          ·
            refine ⟨219240873086685422550029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146160582057790281700019 219240873086685422550029)
            ·
              refine ⟨82215327407507033456261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219240873086685422550029 82215327407507033456261)
              ·
                refine ⟨15415373888907568773049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82215327407507033456261 15415373888907568773049)
                ·
                  rfl

theorem cell19_50661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 4].length) (baseStart_50661 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_50661 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_50661 prefixEnd_50661 := by exact prefixLift 50661
  have htrace : WordTrace (prefixWord ++ tailWord_50661) baseStart_50661 baseEnd_50661 := by
    simpa [prefixWord, tailWord_50661, baseEnd_50661] using wordTrace_append hprefix tailTrace_50661
  have hstable : (prefixWord ++ tailWord_50661).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50661).length < 2 ^ (prefixWord ++ tailWord_50661).sum := by decide
  have hdescent : baseEnd_50661 < baseStart_50661 := by decide
  rcases family_descends (prefixWord ++ tailWord_50661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50678 : List Nat := [5, 1, 1, 1, 2, 3, 3, 3]
def baseStart_50678 : Nat := 118140960795 + 50678 * 2 ^ 59
def prefixEnd_50678 : Nat := 4983230072969 + 3 ^ 40 * 50678 * 2
def baseEnd_50678 : Nat := 15420546731056566395225

theorem tailTrace_50678 : CollatzResearch.WordTrace tailWord_50678 prefixEnd_50678 15420546731056566395225 := by
  unfold tailWord_50678
  simp only [CollatzResearch.WordTrace]
  refine ⟨115523656900608497402543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1232252340273157305627125 115523656900608497402543)
  ·
    refine ⟨173285485350912746103815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115523656900608497402543 173285485350912746103815)
    ·
      refine ⟨259928228026369119155723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173285485350912746103815 259928228026369119155723)
      ·
        refine ⟨389892342039553678733585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259928228026369119155723 389892342039553678733585)
        ·
          refine ⟨292419256529665259050189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389892342039553678733585 292419256529665259050189)
          ·
            refine ⟨109657221198624472143821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 292419256529665259050189 109657221198624472143821)
            ·
              refine ⟨41121457949484177053933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109657221198624472143821 41121457949484177053933)
              ·
                refine ⟨15420546731056566395225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41121457949484177053933 15420546731056566395225)
                ·
                  rfl

theorem cell19_50678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_50678 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_50678 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_50678 prefixEnd_50678 := by exact prefixLift 50678
  have htrace : WordTrace (prefixWord ++ tailWord_50678) baseStart_50678 baseEnd_50678 := by
    simpa [prefixWord, tailWord_50678, baseEnd_50678] using wordTrace_append hprefix tailTrace_50678
  have hstable : (prefixWord ++ tailWord_50678).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50678).length < 2 ^ (prefixWord ++ tailWord_50678).sum := by decide
  have hdescent : baseEnd_50678 < baseStart_50678 := by decide
  rcases family_descends (prefixWord ++ tailWord_50678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50680 : List Nat := [2, 1, 2, 1, 1, 6, 3, 3]
def baseStart_50680 : Nat := 118140960795 + 50680 * 2 ^ 59
def prefixEnd_50680 : Nat := 4983230072969 + 3 ^ 40 * 50680 * 2
def baseEnd_50680 : Nat := 15421155300721154350775

theorem tailTrace_50680 : CollatzResearch.WordTrace tailWord_50680 prefixEnd_50680 15421155300721154350775 := by
  unfold tailWord_50680
  simp only [CollatzResearch.WordTrace]
  refine ⟨924225728201245150006747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1232300970934993533342329 924225728201245150006747)
  ·
    refine ⟨1386338592301867725010121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 924225728201245150006747 1386338592301867725010121)
    ·
      refine ⟨1039753944226400793757591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1386338592301867725010121 1039753944226400793757591)
      ·
        refine ⟨1559630916339601190636387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1039753944226400793757591 1559630916339601190636387)
        ·
          refine ⟨2339446374509401785954581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1559630916339601190636387 2339446374509401785954581)
          ·
            refine ⟨109661548805128208716621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2339446374509401785954581 109661548805128208716621)
            ·
              refine ⟨41123080801923078268733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109661548805128208716621 41123080801923078268733)
              ·
                refine ⟨15421155300721154350775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41123080801923078268733 15421155300721154350775)
                ·
                  rfl

theorem cell19_50680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 3].length) (baseStart_50680 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_50680 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_50680 prefixEnd_50680 := by exact prefixLift 50680
  have htrace : WordTrace (prefixWord ++ tailWord_50680) baseStart_50680 baseEnd_50680 := by
    simpa [prefixWord, tailWord_50680, baseEnd_50680] using wordTrace_append hprefix tailTrace_50680
  have hstable : (prefixWord ++ tailWord_50680).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50680).length < 2 ^ (prefixWord ++ tailWord_50680).sum := by decide
  have hdescent : baseEnd_50680 < baseStart_50680 := by decide
  rcases family_descends (prefixWord ++ tailWord_50680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50739 : List Nat := [1, 1, 1, 2, 4, 4, 1, 5]
def baseStart_50739 : Nat := 118140960795 + 50739 * 2 ^ 59
def prefixEnd_50739 : Nat := 4983230072969 + 3 ^ 40 * 50739 * 2
def baseEnd_50739 : Nat := 15439108105826499039503

theorem tailTrace_50739 : CollatzResearch.WordTrace tailWord_50739 prefixEnd_50739 15439108105826499039503 := by
  unfold tailWord_50739
  simp only [CollatzResearch.WordTrace]
  refine ⟨1850603363188743376411271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1233735575459162250940847 1850603363188743376411271)
  ·
    refine ⟨2775905044783115064616907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1850603363188743376411271 2775905044783115064616907)
    ·
      refine ⟨4163857567174672596925361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2775905044783115064616907 4163857567174672596925361)
      ·
        refine ⟨3122893175381004447694021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4163857567174672596925361 3122893175381004447694021)
        ·
          refine ⟨585542470383938333942629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3122893175381004447694021 585542470383938333942629)
          ·
            refine ⟨109789213196988437614243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 585542470383938333942629 109789213196988437614243)
            ·
              refine ⟨164683819795482656421365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109789213196988437614243 164683819795482656421365)
              ·
                refine ⟨15439108105826499039503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 164683819795482656421365 15439108105826499039503)
                ·
                  rfl

theorem cell19_50739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 5].length) (baseStart_50739 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_50739 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_50739 prefixEnd_50739 := by exact prefixLift 50739
  have htrace : WordTrace (prefixWord ++ tailWord_50739) baseStart_50739 baseEnd_50739 := by
    simpa [prefixWord, tailWord_50739, baseEnd_50739] using wordTrace_append hprefix tailTrace_50739
  have hstable : (prefixWord ++ tailWord_50739).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50739).length < 2 ^ (prefixWord ++ tailWord_50739).sum := by decide
  have hdescent : baseEnd_50739 < baseStart_50739 := by decide
  rcases family_descends (prefixWord ++ tailWord_50739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50902 : List Nat := [5, 2, 1, 3, 1, 2, 2, 3]
def baseStart_50902 : Nat := 118140960795 + 50902 * 2 ^ 59
def prefixEnd_50902 : Nat := 4983230072969 + 3 ^ 40 * 50902 * 2
def baseEnd_50902 : Nat := 15488706533490417416837

theorem tailTrace_50902 : CollatzResearch.WordTrace tailWord_50902 prefixEnd_50902 15488706533490417416837 := by
  unfold tailWord_50902
  simp only [CollatzResearch.WordTrace]
  refine ⟨116034278849888888412185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1237698974398814809729973 116034278849888888412185)
  ·
    refine ⟨87025709137416666309139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116034278849888888412185 87025709137416666309139)
    ·
      refine ⟨130538563706124999463709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87025709137416666309139 130538563706124999463709)
      ·
        refine ⟨48951961389796874798891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130538563706124999463709 48951961389796874798891)
        ·
          refine ⟨73427942084695312198337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48951961389796874798891 73427942084695312198337)
          ·
            refine ⟨55070956563521484148753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73427942084695312198337 55070956563521484148753)
            ·
              refine ⟨41303217422641113111565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55070956563521484148753 41303217422641113111565)
              ·
                refine ⟨15488706533490417416837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41303217422641113111565 15488706533490417416837)
                ·
                  rfl

theorem cell19_50902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_50902 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_50902 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_50902 prefixEnd_50902 := by exact prefixLift 50902
  have htrace : WordTrace (prefixWord ++ tailWord_50902) baseStart_50902 baseEnd_50902 := by
    simpa [prefixWord, tailWord_50902, baseEnd_50902] using wordTrace_append hprefix tailTrace_50902
  have hstable : (prefixWord ++ tailWord_50902).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50902).length < 2 ^ (prefixWord ++ tailWord_50902).sum := by decide
  have hdescent : baseEnd_50902 < baseStart_50902 := by decide
  rcases family_descends (prefixWord ++ tailWord_50902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50929 : List Nat := [1, 2, 2, 2, 2, 5, 5]
def baseStart_50929 : Nat := 118140960795 + 50929 * 2 ^ 59
def prefixEnd_50929 : Nat := 4983230072969 + 3 ^ 40 * 50929 * 2
def baseEnd_50929 : Nat := 5165640741320784938921

theorem tailTrace_50929 : CollatzResearch.WordTrace tailWord_50929 prefixEnd_50929 5165640741320784938921 := by
  unfold tailWord_50929
  simp only [CollatzResearch.WordTrace]
  refine ⟨1857533232500405825827841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1238355488333603883885227 1857533232500405825827841)
  ·
    refine ⟨1393149924375304369370881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1857533232500405825827841 1393149924375304369370881)
    ·
      refine ⟨1044862443281478277028161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1393149924375304369370881 1044862443281478277028161)
      ·
        refine ⟨783646832461108707771121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1044862443281478277028161 783646832461108707771121)
        ·
          refine ⟨587735124345831530828341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 783646832461108707771121 587735124345831530828341)
          ·
            refine ⟨55100167907421706015157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 587735124345831530828341 55100167907421706015157)
            ·
              refine ⟨5165640741320784938921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55100167907421706015157 5165640741320784938921)
              ·
                rfl

theorem cell19_50929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 5].length) (baseStart_50929 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_50929 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_50929 prefixEnd_50929 := by exact prefixLift 50929
  have htrace : WordTrace (prefixWord ++ tailWord_50929) baseStart_50929 baseEnd_50929 := by
    simpa [prefixWord, tailWord_50929, baseEnd_50929] using wordTrace_append hprefix tailTrace_50929
  have hstable : (prefixWord ++ tailWord_50929).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50929).length < 2 ^ (prefixWord ++ tailWord_50929).sum := by decide
  have hdescent : baseEnd_50929 < baseStart_50929 := by decide
  rcases family_descends (prefixWord ++ tailWord_50929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50931 : List Nat := [1, 1, 1, 2, 2, 3, 9]
def baseStart_50931 : Nat := 118140960795 + 50931 * 2 ^ 59
def prefixEnd_50931 : Nat := 4983230072969 + 3 ^ 40 * 50931 * 2
def baseEnd_50931 : Nat := 5165843597875647590771

theorem tailTrace_50931 : CollatzResearch.WordTrace tailWord_50931 prefixEnd_50931 5165843597875647590771 := by
  unfold tailWord_50931
  simp only [CollatzResearch.WordTrace]
  refine ⟨1857606178493160167400647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1238404118995440111600431 1857606178493160167400647)
  ·
    refine ⟨2786409267739740251100971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1857606178493160167400647 2786409267739740251100971)
    ·
      refine ⟨4179613901609610376651457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2786409267739740251100971 4179613901609610376651457)
      ·
        refine ⟨3134710426207207782488593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4179613901609610376651457 3134710426207207782488593)
        ·
          refine ⟨2351032819655405836866445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3134710426207207782488593 2351032819655405836866445)
          ·
            refine ⟨881637307370777188824917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2351032819655405836866445 881637307370777188824917)
            ·
              refine ⟨5165843597875647590771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 881637307370777188824917 5165843597875647590771)
              ·
                rfl

theorem cell19_50931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 9].length) (baseStart_50931 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_50931 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_50931 prefixEnd_50931 := by exact prefixLift 50931
  have htrace : WordTrace (prefixWord ++ tailWord_50931) baseStart_50931 baseEnd_50931 := by
    simpa [prefixWord, tailWord_50931, baseEnd_50931] using wordTrace_append hprefix tailTrace_50931
  have hstable : (prefixWord ++ tailWord_50931).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50931).length < 2 ^ (prefixWord ++ tailWord_50931).sum := by decide
  have hdescent : baseEnd_50931 < baseStart_50931 := by decide
  rcases family_descends (prefixWord ++ tailWord_50931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50946 : List Nat := [3, 4, 1, 1, 1, 1, 4, 4]
def baseStart_50946 : Nat := 118140960795 + 50946 * 2 ^ 59
def prefixEnd_50946 : Nat := 4983230072969 + 3 ^ 40 * 50946 * 2
def baseEnd_50946 : Nat := 15502095066111352438939

theorem tailTrace_50946 : CollatzResearch.WordTrace tailWord_50946 prefixEnd_50946 15502095066111352438939 := by
  unfold tailWord_50946
  simp only [CollatzResearch.WordTrace]
  refine ⟨464538318359704432299173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1238768848959211819464461 464538318359704432299173)
  ·
    refine ⟨87100934692444581056095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 464538318359704432299173 87100934692444581056095)
    ·
      refine ⟨130651402038666871584143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87100934692444581056095 130651402038666871584143)
      ·
        refine ⟨195977103058000307376215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130651402038666871584143 195977103058000307376215)
        ·
          refine ⟨293965654587000461064323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195977103058000307376215 293965654587000461064323)
          ·
            refine ⟨440948481880500691596485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293965654587000461064323 440948481880500691596485)
            ·
              refine ⟨82677840352593879674341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 440948481880500691596485 82677840352593879674341)
              ·
                refine ⟨15502095066111352438939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82677840352593879674341 15502095066111352438939)
                ·
                  rfl

theorem cell19_50946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_50946 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_50946 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_50946 prefixEnd_50946 := by exact prefixLift 50946
  have htrace : WordTrace (prefixWord ++ tailWord_50946) baseStart_50946 baseEnd_50946 := by
    simpa [prefixWord, tailWord_50946, baseEnd_50946] using wordTrace_append hprefix tailTrace_50946
  have hstable : (prefixWord ++ tailWord_50946).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50946).length < 2 ^ (prefixWord ++ tailWord_50946).sum := by decide
  have hdescent : baseEnd_50946 < baseStart_50946 := by decide
  rcases family_descends (prefixWord ++ tailWord_50946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50948 : List Nat := [2, 3, 2, 2, 1, 2, 1, 6]
def baseStart_50948 : Nat := 118140960795 + 50948 * 2 ^ 59
def prefixEnd_50948 : Nat := 4983230072969 + 3 ^ 40 * 50948 * 2
def baseEnd_50948 : Nat := 15502703635775940394489

theorem tailTrace_50948 : CollatzResearch.WordTrace tailWord_50948 prefixEnd_50948 15502703635775940394489 := by
  unfold tailWord_50948
  simp only [CollatzResearch.WordTrace]
  refine ⟨929113109715786035384749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1238817479621048047179665 929113109715786035384749)
  ·
    refine ⟨348417416143419763269281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 929113109715786035384749 348417416143419763269281)
    ·
      refine ⟨261313062107564822451961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348417416143419763269281 261313062107564822451961)
      ·
        refine ⟨195984796580673616838971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261313062107564822451961 195984796580673616838971)
        ·
          refine ⟨293977194871010425258457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195984796580673616838971 293977194871010425258457)
          ·
            refine ⟨220482896153257818943843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293977194871010425258457 220482896153257818943843)
            ·
              refine ⟨330724344229886728415765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220482896153257818943843 330724344229886728415765)
              ·
                refine ⟨15502703635775940394489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 330724344229886728415765 15502703635775940394489)
                ·
                  rfl

theorem cell19_50948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_50948 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_50948 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_50948 prefixEnd_50948 := by exact prefixLift 50948
  have htrace : WordTrace (prefixWord ++ tailWord_50948) baseStart_50948 baseEnd_50948 := by
    simpa [prefixWord, tailWord_50948, baseEnd_50948] using wordTrace_append hprefix tailTrace_50948
  have hstable : (prefixWord ++ tailWord_50948).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50948).length < 2 ^ (prefixWord ++ tailWord_50948).sum := by decide
  have hdescent : baseEnd_50948 < baseStart_50948 := by decide
  rcases family_descends (prefixWord ++ tailWord_50948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50967 : List Nat := [1, 1, 3, 4, 2, 1, 2, 5]
def baseStart_50967 : Nat := 118140960795 + 50967 * 2 ^ 59
def prefixEnd_50967 : Nat := 4983230072969 + 3 ^ 40 * 50967 * 2
def baseEnd_50967 : Nat := 15508485047589525972215

theorem tailTrace_50967 : CollatzResearch.WordTrace tailWord_50967 prefixEnd_50967 15508485047589525972215 := by
  unfold tailWord_50967
  simp only [CollatzResearch.WordTrace]
  refine ⟨1858919206362738315711155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1239279470908492210474103 1858919206362738315711155)
  ·
    refine ⟨2788378809544107473566733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1858919206362738315711155 2788378809544107473566733)
    ·
      refine ⟨1045642053579040302587525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2788378809544107473566733 1045642053579040302587525)
      ·
        refine ⟨196057885046070056735161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1045642053579040302587525 196057885046070056735161)
        ·
          refine ⟨147043413784552542551371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196057885046070056735161 147043413784552542551371)
          ·
            refine ⟨220565120676828813827057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147043413784552542551371 220565120676828813827057)
            ·
              refine ⟨165423840507621610370293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220565120676828813827057 165423840507621610370293)
              ·
                refine ⟨15508485047589525972215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 165423840507621610370293 15508485047589525972215)
                ·
                  rfl

theorem cell19_50967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 5].length) (baseStart_50967 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_50967 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_50967 prefixEnd_50967 := by exact prefixLift 50967
  have htrace : WordTrace (prefixWord ++ tailWord_50967) baseStart_50967 baseEnd_50967 := by
    simpa [prefixWord, tailWord_50967, baseEnd_50967] using wordTrace_append hprefix tailTrace_50967
  have hstable : (prefixWord ++ tailWord_50967).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50967).length < 2 ^ (prefixWord ++ tailWord_50967).sum := by decide
  have hdescent : baseEnd_50967 < baseStart_50967 := by decide
  rcases family_descends (prefixWord ++ tailWord_50967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50988 : List Nat := [2, 2, 1, 1, 1, 12]
def baseStart_50988 : Nat := 118140960795 + 50988 * 2 ^ 59
def prefixEnd_50988 : Nat := 4983230072969 + 3 ^ 40 * 50988 * 2
def baseEnd_50988 : Nat := 1723875003229744389499

theorem tailTrace_50988 : CollatzResearch.WordTrace tailWord_50988 prefixEnd_50988 1723875003229744389499 := by
  unfold tailWord_50988
  simp only [CollatzResearch.WordTrace]
  refine ⟨929842569643329451112809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1239790092857772601483745 929842569643329451112809)
  ·
    refine ⟨697381927232497088334607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 929842569643329451112809 697381927232497088334607)
    ·
      refine ⟨1046072890848745632501911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 697381927232497088334607 1046072890848745632501911)
      ·
        refine ⟨1569109336273118448752867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1046072890848745632501911 1569109336273118448752867)
        ·
          refine ⟨2353664004409677673129301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1569109336273118448752867 2353664004409677673129301)
          ·
            refine ⟨1723875003229744389499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 2353664004409677673129301 1723875003229744389499)
            ·
              rfl

theorem cell19_50988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 12].length) (baseStart_50988 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_50988 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_50988 prefixEnd_50988 := by exact prefixLift 50988
  have htrace : WordTrace (prefixWord ++ tailWord_50988) baseStart_50988 baseEnd_50988 := by
    simpa [prefixWord, tailWord_50988, baseEnd_50988] using wordTrace_append hprefix tailTrace_50988
  have hstable : (prefixWord ++ tailWord_50988).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50988).length < 2 ^ (prefixWord ++ tailWord_50988).sum := by decide
  have hdescent : baseEnd_50988 < baseStart_50988 := by decide
  rcases family_descends (prefixWord ++ tailWord_50988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51001 : List Nat := [1, 2, 1, 7, 1, 2, 1, 4]
def baseStart_51001 : Nat := 118140960795 + 51001 * 2 ^ 59
def prefixEnd_51001 : Nat := 4983230072969 + 3 ^ 40 * 51001 * 2
def baseEnd_51001 : Nat := 15518830731887521216567

theorem tailTrace_51001 : CollatzResearch.WordTrace tailWord_51001 prefixEnd_51001 15518830731887521216567 := by
  unfold tailWord_51001
  simp only [CollatzResearch.WordTrace]
  refine ⟨1860159288239562122448857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1240106192159708081632571 1860159288239562122448857)
  ·
    refine ⟨1395119466179671591836643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1860159288239562122448857 1395119466179671591836643)
    ·
      refine ⟨2092679199269507387754965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1395119466179671591836643 2092679199269507387754965)
      ·
        refine ⟨49047168732879079400507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 2092679199269507387754965 49047168732879079400507)
        ·
          refine ⟨73570753099318619100761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49047168732879079400507 73570753099318619100761)
          ·
            refine ⟨55178064824488964325571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73570753099318619100761 55178064824488964325571)
            ·
              refine ⟨82767097236733446488357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55178064824488964325571 82767097236733446488357)
              ·
                refine ⟨15518830731887521216567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82767097236733446488357 15518830731887521216567)
                ·
                  rfl

theorem cell19_51001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 4].length) (baseStart_51001 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_51001 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_51001 prefixEnd_51001 := by exact prefixLift 51001
  have htrace : WordTrace (prefixWord ++ tailWord_51001) baseStart_51001 baseEnd_51001 := by
    simpa [prefixWord, tailWord_51001, baseEnd_51001] using wordTrace_append hprefix tailTrace_51001
  have hstable : (prefixWord ++ tailWord_51001).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51001).length < 2 ^ (prefixWord ++ tailWord_51001).sum := by decide
  have hdescent : baseEnd_51001 < baseStart_51001 := by decide
  rcases family_descends (prefixWord ++ tailWord_51001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51043 : List Nat := [1, 1, 1, 5, 4, 1, 6]
def baseStart_51043 : Nat := 118140960795 + 51043 * 2 ^ 59
def prefixEnd_51043 : Nat := 4983230072969 + 3 ^ 40 * 51043 * 2
def baseEnd_51043 : Nat := 5177203564947956094373

theorem tailTrace_51043 : CollatzResearch.WordTrace tailWord_51043 prefixEnd_51043 5177203564947956094373 := by
  unfold tailWord_51043
  simp only [CollatzResearch.WordTrace]
  refine ⟨1861691154087403295477783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1241127436058268863651855 1861691154087403295477783)
  ·
    refine ⟨2792536731131104943216675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1861691154087403295477783 2792536731131104943216675)
    ·
      refine ⟨4188805096696657414825013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2792536731131104943216675 4188805096696657414825013)
      ·
        refine ⟨392700477815311632639845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4188805096696657414825013 392700477815311632639845)
        ·
          refine ⟨73631339590370931119971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 392700477815311632639845 73631339590370931119971)
          ·
            refine ⟨110447009385556396679957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73631339590370931119971 110447009385556396679957)
            ·
              refine ⟨5177203564947956094373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 110447009385556396679957 5177203564947956094373)
              ·
                rfl

theorem cell19_51043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 6].length) (baseStart_51043 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_51043 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_51043 prefixEnd_51043 := by exact prefixLift 51043
  have htrace : WordTrace (prefixWord ++ tailWord_51043) baseStart_51043 baseEnd_51043 := by
    simpa [prefixWord, tailWord_51043, baseEnd_51043] using wordTrace_append hprefix tailTrace_51043
  have hstable : (prefixWord ++ tailWord_51043).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51043).length < 2 ^ (prefixWord ++ tailWord_51043).sum := by decide
  have hdescent : baseEnd_51043 < baseStart_51043 := by decide
  rcases family_descends (prefixWord ++ tailWord_51043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51094 : List Nat := [5, 3, 1, 1, 2, 2, 5]
def baseStart_51094 : Nat := 118140960795 + 51094 * 2 ^ 59
def prefixEnd_51094 : Nat := 4983230072969 + 3 ^ 40 * 51094 * 2
def baseEnd_51094 : Nat := 5182376407096953716549

theorem tailTrace_51094 : CollatzResearch.WordTrace tailWord_51094 prefixEnd_51094 5182376407096953716549 := by
  unfold tailWord_51094
  simp only [CollatzResearch.WordTrace]
  refine ⟨116471954806414937849021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1242367517935092670389557 116471954806414937849021)
  ·
    refine ⟨43676983052405601693383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116471954806414937849021 43676983052405601693383)
    ·
      refine ⟨65515474578608402540075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43676983052405601693383 65515474578608402540075)
      ·
        refine ⟨98273211867912603810113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65515474578608402540075 98273211867912603810113)
        ·
          refine ⟨73704908900934452857585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98273211867912603810113 73704908900934452857585)
          ·
            refine ⟨55278681675700839643189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73704908900934452857585 55278681675700839643189)
            ·
              refine ⟨5182376407096953716549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55278681675700839643189 5182376407096953716549)
              ·
                rfl

theorem cell19_51094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 5].length) (baseStart_51094 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_51094 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_51094 prefixEnd_51094 := by exact prefixLift 51094
  have htrace : WordTrace (prefixWord ++ tailWord_51094) baseStart_51094 baseEnd_51094 := by
    simpa [prefixWord, tailWord_51094, baseEnd_51094] using wordTrace_append hprefix tailTrace_51094
  have hstable : (prefixWord ++ tailWord_51094).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51094).length < 2 ^ (prefixWord ++ tailWord_51094).sum := by decide
  have hdescent : baseEnd_51094 < baseStart_51094 := by decide
  rcases family_descends (prefixWord ++ tailWord_51094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51096 : List Nat := [2, 1, 2, 6, 2, 1, 5]
def baseStart_51096 : Nat := 118140960795 + 51096 * 2 ^ 59
def prefixEnd_51096 : Nat := 4983230072969 + 3 ^ 40 * 51096 * 2
def baseEnd_51096 : Nat := 5182579263651816368399

theorem tailTrace_51096 : CollatzResearch.WordTrace tailWord_51096 prefixEnd_51096 5182579263651816368399 := by
  unfold tailWord_51096
  simp only [CollatzResearch.WordTrace]
  refine ⟨931812111447696673578571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1242416148596928898104761 931812111447696673578571)
  ·
    refine ⟨1397718167171545010367857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 931812111447696673578571 1397718167171545010367857)
    ·
      refine ⟨1048288625378658757775893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1397718167171545010367857 1048288625378658757775893)
      ·
        refine ⟨49138529314624629270745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1048288625378658757775893 49138529314624629270745)
        ·
          refine ⟨36853896985968471953059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49138529314624629270745 36853896985968471953059)
          ·
            refine ⟨55280845478952707929589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36853896985968471953059 55280845478952707929589)
            ·
              refine ⟨5182579263651816368399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55280845478952707929589 5182579263651816368399)
              ·
                rfl

theorem cell19_51096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 5].length) (baseStart_51096 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_51096 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_51096 prefixEnd_51096 := by exact prefixLift 51096
  have htrace : WordTrace (prefixWord ++ tailWord_51096) baseStart_51096 baseEnd_51096 := by
    simpa [prefixWord, tailWord_51096, baseEnd_51096] using wordTrace_append hprefix tailTrace_51096
  have hstable : (prefixWord ++ tailWord_51096).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51096).length < 2 ^ (prefixWord ++ tailWord_51096).sum := by decide
  have hdescent : baseEnd_51096 < baseStart_51096 := by decide
  rcases family_descends (prefixWord ++ tailWord_51096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51100 : List Nat := [2, 2, 3, 3, 1, 1, 7]
def baseStart_51100 : Nat := 118140960795 + 51100 * 2 ^ 59
def prefixEnd_51100 : Nat := 4983230072969 + 3 ^ 40 * 51100 * 2
def baseEnd_51100 : Nat := 5182984976761541672099

theorem tailTrace_51100 : CollatzResearch.WordTrace tailWord_51100 prefixEnd_51100 5182984976761541672099 := by
  unfold tailWord_51100
  simp only [CollatzResearch.WordTrace]
  refine ⟨931885057440451015151377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1242513409920601353535169 931885057440451015151377)
  ·
    refine ⟨698913793080338261363533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 931885057440451015151377 698913793080338261363533)
    ·
      refine ⟨262092672405126848011325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 698913793080338261363533 262092672405126848011325)
      ·
        refine ⟨98284752151922568004247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262092672405126848011325 98284752151922568004247)
        ·
          refine ⟨147427128227883852006371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98284752151922568004247 147427128227883852006371)
          ·
            refine ⟨221140692341825778009557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147427128227883852006371 221140692341825778009557)
            ·
              refine ⟨5182984976761541672099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 221140692341825778009557 5182984976761541672099)
              ·
                rfl

theorem cell19_51100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 7].length) (baseStart_51100 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_51100 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_51100 prefixEnd_51100 := by exact prefixLift 51100
  have htrace : WordTrace (prefixWord ++ tailWord_51100) baseStart_51100 baseEnd_51100 := by
    simpa [prefixWord, tailWord_51100, baseEnd_51100] using wordTrace_append hprefix tailTrace_51100
  have hstable : (prefixWord ++ tailWord_51100).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51100).length < 2 ^ (prefixWord ++ tailWord_51100).sum := by decide
  have hdescent : baseEnd_51100 < baseStart_51100 := by decide
  rcases family_descends (prefixWord ++ tailWord_51100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51170 : List Nat := [3, 3, 3, 1, 3, 1, 1, 4]
def baseStart_51170 : Nat := 118140960795 + 51170 * 2 ^ 59
def prefixEnd_51170 : Nat := 4983230072969 + 3 ^ 40 * 51170 * 2
def baseEnd_51170 : Nat := 15570254868545203460551

theorem tailTrace_51170 : CollatzResearch.WordTrace tailWord_51170 prefixEnd_51170 15570254868545203460551 := by
  unfold tailWord_51170
  simp only [CollatzResearch.WordTrace]
  refine ⟨466580806156825996337741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1244215483084869323567309 466580806156825996337741)
  ·
    refine ⟨174967802308809748626653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 466580806156825996337741 174967802308809748626653)
    ·
      refine ⟨65612925865803655734995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174967802308809748626653 65612925865803655734995)
      ·
        refine ⟨98419388798705483602493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65612925865803655734995 98419388798705483602493)
        ·
          refine ⟨36907270799514556350935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98419388798705483602493 36907270799514556350935)
          ·
            refine ⟨55360906199271834526403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36907270799514556350935 55360906199271834526403)
            ·
              refine ⟨83041359298907751789605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55360906199271834526403 83041359298907751789605)
              ·
                refine ⟨15570254868545203460551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83041359298907751789605 15570254868545203460551)
                ·
                  rfl

theorem cell19_51170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 4].length) (baseStart_51170 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_51170 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_51170 prefixEnd_51170 := by exact prefixLift 51170
  have htrace : WordTrace (prefixWord ++ tailWord_51170) baseStart_51170 baseEnd_51170 := by
    simpa [prefixWord, tailWord_51170, baseEnd_51170] using wordTrace_append hprefix tailTrace_51170
  have hstable : (prefixWord ++ tailWord_51170).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51170).length < 2 ^ (prefixWord ++ tailWord_51170).sum := by decide
  have hdescent : baseEnd_51170 < baseStart_51170 := by decide
  rcases family_descends (prefixWord ++ tailWord_51170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51197 : List Nat := [1, 4, 1, 1, 1, 2, 2, 7]
def baseStart_51197 : Nat := 118140960795 + 51197 * 2 ^ 59
def prefixEnd_51197 : Nat := 4983230072969 + 3 ^ 40 * 51197 * 2
def baseEnd_51197 : Nat := 15578470559017140860477

theorem tailTrace_51197 : CollatzResearch.WordTrace tailWord_51197 prefixEnd_51197 15578470559017140860477 := by
  unfold tailWord_51197
  simp only [CollatzResearch.WordTrace]
  refine ⟨1867307995529487596583845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1244871997019658397722563 1867307995529487596583845)
  ·
    refine ⟨350120249161778924359471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1867307995529487596583845 350120249161778924359471)
    ·
      refine ⟨525180373742668386539207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350120249161778924359471 525180373742668386539207)
      ·
        refine ⟨787770560614002579808811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 525180373742668386539207 787770560614002579808811)
        ·
          refine ⟨1181655840921003869713217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 787770560614002579808811 1181655840921003869713217)
          ·
            refine ⟨886241880690752902284913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1181655840921003869713217 886241880690752902284913)
            ·
              refine ⟨664681410518064676713685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 886241880690752902284913 664681410518064676713685)
              ·
                refine ⟨15578470559017140860477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 664681410518064676713685 15578470559017140860477)
                ·
                  rfl

theorem cell19_51197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 7].length) (baseStart_51197 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_51197 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_51197 prefixEnd_51197 := by exact prefixLift 51197
  have htrace : WordTrace (prefixWord ++ tailWord_51197) baseStart_51197 baseEnd_51197 := by
    simpa [prefixWord, tailWord_51197, baseEnd_51197] using wordTrace_append hprefix tailTrace_51197
  have hstable : (prefixWord ++ tailWord_51197).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51197).length < 2 ^ (prefixWord ++ tailWord_51197).sum := by decide
  have hdescent : baseEnd_51197 < baseStart_51197 := by decide
  rcases family_descends (prefixWord ++ tailWord_51197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51235 : List Nat := [1, 1, 1, 4, 3, 1, 2, 6]
def baseStart_51235 : Nat := 118140960795 + 51235 * 2 ^ 59
def prefixEnd_51235 : Nat := 4983230072969 + 3 ^ 40 * 51235 * 2
def baseEnd_51235 : Nat := 15590033382644312015929

theorem tailTrace_51235 : CollatzResearch.WordTrace tailWord_51235 prefixEnd_51235 15590033382644312015929 := by
  unfold tailWord_51235
  simp only [CollatzResearch.WordTrace]
  refine ⟨1868693969391820086467159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1245795979594546724311439 1868693969391820086467159)
  ·
    refine ⟨2803040954087730129700739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1868693969391820086467159 2803040954087730129700739)
    ·
      refine ⟨4204561431131595194551109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2803040954087730129700739 4204561431131595194551109)
      ·
        refine ⟨788355268337174098978333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4204561431131595194551109 788355268337174098978333)
        ·
          refine ⟨295633225626440287116875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 788355268337174098978333 295633225626440287116875)
          ·
            refine ⟨443449838439660430675313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295633225626440287116875 443449838439660430675313)
            ·
              refine ⟨332587378829745323006485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 443449838439660430675313 332587378829745323006485)
              ·
                refine ⟨15590033382644312015929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 332587378829745323006485 15590033382644312015929)
                ·
                  rfl

theorem cell19_51235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 6].length) (baseStart_51235 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_51235 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_51235 prefixEnd_51235 := by exact prefixLift 51235
  have htrace : WordTrace (prefixWord ++ tailWord_51235) baseStart_51235 baseEnd_51235 := by
    simpa [prefixWord, tailWord_51235, baseEnd_51235] using wordTrace_append hprefix tailTrace_51235
  have hstable : (prefixWord ++ tailWord_51235).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51235).length < 2 ^ (prefixWord ++ tailWord_51235).sum := by decide
  have hdescent : baseEnd_51235 < baseStart_51235 := by decide
  rcases family_descends (prefixWord ++ tailWord_51235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51250 : List Nat := [3, 2, 1, 1, 2, 5, 2, 3]
def baseStart_51250 : Nat := 118140960795 + 51250 * 2 ^ 59
def prefixEnd_51250 : Nat := 4983230072969 + 3 ^ 40 * 51250 * 2
def baseEnd_51250 : Nat := 15594597655128721682555

theorem tailTrace_51250 : CollatzResearch.WordTrace tailWord_51250 prefixEnd_51250 15594597655128721682555 := by
  unfold tailWord_51250
  simp only [CollatzResearch.WordTrace]
  refine ⟨467310266084369412065801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1246160709558318432175469 467310266084369412065801)
  ·
    refine ⟨350482699563277059049351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 467310266084369412065801 350482699563277059049351)
    ·
      refine ⟨525724049344915588574027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350482699563277059049351 525724049344915588574027)
      ·
        refine ⟨788586074017373382861041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 525724049344915588574027 788586074017373382861041)
        ·
          refine ⟨591439555513030037145781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 788586074017373382861041 591439555513030037145781)
          ·
            refine ⟨55447458329346565982417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 591439555513030037145781 55447458329346565982417)
            ·
              refine ⟨41585593747009924486813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55447458329346565982417 41585593747009924486813)
              ·
                refine ⟨15594597655128721682555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41585593747009924486813 15594597655128721682555)
                ·
                  rfl

theorem cell19_51250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_51250 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_51250 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_51250 prefixEnd_51250 := by exact prefixLift 51250
  have htrace : WordTrace (prefixWord ++ tailWord_51250) baseStart_51250 baseEnd_51250 := by
    simpa [prefixWord, tailWord_51250, baseEnd_51250] using wordTrace_append hprefix tailTrace_51250
  have hstable : (prefixWord ++ tailWord_51250).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51250).length < 2 ^ (prefixWord ++ tailWord_51250).sum := by decide
  have hdescent : baseEnd_51250 < baseStart_51250 := by decide
  rcases family_descends (prefixWord ++ tailWord_51250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51286 : List Nat := [5, 2, 2, 1, 1, 2, 2, 4]
def baseStart_51286 : Nat := 118140960795 + 51286 * 2 ^ 59
def prefixEnd_51286 : Nat := 4983230072969 + 3 ^ 40 * 51286 * 2
def baseEnd_51286 : Nat := 15605551909091304882457

theorem tailTrace_51286 : CollatzResearch.WordTrace tailWord_51286 prefixEnd_51286 15605551909091304882457 := by
  unfold tailWord_51286
  simp only [CollatzResearch.WordTrace]
  refine ⟨116909630762940987285857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1247036061471370531049141 116909630762940987285857)
  ·
    refine ⟨87682223072205740464393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116909630762940987285857 87682223072205740464393)
    ·
      refine ⟨65761667304154305348295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87682223072205740464393 65761667304154305348295)
      ·
        refine ⟨98642500956231458022443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65761667304154305348295 98642500956231458022443)
        ·
          refine ⟨147963751434347187033665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98642500956231458022443 147963751434347187033665)
          ·
            refine ⟨110972813575760390275249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147963751434347187033665 110972813575760390275249)
            ·
              refine ⟨83229610181820292706437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110972813575760390275249 83229610181820292706437)
              ·
                refine ⟨15605551909091304882457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83229610181820292706437 15605551909091304882457)
                ·
                  rfl

theorem cell19_51286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_51286 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_51286 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_51286 prefixEnd_51286 := by exact prefixLift 51286
  have htrace : WordTrace (prefixWord ++ tailWord_51286) baseStart_51286 baseEnd_51286 := by
    simpa [prefixWord, tailWord_51286, baseEnd_51286] using wordTrace_append hprefix tailTrace_51286
  have hstable : (prefixWord ++ tailWord_51286).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51286).length < 2 ^ (prefixWord ++ tailWord_51286).sum := by decide
  have hdescent : baseEnd_51286 < baseStart_51286 := by decide
  rcases family_descends (prefixWord ++ tailWord_51286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51311 : List Nat := [1, 1, 2, 1, 3, 4, 2, 5]
def baseStart_51311 : Nat := 118140960795 + 51311 * 2 ^ 59
def prefixEnd_51311 : Nat := 4983230072969 + 3 ^ 40 * 51311 * 2
def baseEnd_51311 : Nat := 15613159029898654326833

theorem tailTrace_51311 : CollatzResearch.WordTrace tailWord_51311 prefixEnd_51311 15613159029898654326833 := by
  unfold tailWord_51311
  simp only [CollatzResearch.WordTrace]
  refine ⟨1871465917116485066233787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1247643944744323377489191 1871465917116485066233787)
  ·
    refine ⟨2807198875674727599350681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1871465917116485066233787 2807198875674727599350681)
    ·
      refine ⟨2105399156756045699513011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2807198875674727599350681 2105399156756045699513011)
      ·
        refine ⟨3158098735134068549269517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2105399156756045699513011 3158098735134068549269517)
        ·
          refine ⟨1184287025675275705976069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3158098735134068549269517 1184287025675275705976069)
          ·
            refine ⟨222053817314114194870513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1184287025675275705976069 222053817314114194870513)
            ·
              refine ⟨166540362985585646152885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222053817314114194870513 166540362985585646152885)
              ·
                refine ⟨15613159029898654326833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 166540362985585646152885 15613159029898654326833)
                ·
                  rfl

theorem cell19_51311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 5].length) (baseStart_51311 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_51311 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_51311 prefixEnd_51311 := by exact prefixLift 51311
  have htrace : WordTrace (prefixWord ++ tailWord_51311) baseStart_51311 baseEnd_51311 := by
    simpa [prefixWord, tailWord_51311, baseEnd_51311] using wordTrace_append hprefix tailTrace_51311
  have hstable : (prefixWord ++ tailWord_51311).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51311).length < 2 ^ (prefixWord ++ tailWord_51311).sum := by decide
  have hdescent : baseEnd_51311 < baseStart_51311 := by decide
  rcases family_descends (prefixWord ++ tailWord_51311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51330 : List Nat := [3, 4, 12]
def baseStart_51330 : Nat := 118140960795 + 51330 * 2 ^ 59
def prefixEnd_51330 : Nat := 4983230072969 + 3 ^ 40 * 51330 * 2
def baseEnd_51330 : Nat := 64275475068774649813

theorem tailTrace_51330 : CollatzResearch.WordTrace tailWord_51330 prefixEnd_51330 64275475068774649813 := by
  unfold tailWord_51330
  simp only [CollatzResearch.WordTrace]
  refine ⟨468039726011912827793861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1248105936031767540783629 468039726011912827793861)
  ·
    refine ⟨87757448627233655211349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 468039726011912827793861 87757448627233655211349)
    ·
      refine ⟨64275475068774649813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 12 87757448627233655211349 64275475068774649813)
      ·
        rfl

theorem cell19_51330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 12].length) (baseStart_51330 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_51330 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_51330 prefixEnd_51330 := by exact prefixLift 51330
  have htrace : WordTrace (prefixWord ++ tailWord_51330) baseStart_51330 baseEnd_51330 := by
    simpa [prefixWord, tailWord_51330, baseEnd_51330] using wordTrace_append hprefix tailTrace_51330
  have hstable : (prefixWord ++ tailWord_51330).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51330).length < 2 ^ (prefixWord ++ tailWord_51330).sum := by decide
  have hdescent : baseEnd_51330 < baseStart_51330 := by decide
  rcases family_descends (prefixWord ++ tailWord_51330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51364 : List Nat := [2, 3, 1, 2, 4, 1, 3, 3]
def baseStart_51364 : Nat := 118140960795 + 51364 * 2 ^ 59
def prefixEnd_51364 : Nat := 4983230072969 + 3 ^ 40 * 51364 * 2
def baseEnd_51364 : Nat := 15629286126010235148911

theorem tailTrace_51364 : CollatzResearch.WordTrace tailWord_51364 prefixEnd_51364 15629286126010235148911 := by
  unfold tailWord_51364
  simp only [CollatzResearch.WordTrace]
  refine ⟨936699492962237558956573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1248932657282983411942097 936699492962237558956573)
  ·
    refine ⟨351262309860839084608715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 936699492962237558956573 351262309860839084608715)
    ·
      refine ⟨526893464791258626913073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351262309860839084608715 526893464791258626913073)
      ·
        refine ⟨395170098593443970184805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 526893464791258626913073 395170098593443970184805)
        ·
          refine ⟨74094393486270744409651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 395170098593443970184805 74094393486270744409651)
          ·
            refine ⟨111141590229406116614477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74094393486270744409651 111141590229406116614477)
            ·
              refine ⟨41678096336027293730429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111141590229406116614477 41678096336027293730429)
              ·
                refine ⟨15629286126010235148911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41678096336027293730429 15629286126010235148911)
                ·
                  rfl

theorem cell19_51364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 3].length) (baseStart_51364 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_51364 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_51364 prefixEnd_51364 := by exact prefixLift 51364
  have htrace : WordTrace (prefixWord ++ tailWord_51364) baseStart_51364 baseEnd_51364 := by
    simpa [prefixWord, tailWord_51364, baseEnd_51364] using wordTrace_append hprefix tailTrace_51364
  have hstable : (prefixWord ++ tailWord_51364).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51364).length < 2 ^ (prefixWord ++ tailWord_51364).sum := by decide
  have hdescent : baseEnd_51364 < baseStart_51364 := by decide
  rcases family_descends (prefixWord ++ tailWord_51364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51421 : List Nat := [1, 4, 3, 2, 1, 1, 4, 3]
def baseStart_51421 : Nat := 118140960795 + 51421 * 2 ^ 59
def prefixEnd_51421 : Nat := 4983230072969 + 3 ^ 40 * 51421 * 2
def baseEnd_51421 : Nat := 15646630361450991882089

theorem tailTrace_51421 : CollatzResearch.WordTrace tailWord_51421 prefixEnd_51421 15646630361450991882089 := by
  unfold tailWord_51421
  simp only [CollatzResearch.WordTrace]
  refine ⟨1875477946717973852738117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1250318631145315901825411 1875477946717973852738117)
  ·
    refine ⟨351652115009620097388397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1875477946717973852738117 351652115009620097388397)
    ·
      refine ⟨131869543128607536520649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 351652115009620097388397 131869543128607536520649)
      ·
        refine ⟨98902157346455652390487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131869543128607536520649 98902157346455652390487)
        ·
          refine ⟨148353236019683478585731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98902157346455652390487 148353236019683478585731)
          ·
            refine ⟨222529854029525217878597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148353236019683478585731 222529854029525217878597)
            ·
              refine ⟨41724347630535978352237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 222529854029525217878597 41724347630535978352237)
              ·
                refine ⟨15646630361450991882089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41724347630535978352237 15646630361450991882089)
                ·
                  rfl

theorem cell19_51421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 3].length) (baseStart_51421 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_51421 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_51421 prefixEnd_51421 := by exact prefixLift 51421
  have htrace : WordTrace (prefixWord ++ tailWord_51421) baseStart_51421 baseEnd_51421 := by
    simpa [prefixWord, tailWord_51421, baseEnd_51421] using wordTrace_append hprefix tailTrace_51421
  have hstable : (prefixWord ++ tailWord_51421).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51421).length < 2 ^ (prefixWord ++ tailWord_51421).sum := by decide
  have hdescent : baseEnd_51421 < baseStart_51421 := by decide
  rcases family_descends (prefixWord ++ tailWord_51421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51425 : List Nat := [1, 2, 3, 1, 3, 1, 3, 5]
def baseStart_51425 : Nat := 118140960795 + 51425 * 2 ^ 59
def prefixEnd_51425 : Nat := 4983230072969 + 3 ^ 40 * 51425 * 2
def baseEnd_51425 : Nat := 15647847500780167793189

theorem tailTrace_51425 : CollatzResearch.WordTrace tailWord_51425 prefixEnd_51425 15647847500780167793189 := by
  unfold tailWord_51425
  simp only [CollatzResearch.WordTrace]
  refine ⟨1875623838703482535883729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1250415892468988357255819 1875623838703482535883729)
  ·
    refine ⟨1406717879027611901912797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1875623838703482535883729 1406717879027611901912797)
    ·
      refine ⟨527519204635354463217299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1406717879027611901912797 527519204635354463217299)
      ·
        refine ⟨791278806953031694825949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 527519204635354463217299 791278806953031694825949)
        ·
          refine ⟨296729552607386885559731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 791278806953031694825949 296729552607386885559731)
          ·
            refine ⟨445094328911080328339597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296729552607386885559731 445094328911080328339597)
            ·
              refine ⟨166910373341655123127349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 445094328911080328339597 166910373341655123127349)
              ·
                refine ⟨15647847500780167793189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 166910373341655123127349 15647847500780167793189)
                ·
                  rfl

theorem cell19_51425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 5].length) (baseStart_51425 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_51425 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_51425 prefixEnd_51425 := by exact prefixLift 51425
  have htrace : WordTrace (prefixWord ++ tailWord_51425) baseStart_51425 baseEnd_51425 := by
    simpa [prefixWord, tailWord_51425, baseEnd_51425] using wordTrace_append hprefix tailTrace_51425
  have hstable : (prefixWord ++ tailWord_51425).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51425).length < 2 ^ (prefixWord ++ tailWord_51425).sum := by decide
  have hdescent : baseEnd_51425 < baseStart_51425 := by decide
  rcases family_descends (prefixWord ++ tailWord_51425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51442 : List Nat := [3, 2, 1, 3, 2, 3, 5]
def baseStart_51442 : Nat := 118140960795 + 51442 * 2 ^ 59
def prefixEnd_51442 : Nat := 4983230072969 + 3 ^ 40 * 51442 * 2
def baseEnd_51442 : Nat := 5217673447643055138455

theorem tailTrace_51442 : CollatzResearch.WordTrace tailWord_51442 prefixEnd_51442 5217673447643055138455 := by
  unfold tailWord_51442
  simp only [CollatzResearch.WordTrace]
  refine ⟨469060969910473609813145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1250829253094596292835053 469060969910473609813145)
  ·
    refine ⟨351795727432855207359859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 469060969910473609813145 351795727432855207359859)
    ·
      refine ⟨527693591149282811039789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351795727432855207359859 527693591149282811039789)
      ·
        refine ⟨197885096680981054139921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 527693591149282811039789 197885096680981054139921)
        ·
          refine ⟨148413822510735790604941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197885096680981054139921 148413822510735790604941)
          ·
            refine ⟨55655183441525921476853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148413822510735790604941 55655183441525921476853)
            ·
              refine ⟨5217673447643055138455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55655183441525921476853 5217673447643055138455)
              ·
                rfl

theorem cell19_51442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 5].length) (baseStart_51442 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_51442 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_51442 prefixEnd_51442 := by exact prefixLift 51442
  have htrace : WordTrace (prefixWord ++ tailWord_51442) baseStart_51442 baseEnd_51442 := by
    simpa [prefixWord, tailWord_51442, baseEnd_51442] using wordTrace_append hprefix tailTrace_51442
  have hstable : (prefixWord ++ tailWord_51442).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51442).length < 2 ^ (prefixWord ++ tailWord_51442).sum := by decide
  have hdescent : baseEnd_51442 < baseStart_51442 := by decide
  rcases family_descends (prefixWord ++ tailWord_51442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51495 : List Nat := [1, 1, 8, 1, 2, 6]
def baseStart_51495 : Nat := 118140960795 + 51495 * 2 ^ 59
def prefixEnd_51495 : Nat := 4983230072969 + 3 ^ 40 * 51495 * 2
def baseEnd_51495 : Nat := 1741016382115638470827

theorem tailTrace_51495 : CollatzResearch.WordTrace tailWord_51495 prefixEnd_51495 1741016382115638470827 := by
  unfold tailWord_51495
  simp only [CollatzResearch.WordTrace]
  refine ⟨1878176948449884490931939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1252117965633256327287959 1878176948449884490931939)
  ·
    refine ⟨2817265422674826736397909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1878176948449884490931939 2817265422674826736397909)
    ·
      refine ⟨33014829171970625817163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 2817265422674826736397909 33014829171970625817163)
      ·
        refine ⟨49522243757955938725745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33014829171970625817163 49522243757955938725745)
        ·
          refine ⟨37141682818466954044309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49522243757955938725745 37141682818466954044309)
          ·
            refine ⟨1741016382115638470827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37141682818466954044309 1741016382115638470827)
            ·
              rfl

theorem cell19_51495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 6].length) (baseStart_51495 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_51495 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_51495 prefixEnd_51495 := by exact prefixLift 51495
  have htrace : WordTrace (prefixWord ++ tailWord_51495) baseStart_51495 baseEnd_51495 := by
    simpa [prefixWord, tailWord_51495, baseEnd_51495] using wordTrace_append hprefix tailTrace_51495
  have hstable : (prefixWord ++ tailWord_51495).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51495).length < 2 ^ (prefixWord ++ tailWord_51495).sum := by decide
  have hdescent : baseEnd_51495 < baseStart_51495 := by decide
  rcases family_descends (prefixWord ++ tailWord_51495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51518 : List Nat := [4, 2, 1, 2, 1, 2, 3, 4]
def baseStart_51518 : Nat := 118140960795 + 51518 * 2 ^ 59
def prefixEnd_51518 : Nat := 4983230072969 + 3 ^ 40 * 51518 * 2
def baseEnd_51518 : Nat := 15676145990183507726269

theorem tailTrace_51518 : CollatzResearch.WordTrace tailWord_51518 prefixEnd_51518 15676145990183507726269 := by
  unfold tailWord_51518
  simp only [CollatzResearch.WordTrace]
  refine ⟨234876978420819927377401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1252677218244372946012805 234876978420819927377401)
  ·
    refine ⟨176157733815614945533051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234876978420819927377401 176157733815614945533051)
    ·
      refine ⟨264236600723422418299577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176157733815614945533051 264236600723422418299577)
      ·
        refine ⟨198177450542566813724683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264236600723422418299577 198177450542566813724683)
        ·
          refine ⟨297266175813850220587025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198177450542566813724683 297266175813850220587025)
          ·
            refine ⟨222949631860387665440269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297266175813850220587025 222949631860387665440269)
            ·
              refine ⟨83606111947645374540101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 222949631860387665440269 83606111947645374540101)
              ·
                refine ⟨15676145990183507726269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83606111947645374540101 15676145990183507726269)
                ·
                  rfl

theorem cell19_51518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_51518 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_51518 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_51518 prefixEnd_51518 := by exact prefixLift 51518
  have htrace : WordTrace (prefixWord ++ tailWord_51518) baseStart_51518 baseEnd_51518 := by
    simpa [prefixWord, tailWord_51518, baseEnd_51518] using wordTrace_append hprefix tailTrace_51518
  have hstable : (prefixWord ++ tailWord_51518).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51518).length < 2 ^ (prefixWord ++ tailWord_51518).sum := by decide
  have hdescent : baseEnd_51518 < baseStart_51518 := by decide
  rcases family_descends (prefixWord ++ tailWord_51518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51537 : List Nat := [1, 2, 2, 1, 4, 3, 3, 3]
def baseStart_51537 : Nat := 118140960795 + 51537 * 2 ^ 59
def prefixEnd_51537 : Nat := 4983230072969 + 3 ^ 40 * 51537 * 2
def baseEnd_51537 : Nat := 15681927401997093303995

theorem tailTrace_51537 : CollatzResearch.WordTrace tailWord_51537 prefixEnd_51537 15681927401997093303995 := by
  unfold tailWord_51537
  simp only [CollatzResearch.WordTrace]
  refine ⟨1879708814297725663960865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1253139209531817109307243 1879708814297725663960865)
  ·
    refine ⟨1409781610723294247970649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1879708814297725663960865 1409781610723294247970649)
    ·
      refine ⟨1057336208042470685977987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1409781610723294247970649 1057336208042470685977987)
      ·
        refine ⟨1586004312063706028966981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1057336208042470685977987 1586004312063706028966981)
        ·
          refine ⟨297375808511944880431309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1586004312063706028966981 297375808511944880431309)
          ·
            refine ⟨111515928191979330161741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 297375808511944880431309 111515928191979330161741)
            ·
              refine ⟨41818473071992248810653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111515928191979330161741 41818473071992248810653)
              ·
                refine ⟨15681927401997093303995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41818473071992248810653 15681927401997093303995)
                ·
                  rfl

theorem cell19_51537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 3].length) (baseStart_51537 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_51537 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_51537 prefixEnd_51537 := by exact prefixLift 51537
  have htrace : WordTrace (prefixWord ++ tailWord_51537) baseStart_51537 baseEnd_51537 := by
    simpa [prefixWord, tailWord_51537, baseEnd_51537] using wordTrace_append hprefix tailTrace_51537
  have hstable : (prefixWord ++ tailWord_51537).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51537).length < 2 ^ (prefixWord ++ tailWord_51537).sum := by decide
  have hdescent : baseEnd_51537 < baseStart_51537 := by decide
  rcases family_descends (prefixWord ++ tailWord_51537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51550 : List Nat := [4, 4, 2, 1, 1, 1, 6]
def baseStart_51550 : Nat := 118140960795 + 51550 * 2 ^ 59
def prefixEnd_51550 : Nat := 4983230072969 + 3 ^ 40 * 51550 * 2
def baseEnd_51550 : Nat := 5228627701605638338357

theorem tailTrace_51550 : CollatzResearch.WordTrace tailWord_51550 prefixEnd_51550 5228627701605638338357 := by
  unfold tailWord_51550
  simp only [CollatzResearch.WordTrace]
  refine ⟨235022870406328610523013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1253455308833752589456069 235022870406328610523013)
  ·
    refine ⟨44066788201186614473065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 235022870406328610523013 44066788201186614473065)
    ·
      refine ⟨33050091150889960854799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44066788201186614473065 33050091150889960854799)
      ·
        refine ⟨49575136726334941282199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33050091150889960854799 49575136726334941282199)
        ·
          refine ⟨74362705089502411923299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49575136726334941282199 74362705089502411923299)
          ·
            refine ⟨111544057634253617884949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74362705089502411923299 111544057634253617884949)
            ·
              refine ⟨5228627701605638338357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 111544057634253617884949 5228627701605638338357)
              ·
                rfl

theorem cell19_51550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 6].length) (baseStart_51550 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_51550 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_51550 prefixEnd_51550 := by exact prefixLift 51550
  have htrace : WordTrace (prefixWord ++ tailWord_51550) baseStart_51550 baseEnd_51550 := by
    simpa [prefixWord, tailWord_51550, baseEnd_51550] using wordTrace_append hprefix tailTrace_51550
  have hstable : (prefixWord ++ tailWord_51550).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51550).length < 2 ^ (prefixWord ++ tailWord_51550).sum := by decide
  have hdescent : baseEnd_51550 < baseStart_51550 := by decide
  rcases family_descends (prefixWord ++ tailWord_51550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51596 : List Nat := [2, 2, 1, 2, 1, 5, 1, 5]
def baseStart_51596 : Nat := 118140960795 + 51596 * 2 ^ 59
def prefixEnd_51596 : Nat := 4983230072969 + 3 ^ 40 * 51596 * 2
def baseEnd_51596 : Nat := 15699880207102437992723

theorem tailTrace_51596 : CollatzResearch.WordTrace tailWord_51596 prefixEnd_51596 15699880207102437992723 := by
  unfold tailWord_51596
  simp only [CollatzResearch.WordTrace]
  refine ⟨940930360541989370179321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1254573814055985826905761 940930360541989370179321)
  ·
    refine ⟨705697770406492027634491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 940930360541989370179321 705697770406492027634491)
    ·
      refine ⟨1058546655609738041451737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 705697770406492027634491 1058546655609738041451737)
      ·
        refine ⟨793909991707303531088803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1058546655609738041451737 793909991707303531088803)
        ·
          refine ⟨1190864987560955296633205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793909991707303531088803 1190864987560955296633205)
          ·
            refine ⟨111643592583839559059363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1190864987560955296633205 111643592583839559059363)
            ·
              refine ⟨167465388875759338589045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111643592583839559059363 167465388875759338589045)
              ·
                refine ⟨15699880207102437992723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 167465388875759338589045 15699880207102437992723)
                ·
                  rfl

theorem cell19_51596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_51596 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_51596 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_51596 prefixEnd_51596 := by exact prefixLift 51596
  have htrace : WordTrace (prefixWord ++ tailWord_51596) baseStart_51596 baseEnd_51596 := by
    simpa [prefixWord, tailWord_51596, baseEnd_51596] using wordTrace_append hprefix tailTrace_51596
  have hstable : (prefixWord ++ tailWord_51596).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51596).length < 2 ^ (prefixWord ++ tailWord_51596).sum := by decide
  have hdescent : baseEnd_51596 < baseStart_51596 := by decide
  rcases family_descends (prefixWord ++ tailWord_51596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51613 : List Nat := [1, 4, 2, 1, 4, 2, 5]
def baseStart_51613 : Nat := 118140960795 + 51613 * 2 ^ 59
def prefixEnd_51613 : Nat := 4983230072969 + 3 ^ 40 * 51613 * 2
def baseEnd_51613 : Nat := 5235017683083811871633

theorem tailTrace_51613 : CollatzResearch.WordTrace tailWord_51613 prefixEnd_51613 5235017683083811871633 := by
  unfold tailWord_51613
  simp only [CollatzResearch.WordTrace]
  refine ⟨1882480762022390643727493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1254987174681593762484995 1882480762022390643727493)
  ·
    refine ⟨352965142879198245698905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1882480762022390643727493 352965142879198245698905)
    ·
      refine ⟨264723857159398684274179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352965142879198245698905 264723857159398684274179)
      ·
        refine ⟨397085785739098026411269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264723857159398684274179 397085785739098026411269)
        ·
          refine ⟨74453584826080879952113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 397085785739098026411269 74453584826080879952113)
          ·
            refine ⟨55840188619560659964085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74453584826080879952113 55840188619560659964085)
            ·
              refine ⟨5235017683083811871633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55840188619560659964085 5235017683083811871633)
              ·
                rfl

theorem cell19_51613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 5].length) (baseStart_51613 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_51613 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_51613 prefixEnd_51613 := by exact prefixLift 51613
  have htrace : WordTrace (prefixWord ++ tailWord_51613) baseStart_51613 baseEnd_51613 := by
    simpa [prefixWord, tailWord_51613, baseEnd_51613] using wordTrace_append hprefix tailTrace_51613
  have hstable : (prefixWord ++ tailWord_51613).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51613).length < 2 ^ (prefixWord ++ tailWord_51613).sum := by decide
  have hdescent : baseEnd_51613 < baseStart_51613 := by decide
  rcases family_descends (prefixWord ++ tailWord_51613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51634 : List Nat := [3, 2, 1, 1, 1, 1, 6, 4]
def baseStart_51634 : Nat := 118140960795 + 51634 * 2 ^ 59
def prefixEnd_51634 : Nat := 4983230072969 + 3 ^ 40 * 51634 * 2
def baseEnd_51634 : Nat := 15711443030729609148175

theorem tailTrace_51634 : CollatzResearch.WordTrace tailWord_51634 prefixEnd_51634 15711443030729609148175 := by
  unfold tailWord_51634
  simp only [CollatzResearch.WordTrace]
  refine ⟨470811673736577807560489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1255497796630874153494637 470811673736577807560489)
  ·
    refine ⟨353108755302433355670367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 470811673736577807560489 353108755302433355670367)
    ·
      refine ⟨529663132953650033505551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353108755302433355670367 529663132953650033505551)
      ·
        refine ⟨794494699430475050258327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529663132953650033505551 794494699430475050258327)
        ·
          refine ⟨1191742049145712575387491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 794494699430475050258327 1191742049145712575387491)
          ·
            refine ⟨1787613073718568863081237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1191742049145712575387491 1787613073718568863081237)
            ·
              refine ⟨83794362830557915456933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1787613073718568863081237 83794362830557915456933)
              ·
                refine ⟨15711443030729609148175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83794362830557915456933 15711443030729609148175)
                ·
                  rfl

theorem cell19_51634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_51634 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_51634 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_51634 prefixEnd_51634 := by exact prefixLift 51634
  have htrace : WordTrace (prefixWord ++ tailWord_51634) baseStart_51634 baseEnd_51634 := by
    simpa [prefixWord, tailWord_51634, baseEnd_51634] using wordTrace_append hprefix tailTrace_51634
  have hstable : (prefixWord ++ tailWord_51634).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51634).length < 2 ^ (prefixWord ++ tailWord_51634).sum := by decide
  have hdescent : baseEnd_51634 < baseStart_51634 := by decide
  rcases family_descends (prefixWord ++ tailWord_51634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51725 : List Nat := [1, 7, 1, 1, 1, 2, 6]
def baseStart_51725 : Nat := 118140960795 + 51725 * 2 ^ 59
def prefixEnd_51725 : Nat := 4983230072969 + 3 ^ 40 * 51725 * 2
def baseEnd_51725 : Nat := 5246377650156120375235

theorem tailTrace_51725 : CollatzResearch.WordTrace tailWord_51725 prefixEnd_51725 5246377650156120375235 := by
  unfold tailWord_51725
  simp only [CollatzResearch.WordTrace]
  refine ⟨1886565737616633771804629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1257710491744422514536419 1886565737616633771804629)
  ·
    refine ⟨44216384475389854026671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 1886565737616633771804629 44216384475389854026671)
    ·
      refine ⟨66324576713084781040007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44216384475389854026671 66324576713084781040007)
      ·
        refine ⟨99486865069627171560011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66324576713084781040007 99486865069627171560011)
        ·
          refine ⟨149230297604440757340017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99486865069627171560011 149230297604440757340017)
          ·
            refine ⟨111922723203330568005013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149230297604440757340017 111922723203330568005013)
            ·
              refine ⟨5246377650156120375235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 111922723203330568005013 5246377650156120375235)
              ·
                rfl

theorem cell19_51725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 6].length) (baseStart_51725 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_51725 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_51725 prefixEnd_51725 := by exact prefixLift 51725
  have htrace : WordTrace (prefixWord ++ tailWord_51725) baseStart_51725 baseEnd_51725 := by
    simpa [prefixWord, tailWord_51725, baseEnd_51725] using wordTrace_append hprefix tailTrace_51725
  have hstable : (prefixWord ++ tailWord_51725).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51725).length < 2 ^ (prefixWord ++ tailWord_51725).sum := by decide
  have hdescent : baseEnd_51725 < baseStart_51725 := by decide
  rcases family_descends (prefixWord ++ tailWord_51725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51731 : List Nat := [1, 1, 1, 2, 1, 5, 8]
def baseStart_51731 : Nat := 118140960795 + 51731 * 2 ^ 59
def prefixEnd_51731 : Nat := 4983230072969 + 3 ^ 40 * 51731 * 2
def baseEnd_51731 : Nat := 5246986219820708330785

theorem tailTrace_51731 : CollatzResearch.WordTrace tailWord_51731 prefixEnd_51731 5246986219820708330785 := by
  unfold tailWord_51731
  simp only [CollatzResearch.WordTrace]
  refine ⟨1886784575594896796523047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1257856383729931197682031 1886784575594896796523047)
  ·
    refine ⟨2830176863392345194784571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1886784575594896796523047 2830176863392345194784571)
    ·
      refine ⟨4245265295088517792176857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2830176863392345194784571 4245265295088517792176857)
      ·
        refine ⟨3183948971316388344132643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4245265295088517792176857 3183948971316388344132643)
        ·
          refine ⟨4775923456974582516198965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3183948971316388344132643 4775923456974582516198965)
          ·
            refine ⟨447742824091367110893653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4775923456974582516198965 447742824091367110893653)
            ·
              refine ⟨5246986219820708330785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 447742824091367110893653 5246986219820708330785)
              ·
                rfl

theorem cell19_51731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 8].length) (baseStart_51731 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_51731 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_51731 prefixEnd_51731 := by exact prefixLift 51731
  have htrace : WordTrace (prefixWord ++ tailWord_51731) baseStart_51731 baseEnd_51731 := by
    simpa [prefixWord, tailWord_51731, baseEnd_51731] using wordTrace_append hprefix tailTrace_51731
  have hstable : (prefixWord ++ tailWord_51731).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51731).length < 2 ^ (prefixWord ++ tailWord_51731).sum := by decide
  have hdescent : baseEnd_51731 < baseStart_51731 := by decide
  rcases family_descends (prefixWord ++ tailWord_51731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51757 : List Nat := [1, 5, 4, 1, 2, 1, 2, 3]
def baseStart_51757 : Nat := 118140960795 + 51757 * 2 ^ 59
def prefixEnd_51757 : Nat := 4983230072969 + 3 ^ 40 * 51757 * 2
def baseEnd_51757 : Nat := 15748870065101768414507

theorem tailTrace_51757 : CollatzResearch.WordTrace tailWord_51757 prefixEnd_51757 15748870065101768414507 := by
  unfold tailWord_51757
  simp only [CollatzResearch.WordTrace]
  refine ⟨1887732873500703236969525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1258488582333802157979683 1887732873500703236969525)
  ·
    refine ⟨176974956890690928465893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1887732873500703236969525 176974956890690928465893)
    ·
      refine ⟨33182804417004549087355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176974956890690928465893 33182804417004549087355)
      ·
        refine ⟨49774206625506823631033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33182804417004549087355 49774206625506823631033)
        ·
          refine ⟨37330654969130117723275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49774206625506823631033 37330654969130117723275)
          ·
            refine ⟨55995982453695176584913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37330654969130117723275 55995982453695176584913)
            ·
              refine ⟨41996986840271382438685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55995982453695176584913 41996986840271382438685)
              ·
                refine ⟨15748870065101768414507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41996986840271382438685 15748870065101768414507)
                ·
                  rfl

theorem cell19_51757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 3].length) (baseStart_51757 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_51757 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_51757 prefixEnd_51757 := by exact prefixLift 51757
  have htrace : WordTrace (prefixWord ++ tailWord_51757) baseStart_51757 baseEnd_51757 := by
    simpa [prefixWord, tailWord_51757, baseEnd_51757] using wordTrace_append hprefix tailTrace_51757
  have hstable : (prefixWord ++ tailWord_51757).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51757).length < 2 ^ (prefixWord ++ tailWord_51757).sum := by decide
  have hdescent : baseEnd_51757 < baseStart_51757 := by decide
  rcases family_descends (prefixWord ++ tailWord_51757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51780 : List Nat := [2, 3, 5, 1, 1, 2, 5]
def baseStart_51780 : Nat := 118140960795 + 51780 * 2 ^ 59
def prefixEnd_51780 : Nat := 4983230072969 + 3 ^ 40 * 51780 * 2
def baseEnd_51780 : Nat := 5251956205414843301111

theorem tailTrace_51780 : CollatzResearch.WordTrace tailWord_51780 prefixEnd_51780 5251956205414843301111 := by
  unfold tailWord_51780
  simp only [CollatzResearch.WordTrace]
  refine ⟨944285876208689082528397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1259047834944918776704529 944285876208689082528397)
  ·
    refine ⟨354107203578258405948149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 944285876208689082528397 354107203578258405948149)
    ·
      refine ⟨33197550335461725557639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 354107203578258405948149 33197550335461725557639)
      ·
        refine ⟨49796325503192588336459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33197550335461725557639 49796325503192588336459)
        ·
          refine ⟨74694488254788882504689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49796325503192588336459 74694488254788882504689)
          ·
            refine ⟨56020866191091661878517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74694488254788882504689 56020866191091661878517)
            ·
              refine ⟨5251956205414843301111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56020866191091661878517 5251956205414843301111)
              ·
                rfl

theorem cell19_51780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 5].length) (baseStart_51780 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_51780 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_51780 prefixEnd_51780 := by exact prefixLift 51780
  have htrace : WordTrace (prefixWord ++ tailWord_51780) baseStart_51780 baseEnd_51780 := by
    simpa [prefixWord, tailWord_51780, baseEnd_51780] using wordTrace_append hprefix tailTrace_51780
  have hstable : (prefixWord ++ tailWord_51780).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51780).length < 2 ^ (prefixWord ++ tailWord_51780).sum := by decide
  have hdescent : baseEnd_51780 < baseStart_51780 := by decide
  rcases family_descends (prefixWord ++ tailWord_51780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51782 : List Nat := [6, 1, 1, 1, 2, 3, 5]
def baseStart_51782 : Nat := 118140960795 + 51782 * 2 ^ 59
def prefixEnd_51782 : Nat := 4983230072969 + 3 ^ 40 * 51782 * 2
def baseEnd_51782 : Nat := 5252159061969705952961

theorem tailTrace_51782 : CollatzResearch.WordTrace tailWord_51782 prefixEnd_51782 5252159061969705952961 := by
  unfold tailWord_51782
  simp only [CollatzResearch.WordTrace]
  refine ⟨59020146825316640832175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1259096465606755004419733 59020146825316640832175)
  ·
    refine ⟨88530220237974961248263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59020146825316640832175 88530220237974961248263)
    ·
      refine ⟨132795330356962441872395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88530220237974961248263 132795330356962441872395)
      ·
        refine ⟨199192995535443662808593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132795330356962441872395 199192995535443662808593)
        ·
          refine ⟨149394746651582747106445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199192995535443662808593 149394746651582747106445)
          ·
            refine ⟨56023029994343530164917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149394746651582747106445 56023029994343530164917)
            ·
              refine ⟨5252159061969705952961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56023029994343530164917 5252159061969705952961)
              ·
                rfl

theorem cell19_51782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 5].length) (baseStart_51782 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_51782 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_51782 prefixEnd_51782 := by exact prefixLift 51782
  have htrace : WordTrace (prefixWord ++ tailWord_51782) baseStart_51782 baseEnd_51782 := by
    simpa [prefixWord, tailWord_51782, baseEnd_51782] using wordTrace_append hprefix tailTrace_51782
  have hstable : (prefixWord ++ tailWord_51782).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51782).length < 2 ^ (prefixWord ++ tailWord_51782).sum := by decide
  have hdescent : baseEnd_51782 < baseStart_51782 := by decide
  rcases family_descends (prefixWord ++ tailWord_51782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51786 : List Nat := [3, 1, 2, 1, 1, 6, 5]
def baseStart_51786 : Nat := 118140960795 + 51786 * 2 ^ 59
def prefixEnd_51786 : Nat := 4983230072969 + 3 ^ 40 * 51786 * 2
def baseEnd_51786 : Nat := 5252564775079431256661

theorem tailTrace_51786 : CollatzResearch.WordTrace tailWord_51786 prefixEnd_51786 5252564775079431256661 := by
  unfold tailWord_51786
  simp only [CollatzResearch.WordTrace]
  refine ⟨472197647598910297443803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1259193726930427459850141 472197647598910297443803)
  ·
    refine ⟨708296471398365446165705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 472197647598910297443803 708296471398365446165705)
    ·
      refine ⟨531222353548774084624279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 708296471398365446165705 531222353548774084624279)
      ·
        refine ⟨796833530323161126936419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531222353548774084624279 796833530323161126936419)
        ·
          refine ⟨1195250295484741690404629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 796833530323161126936419 1195250295484741690404629)
          ·
            refine ⟨56027357600847266737717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1195250295484741690404629 56027357600847266737717)
            ·
              refine ⟨5252564775079431256661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56027357600847266737717 5252564775079431256661)
              ·
                rfl

theorem cell19_51786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 5].length) (baseStart_51786 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_51786 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_51786 prefixEnd_51786 := by exact prefixLift 51786
  have htrace : WordTrace (prefixWord ++ tailWord_51786) baseStart_51786 baseEnd_51786 := by
    simpa [prefixWord, tailWord_51786, baseEnd_51786] using wordTrace_append hprefix tailTrace_51786
  have hstable : (prefixWord ++ tailWord_51786).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51786).length < 2 ^ (prefixWord ++ tailWord_51786).sum := by decide
  have hdescent : baseEnd_51786 < baseStart_51786 := by decide
  rcases family_descends (prefixWord ++ tailWord_51786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51845 : List Nat := [1, 3, 1, 1, 4, 9]
def baseStart_51845 : Nat := 118140960795 + 51845 * 2 ^ 59
def prefixEnd_51845 : Nat := 4983230072969 + 3 ^ 40 * 51845 * 2
def baseEnd_51845 : Nat := 1752849681149293162079

theorem tailTrace_51845 : CollatzResearch.WordTrace tailWord_51845 prefixEnd_51845 1752849681149293162079 := by
  unfold tailWord_51845
  simp only [CollatzResearch.WordTrace]
  refine ⟨1890942497181894266172989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1260628331454596177448659 1890942497181894266172989)
  ·
    refine ⟨709103436443210349814871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1890942497181894266172989 709103436443210349814871)
    ·
      refine ⟨1063655154664815524722307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 709103436443210349814871 1063655154664815524722307)
      ·
        refine ⟨1595482731997223287083461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1063655154664815524722307 1595482731997223287083461)
        ·
          refine ⟨299153012249479366328149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1595482731997223287083461 299153012249479366328149)
          ·
            refine ⟨1752849681149293162079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 299153012249479366328149 1752849681149293162079)
            ·
              rfl

theorem cell19_51845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 9].length) (baseStart_51845 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_51845 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_51845 prefixEnd_51845 := by exact prefixLift 51845
  have htrace : WordTrace (prefixWord ++ tailWord_51845) baseStart_51845 baseEnd_51845 := by
    simpa [prefixWord, tailWord_51845, baseEnd_51845] using wordTrace_append hprefix tailTrace_51845
  have hstable : (prefixWord ++ tailWord_51845).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51845).length < 2 ^ (prefixWord ++ tailWord_51845).sum := by decide
  have hdescent : baseEnd_51845 < baseStart_51845 := by decide
  rcases family_descends (prefixWord ++ tailWord_51845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51860 : List Nat := [2, 4, 2, 2, 1, 1, 3, 4]
def baseStart_51860 : Nat := 118140960795 + 51860 * 2 ^ 59
def prefixEnd_51860 : Nat := 4983230072969 + 3 ^ 40 * 51860 * 2
def baseEnd_51860 : Nat := 15780211402828048125337

theorem tailTrace_51860 : CollatzResearch.WordTrace tailWord_51860 prefixEnd_51860 15780211402828048125337 := by
  unfold tailWord_51860
  simp only [CollatzResearch.WordTrace]
  refine ⟨945744796063775913984517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1260993061418367885312689 945744796063775913984517)
  ·
    refine ⟨177327149261957983872097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 945744796063775913984517 177327149261957983872097)
    ·
      refine ⟨132995361946468487904073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177327149261957983872097 132995361946468487904073)
      ·
        refine ⟨99746521459851365928055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132995361946468487904073 99746521459851365928055)
        ·
          refine ⟨149619782189777048892083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99746521459851365928055 149619782189777048892083)
          ·
            refine ⟨224429673284665573338125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149619782189777048892083 224429673284665573338125)
            ·
              refine ⟨84161127481749590001797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 224429673284665573338125 84161127481749590001797)
              ·
                refine ⟨15780211402828048125337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84161127481749590001797 15780211402828048125337)
                ·
                  rfl

theorem cell19_51860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_51860 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_51860 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_51860 prefixEnd_51860 := by exact prefixLift 51860
  have htrace : WordTrace (prefixWord ++ tailWord_51860) baseStart_51860 baseEnd_51860 := by
    simpa [prefixWord, tailWord_51860, baseEnd_51860] using wordTrace_append hprefix tailTrace_51860
  have hstable : (prefixWord ++ tailWord_51860).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51860).length < 2 ^ (prefixWord ++ tailWord_51860).sum := by decide
  have hdescent : baseEnd_51860 < baseStart_51860 := by decide
  rcases family_descends (prefixWord ++ tailWord_51860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51921 : List Nat := [1, 2, 2, 1, 2, 3, 2, 6]
def baseStart_51921 : Nat := 118140960795 + 51921 * 2 ^ 59
def prefixEnd_51921 : Nat := 4983230072969 + 3 ^ 40 * 51921 * 2
def baseEnd_51921 : Nat := 15798772777597980769615

theorem tailTrace_51921 : CollatzResearch.WordTrace tailWord_51921 prefixEnd_51921 15798772777597980769615 := by
  unfold tailWord_51921
  simp only [CollatzResearch.WordTrace]
  refine ⟨1893714444906559245939617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1262476296604372830626411 1893714444906559245939617)
  ·
    refine ⟨1420285833679919434454713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1893714444906559245939617 1420285833679919434454713)
    ·
      refine ⟨1065214375259939575841035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1420285833679919434454713 1065214375259939575841035)
      ·
        refine ⟨1597821562889909363761553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1065214375259939575841035 1597821562889909363761553)
        ·
          refine ⟨1198366172167432022821165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1597821562889909363761553 1198366172167432022821165)
          ·
            refine ⟨449387314562787008557937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1198366172167432022821165 449387314562787008557937)
            ·
              refine ⟨337040485922090256418453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 449387314562787008557937 337040485922090256418453)
              ·
                refine ⟨15798772777597980769615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 337040485922090256418453 15798772777597980769615)
                ·
                  rfl

theorem cell19_51921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 6].length) (baseStart_51921 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_51921 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_51921 prefixEnd_51921 := by exact prefixLift 51921
  have htrace : WordTrace (prefixWord ++ tailWord_51921) baseStart_51921 baseEnd_51921 := by
    simpa [prefixWord, tailWord_51921, baseEnd_51921] using wordTrace_append hprefix tailTrace_51921
  have hstable : (prefixWord ++ tailWord_51921).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51921).length < 2 ^ (prefixWord ++ tailWord_51921).sum := by decide
  have hdescent : baseEnd_51921 < baseStart_51921 := by decide
  rcases family_descends (prefixWord ++ tailWord_51921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51976 : List Nat := [2, 1, 3, 2, 2, 3, 2, 4]
def baseStart_51976 : Nat := 118140960795 + 51976 * 2 ^ 59
def prefixEnd_51976 : Nat := 4983230072969 + 3 ^ 40 * 51976 * 2
def baseEnd_51976 : Nat := 15815508443374149547243

theorem tailTrace_51976 : CollatzResearch.WordTrace tailWord_51976 prefixEnd_51976 15815508443374149547243 := by
  unfold tailWord_51976
  simp only [CollatzResearch.WordTrace]
  refine ⟨947860229853651819595891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1263813639804869092794521 947860229853651819595891)
  ·
    refine ⟨1421790344780477729393837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 947860229853651819595891 1421790344780477729393837)
    ·
      refine ⟨533171379292679148522689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1421790344780477729393837 533171379292679148522689)
      ·
        refine ⟨399878534469509361392017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 533171379292679148522689 399878534469509361392017)
        ·
          refine ⟨299908900852132021044013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 399878534469509361392017 299908900852132021044013)
          ·
            refine ⟨112465837819549507891505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 299908900852132021044013 112465837819549507891505)
            ·
              refine ⟨84349378364662130918629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112465837819549507891505 84349378364662130918629)
              ·
                refine ⟨15815508443374149547243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84349378364662130918629 15815508443374149547243)
                ·
                  rfl

theorem cell19_51976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_51976 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_51976 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_51976 prefixEnd_51976 := by exact prefixLift 51976
  have htrace : WordTrace (prefixWord ++ tailWord_51976) baseStart_51976 baseEnd_51976 := by
    simpa [prefixWord, tailWord_51976, baseEnd_51976] using wordTrace_append hprefix tailTrace_51976
  have hstable : (prefixWord ++ tailWord_51976).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51976).length < 2 ^ (prefixWord ++ tailWord_51976).sum := by decide
  have hdescent : baseEnd_51976 < baseStart_51976 := by decide
  rcases family_descends (prefixWord ++ tailWord_51976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52014 : List Nat := [4, 1, 3, 2, 1, 8]
def baseStart_52014 : Nat := 118140960795 + 52014 * 2 ^ 59
def prefixEnd_52014 : Nat := 4983230072969 + 3 ^ 40 * 52014 * 2
def baseEnd_52014 : Nat := 1758563474111257855855

theorem tailTrace_52014 : CollatzResearch.WordTrace tailWord_52014 prefixEnd_52014 1758563474111257855855 := by
  unfold tailWord_52014
  simp only [CollatzResearch.WordTrace]
  refine ⟨237138304196204516134387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1264737622379757419383397 237138304196204516134387)
  ·
    refine ⟨355707456294306774201581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237138304196204516134387 355707456294306774201581)
    ·
      refine ⟨133390296110365040325593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355707456294306774201581 133390296110365040325593)
      ·
        refine ⟨100042722082773780244195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133390296110365040325593 100042722082773780244195)
        ·
          refine ⟨150064083124160670366293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100042722082773780244195 150064083124160670366293)
          ·
            refine ⟨1758563474111257855855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 150064083124160670366293 1758563474111257855855)
            ·
              rfl

theorem cell19_52014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 8].length) (baseStart_52014 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_52014 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_52014 prefixEnd_52014 := by exact prefixLift 52014
  have htrace : WordTrace (prefixWord ++ tailWord_52014) baseStart_52014 baseEnd_52014 := by
    simpa [prefixWord, tailWord_52014, baseEnd_52014] using wordTrace_append hprefix tailTrace_52014
  have hstable : (prefixWord ++ tailWord_52014).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52014).length < 2 ^ (prefixWord ++ tailWord_52014).sum := by decide
  have hdescent : baseEnd_52014 < baseStart_52014 := by decide
  rcases family_descends (prefixWord ++ tailWord_52014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52029 : List Nat := [1, 4, 1, 4, 3, 1, 1, 4]
def baseStart_52029 : Nat := 118140960795 + 52029 * 2 ^ 59
def prefixEnd_52029 : Nat := 4983230072969 + 3 ^ 40 * 52029 * 2
def baseEnd_52029 : Nat := 15831635539485730369321

theorem tailTrace_52029 : CollatzResearch.WordTrace tailWord_52029 prefixEnd_52029 15831635539485730369321 := by
  unfold tailWord_52029
  simp only [CollatzResearch.WordTrace]
  refine ⟨1897653528515293690871141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1265102352343529127247427 1897653528515293690871141)
  ·
    refine ⟨355810036596617567038339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1897653528515293690871141 355810036596617567038339)
    ·
      refine ⟨533715054894926350557509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355810036596617567038339 533715054894926350557509)
      ·
        refine ⟨100071572792798690729533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 533715054894926350557509 100071572792798690729533)
        ·
          refine ⟨37526839797299509023575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100071572792798690729533 37526839797299509023575)
          ·
            refine ⟨56290259695949263535363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37526839797299509023575 56290259695949263535363)
            ·
              refine ⟨84435389543923895303045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56290259695949263535363 84435389543923895303045)
              ·
                refine ⟨15831635539485730369321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84435389543923895303045 15831635539485730369321)
                ·
                  rfl

theorem cell19_52029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 4].length) (baseStart_52029 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_52029 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_52029 prefixEnd_52029 := by exact prefixLift 52029
  have htrace : WordTrace (prefixWord ++ tailWord_52029) baseStart_52029 baseEnd_52029 := by
    simpa [prefixWord, tailWord_52029, baseEnd_52029] using wordTrace_append hprefix tailTrace_52029
  have hstable : (prefixWord ++ tailWord_52029).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52029).length < 2 ^ (prefixWord ++ tailWord_52029).sum := by decide
  have hdescent : baseEnd_52029 < baseStart_52029 := by decide
  rcases family_descends (prefixWord ++ tailWord_52029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52276 : List Nat := [2, 5, 1, 2, 1, 3, 2, 3]
def baseStart_52276 : Nat := 118140960795 + 52276 * 2 ^ 59
def prefixEnd_52276 : Nat := 4983230072969 + 3 ^ 40 * 52276 * 2
def baseEnd_52276 : Nat := 15906793893062342879759

theorem tailTrace_52276 : CollatzResearch.WordTrace tailWord_52276 prefixEnd_52276 15906793893062342879759 := by
  unfold tailWord_52276
  simp only [CollatzResearch.WordTrace]
  refine ⟨953331179310227437556341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1271108239080303250075121 953331179310227437556341)
  ·
    refine ⟨89374798060333822270907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 953331179310227437556341 89374798060333822270907)
    ·
      refine ⟨134062197090500733406361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89374798060333822270907 134062197090500733406361)
      ·
        refine ⟨100546647817875550054771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134062197090500733406361 100546647817875550054771)
        ·
          refine ⟨150819971726813325082157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100546647817875550054771 150819971726813325082157)
          ·
            refine ⟨56557489397554996905809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150819971726813325082157 56557489397554996905809)
            ·
              refine ⟨42418117048166247679357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56557489397554996905809 42418117048166247679357)
              ·
                refine ⟨15906793893062342879759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42418117048166247679357 15906793893062342879759)
                ·
                  rfl

theorem cell19_52276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 3].length) (baseStart_52276 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_52276 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_52276 prefixEnd_52276 := by exact prefixLift 52276
  have htrace : WordTrace (prefixWord ++ tailWord_52276) baseStart_52276 baseEnd_52276 := by
    simpa [prefixWord, tailWord_52276, baseEnd_52276] using wordTrace_append hprefix tailTrace_52276
  have hstable : (prefixWord ++ tailWord_52276).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52276).length < 2 ^ (prefixWord ++ tailWord_52276).sum := by decide
  have hdescent : baseEnd_52276 < baseStart_52276 := by decide
  rcases family_descends (prefixWord ++ tailWord_52276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52278 : List Nat := [5, 1, 2, 1, 1, 2, 4, 3]
def baseStart_52278 : Nat := 118140960795 + 52278 * 2 ^ 59
def prefixEnd_52278 : Nat := 4983230072969 + 3 ^ 40 * 52278 * 2
def baseEnd_52278 : Nat := 15907402462726930835309

theorem tailTrace_52278 : CollatzResearch.WordTrace tailWord_52278 prefixEnd_52278 15907402462726930835309 := by
  unfold tailWord_52278
  simp only [CollatzResearch.WordTrace]
  refine ⟨119170956538325576042843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1271156869742139477790325 119170956538325576042843)
  ·
    refine ⟨178756434807488364064265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119170956538325576042843 178756434807488364064265)
    ·
      refine ⟨134067326105616273048199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178756434807488364064265 134067326105616273048199)
      ·
        refine ⟨201100989158424409572299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134067326105616273048199 201100989158424409572299)
        ·
          refine ⟨301651483737636614358449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201100989158424409572299 301651483737636614358449)
          ·
            refine ⟨226238612803227460768837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301651483737636614358449 226238612803227460768837)
            ·
              refine ⟨42419739900605148894157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 226238612803227460768837 42419739900605148894157)
              ·
                refine ⟨15907402462726930835309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42419739900605148894157 15907402462726930835309)
                ·
                  rfl

theorem cell19_52278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_52278 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_52278 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_52278 prefixEnd_52278 := by exact prefixLift 52278
  have htrace : WordTrace (prefixWord ++ tailWord_52278) baseStart_52278 baseEnd_52278 := by
    simpa [prefixWord, tailWord_52278, baseEnd_52278] using wordTrace_append hprefix tailTrace_52278
  have hstable : (prefixWord ++ tailWord_52278).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52278).length < 2 ^ (prefixWord ++ tailWord_52278).sum := by decide
  have hdescent : baseEnd_52278 < baseStart_52278 := by decide
  rcases family_descends (prefixWord ++ tailWord_52278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52280 : List Nat := [2, 1, 2, 1, 5, 1, 4, 3]
def baseStart_52280 : Nat := 118140960795 + 52280 * 2 ^ 59
def prefixEnd_52280 : Nat := 4983230072969 + 3 ^ 40 * 52280 * 2
def baseEnd_52280 : Nat := 15908011032391518790859

theorem tailTrace_52280 : CollatzResearch.WordTrace tailWord_52280 prefixEnd_52280 15908011032391518790859 := by
  unfold tailWord_52280
  simp only [CollatzResearch.WordTrace]
  refine ⟨953404125302981779129147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1271205500403975705505529 953404125302981779129147)
  ·
    refine ⟨1430106187954472668693721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 953404125302981779129147 1430106187954472668693721)
    ·
      refine ⟨1072579640965854501520291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1430106187954472668693721 1072579640965854501520291)
      ·
        refine ⟨1608869461448781752280437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1072579640965854501520291 1608869461448781752280437)
        ·
          refine ⟨150831512010823289276291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1608869461448781752280437 150831512010823289276291)
          ·
            refine ⟨226247268016234933914437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150831512010823289276291 226247268016234933914437)
            ·
              refine ⟨42421362753044050108957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 226247268016234933914437 42421362753044050108957)
              ·
                refine ⟨15908011032391518790859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42421362753044050108957 15908011032391518790859)
                ·
                  rfl

theorem cell19_52280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 3].length) (baseStart_52280 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_52280 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_52280 prefixEnd_52280 := by exact prefixLift 52280
  have htrace : WordTrace (prefixWord ++ tailWord_52280) baseStart_52280 baseEnd_52280 := by
    simpa [prefixWord, tailWord_52280, baseEnd_52280] using wordTrace_append hprefix tailTrace_52280
  have hstable : (prefixWord ++ tailWord_52280).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52280).length < 2 ^ (prefixWord ++ tailWord_52280).sum := by decide
  have hdescent : baseEnd_52280 < baseStart_52280 := by decide
  rcases family_descends (prefixWord ++ tailWord_52280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52320 : List Nat := [2, 1, 1, 3, 2, 2, 4, 4]
def baseStart_52320 : Nat := 118140960795 + 52320 * 2 ^ 59
def prefixEnd_52320 : Nat := 4983230072969 + 3 ^ 40 * 52320 * 2
def baseEnd_52320 : Nat := 15920182425683277901861

theorem tailTrace_52320 : CollatzResearch.WordTrace tailWord_52320 prefixEnd_52320 15920182425683277901861 := by
  unfold tailWord_52320
  simp only [CollatzResearch.WordTrace]
  refine ⟨954133585230525194857207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1272178113640700259809609 954133585230525194857207)
  ·
    refine ⟨1431200377845787792285811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 954133585230525194857207 1431200377845787792285811)
    ·
      refine ⟨2146800566768681688428717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1431200377845787792285811 2146800566768681688428717)
      ·
        refine ⟨805050212538255633160769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2146800566768681688428717 805050212538255633160769)
        ·
          refine ⟨603787659403691724870577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 805050212538255633160769 603787659403691724870577)
          ·
            refine ⟨452840744552768793652933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 603787659403691724870577 452840744552768793652933)
            ·
              refine ⟨84907639603644148809925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 452840744552768793652933 84907639603644148809925)
              ·
                refine ⟨15920182425683277901861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84907639603644148809925 15920182425683277901861)
                ·
                  rfl

theorem cell19_52320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_52320 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_52320 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_52320 prefixEnd_52320 := by exact prefixLift 52320
  have htrace : WordTrace (prefixWord ++ tailWord_52320) baseStart_52320 baseEnd_52320 := by
    simpa [prefixWord, tailWord_52320, baseEnd_52320] using wordTrace_append hprefix tailTrace_52320
  have hstable : (prefixWord ++ tailWord_52320).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52320).length < 2 ^ (prefixWord ++ tailWord_52320).sum := by decide
  have hdescent : baseEnd_52320 < baseStart_52320 := by decide
  rcases family_descends (prefixWord ++ tailWord_52320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52375 : List Nat := [1, 1, 3, 3, 3, 3, 1, 4]
def baseStart_52375 : Nat := 118140960795 + 52375 * 2 ^ 59
def prefixEnd_52375 : Nat := 4983230072969 + 3 ^ 40 * 52375 * 2
def baseEnd_52375 : Nat := 15936918091459446679489

theorem tailTrace_52375 : CollatzResearch.WordTrace tailWord_52375 prefixEnd_52375 15936918091459446679489 := by
  unfold tailWord_52375
  simp only [CollatzResearch.WordTrace]
  refine ⟨1910273185261794782966579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1273515456841196521977719 1910273185261794782966579)
  ·
    refine ⟨2865409777892692174449869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1910273185261794782966579 2865409777892692174449869)
    ·
      refine ⟨1074528666709759565418701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2865409777892692174449869 1074528666709759565418701)
      ·
        refine ⟨402948250016159837032013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1074528666709759565418701 402948250016159837032013)
        ·
          refine ⟨151105593756059938887005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 402948250016159837032013 151105593756059938887005)
          ·
            refine ⟨56664597658522477082627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151105593756059938887005 56664597658522477082627)
            ·
              refine ⟨84996896487783715623941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56664597658522477082627 84996896487783715623941)
              ·
                refine ⟨15936918091459446679489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84996896487783715623941 15936918091459446679489)
                ·
                  rfl

theorem cell19_52375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 4].length) (baseStart_52375 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_52375 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_52375 prefixEnd_52375 := by exact prefixLift 52375
  have htrace : WordTrace (prefixWord ++ tailWord_52375) baseStart_52375 baseEnd_52375 := by
    simpa [prefixWord, tailWord_52375, baseEnd_52375] using wordTrace_append hprefix tailTrace_52375
  have hstable : (prefixWord ++ tailWord_52375).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52375).length < 2 ^ (prefixWord ++ tailWord_52375).sum := by decide
  have hdescent : baseEnd_52375 < baseStart_52375 := by decide
  rcases family_descends (prefixWord ++ tailWord_52375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52434 : List Nat := [3, 2, 2, 2, 1, 1, 2, 6]
def baseStart_52434 : Nat := 118140960795 + 52434 * 2 ^ 59
def prefixEnd_52434 : Nat := 4983230072969 + 3 ^ 40 * 52434 * 2
def baseEnd_52434 : Nat := 15954870896564791368217

theorem tailTrace_52434 : CollatzResearch.WordTrace tailWord_52434 prefixEnd_52434 15954870896564791368217 := by
  unfold tailWord_52434
  simp only [CollatzResearch.WordTrace]
  refine ⟨478106273012011964841089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1274950061365365239576237 478106273012011964841089)
  ·
    refine ⟨358579704759008973630817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 478106273012011964841089 358579704759008973630817)
    ·
      refine ⟨268934778569256730223113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358579704759008973630817 268934778569256730223113)
      ·
        refine ⟨201701083926942547667335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268934778569256730223113 201701083926942547667335)
        ·
          refine ⟨302551625890413821501003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201701083926942547667335 302551625890413821501003)
          ·
            refine ⟨453827438835620732251505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302551625890413821501003 453827438835620732251505)
            ·
              refine ⟨340370579126715549188629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 453827438835620732251505 340370579126715549188629)
              ·
                refine ⟨15954870896564791368217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 340370579126715549188629 15954870896564791368217)
                ·
                  rfl

theorem cell19_52434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_52434 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_52434 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_52434 prefixEnd_52434 := by exact prefixLift 52434
  have htrace : WordTrace (prefixWord ++ tailWord_52434) baseStart_52434 baseEnd_52434 := by
    simpa [prefixWord, tailWord_52434, baseEnd_52434] using wordTrace_append hprefix tailTrace_52434
  have hstable : (prefixWord ++ tailWord_52434).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52434).length < 2 ^ (prefixWord ++ tailWord_52434).sum := by decide
  have hdescent : baseEnd_52434 < baseStart_52434 := by decide
  rcases family_descends (prefixWord ++ tailWord_52434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52491 : List Nat := [1, 1, 1, 1, 5, 4, 2, 4]
def baseStart_52491 : Nat := 118140960795 + 52491 * 2 ^ 59
def prefixEnd_52491 : Nat := 4983230072969 + 3 ^ 40 * 52491 * 2
def baseEnd_52491 : Nat := 15972215132005548101395

theorem tailTrace_52491 : CollatzResearch.WordTrace tailWord_52491 prefixEnd_52491 15972215132005548101395 := by
  unfold tailWord_52491
  simp only [CollatzResearch.WordTrace]
  refine ⟨1914504052841546594189327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1276336035227697729459551 1914504052841546594189327)
  ·
    refine ⟨2871756079262319891283991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1914504052841546594189327 2871756079262319891283991)
    ·
      refine ⟨4307634118893479836925987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2871756079262319891283991 4307634118893479836925987)
      ·
        refine ⟨6461451178340219755388981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4307634118893479836925987 6461451178340219755388981)
        ·
          refine ⟨605761047969395602067717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6461451178340219755388981 605761047969395602067717)
          ·
            refine ⟨113580196494261675387697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 605761047969395602067717 113580196494261675387697)
            ·
              refine ⟨85185147370696256540773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113580196494261675387697 85185147370696256540773)
              ·
                refine ⟨15972215132005548101395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85185147370696256540773 15972215132005548101395)
                ·
                  rfl

theorem cell19_52491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 4].length) (baseStart_52491 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_52491 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_52491 prefixEnd_52491 := by exact prefixLift 52491
  have htrace : WordTrace (prefixWord ++ tailWord_52491) baseStart_52491 baseEnd_52491 := by
    simpa [prefixWord, tailWord_52491, baseEnd_52491] using wordTrace_append hprefix tailTrace_52491
  have hstable : (prefixWord ++ tailWord_52491).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52491).length < 2 ^ (prefixWord ++ tailWord_52491).sum := by decide
  have hdescent : baseEnd_52491 < baseStart_52491 := by decide
  rcases family_descends (prefixWord ++ tailWord_52491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52531 : List Nat := [1, 1, 1, 2, 5, 9]
def baseStart_52531 : Nat := 118140960795 + 52531 * 2 ^ 59
def prefixEnd_52531 : Nat := 4983230072969 + 3 ^ 40 * 52531 * 2
def baseEnd_52531 : Nat := 1776042947255256356933

theorem tailTrace_52531 : CollatzResearch.WordTrace tailWord_52531 prefixEnd_52531 1776042947255256356933 := by
  unfold tailWord_52531
  simp only [CollatzResearch.WordTrace]
  refine ⟨1915962972696633425645447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1277308648464422283763631 1915962972696633425645447)
  ·
    refine ⟨2873944459044950138468171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1915962972696633425645447 2873944459044950138468171)
    ·
      refine ⟨4310916688567425207702257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2873944459044950138468171 4310916688567425207702257)
      ·
        refine ⟨3233187516425568905776693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4310916688567425207702257 3233187516425568905776693)
        ·
          refine ⟨303111329664897084916565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3233187516425568905776693 303111329664897084916565)
          ·
            refine ⟨1776042947255256356933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 303111329664897084916565 1776042947255256356933)
            ·
              rfl

theorem cell19_52531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 9].length) (baseStart_52531 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_52531 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_52531 prefixEnd_52531 := by exact prefixLift 52531
  have htrace : WordTrace (prefixWord ++ tailWord_52531) baseStart_52531 baseEnd_52531 := by
    simpa [prefixWord, tailWord_52531, baseEnd_52531] using wordTrace_append hprefix tailTrace_52531
  have hstable : (prefixWord ++ tailWord_52531).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52531).length < 2 ^ (prefixWord ++ tailWord_52531).sum := by decide
  have hdescent : baseEnd_52531 < baseStart_52531 := by decide
  rcases family_descends (prefixWord ++ tailWord_52531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52565 : List Nat := [1, 3, 2, 2, 3, 2, 3, 3]
def baseStart_52565 : Nat := 118140960795 + 52565 * 2 ^ 59
def prefixEnd_52565 : Nat := 4983230072969 + 3 ^ 40 * 52565 * 2
def baseEnd_52565 : Nat := 15994732209595302456749

theorem tailTrace_52565 : CollatzResearch.WordTrace tailWord_52565 prefixEnd_52565 15994732209595302456749 := by
  unfold tailWord_52565
  simp only [CollatzResearch.WordTrace]
  refine ⟨1917203054573457232383149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1278135369715638154922099 1917203054573457232383149)
  ·
    refine ⟨718951145465046462143681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1917203054573457232383149 718951145465046462143681)
    ·
      refine ⟨539213359098784846607761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 718951145465046462143681 539213359098784846607761)
      ·
        refine ⟨404410019324088634955821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 539213359098784846607761 404410019324088634955821)
        ·
          refine ⟨151653757246533238108433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 404410019324088634955821 151653757246533238108433)
          ·
            refine ⟨113740317934899928581325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151653757246533238108433 113740317934899928581325)
            ·
              refine ⟨42652619225587473217997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113740317934899928581325 42652619225587473217997)
              ·
                refine ⟨15994732209595302456749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42652619225587473217997 15994732209595302456749)
                ·
                  rfl

theorem cell19_52565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 3].length) (baseStart_52565 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_52565 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_52565 prefixEnd_52565 := by exact prefixLift 52565
  have htrace : WordTrace (prefixWord ++ tailWord_52565) baseStart_52565 baseEnd_52565 := by
    simpa [prefixWord, tailWord_52565, baseEnd_52565] using wordTrace_append hprefix tailTrace_52565
  have hstable : (prefixWord ++ tailWord_52565).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52565).length < 2 ^ (prefixWord ++ tailWord_52565).sum := by decide
  have hdescent : baseEnd_52565 < baseStart_52565 := by decide
  rcases family_descends (prefixWord ++ tailWord_52565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52569 : List Nat := [1, 2, 1, 2, 2, 2, 2, 7]
def baseStart_52569 : Nat := 118140960795 + 52569 * 2 ^ 59
def prefixEnd_52569 : Nat := 4983230072969 + 3 ^ 40 * 52569 * 2
def baseEnd_52569 : Nat := 15995949348924478367849

theorem tailTrace_52569 : CollatzResearch.WordTrace tailWord_52569 prefixEnd_52569 15995949348924478367849 := by
  unfold tailWord_52569
  simp only [CollatzResearch.WordTrace]
  refine ⟨1917348946558965915528761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1278232631039310610352507 1917348946558965915528761)
  ·
    refine ⟨1438011709919224436646571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1917348946558965915528761 1438011709919224436646571)
    ·
      refine ⟨2157017564878836654969857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1438011709919224436646571 2157017564878836654969857)
      ·
        refine ⟨1617763173659127491227393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2157017564878836654969857 1617763173659127491227393)
        ·
          refine ⟨1213322380244345618420545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1617763173659127491227393 1213322380244345618420545)
          ·
            refine ⟨909991785183259213815409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1213322380244345618420545 909991785183259213815409)
            ·
              refine ⟨682493838887444410361557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 909991785183259213815409 682493838887444410361557)
              ·
                refine ⟨15995949348924478367849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 682493838887444410361557 15995949348924478367849)
                ·
                  rfl

theorem cell19_52569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 7].length) (baseStart_52569 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_52569 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_52569 prefixEnd_52569 := by exact prefixLift 52569
  have htrace : WordTrace (prefixWord ++ tailWord_52569) baseStart_52569 baseEnd_52569 := by
    simpa [prefixWord, tailWord_52569, baseEnd_52569] using wordTrace_append hprefix tailTrace_52569
  have hstable : (prefixWord ++ tailWord_52569).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52569).length < 2 ^ (prefixWord ++ tailWord_52569).sum := by decide
  have hdescent : baseEnd_52569 < baseStart_52569 := by decide
  rcases family_descends (prefixWord ++ tailWord_52569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52622 : List Nat := [4, 1, 1, 4, 2, 1, 1, 5]
def baseStart_52622 : Nat := 118140960795 + 52622 * 2 ^ 59
def prefixEnd_52622 : Nat := 4983230072969 + 3 ^ 40 * 52622 * 2
def baseEnd_52622 : Nat := 16012076445036059189927

theorem tailTrace_52622 : CollatzResearch.WordTrace tailWord_52622 prefixEnd_52622 16012076445036059189927 := by
  unfold tailWord_52622
  simp only [CollatzResearch.WordTrace]
  refine ⟨239910251920869495901015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1279521343577970644805413 239910251920869495901015)
  ·
    refine ⟨359865377881304243851523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239910251920869495901015 359865377881304243851523)
    ·
      refine ⟨539798066821956365777285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359865377881304243851523 539798066821956365777285)
      ·
        refine ⟨101212137529116818583241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 539798066821956365777285 101212137529116818583241)
        ·
          refine ⟨75909103146837613937431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101212137529116818583241 75909103146837613937431)
          ·
            refine ⟨113863654720256420906147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75909103146837613937431 113863654720256420906147)
            ·
              refine ⟨170795482080384631359221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113863654720256420906147 170795482080384631359221)
              ·
                refine ⟨16012076445036059189927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 170795482080384631359221 16012076445036059189927)
                ·
                  rfl

theorem cell19_52622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_52622 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_52622 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_52622 prefixEnd_52622 := by exact prefixLift 52622
  have htrace : WordTrace (prefixWord ++ tailWord_52622) baseStart_52622 baseEnd_52622 := by
    simpa [prefixWord, tailWord_52622, baseEnd_52622] using wordTrace_append hprefix tailTrace_52622
  have hstable : (prefixWord ++ tailWord_52622).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52622).length < 2 ^ (prefixWord ++ tailWord_52622).sum := by decide
  have hdescent : baseEnd_52622 < baseStart_52622 := by decide
  rcases family_descends (prefixWord ++ tailWord_52622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52664 : List Nat := [2, 1, 2, 1, 2, 2, 3, 6]
def baseStart_52664 : Nat := 118140960795 + 52664 * 2 ^ 59
def prefixEnd_52664 : Nat := 4983230072969 + 3 ^ 40 * 52664 * 2
def baseEnd_52664 : Nat := 16024856407992406256479

theorem tailTrace_52664 : CollatzResearch.WordTrace tailWord_52664 prefixEnd_52664 16024856407992406256479 := by
  unfold tailWord_52664
  simp only [CollatzResearch.WordTrace]
  refine ⟨960406940607398570118523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1280542587476531426824697 960406940607398570118523)
  ·
    refine ⟨1440610410911097855177785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 960406940607398570118523 1440610410911097855177785)
    ·
      refine ⟨1080457808183323391383339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1440610410911097855177785 1080457808183323391383339)
      ·
        refine ⟨1620686712274985087075009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1080457808183323391383339 1620686712274985087075009)
        ·
          refine ⟨1215515034206238815306257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1620686712274985087075009 1215515034206238815306257)
          ·
            refine ⟨911636275654679111479693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1215515034206238815306257 911636275654679111479693)
            ·
              refine ⟨341863603370504666804885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 911636275654679111479693 341863603370504666804885)
              ·
                refine ⟨16024856407992406256479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 341863603370504666804885 16024856407992406256479)
                ·
                  rfl

theorem cell19_52664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_52664 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_52664 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_52664 prefixEnd_52664 := by exact prefixLift 52664
  have htrace : WordTrace (prefixWord ++ tailWord_52664) baseStart_52664 baseEnd_52664 := by
    simpa [prefixWord, tailWord_52664, baseEnd_52664] using wordTrace_append hprefix tailTrace_52664
  have hstable : (prefixWord ++ tailWord_52664).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52664).length < 2 ^ (prefixWord ++ tailWord_52664).sum := by decide
  have hdescent : baseEnd_52664 < baseStart_52664 := by decide
  rcases family_descends (prefixWord ++ tailWord_52664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52683 : List Nat := [1, 1, 1, 1, 3, 3, 4, 5]
def baseStart_52683 : Nat := 118140960795 + 52683 * 2 ^ 59
def prefixEnd_52683 : Nat := 4983230072969 + 3 ^ 40 * 52683 * 2
def baseEnd_52683 : Nat := 16030637819805991834205

theorem tailTrace_52683 : CollatzResearch.WordTrace tailWord_52683 prefixEnd_52683 16030637819805991834205 := by
  unfold tailWord_52683
  simp only [CollatzResearch.WordTrace]
  refine ⟨1921506868145963385178703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1281004578763975590119135 1921506868145963385178703)
  ·
    refine ⟨2882260302218945077768055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1921506868145963385178703 2882260302218945077768055)
    ·
      refine ⟨4323390453328417616652083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2882260302218945077768055 4323390453328417616652083)
      ·
        refine ⟨6485085679992626424978125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4323390453328417616652083 6485085679992626424978125)
        ·
          refine ⟨2431907129997234909366797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6485085679992626424978125 2431907129997234909366797)
          ·
            refine ⟨911965173748963091012549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2431907129997234909366797 911965173748963091012549)
            ·
              refine ⟨170993470077930579564853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 911965173748963091012549 170993470077930579564853)
              ·
                refine ⟨16030637819805991834205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 170993470077930579564853 16030637819805991834205)
                ·
                  rfl

theorem cell19_52683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 5].length) (baseStart_52683 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_52683 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_52683 prefixEnd_52683 := by exact prefixLift 52683
  have htrace : WordTrace (prefixWord ++ tailWord_52683) baseStart_52683 baseEnd_52683 := by
    simpa [prefixWord, tailWord_52683, baseEnd_52683] using wordTrace_append hprefix tailTrace_52683
  have hstable : (prefixWord ++ tailWord_52683).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52683).length < 2 ^ (prefixWord ++ tailWord_52683).sum := by decide
  have hdescent : baseEnd_52683 < baseStart_52683 := by decide
  rcases family_descends (prefixWord ++ tailWord_52683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52793 : List Nat := [1, 2, 1, 5, 1, 4, 2, 3]
def baseStart_52793 : Nat := 118140960795 + 52793 * 2 ^ 59
def prefixEnd_52793 : Nat := 4983230072969 + 3 ^ 40 * 52793 * 2
def baseEnd_52793 : Nat := 16064109151358329389461

theorem tailTrace_52793 : CollatzResearch.WordTrace tailWord_52793 prefixEnd_52793 16064109151358329389461 := by
  unfold tailWord_52793
  simp only [CollatzResearch.WordTrace]
  refine ⟨1925518897747452171683033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1283679265164968114455355 1925518897747452171683033)
  ·
    refine ⟨1444139173310589128762275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1925518897747452171683033 1444139173310589128762275)
    ·
      refine ⟨2166208759965883693143413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1444139173310589128762275 2166208759965883693143413)
      ·
        refine ⟨203082071246801596232195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2166208759965883693143413 203082071246801596232195)
        ·
          refine ⟨304623106870202394348293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203082071246801596232195 304623106870202394348293)
          ·
            refine ⟨57116832538162948940305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 304623106870202394348293 57116832538162948940305)
            ·
              refine ⟨42837624403622211705229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57116832538162948940305 42837624403622211705229)
              ·
                refine ⟨16064109151358329389461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42837624403622211705229 16064109151358329389461)
                ·
                  rfl

theorem cell19_52793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 3].length) (baseStart_52793 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_52793 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_52793 prefixEnd_52793 := by exact prefixLift 52793
  have htrace : WordTrace (prefixWord ++ tailWord_52793) baseStart_52793 baseEnd_52793 := by
    simpa [prefixWord, tailWord_52793, baseEnd_52793] using wordTrace_append hprefix tailTrace_52793
  have hstable : (prefixWord ++ tailWord_52793).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52793).length < 2 ^ (prefixWord ++ tailWord_52793).sum := by decide
  have hdescent : baseEnd_52793 < baseStart_52793 := by decide
  rcases family_descends (prefixWord ++ tailWord_52793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52829 : List Nat := [1, 4, 4, 2, 1, 1, 2, 4]
def baseStart_52829 : Nat := 118140960795 + 52829 * 2 ^ 59
def prefixEnd_52829 : Nat := 4983230072969 + 3 ^ 40 * 52829 * 2
def baseEnd_52829 : Nat := 16075063405320912589363

theorem tailTrace_52829 : CollatzResearch.WordTrace tailWord_52829 prefixEnd_52829 16075063405320912589363 := by
  unfold tailWord_52829
  simp only [CollatzResearch.WordTrace]
  refine ⟨1926831925617030319993541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1284554617078020213329027 1926831925617030319993541)
  ·
    refine ⟨361280986053193184998789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1926831925617030319993541 361280986053193184998789)
    ·
      refine ⟨67740184884973722187273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 361280986053193184998789 67740184884973722187273)
      ·
        refine ⟨50805138663730291640455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67740184884973722187273 50805138663730291640455)
        ·
          refine ⟨76207707995595437460683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50805138663730291640455 76207707995595437460683)
          ·
            refine ⟨114311561993393156191025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76207707995595437460683 114311561993393156191025)
            ·
              refine ⟨85733671495044867143269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114311561993393156191025 85733671495044867143269)
              ·
                refine ⟨16075063405320912589363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85733671495044867143269 16075063405320912589363)
                ·
                  rfl

theorem cell19_52829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 4].length) (baseStart_52829 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_52829 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_52829 prefixEnd_52829 := by exact prefixLift 52829
  have htrace : WordTrace (prefixWord ++ tailWord_52829) baseStart_52829 baseEnd_52829 := by
    simpa [prefixWord, tailWord_52829, baseEnd_52829] using wordTrace_append hprefix tailTrace_52829
  have hstable : (prefixWord ++ tailWord_52829).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52829).length < 2 ^ (prefixWord ++ tailWord_52829).sum := by decide
  have hdescent : baseEnd_52829 < baseStart_52829 := by decide
  rcases family_descends (prefixWord ++ tailWord_52829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52835 : List Nat := [1, 1, 1, 5, 1, 3, 1, 6]
def baseStart_52835 : Nat := 118140960795 + 52835 * 2 ^ 59
def prefixEnd_52835 : Nat := 4983230072969 + 3 ^ 40 * 52835 * 2
def baseEnd_52835 : Nat := 16076889114314676456013

theorem tailTrace_52835 : CollatzResearch.WordTrace tailWord_52835 prefixEnd_52835 16076889114314676456013 := by
  unfold tailWord_52835
  simp only [CollatzResearch.WordTrace]
  refine ⟨1927050763595293344711959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1284700509063528896474639 1927050763595293344711959)
  ·
    refine ⟨2890576145392940017067939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1927050763595293344711959 2890576145392940017067939)
    ·
      refine ⟨4335864218089410025601909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2890576145392940017067939 4335864218089410025601909)
      ·
        refine ⟨406487270445882189900179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4335864218089410025601909 406487270445882189900179)
        ·
          refine ⟨609730905668823284850269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406487270445882189900179 609730905668823284850269)
          ·
            refine ⟨228649089625808731818851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 609730905668823284850269 228649089625808731818851)
            ·
              refine ⟨342973634438713097728277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228649089625808731818851 342973634438713097728277)
              ·
                refine ⟨16076889114314676456013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 342973634438713097728277 16076889114314676456013)
                ·
                  rfl

theorem cell19_52835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 6].length) (baseStart_52835 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_52835 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_52835 prefixEnd_52835 := by exact prefixLift 52835
  have htrace : WordTrace (prefixWord ++ tailWord_52835) baseStart_52835 baseEnd_52835 := by
    simpa [prefixWord, tailWord_52835, baseEnd_52835] using wordTrace_append hprefix tailTrace_52835
  have hstable : (prefixWord ++ tailWord_52835).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52835).length < 2 ^ (prefixWord ++ tailWord_52835).sum := by decide
  have hdescent : baseEnd_52835 < baseStart_52835 := by decide
  rcases family_descends (prefixWord ++ tailWord_52835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53006 : List Nat := [4, 1, 1, 2, 1, 1, 3, 6]
def baseStart_53006 : Nat := 118140960795 + 53006 * 2 ^ 59
def prefixEnd_53006 : Nat := 4983230072969 + 3 ^ 40 * 53006 * 2
def baseEnd_53006 : Nat := 16128921820636946655547

theorem tailTrace_53006 : CollatzResearch.WordTrace tailWord_53006 prefixEnd_53006 16128921820636946655547 := by
  unfold tailWord_53006
  simp only [CollatzResearch.WordTrace]
  refine ⟨241660955746973693648359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1288858430650526366124581 241660955746973693648359)
  ·
    refine ⟨362491433620460540472539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241660955746973693648359 362491433620460540472539)
    ·
      refine ⟨543737150430690810708809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362491433620460540472539 543737150430690810708809)
      ·
        refine ⟨407802862823018108031607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 543737150430690810708809 407802862823018108031607)
        ·
          refine ⟨611704294234527162047411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407802862823018108031607 611704294234527162047411)
          ·
            refine ⟨917556441351790743071117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611704294234527162047411 917556441351790743071117)
            ·
              refine ⟨344083665506921528651669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 917556441351790743071117 344083665506921528651669)
              ·
                refine ⟨16128921820636946655547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 344083665506921528651669 16128921820636946655547)
                ·
                  rfl

theorem cell19_53006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_53006 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_53006 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_53006 prefixEnd_53006 := by exact prefixLift 53006
  have htrace : WordTrace (prefixWord ++ tailWord_53006) baseStart_53006 baseEnd_53006 := by
    simpa [prefixWord, tailWord_53006, baseEnd_53006] using wordTrace_append hprefix tailTrace_53006
  have hstable : (prefixWord ++ tailWord_53006).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53006).length < 2 ^ (prefixWord ++ tailWord_53006).sum := by decide
  have hdescent : baseEnd_53006 < baseStart_53006 := by decide
  rcases family_descends (prefixWord ++ tailWord_53006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53025 : List Nat := [1, 2, 3, 2, 1, 3, 2, 5]
def baseStart_53025 : Nat := 118140960795 + 53025 * 2 ^ 59
def prefixEnd_53025 : Nat := 4983230072969 + 3 ^ 40 * 53025 * 2
def baseEnd_53025 : Nat := 16134703232450532233273

theorem tailTrace_53025 : CollatzResearch.WordTrace tailWord_53025 prefixEnd_53025 16134703232450532233273 := by
  unfold tailWord_53025
  simp only [CollatzResearch.WordTrace]
  refine ⟨1933980632906955794128529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1289320421937970529419019 1933980632906955794128529)
  ·
    refine ⟨1450485474680216845596397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1933980632906955794128529 1450485474680216845596397)
    ·
      refine ⟨543932053005081317098649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1450485474680216845596397 543932053005081317098649)
      ·
        refine ⟨407949039753810987823987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 543932053005081317098649 407949039753810987823987)
        ·
          refine ⟨611923559630716481735981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407949039753810987823987 611923559630716481735981)
          ·
            refine ⟨229471334861518680650993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 611923559630716481735981 229471334861518680650993)
            ·
              refine ⟨172103501146139010488245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229471334861518680650993 172103501146139010488245)
              ·
                refine ⟨16134703232450532233273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 172103501146139010488245 16134703232450532233273)
                ·
                  rfl

theorem cell19_53025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 5].length) (baseStart_53025 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_53025 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_53025 prefixEnd_53025 := by exact prefixLift 53025
  have htrace : WordTrace (prefixWord ++ tailWord_53025) baseStart_53025 baseEnd_53025 := by
    simpa [prefixWord, tailWord_53025, baseEnd_53025] using wordTrace_append hprefix tailTrace_53025
  have hstable : (prefixWord ++ tailWord_53025).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53025).length < 2 ^ (prefixWord ++ tailWord_53025).sum := by decide
  have hdescent : baseEnd_53025 < baseStart_53025 := by decide
  rcases family_descends (prefixWord ++ tailWord_53025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53063 : List Nat := [1, 1, 4, 1, 2, 1, 5, 4]
def baseStart_53063 : Nat := 118140960795 + 53063 * 2 ^ 59
def prefixEnd_53063 : Nat := 4983230072969 + 3 ^ 40 * 53063 * 2
def baseEnd_53063 : Nat := 16146266056077703388725

theorem tailTrace_53063 : CollatzResearch.WordTrace tailWord_53063 prefixEnd_53063 16146266056077703388725 := by
  unfold tailWord_53063
  simp only [CollatzResearch.WordTrace]
  refine ⟨1935366606769288284011843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1290244404512858856007895 1935366606769288284011843)
  ·
    refine ⟨2903049910153932426017765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1935366606769288284011843 2903049910153932426017765)
    ·
      refine ⟨544321858153862329878331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2903049910153932426017765 544321858153862329878331)
      ·
        refine ⟨816482787230793494817497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 544321858153862329878331 816482787230793494817497)
        ·
          refine ⟨612362090423095121113123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 816482787230793494817497 612362090423095121113123)
          ·
            refine ⟨918543135634642681669685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612362090423095121113123 918543135634642681669685)
            ·
              refine ⟨86113418965747751406533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 918543135634642681669685 86113418965747751406533)
              ·
                refine ⟨16146266056077703388725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86113418965747751406533 16146266056077703388725)
                ·
                  rfl

theorem cell19_53063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 4].length) (baseStart_53063 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_53063 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_53063 prefixEnd_53063 := by exact prefixLift 53063
  have htrace : WordTrace (prefixWord ++ tailWord_53063) baseStart_53063 baseEnd_53063 := by
    simpa [prefixWord, tailWord_53063, baseEnd_53063] using wordTrace_append hprefix tailTrace_53063
  have hstable : (prefixWord ++ tailWord_53063).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53063).length < 2 ^ (prefixWord ++ tailWord_53063).sum := by decide
  have hdescent : baseEnd_53063 < baseStart_53063 := by decide
  rcases family_descends (prefixWord ++ tailWord_53063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53154 : List Nat := [3, 3, 1, 2, 4, 1, 5]
def baseStart_53154 : Nat := 118140960795 + 53154 * 2 ^ 59
def prefixEnd_53154 : Nat := 4983230072969 + 3 ^ 40 * 53154 * 2
def baseEnd_53154 : Nat := 5391318658605485122085

theorem tailTrace_53154 : CollatzResearch.WordTrace tailWord_53154 prefixEnd_53154 5391318658605485122085 := by
  unfold tailWord_53154
  simp only [CollatzResearch.WordTrace]
  refine ⟨484671412359902706393629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1292457099626407217049677 484671412359902706393629)
  ·
    refine ⟨181751779634963514897611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 484671412359902706393629 181751779634963514897611)
    ·
      refine ⟨272627669452445272346417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181751779634963514897611 272627669452445272346417)
      ·
        refine ⟨204470752089333954259813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272627669452445272346417 204470752089333954259813)
        ·
          refine ⟨38338266016750116423715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204470752089333954259813 38338266016750116423715)
          ·
            refine ⟨57507399025125174635573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38338266016750116423715 57507399025125174635573)
            ·
              refine ⟨5391318658605485122085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57507399025125174635573 5391318658605485122085)
              ·
                rfl

theorem cell19_53154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 5].length) (baseStart_53154 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_53154 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_53154 prefixEnd_53154 := by exact prefixLift 53154
  have htrace : WordTrace (prefixWord ++ tailWord_53154) baseStart_53154 baseEnd_53154 := by
    simpa [prefixWord, tailWord_53154, baseEnd_53154] using wordTrace_append hprefix tailTrace_53154
  have hstable : (prefixWord ++ tailWord_53154).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53154).length < 2 ^ (prefixWord ++ tailWord_53154).sum := by decide
  have hdescent : baseEnd_53154 < baseStart_53154 := by decide
  rcases family_descends (prefixWord ++ tailWord_53154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53177 : List Nat := [1, 2, 1, 4, 2, 1, 4, 4]
def baseStart_53177 : Nat := 118140960795 + 53177 * 2 ^ 59
def prefixEnd_53177 : Nat := 4983230072969 + 3 ^ 40 * 53177 * 2
def baseEnd_53177 : Nat := 16180954526959216855081

theorem tailTrace_53177 : CollatzResearch.WordTrace tailWord_53177 prefixEnd_53177 16180954526959216855081 := by
  unfold tailWord_53177
  simp only [CollatzResearch.WordTrace]
  refine ⟨1939524528356285753661785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1293016352237523835774523 1939524528356285753661785)
  ·
    refine ⟨1454643396267214315246339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1939524528356285753661785 1454643396267214315246339)
    ·
      refine ⟨2181965094400821472869509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1454643396267214315246339 2181965094400821472869509)
      ·
        refine ⟨409118455200154026163033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2181965094400821472869509 409118455200154026163033)
        ·
          refine ⟨306838841400115519622275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409118455200154026163033 306838841400115519622275)
          ·
            refine ⟨460258262100173279433413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306838841400115519622275 460258262100173279433413)
            ·
              refine ⟨86298424143782489893765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 460258262100173279433413 86298424143782489893765)
              ·
                refine ⟨16180954526959216855081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86298424143782489893765 16180954526959216855081)
                ·
                  rfl

theorem cell19_53177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 4].length) (baseStart_53177 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_53177 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_53177 prefixEnd_53177 := by exact prefixLift 53177
  have htrace : WordTrace (prefixWord ++ tailWord_53177) baseStart_53177 baseEnd_53177 := by
    simpa [prefixWord, tailWord_53177, baseEnd_53177] using wordTrace_append hprefix tailTrace_53177
  have hstable : (prefixWord ++ tailWord_53177).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53177).length < 2 ^ (prefixWord ++ tailWord_53177).sum := by decide
  have hdescent : baseEnd_53177 < baseStart_53177 := by decide
  rcases family_descends (prefixWord ++ tailWord_53177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53179 : List Nat := [1, 1, 1, 1, 1, 2, 2, 10]
def baseStart_53179 : Nat := 118140960795 + 53179 * 2 ^ 59
def prefixEnd_53179 : Nat := 4983230072969 + 3 ^ 40 * 53179 * 2
def baseEnd_53179 : Nat := 16181563096623804810631

theorem tailTrace_53179 : CollatzResearch.WordTrace tailWord_53179 prefixEnd_53179 16181563096623804810631 := by
  unfold tailWord_53179
  simp only [CollatzResearch.WordTrace]
  refine ⟨1939597474349040095234591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1293064982899360063489727 1939597474349040095234591)
  ·
    refine ⟨2909396211523560142851887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1939597474349040095234591 2909396211523560142851887)
    ·
      refine ⟨4364094317285340214277831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2909396211523560142851887 4364094317285340214277831)
      ·
        refine ⟨6546141475928010321416747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4364094317285340214277831 6546141475928010321416747)
        ·
          refine ⟨9819212213892015482125121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6546141475928010321416747 9819212213892015482125121)
          ·
            refine ⟨7364409160419011611593841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9819212213892015482125121 7364409160419011611593841)
            ·
              refine ⟨5523306870314258708695381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7364409160419011611593841 5523306870314258708695381)
              ·
                refine ⟨16181563096623804810631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 5523306870314258708695381 16181563096623804810631)
                ·
                  rfl

theorem cell19_53179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 10].length) (baseStart_53179 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_53179 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_53179 prefixEnd_53179 := by exact prefixLift 53179
  have htrace : WordTrace (prefixWord ++ tailWord_53179) baseStart_53179 baseEnd_53179 := by
    simpa [prefixWord, tailWord_53179, baseEnd_53179] using wordTrace_append hprefix tailTrace_53179
  have hstable : (prefixWord ++ tailWord_53179).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53179).length < 2 ^ (prefixWord ++ tailWord_53179).sum := by decide
  have hdescent : baseEnd_53179 < baseStart_53179 := by decide
  rcases family_descends (prefixWord ++ tailWord_53179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53196 : List Nat := [2, 2, 1, 4, 1, 2, 2, 5]
def baseStart_53196 : Nat := 118140960795 + 53196 * 2 ^ 59
def prefixEnd_53196 : Nat := 4983230072969 + 3 ^ 40 * 53196 * 2
def baseEnd_53196 : Nat := 16186735938772802432807

theorem tailTrace_53196 : CollatzResearch.WordTrace tailWord_53196 prefixEnd_53196 16186735938772802432807 := by
  unfold tailWord_53196
  simp only [CollatzResearch.WordTrace]
  refine ⟨970108757643725999301721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1293478343524967999068961 970108757643725999301721)
  ·
    refine ⟨727581568232794499476291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 970108757643725999301721 727581568232794499476291)
    ·
      refine ⟨1091372352349191749214437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 727581568232794499476291 1091372352349191749214437)
      ·
        refine ⟨204632316065473452977707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1091372352349191749214437 204632316065473452977707)
        ·
          refine ⟨306948474098210179466561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204632316065473452977707 306948474098210179466561)
          ·
            refine ⟨230211355573657634599921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306948474098210179466561 230211355573657634599921)
            ·
              refine ⟨172658516680243225949941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230211355573657634599921 172658516680243225949941)
              ·
                refine ⟨16186735938772802432807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 172658516680243225949941 16186735938772802432807)
                ·
                  rfl

theorem cell19_53196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_53196 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_53196 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_53196 prefixEnd_53196 := by exact prefixLift 53196
  have htrace : WordTrace (prefixWord ++ tailWord_53196) baseStart_53196 baseEnd_53196 := by
    simpa [prefixWord, tailWord_53196, baseEnd_53196] using wordTrace_append hprefix tailTrace_53196
  have hstable : (prefixWord ++ tailWord_53196).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53196).length < 2 ^ (prefixWord ++ tailWord_53196).sum := by decide
  have hdescent : baseEnd_53196 < baseStart_53196 := by decide
  rcases family_descends (prefixWord ++ tailWord_53196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53213 : List Nat := [1, 4, 3, 1, 4, 6]
def baseStart_53213 : Nat := 118140960795 + 53213 * 2 ^ 59
def prefixEnd_53213 : Nat := 4983230072969 + 3 ^ 40 * 53213 * 2
def baseEnd_53213 : Nat := 1799100975657977783887

theorem tailTrace_53213 : CollatzResearch.WordTrace tailWord_53213 prefixEnd_53213 1799100975657977783887 := by
  unfold tailWord_53213
  simp only [CollatzResearch.WordTrace]
  refine ⟨1940837556225863901972293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1293891704150575934648195 1940837556225863901972293)
  ·
    refine ⟨363907041792349481619805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1940837556225863901972293 363907041792349481619805)
    ·
      refine ⟨136465140672131055607427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 363907041792349481619805 136465140672131055607427)
      ·
        refine ⟨204697711008196583411141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136465140672131055607427 204697711008196583411141)
        ·
          refine ⟨38380820814036859389589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204697711008196583411141 38380820814036859389589)
          ·
            refine ⟨1799100975657977783887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 38380820814036859389589 1799100975657977783887)
            ·
              rfl

theorem cell19_53213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 6].length) (baseStart_53213 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_53213 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_53213 prefixEnd_53213 := by exact prefixLift 53213
  have htrace : WordTrace (prefixWord ++ tailWord_53213) baseStart_53213 baseEnd_53213 := by
    simpa [prefixWord, tailWord_53213, baseEnd_53213] using wordTrace_append hprefix tailTrace_53213
  have hstable : (prefixWord ++ tailWord_53213).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53213).length < 2 ^ (prefixWord ++ tailWord_53213).sum := by decide
  have hdescent : baseEnd_53213 < baseStart_53213 := by decide
  rcases family_descends (prefixWord ++ tailWord_53213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53268 : List Nat := [2, 4, 3, 2, 1, 1, 6]
def baseStart_53268 : Nat := 118140960795 + 53268 * 2 ^ 59
def prefixEnd_53268 : Nat := 4983230072969 + 3 ^ 40 * 53268 * 2
def baseEnd_53268 : Nat := 5402881482232656277537

theorem tailTrace_53268 : CollatzResearch.WordTrace tailWord_53268 prefixEnd_53268 5402881482232656277537 := by
  unfold tailWord_53268
  simp only [CollatzResearch.WordTrace]
  refine ⟨971421785513304147612229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1295229047351072196816305 971421785513304147612229)
  ·
    refine ⟨182141584783744527677293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 971421785513304147612229 182141584783744527677293)
    ·
      refine ⟨68303094293904197878985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182141584783744527677293 68303094293904197878985)
      ·
        refine ⟨51227320720428148409239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68303094293904197878985 51227320720428148409239)
        ·
          refine ⟨76840981080642222613859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51227320720428148409239 76840981080642222613859)
          ·
            refine ⟨115261471620963333920789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76840981080642222613859 115261471620963333920789)
            ·
              refine ⟨5402881482232656277537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 115261471620963333920789 5402881482232656277537)
              ·
                rfl

theorem cell19_53268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 6].length) (baseStart_53268 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_53268 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_53268 prefixEnd_53268 := by exact prefixLift 53268
  have htrace : WordTrace (prefixWord ++ tailWord_53268) baseStart_53268 baseEnd_53268 := by
    simpa [prefixWord, tailWord_53268, baseEnd_53268] using wordTrace_append hprefix tailTrace_53268
  have hstable : (prefixWord ++ tailWord_53268).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53268).length < 2 ^ (prefixWord ++ tailWord_53268).sum := by decide
  have hdescent : baseEnd_53268 < baseStart_53268 := by decide
  rcases family_descends (prefixWord ++ tailWord_53268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53342 : List Nat := [4, 4, 1, 1, 2, 1, 2, 4]
def baseStart_53342 : Nat := 118140960795 + 53342 * 2 ^ 59
def prefixEnd_53342 : Nat := 4983230072969 + 3 ^ 40 * 53342 * 2
def baseEnd_53342 : Nat := 16231161524287723187965

theorem tailTrace_53342 : CollatzResearch.WordTrace tailWord_53342 prefixEnd_53342 16231161524287723187965 := by
  unfold tailWord_53342
  simp only [CollatzResearch.WordTrace]
  refine ⟨243192821594814866677285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1297028381839012622278853 243192821594814866677285)
  ·
    refine ⟨45598654049027787501991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243192821594814866677285 45598654049027787501991)
    ·
      refine ⟨68397981073541681252987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45598654049027787501991 68397981073541681252987)
      ·
        refine ⟨102596971610312521879481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68397981073541681252987 102596971610312521879481)
        ·
          refine ⟨76947728707734391409611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102596971610312521879481 76947728707734391409611)
          ·
            refine ⟨115421593061601587114417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76947728707734391409611 115421593061601587114417)
            ·
              refine ⟨86566194796201190335813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115421593061601587114417 86566194796201190335813)
              ·
                refine ⟨16231161524287723187965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86566194796201190335813 16231161524287723187965)
                ·
                  rfl

theorem cell19_53342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_53342 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_53342 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_53342 prefixEnd_53342 := by exact prefixLift 53342
  have htrace : WordTrace (prefixWord ++ tailWord_53342) baseStart_53342 baseEnd_53342 := by
    simpa [prefixWord, tailWord_53342, baseEnd_53342] using wordTrace_append hprefix tailTrace_53342
  have hstable : (prefixWord ++ tailWord_53342).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53342).length < 2 ^ (prefixWord ++ tailWord_53342).sum := by decide
  have hdescent : baseEnd_53342 < baseStart_53342 := by decide
  rcases family_descends (prefixWord ++ tailWord_53342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53405 : List Nat := [1, 4, 2, 1, 1, 3, 3, 4]
def baseStart_53405 : Nat := 118140960795 + 53405 * 2 ^ 59
def prefixEnd_53405 : Nat := 4983230072969 + 3 ^ 40 * 53405 * 2
def baseEnd_53405 : Nat := 16250331468722243787793

theorem tailTrace_53405 : CollatzResearch.WordTrace tailWord_53405 prefixEnd_53405 16250331468722243787793 := by
  unfold tailWord_53405
  simp only [CollatzResearch.WordTrace]
  refine ⟨1947840371530280692961669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1298560247686853795307779 1947840371530280692961669)
  ·
    refine ⟨365220069661927629930313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1947840371530280692961669 365220069661927629930313)
    ·
      refine ⟨273915052246445722447735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365220069661927629930313 273915052246445722447735)
      ·
        refine ⟨410872578369668583671603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273915052246445722447735 410872578369668583671603)
        ·
          refine ⟨616308867554502875507405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410872578369668583671603 616308867554502875507405)
          ·
            refine ⟨231115825332938578315277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 616308867554502875507405 231115825332938578315277)
            ·
              refine ⟨86668434499851966868229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231115825332938578315277 86668434499851966868229)
              ·
                refine ⟨16250331468722243787793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86668434499851966868229 16250331468722243787793)
                ·
                  rfl

theorem cell19_53405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 4].length) (baseStart_53405 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_53405 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_53405 prefixEnd_53405 := by exact prefixLift 53405
  have htrace : WordTrace (prefixWord ++ tailWord_53405) baseStart_53405 baseEnd_53405 := by
    simpa [prefixWord, tailWord_53405, baseEnd_53405] using wordTrace_append hprefix tailTrace_53405
  have hstable : (prefixWord ++ tailWord_53405).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53405).length < 2 ^ (prefixWord ++ tailWord_53405).sum := by decide
  have hdescent : baseEnd_53405 < baseStart_53405 := by decide
  rcases family_descends (prefixWord ++ tailWord_53405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53441 : List Nat := [1, 2, 6, 1, 2, 1, 6]
def baseStart_53441 : Nat := 118140960795 + 53441 * 2 ^ 59
def prefixEnd_53441 : Nat := 4983230072969 + 3 ^ 40 * 53441 * 2
def baseEnd_53441 : Nat := 5420428574228275662565

theorem tailTrace_53441 : CollatzResearch.WordTrace tailWord_53441 prefixEnd_53441 5420428574228275662565 := by
  unfold tailWord_53441
  simp only [CollatzResearch.WordTrace]
  refine ⟨1949153399399858841272177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1299435599599905894181451 1949153399399858841272177)
  ·
    refine ⟨1461865049549894130954133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1949153399399858841272177 1461865049549894130954133)
    ·
      refine ⟨68524924197651287388475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1461865049549894130954133 68524924197651287388475)
      ·
        refine ⟨102787386296476931082713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68524924197651287388475 102787386296476931082713)
        ·
          refine ⟨77090539722357698312035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102787386296476931082713 77090539722357698312035)
          ·
            refine ⟨115635809583536547468053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77090539722357698312035 115635809583536547468053)
            ·
              refine ⟨5420428574228275662565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 115635809583536547468053 5420428574228275662565)
              ·
                rfl

theorem cell19_53441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 6].length) (baseStart_53441 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_53441 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_53441 prefixEnd_53441 := by exact prefixLift 53441
  have htrace : WordTrace (prefixWord ++ tailWord_53441) baseStart_53441 baseEnd_53441 := by
    simpa [prefixWord, tailWord_53441, baseEnd_53441] using wordTrace_append hprefix tailTrace_53441
  have hstable : (prefixWord ++ tailWord_53441).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53441).length < 2 ^ (prefixWord ++ tailWord_53441).sum := by decide
  have hdescent : baseEnd_53441 < baseStart_53441 := by decide
  rcases family_descends (prefixWord ++ tailWord_53441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53475 : List Nat := [1, 1, 1, 8, 2, 1, 2, 3]
def baseStart_53475 : Nat := 118140960795 + 53475 * 2 ^ 59
def prefixEnd_53475 : Nat := 4983230072969 + 3 ^ 40 * 53475 * 2
def baseEnd_53475 : Nat := 16271631406982822232047

theorem tailTrace_53475 : CollatzResearch.WordTrace tailWord_53475 prefixEnd_53475 16271631406982822232047 := by
  unfold tailWord_53475
  simp only [CollatzResearch.WordTrace]
  refine ⟨1950393481276682648009879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1300262320851121765339919 1950393481276682648009879)
  ·
    refine ⟨2925590221915023972014819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1950393481276682648009879 2925590221915023972014819)
    ·
      refine ⟨4388385332872535958022229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2925590221915023972014819 4388385332872535958022229)
      ·
        refine ⟨51426390619600030758073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 4388385332872535958022229 51426390619600030758073)
        ·
          refine ⟨38569792964700023068555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51426390619600030758073 38569792964700023068555)
          ·
            refine ⟨57854689447050034602833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38569792964700023068555 57854689447050034602833)
            ·
              refine ⟨43391017085287525952125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57854689447050034602833 43391017085287525952125)
              ·
                refine ⟨16271631406982822232047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43391017085287525952125 16271631406982822232047)
                ·
                  rfl

theorem cell19_53475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 3].length) (baseStart_53475 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_53475 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_53475 prefixEnd_53475 := by exact prefixLift 53475
  have htrace : WordTrace (prefixWord ++ tailWord_53475) baseStart_53475 baseEnd_53475 := by
    simpa [prefixWord, tailWord_53475, baseEnd_53475] using wordTrace_append hprefix tailTrace_53475
  have hstable : (prefixWord ++ tailWord_53475).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53475).length < 2 ^ (prefixWord ++ tailWord_53475).sum := by decide
  have hdescent : baseEnd_53475 < baseStart_53475 := by decide
  rcases family_descends (prefixWord ++ tailWord_53475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53479 : List Nat := [1, 1, 5, 3, 1, 1, 4, 3]
def baseStart_53479 : Nat := 118140960795 + 53479 * 2 ^ 59
def prefixEnd_53479 : Nat := 4983230072969 + 3 ^ 40 * 53479 * 2
def baseEnd_53479 : Nat := 16272848546311998143147

theorem tailTrace_53479 : CollatzResearch.WordTrace tailWord_53479 prefixEnd_53479 16272848546311998143147 := by
  unfold tailWord_53479
  simp only [CollatzResearch.WordTrace]
  refine ⟨1950539373262191331155491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1300359582174794220770327 1950539373262191331155491)
  ·
    refine ⟨2925809059893286996733237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1950539373262191331155491 2925809059893286996733237)
    ·
      refine ⟨274294599364995655943741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2925809059893286996733237 274294599364995655943741)
      ·
        refine ⟨102860474761873370978903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274294599364995655943741 102860474761873370978903)
        ·
          refine ⟨154290712142810056468355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102860474761873370978903 154290712142810056468355)
          ·
            refine ⟨231436068214215084702533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154290712142810056468355 231436068214215084702533)
            ·
              refine ⟨43394262790165328381725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 231436068214215084702533 43394262790165328381725)
              ·
                refine ⟨16272848546311998143147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43394262790165328381725 16272848546311998143147)
                ·
                  rfl

theorem cell19_53479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 3].length) (baseStart_53479 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_53479 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_53479 prefixEnd_53479 := by exact prefixLift 53479
  have htrace : WordTrace (prefixWord ++ tailWord_53479) baseStart_53479 baseEnd_53479 := by
    simpa [prefixWord, tailWord_53479, baseEnd_53479] using wordTrace_append hprefix tailTrace_53479
  have hstable : (prefixWord ++ tailWord_53479).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53479).length < 2 ^ (prefixWord ++ tailWord_53479).sum := by decide
  have hdescent : baseEnd_53479 < baseStart_53479 := by decide
  rcases family_descends (prefixWord ++ tailWord_53479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53483 : List Nat := [1, 1, 1, 1, 2, 5, 3, 5]
def baseStart_53483 : Nat := 118140960795 + 53483 * 2 ^ 59
def prefixEnd_53483 : Nat := 4983230072969 + 3 ^ 40 * 53483 * 2
def baseEnd_53483 : Nat := 16274065685641174054247

theorem tailTrace_53483 : CollatzResearch.WordTrace tailWord_53483 prefixEnd_53483 16274065685641174054247 := by
  unfold tailWord_53483
  simp only [CollatzResearch.WordTrace]
  refine ⟨1950685265247700014301103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1300456843498466676200735 1950685265247700014301103)
  ·
    refine ⟨2926027897871550021451655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1950685265247700014301103 2926027897871550021451655)
    ·
      refine ⟨4389041846807325032177483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2926027897871550021451655 4389041846807325032177483)
      ·
        refine ⟨6583562770210987548266225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4389041846807325032177483 6583562770210987548266225)
        ·
          refine ⟨4937672077658240661199669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6583562770210987548266225 4937672077658240661199669)
          ·
            refine ⟨462906757280460061987469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4937672077658240661199669 462906757280460061987469)
            ·
              refine ⟨173590033980172523245301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 462906757280460061987469 173590033980172523245301)
              ·
                refine ⟨16274065685641174054247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 173590033980172523245301 16274065685641174054247)
                ·
                  rfl

theorem cell19_53483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 5].length) (baseStart_53483 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_53483 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_53483 prefixEnd_53483 := by exact prefixLift 53483
  have htrace : WordTrace (prefixWord ++ tailWord_53483) baseStart_53483 baseEnd_53483 := by
    simpa [prefixWord, tailWord_53483, baseEnd_53483] using wordTrace_append hprefix tailTrace_53483
  have hstable : (prefixWord ++ tailWord_53483).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53483).length < 2 ^ (prefixWord ++ tailWord_53483).sum := by decide
  have hdescent : baseEnd_53483 < baseStart_53483 := by decide
  rcases family_descends (prefixWord ++ tailWord_53483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53500 : List Nat := [2, 2, 2, 1, 4, 3, 5]
def baseStart_53500 : Nat := 118140960795 + 53500 * 2 ^ 59
def prefixEnd_53500 : Nat := 4983230072969 + 3 ^ 40 * 53500 * 2
def baseEnd_53500 : Nat := 5426412842596723892141

theorem tailTrace_53500 : CollatzResearch.WordTrace tailWord_53500 prefixEnd_53500 5426412842596723892141 := by
  unfold tailWord_53500
  simp only [CollatzResearch.WordTrace]
  refine ⟨975652653093055958834977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1300870204124074611779969 975652653093055958834977)
  ·
    refine ⟨731739489819791969126233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 975652653093055958834977 731739489819791969126233)
    ·
      refine ⟨548804617364843976844675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 731739489819791969126233 548804617364843976844675)
      ·
        refine ⟨823206926047265965267013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548804617364843976844675 823206926047265965267013)
        ·
          refine ⟨154351298633862368487565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 823206926047265965267013 154351298633862368487565)
          ·
            refine ⟨57881736987698388182837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154351298633862368487565 57881736987698388182837)
            ·
              refine ⟨5426412842596723892141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57881736987698388182837 5426412842596723892141)
              ·
                rfl

theorem cell19_53500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 5].length) (baseStart_53500 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_53500 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_53500 prefixEnd_53500 := by exact prefixLift 53500
  have htrace : WordTrace (prefixWord ++ tailWord_53500) baseStart_53500 baseEnd_53500 := by
    simpa [prefixWord, tailWord_53500, baseEnd_53500] using wordTrace_append hprefix tailTrace_53500
  have hstable : (prefixWord ++ tailWord_53500).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53500).length < 2 ^ (prefixWord ++ tailWord_53500).sum := by decide
  have hdescent : baseEnd_53500 < baseStart_53500 := by decide
  rcases family_descends (prefixWord ++ tailWord_53500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53521 : List Nat := [1, 2, 2, 1, 1, 5, 1, 6]
def baseStart_53521 : Nat := 118140960795 + 53521 * 2 ^ 59
def prefixEnd_53521 : Nat := 4983230072969 + 3 ^ 40 * 53521 * 2
def baseEnd_53521 : Nat := 16285628509268345209699

theorem tailTrace_53521 : CollatzResearch.WordTrace tailWord_53521 prefixEnd_53521 16285628509268345209699 := by
  unfold tailWord_53521
  simp only [CollatzResearch.WordTrace]
  refine ⟨1952071239110032504184417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1301380826073355002789611 1952071239110032504184417)
  ·
    refine ⟨1464053429332524378138313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1952071239110032504184417 1464053429332524378138313)
    ·
      refine ⟨1098040071999393283603735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1464053429332524378138313 1098040071999393283603735)
      ·
        refine ⟨1647060107999089925405603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1098040071999393283603735 1647060107999089925405603)
        ·
          refine ⟨2470590161998634888108405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1647060107999089925405603 2470590161998634888108405)
          ·
            refine ⟨231617827687372020760163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2470590161998634888108405 231617827687372020760163)
            ·
              refine ⟨347426741531058031140245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231617827687372020760163 347426741531058031140245)
              ·
                refine ⟨16285628509268345209699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 347426741531058031140245 16285628509268345209699)
                ·
                  rfl

theorem cell19_53521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 6].length) (baseStart_53521 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_53521 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_53521 prefixEnd_53521 := by exact prefixLift 53521
  have htrace : WordTrace (prefixWord ++ tailWord_53521) baseStart_53521 baseEnd_53521 := by
    simpa [prefixWord, tailWord_53521, baseEnd_53521] using wordTrace_append hprefix tailTrace_53521
  have hstable : (prefixWord ++ tailWord_53521).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53521).length < 2 ^ (prefixWord ++ tailWord_53521).sum := by decide
  have hdescent : baseEnd_53521 < baseStart_53521 := by decide
  rcases family_descends (prefixWord ++ tailWord_53521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53538 : List Nat := [3, 3, 1, 1, 3, 1, 2, 5]
def baseStart_53538 : Nat := 118140960795 + 53538 * 2 ^ 59
def prefixEnd_53538 : Nat := 4983230072969 + 3 ^ 40 * 53538 * 2
def baseEnd_53538 : Nat := 16290801351417342831875

theorem tailTrace_53538 : CollatzResearch.WordTrace tailWord_53538 prefixEnd_53538 16290801351417342831875 := by
  unfold tailWord_53538
  simp only [CollatzResearch.WordTrace]
  refine ⟨488172820012111101888317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1301794186698962938368845 488172820012111101888317)
  ·
    refine ⟨183064807504541663208119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 488172820012111101888317 183064807504541663208119)
    ·
      refine ⟨274597211256812494812179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183064807504541663208119 274597211256812494812179)
      ·
        refine ⟨411895816885218742218269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274597211256812494812179 411895816885218742218269)
        ·
          refine ⟨154460931331957028331851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 411895816885218742218269 154460931331957028331851)
          ·
            refine ⟨231691396997935542497777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154460931331957028331851 231691396997935542497777)
            ·
              refine ⟨173768547748451656873333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231691396997935542497777 173768547748451656873333)
              ·
                refine ⟨16290801351417342831875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 173768547748451656873333 16290801351417342831875)
                ·
                  rfl

theorem cell19_53538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_53538 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_53538 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_53538 prefixEnd_53538 := by exact prefixLift 53538
  have htrace : WordTrace (prefixWord ++ tailWord_53538) baseStart_53538 baseEnd_53538 := by
    simpa [prefixWord, tailWord_53538, baseEnd_53538] using wordTrace_append hprefix tailTrace_53538
  have hstable : (prefixWord ++ tailWord_53538).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53538).length < 2 ^ (prefixWord ++ tailWord_53538).sum := by decide
  have hdescent : baseEnd_53538 < baseStart_53538 := by decide
  rcases family_descends (prefixWord ++ tailWord_53538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53572 : List Nat := [2, 3, 4, 1, 2, 2, 1, 4]
def baseStart_53572 : Nat := 118140960795 + 53572 * 2 ^ 59
def prefixEnd_53572 : Nat := 4983230072969 + 3 ^ 40 * 53572 * 2
def baseEnd_53572 : Nat := 16301147035715338076227

theorem tailTrace_53572 : CollatzResearch.WordTrace tailWord_53572 prefixEnd_53572 16301147035715338076227 := by
  unfold tailWord_53572
  simp only [CollatzResearch.WordTrace]
  refine ⟨976965680962634107145485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1302620907950178809527313 976965680962634107145485)
  ·
    refine ⟨366362130360987790179557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 976965680962634107145485 366362130360987790179557)
    ·
      refine ⟨68692899442685210658667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 366362130360987790179557 68692899442685210658667)
      ·
        refine ⟨103039349164027815988001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68692899442685210658667 103039349164027815988001)
        ·
          refine ⟨77279511873020861991001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103039349164027815988001 77279511873020861991001)
          ·
            refine ⟨57959633904765646493251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77279511873020861991001 57959633904765646493251)
            ·
              refine ⟨86939450857148469739877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57959633904765646493251 86939450857148469739877)
              ·
                refine ⟨16301147035715338076227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86939450857148469739877 16301147035715338076227)
                ·
                  rfl

theorem cell19_53572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 4].length) (baseStart_53572 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_53572 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_53572 prefixEnd_53572 := by exact prefixLift 53572
  have htrace : WordTrace (prefixWord ++ tailWord_53572) baseStart_53572 baseEnd_53572 := by
    simpa [prefixWord, tailWord_53572, baseEnd_53572] using wordTrace_append hprefix tailTrace_53572
  have hstable : (prefixWord ++ tailWord_53572).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53572).length < 2 ^ (prefixWord ++ tailWord_53572).sum := by decide
  have hdescent : baseEnd_53572 < baseStart_53572 := by decide
  rcases family_descends (prefixWord ++ tailWord_53572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53616 : List Nat := [2, 1, 1, 1, 4, 4, 6]
def baseStart_53616 : Nat := 118140960795 + 53616 * 2 ^ 59
def prefixEnd_53616 : Nat := 4983230072969 + 3 ^ 40 * 53616 * 2
def baseEnd_53616 : Nat := 5438178522778757699443

theorem tailTrace_53616 : CollatzResearch.WordTrace tailWord_53616 prefixEnd_53616 5438178522778757699443 := by
  unfold tailWord_53616
  simp only [CollatzResearch.WordTrace]
  refine ⟨977768086882931864446351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1303690782510575819261801 977768086882931864446351)
  ·
    refine ⟨1466652130324397796669527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 977768086882931864446351 1466652130324397796669527)
    ·
      refine ⟨2199978195486596695004291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1466652130324397796669527 2199978195486596695004291)
      ·
        refine ⟨3299967293229895042506437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2199978195486596695004291 3299967293229895042506437)
        ·
          refine ⟨618743867480605320469957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3299967293229895042506437 618743867480605320469957)
          ·
            refine ⟨116014475152613497588117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 618743867480605320469957 116014475152613497588117)
            ·
              refine ⟨5438178522778757699443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 116014475152613497588117 5438178522778757699443)
              ·
                rfl

theorem cell19_53616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 6].length) (baseStart_53616 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_53616 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_53616 prefixEnd_53616 := by exact prefixLift 53616
  have htrace : WordTrace (prefixWord ++ tailWord_53616) baseStart_53616 baseEnd_53616 := by
    simpa [prefixWord, tailWord_53616, baseEnd_53616] using wordTrace_append hprefix tailTrace_53616
  have hstable : (prefixWord ++ tailWord_53616).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53616).length < 2 ^ (prefixWord ++ tailWord_53616).sum := by decide
  have hdescent : baseEnd_53616 < baseStart_53616 := by decide
  rcases family_descends (prefixWord ++ tailWord_53616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53671 : List Nat := [1, 1, 6, 1, 1, 4, 5]
def baseStart_53671 : Nat := 118140960795 + 53671 * 2 ^ 59
def prefixEnd_53671 : Nat := 4983230072969 + 3 ^ 40 * 53671 * 2
def baseEnd_53671 : Nat := 5443757078037480625319

theorem tailTrace_53671 : CollatzResearch.WordTrace tailWord_53671 prefixEnd_53671 5443757078037480625319 := by
  unfold tailWord_53671
  simp only [CollatzResearch.WordTrace]
  refine ⟨1957542188566608122144867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1305028125711072081429911 1957542188566608122144867)
  ·
    refine ⟨2936313282849912183217301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1957542188566608122144867 2936313282849912183217301)
    ·
      refine ⟨137639685133589633588311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2936313282849912183217301 137639685133589633588311)
      ·
        refine ⟨206459527700384450382467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137639685133589633588311 206459527700384450382467)
        ·
          refine ⟨309689291550576675573701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206459527700384450382467 309689291550576675573701)
          ·
            refine ⟨58066742165733126670069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 309689291550576675573701 58066742165733126670069)
            ·
              refine ⟨5443757078037480625319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58066742165733126670069 5443757078037480625319)
              ·
                rfl

theorem cell19_53671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 5].length) (baseStart_53671 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_53671 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_53671 prefixEnd_53671 := by exact prefixLift 53671
  have htrace : WordTrace (prefixWord ++ tailWord_53671) baseStart_53671 baseEnd_53671 := by
    simpa [prefixWord, tailWord_53671, baseEnd_53671] using wordTrace_append hprefix tailTrace_53671
  have hstable : (prefixWord ++ tailWord_53671).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53671).length < 2 ^ (prefixWord ++ tailWord_53671).sum := by decide
  have hdescent : baseEnd_53671 < baseStart_53671 := by decide
  rcases family_descends (prefixWord ++ tailWord_53671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53762 : List Nat := [3, 4, 1, 2, 2, 1, 3, 3]
def baseStart_53762 : Nat := 118140960795 + 53762 * 2 ^ 59
def prefixEnd_53762 : Nat := 4983230072969 + 3 ^ 40 * 53762 * 2
def baseEnd_53762 : Nat := 16358961153851193853487

theorem tailTrace_53762 : CollatzResearch.WordTrace tailWord_53762 prefixEnd_53762 16358961153851193853487 := by
  unfold tailWord_53762
  simp only [CollatzResearch.WordTrace]
  refine ⟨490215307809232665926885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1307240820824620442471693 490215307809232665926885)
  ·
    refine ⟨91915370214231124861291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 490215307809232665926885 91915370214231124861291)
    ·
      refine ⟨137873055321346687291937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91915370214231124861291 137873055321346687291937)
      ·
        refine ⟨103404791491010015468953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137873055321346687291937 103404791491010015468953)
        ·
          refine ⟨77553593618257511601715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103404791491010015468953 77553593618257511601715)
          ·
            refine ⟨116330390427386267402573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77553593618257511601715 116330390427386267402573)
            ·
              refine ⟨43623896410269850275965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116330390427386267402573 43623896410269850275965)
              ·
                refine ⟨16358961153851193853487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43623896410269850275965 16358961153851193853487)
                ·
                  rfl

theorem cell19_53762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_53762 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_53762 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_53762 prefixEnd_53762 := by exact prefixLift 53762
  have htrace : WordTrace (prefixWord ++ tailWord_53762) baseStart_53762 baseEnd_53762 := by
    simpa [prefixWord, tailWord_53762, baseEnd_53762] using wordTrace_append hprefix tailTrace_53762
  have hstable : (prefixWord ++ tailWord_53762).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53762).length < 2 ^ (prefixWord ++ tailWord_53762).sum := by decide
  have hdescent : baseEnd_53762 < baseStart_53762 := by decide
  rcases family_descends (prefixWord ++ tailWord_53762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53764 : List Nat := [2, 3, 2, 3, 1, 2, 3, 3]
def baseStart_53764 : Nat := 118140960795 + 53764 * 2 ^ 59
def prefixEnd_53764 : Nat := 4983230072969 + 3 ^ 40 * 53764 * 2
def baseEnd_53764 : Nat := 16359569723515781809037

theorem tailTrace_53764 : CollatzResearch.WordTrace tailWord_53764 prefixEnd_53764 16359569723515781809037 := by
  unfold tailWord_53764
  simp only [CollatzResearch.WordTrace]
  refine ⟨980467088614842502640173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1307289451486456670186897 980467088614842502640173)
  ·
    refine ⟨367675158230565938490065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 980467088614842502640173 367675158230565938490065)
    ·
      refine ⟨275756368672924453867549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367675158230565938490065 275756368672924453867549)
      ·
        refine ⟨103408638252346670200331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275756368672924453867549 103408638252346670200331)
        ·
          refine ⟨155112957378520005300497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103408638252346670200331 155112957378520005300497)
          ·
            refine ⟨116334718033890003975373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155112957378520005300497 116334718033890003975373)
            ·
              refine ⟨43625519262708751490765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116334718033890003975373 43625519262708751490765)
              ·
                refine ⟨16359569723515781809037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43625519262708751490765 16359569723515781809037)
                ·
                  rfl

theorem cell19_53764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 3].length) (baseStart_53764 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_53764 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_53764 prefixEnd_53764 := by exact prefixLift 53764
  have htrace : WordTrace (prefixWord ++ tailWord_53764) baseStart_53764 baseEnd_53764 := by
    simpa [prefixWord, tailWord_53764, baseEnd_53764] using wordTrace_append hprefix tailTrace_53764
  have hstable : (prefixWord ++ tailWord_53764).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53764).length < 2 ^ (prefixWord ++ tailWord_53764).sum := by decide
  have hdescent : baseEnd_53764 < baseStart_53764 := by decide
  rcases family_descends (prefixWord ++ tailWord_53764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53821 : List Nat := [1, 4, 1, 3, 2, 3, 2, 3]
def baseStart_53821 : Nat := 118140960795 + 53821 * 2 ^ 59
def prefixEnd_53821 : Nat := 4983230072969 + 3 ^ 40 * 53821 * 2
def baseEnd_53821 : Nat := 16376913958956538542215

theorem tailTrace_53821 : CollatzResearch.WordTrace tailWord_53821 prefixEnd_53821 16376913958956538542215 := by
  unfold tailWord_53821
  simp only [CollatzResearch.WordTrace]
  refine ⟨1963013138023183740105317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1308675425348789160070211 1963013138023183740105317)
  ·
    refine ⟨368064963379346951269747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1963013138023183740105317 368064963379346951269747)
    ·
      refine ⟨552097445069020426904621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368064963379346951269747 552097445069020426904621)
      ·
        refine ⟨207036541900882660089233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 552097445069020426904621 207036541900882660089233)
        ·
          refine ⟨155277406425661995066925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207036541900882660089233 155277406425661995066925)
          ·
            refine ⟨58229027409623248150097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155277406425661995066925 58229027409623248150097)
            ·
              refine ⟨43671770557217436112573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58229027409623248150097 43671770557217436112573)
              ·
                refine ⟨16376913958956538542215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43671770557217436112573 16376913958956538542215)
                ·
                  rfl

theorem cell19_53821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 3].length) (baseStart_53821 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_53821 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_53821 prefixEnd_53821 := by exact prefixLift 53821
  have htrace : WordTrace (prefixWord ++ tailWord_53821) baseStart_53821 baseEnd_53821 := by
    simpa [prefixWord, tailWord_53821, baseEnd_53821] using wordTrace_append hprefix tailTrace_53821
  have hstable : (prefixWord ++ tailWord_53821).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53821).length < 2 ^ (prefixWord ++ tailWord_53821).sum := by decide
  have hdescent : baseEnd_53821 < baseStart_53821 := by decide
  rcases family_descends (prefixWord ++ tailWord_53821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53844 : List Nat := [2, 4, 1, 1, 1, 3, 7]
def baseStart_53844 : Nat := 118140960795 + 53844 * 2 ^ 59
def prefixEnd_53844 : Nat := 4983230072969 + 3 ^ 40 * 53844 * 2
def baseEnd_53844 : Nat := 5461304170033100010347

theorem tailTrace_53844 : CollatzResearch.WordTrace tailWord_53844 prefixEnd_53844 5461304170033100010347 := by
  unfold tailWord_53844
  simp only [CollatzResearch.WordTrace]
  refine ⟨981926008469929334096293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1309234677959905778795057 981926008469929334096293)
  ·
    refine ⟨184111126588111750143055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 981926008469929334096293 184111126588111750143055)
    ·
      refine ⟨276166689882167625214583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184111126588111750143055 276166689882167625214583)
      ·
        refine ⟨414250034823251437821875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276166689882167625214583 414250034823251437821875)
        ·
          refine ⟨621375052234877156732813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414250034823251437821875 621375052234877156732813)
          ·
            refine ⟨233015644588078933774805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 621375052234877156732813 233015644588078933774805)
            ·
              refine ⟨5461304170033100010347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 233015644588078933774805 5461304170033100010347)
              ·
                rfl

theorem cell19_53844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 7].length) (baseStart_53844 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_53844 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_53844 prefixEnd_53844 := by exact prefixLift 53844
  have htrace : WordTrace (prefixWord ++ tailWord_53844) baseStart_53844 baseEnd_53844 := by
    simpa [prefixWord, tailWord_53844, baseEnd_53844] using wordTrace_append hprefix tailTrace_53844
  have hstable : (prefixWord ++ tailWord_53844).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53844).length < 2 ^ (prefixWord ++ tailWord_53844).sum := by decide
  have hdescent : baseEnd_53844 < baseStart_53844 := by decide
  rcases family_descends (prefixWord ++ tailWord_53844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53861 : List Nat := [1, 3, 1, 3, 4, 1, 2, 4]
def baseStart_53861 : Nat := 118140960795 + 53861 * 2 ^ 59
def prefixEnd_53861 : Nat := 4983230072969 + 3 ^ 40 * 53861 * 2
def baseEnd_53861 : Nat := 16389085352248297653217

theorem tailTrace_53861 : CollatzResearch.WordTrace tailWord_53861 prefixEnd_53861 16389085352248297653217 := by
  unfold tailWord_53861
  simp only [CollatzResearch.WordTrace]
  refine ⟨1964472057878270571561437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1309648038585513714374291 1964472057878270571561437)
  ·
    refine ⟨736677021704351464335539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1964472057878270571561437 736677021704351464335539)
    ·
      refine ⟨1105015532556527196503309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 736677021704351464335539 1105015532556527196503309)
      ·
        refine ⟨414380824708697698688741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1105015532556527196503309 414380824708697698688741)
        ·
          refine ⟨77696404632880818504139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 414380824708697698688741 77696404632880818504139)
          ·
            refine ⟨116544606949321227756209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77696404632880818504139 116544606949321227756209)
            ·
              refine ⟨87408455211990920817157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116544606949321227756209 87408455211990920817157)
              ·
                refine ⟨16389085352248297653217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87408455211990920817157 16389085352248297653217)
                ·
                  rfl

theorem cell19_53861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 4].length) (baseStart_53861 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_53861 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_53861 prefixEnd_53861 := by exact prefixLift 53861
  have htrace : WordTrace (prefixWord ++ tailWord_53861) baseStart_53861 baseEnd_53861 := by
    simpa [prefixWord, tailWord_53861, baseEnd_53861] using wordTrace_append hprefix tailTrace_53861
  have hstable : (prefixWord ++ tailWord_53861).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53861).length < 2 ^ (prefixWord ++ tailWord_53861).sum := by decide
  have hdescent : baseEnd_53861 < baseStart_53861 := by decide
  rcases family_descends (prefixWord ++ tailWord_53861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53914 : List Nat := [3, 1, 1, 6, 2, 1, 1, 4]
def baseStart_53914 : Nat := 118140960795 + 53914 * 2 ^ 59
def prefixEnd_53914 : Nat := 4983230072969 + 3 ^ 40 * 53914 * 2
def baseEnd_53914 : Nat := 16405212448359878475295

theorem tailTrace_53914 : CollatzResearch.WordTrace tailWord_53914 prefixEnd_53914 16405212448359878475295 := by
  unfold tailWord_53914
  simp only [CollatzResearch.WordTrace]
  refine ⟨491601281671565155810199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1310936751124173748827197 491601281671565155810199)
  ·
    refine ⟨737401922507347733715299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 491601281671565155810199 737401922507347733715299)
    ·
      refine ⟨1106102883761021600572949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 737401922507347733715299 1106102883761021600572949)
      ·
        refine ⟨51848572676297887526857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1106102883761021600572949 51848572676297887526857)
        ·
          refine ⟨38886429507223415645143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51848572676297887526857 38886429507223415645143)
          ·
            refine ⟨58329644260835123467715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38886429507223415645143 58329644260835123467715)
            ·
              refine ⟨87494466391252685201573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58329644260835123467715 87494466391252685201573)
              ·
                refine ⟨16405212448359878475295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87494466391252685201573 16405212448359878475295)
                ·
                  rfl

theorem cell19_53914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 4].length) (baseStart_53914 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_53914 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_53914 prefixEnd_53914 := by exact prefixLift 53914
  have htrace : WordTrace (prefixWord ++ tailWord_53914) baseStart_53914 baseEnd_53914 := by
    simpa [prefixWord, tailWord_53914, baseEnd_53914] using wordTrace_append hprefix tailTrace_53914
  have hstable : (prefixWord ++ tailWord_53914).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53914).length < 2 ^ (prefixWord ++ tailWord_53914).sum := by decide
  have hdescent : baseEnd_53914 < baseStart_53914 := by decide
  rcases family_descends (prefixWord ++ tailWord_53914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53992 : List Nat := [2, 1, 4, 1, 4, 2, 2, 3]
def baseStart_53992 : Nat := 118140960795 + 53992 * 2 ^ 59
def prefixEnd_53992 : Nat := 4983230072969 + 3 ^ 40 * 53992 * 2
def baseEnd_53992 : Nat := 16428946665278808741749

theorem tailTrace_53992 : CollatzResearch.WordTrace tailWord_53992 prefixEnd_53992 16428946665278808741749 := by
  unfold tailWord_53992
  simp only [CollatzResearch.WordTrace]
  refine ⟨984625010201839972290115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1312833346935786629720153 984625010201839972290115)
  ·
    refine ⟨1476937515302759958435173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 984625010201839972290115 1476937515302759958435173)
    ·
      refine ⟨276925784119267492206595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1476937515302759958435173 276925784119267492206595)
      ·
        refine ⟨415388676178901238309893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276925784119267492206595 415388676178901238309893)
        ·
          refine ⟨77885376783543982183105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 415388676178901238309893 77885376783543982183105)
          ·
            refine ⟨58414032587657986637329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77885376783543982183105 58414032587657986637329)
            ·
              refine ⟨43810524440743489977997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58414032587657986637329 43810524440743489977997)
              ·
                refine ⟨16428946665278808741749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43810524440743489977997 16428946665278808741749)
                ·
                  rfl

theorem cell19_53992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 3].length) (baseStart_53992 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_53992 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_53992 prefixEnd_53992 := by exact prefixLift 53992
  have htrace : WordTrace (prefixWord ++ tailWord_53992) baseStart_53992 baseEnd_53992 := by
    simpa [prefixWord, tailWord_53992, baseEnd_53992] using wordTrace_append hprefix tailTrace_53992
  have hstable : (prefixWord ++ tailWord_53992).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53992).length < 2 ^ (prefixWord ++ tailWord_53992).sum := by decide
  have hdescent : baseEnd_53992 < baseStart_53992 := by decide
  rcases family_descends (prefixWord ++ tailWord_53992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54070 : List Nat := [5, 1, 2, 2, 2, 7]
def baseStart_54070 : Nat := 118140960795 + 54070 * 2 ^ 59
def prefixEnd_54070 : Nat := 4983230072969 + 3 ^ 40 * 54070 * 2
def baseEnd_54070 : Nat := 1828075653577526556467

theorem tailTrace_54070 : CollatzResearch.WordTrace tailWord_54070 prefixEnd_54070 1828075653577526556467 := by
  unfold tailWord_54070
  simp only [CollatzResearch.WordTrace]
  refine ⟨123255932132568704119979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1314729942747399510613109 123255932132568704119979)
  ·
    refine ⟨184883898198853056179969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123255932132568704119979 184883898198853056179969)
    ·
      refine ⟨138662923649139792134977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184883898198853056179969 138662923649139792134977)
      ·
        refine ⟨103997192736854844101233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138662923649139792134977 103997192736854844101233)
        ·
          refine ⟨77997894552641133075925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103997192736854844101233 77997894552641133075925)
          ·
            refine ⟨1828075653577526556467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 77997894552641133075925 1828075653577526556467)
            ·
              rfl

theorem cell19_54070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 7].length) (baseStart_54070 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_54070 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_54070 prefixEnd_54070 := by exact prefixLift 54070
  have htrace : WordTrace (prefixWord ++ tailWord_54070) baseStart_54070 baseEnd_54070 := by
    simpa [prefixWord, tailWord_54070, baseEnd_54070] using wordTrace_append hprefix tailTrace_54070
  have hstable : (prefixWord ++ tailWord_54070).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54070).length < 2 ^ (prefixWord ++ tailWord_54070).sum := by decide
  have hdescent : baseEnd_54070 < baseStart_54070 := by decide
  rcases family_descends (prefixWord ++ tailWord_54070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54074 : List Nat := [3, 1, 1, 1, 13]
def baseStart_54074 : Nat := 118140960795 + 54074 * 2 ^ 59
def prefixEnd_54074 : Nat := 4983230072969 + 3 ^ 40 * 54074 * 2
def baseEnd_54074 : Nat := 609403630426922774789

theorem tailTrace_54074 : CollatzResearch.WordTrace tailWord_54074 prefixEnd_54074 609403630426922774789 := by
  unfold tailWord_54074
  simp only [CollatzResearch.WordTrace]
  refine ⟨493060201526651987266319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1314827204071071966043517 493060201526651987266319)
  ·
    refine ⟨739590302289977980899479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 493060201526651987266319 739590302289977980899479)
    ·
      refine ⟨1109385453434966971349219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 739590302289977980899479 1109385453434966971349219)
      ·
        refine ⟨1664078180152450457023829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1109385453434966971349219 1664078180152450457023829)
        ·
          refine ⟨609403630426922774789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 1664078180152450457023829 609403630426922774789)
          ·
            rfl

theorem cell19_54074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 13].length) (baseStart_54074 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_54074 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_54074 prefixEnd_54074 := by exact prefixLift 54074
  have htrace : WordTrace (prefixWord ++ tailWord_54074) baseStart_54074 baseEnd_54074 := by
    simpa [prefixWord, tailWord_54074, baseEnd_54074] using wordTrace_append hprefix tailTrace_54074
  have hstable : (prefixWord ++ tailWord_54074).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54074).length < 2 ^ (prefixWord ++ tailWord_54074).sum := by decide
  have hdescent : baseEnd_54074 < baseStart_54074 := by decide
  rcases family_descends (prefixWord ++ tailWord_54074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54165 : List Nat := [1, 3, 2, 1, 1, 6, 2, 3]
def baseStart_54165 : Nat := 118140960795 + 54165 * 2 ^ 59
def prefixEnd_54165 : Nat := 4983230072969 + 3 ^ 40 * 54165 * 2
def baseEnd_54165 : Nat := 16481587941265666896833

theorem tailTrace_54165 : CollatzResearch.WordTrace tailWord_54165 prefixEnd_54165 16481587941265666896833 := by
  unfold tailWord_54165
  simp only [CollatzResearch.WordTrace]
  refine ⟨1975559848776930490627949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1317039899184620327085299 1975559848776930490627949)
  ·
    refine ⟨740834943291348933985481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1975559848776930490627949 740834943291348933985481)
    ·
      refine ⟨555626207468511700489111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 740834943291348933985481 555626207468511700489111)
      ·
        refine ⟨833439311202767550733667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555626207468511700489111 833439311202767550733667)
        ·
          refine ⟨1250158966804151326100501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 833439311202767550733667 1250158966804151326100501)
          ·
            refine ⟨58601201568944593410961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1250158966804151326100501 58601201568944593410961)
            ·
              refine ⟨43950901176708445058221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58601201568944593410961 43950901176708445058221)
              ·
                refine ⟨16481587941265666896833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43950901176708445058221 16481587941265666896833)
                ·
                  rfl

theorem cell19_54165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 3].length) (baseStart_54165 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_54165 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_54165 prefixEnd_54165 := by exact prefixLift 54165
  have htrace : WordTrace (prefixWord ++ tailWord_54165) baseStart_54165 baseEnd_54165 := by
    simpa [prefixWord, tailWord_54165, baseEnd_54165] using wordTrace_append hprefix tailTrace_54165
  have hstable : (prefixWord ++ tailWord_54165).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54165).length < 2 ^ (prefixWord ++ tailWord_54165).sum := by decide
  have hdescent : baseEnd_54165 < baseStart_54165 := by decide
  rcases family_descends (prefixWord ++ tailWord_54165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54258 : List Nat := [3, 2, 1, 5, 1, 2, 1, 4]
def baseStart_54258 : Nat := 118140960795 + 54258 * 2 ^ 59
def prefixEnd_54258 : Nat := 4983230072969 + 3 ^ 40 * 54258 * 2
def baseEnd_54258 : Nat := 16509886430669006829913

theorem tailTrace_54258 : CollatzResearch.WordTrace tailWord_54258 prefixEnd_54258 16509886430669006829913 := by
  unfold tailWord_54258
  simp only [CollatzResearch.WordTrace]
  refine ⟨494737959360001843440857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1319301224960004915842285 494737959360001843440857)
  ·
    refine ⟨371053469520001382580643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 494737959360001843440857 371053469520001382580643)
    ·
      refine ⟨556580204280002073870965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371053469520001382580643 556580204280002073870965)
      ·
        refine ⟨52179394151250194425403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 556580204280002073870965 52179394151250194425403)
        ·
          refine ⟨78269091226875291638105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52179394151250194425403 78269091226875291638105)
          ·
            refine ⟨58701818420156468728579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78269091226875291638105 58701818420156468728579)
            ·
              refine ⟨88052727630234703092869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58701818420156468728579 88052727630234703092869)
              ·
                refine ⟨16509886430669006829913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88052727630234703092869 16509886430669006829913)
                ·
                  rfl

theorem cell19_54258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_54258 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_54258 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_54258 prefixEnd_54258 := by exact prefixLift 54258
  have htrace : WordTrace (prefixWord ++ tailWord_54258) baseStart_54258 baseEnd_54258 := by
    simpa [prefixWord, tailWord_54258, baseEnd_54258] using wordTrace_append hprefix tailTrace_54258
  have hstable : (prefixWord ++ tailWord_54258).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54258).length < 2 ^ (prefixWord ++ tailWord_54258).sum := by decide
  have hdescent : baseEnd_54258 < baseStart_54258 := by decide
  rcases family_descends (prefixWord ++ tailWord_54258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54300 : List Nat := [2, 2, 3, 1, 4, 1, 6]
def baseStart_54300 : Nat := 118140960795 + 54300 * 2 ^ 59
def prefixEnd_54300 : Nat := 4983230072969 + 3 ^ 40 * 54300 * 2
def baseEnd_54300 : Nat := 5507555464541784632155

theorem tailTrace_54300 : CollatzResearch.WordTrace tailWord_54300 prefixEnd_54300 5507555464541784632155 := by
  unfold tailWord_54300
  simp only [CollatzResearch.WordTrace]
  refine ⟨990241851643924273396177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1320322468858565697861569 990241851643924273396177)
  ·
    refine ⟨742681388732943205047133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 990241851643924273396177 742681388732943205047133)
    ·
      refine ⟨278505520774853701892675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 742681388732943205047133 278505520774853701892675)
      ·
        refine ⟨417758281162280552839013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278505520774853701892675 417758281162280552839013)
        ·
          refine ⟨78329677717927603657315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 417758281162280552839013 78329677717927603657315)
          ·
            refine ⟨117494516576891405485973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78329677717927603657315 117494516576891405485973)
            ·
              refine ⟨5507555464541784632155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 117494516576891405485973 5507555464541784632155)
              ·
                rfl

theorem cell19_54300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 6].length) (baseStart_54300 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_54300 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_54300 prefixEnd_54300 := by exact prefixLift 54300
  have htrace : WordTrace (prefixWord ++ tailWord_54300) baseStart_54300 baseEnd_54300 := by
    simpa [prefixWord, tailWord_54300, baseEnd_54300] using wordTrace_append hprefix tailTrace_54300
  have hstable : (prefixWord ++ tailWord_54300).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54300).length < 2 ^ (prefixWord ++ tailWord_54300).sum := by decide
  have hdescent : baseEnd_54300 < baseStart_54300 := by decide
  rcases family_descends (prefixWord ++ tailWord_54300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54321 : List Nat := [1, 2, 2, 3, 1, 2, 2, 6]
def baseStart_54321 : Nat := 118140960795 + 54321 * 2 ^ 59
def prefixEnd_54321 : Nat := 4983230072969 + 3 ^ 40 * 54321 * 2
def baseEnd_54321 : Nat := 16529056375103527429741

theorem tailTrace_54321 : CollatzResearch.WordTrace tailWord_54321 prefixEnd_54321 16529056375103527429741 := by
  unfold tailWord_54321
  simp only [CollatzResearch.WordTrace]
  refine ⟨1981249636211769133306817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1320833090807846088871211 1981249636211769133306817)
  ·
    refine ⟨1485937227158826849980113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1981249636211769133306817 1485937227158826849980113)
    ·
      refine ⟨1114452920369120137485085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1485937227158826849980113 1114452920369120137485085)
      ·
        refine ⟨417919845138420051556907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1114452920369120137485085 417919845138420051556907)
        ·
          refine ⟨626879767707630077335361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417919845138420051556907 626879767707630077335361)
          ·
            refine ⟨470159825780722558001521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 626879767707630077335361 470159825780722558001521)
            ·
              refine ⟨352619869335541918501141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 470159825780722558001521 352619869335541918501141)
              ·
                refine ⟨16529056375103527429741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 352619869335541918501141 16529056375103527429741)
                ·
                  rfl

theorem cell19_54321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 6].length) (baseStart_54321 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_54321 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_54321 prefixEnd_54321 := by exact prefixLift 54321
  have htrace : WordTrace (prefixWord ++ tailWord_54321) baseStart_54321 baseEnd_54321 := by
    simpa [prefixWord, tailWord_54321, baseEnd_54321] using wordTrace_append hprefix tailTrace_54321
  have hstable : (prefixWord ++ tailWord_54321).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54321).length < 2 ^ (prefixWord ++ tailWord_54321).sum := by decide
  have hdescent : baseEnd_54321 < baseStart_54321 := by decide
  rcases family_descends (prefixWord ++ tailWord_54321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54334 : List Nat := [4, 2, 1, 3, 1, 3, 2, 3]
def baseStart_54334 : Nat := 118140960795 + 54334 * 2 ^ 59
def prefixEnd_54334 : Nat := 4983230072969 + 3 ^ 40 * 54334 * 2
def baseEnd_54334 : Nat := 16533012077923349140817

theorem tailTrace_54334 : CollatzResearch.WordTrace tailWord_54334 prefixEnd_54334 16533012077923349140817 := by
  unfold tailWord_54334
  simp only [CollatzResearch.WordTrace]
  refine ⟨247715473145584044191257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1321149190109781569020037 247715473145584044191257)
  ·
    refine ⟨185786604859188033143443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247715473145584044191257 185786604859188033143443)
    ·
      refine ⟨278679907288782049715165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185786604859188033143443 278679907288782049715165)
      ·
        refine ⟨104504965233293268643187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278679907288782049715165 104504965233293268643187)
        ·
          refine ⟨156757447849939902964781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104504965233293268643187 156757447849939902964781)
          ·
            refine ⟨58784042943727463611793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156757447849939902964781 58784042943727463611793)
            ·
              refine ⟨44088032207795597708845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58784042943727463611793 44088032207795597708845)
              ·
                refine ⟨16533012077923349140817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44088032207795597708845 16533012077923349140817)
                ·
                  rfl

theorem cell19_54334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_54334 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_54334 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_54334 prefixEnd_54334 := by exact prefixLift 54334
  have htrace : WordTrace (prefixWord ++ tailWord_54334) baseStart_54334 baseEnd_54334 := by
    simpa [prefixWord, tailWord_54334, baseEnd_54334] using wordTrace_append hprefix tailTrace_54334
  have hstable : (prefixWord ++ tailWord_54334).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54334).length < 2 ^ (prefixWord ++ tailWord_54334).sum := by decide
  have hdescent : baseEnd_54334 < baseStart_54334 := by decide
  rcases family_descends (prefixWord ++ tailWord_54334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54397 : List Nat := [1, 4, 1, 1, 3, 1, 1, 7]
def baseStart_54397 : Nat := 118140960795 + 54397 * 2 ^ 59
def prefixEnd_54397 : Nat := 4983230072969 + 3 ^ 40 * 54397 * 2
def baseEnd_54397 : Nat := 16552182022357869740645

theorem tailTrace_54397 : CollatzResearch.WordTrace tailWord_54397 prefixEnd_54397 16552182022357869740645 := by
  unfold tailWord_54397
  simp only [CollatzResearch.WordTrace]
  refine ⟨1984021583936434113073445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1322681055957622742048963 1984021583936434113073445)
  ·
    refine ⟨372004046988081396201271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1984021583936434113073445 372004046988081396201271)
    ·
      refine ⟨558006070482122094301907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372004046988081396201271 558006070482122094301907)
      ·
        refine ⟨837009105723183141452861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 558006070482122094301907 837009105723183141452861)
        ·
          refine ⟨313878414646193678044823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 837009105723183141452861 313878414646193678044823)
          ·
            refine ⟨470817621969290517067235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313878414646193678044823 470817621969290517067235)
            ·
              refine ⟨706226432953935775600853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470817621969290517067235 706226432953935775600853)
              ·
                refine ⟨16552182022357869740645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 706226432953935775600853 16552182022357869740645)
                ·
                  rfl

theorem cell19_54397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 7].length) (baseStart_54397 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_54397 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_54397 prefixEnd_54397 := by exact prefixLift 54397
  have htrace : WordTrace (prefixWord ++ tailWord_54397) baseStart_54397 baseEnd_54397 := by
    simpa [prefixWord, tailWord_54397, baseEnd_54397] using wordTrace_append hprefix tailTrace_54397
  have hstable : (prefixWord ++ tailWord_54397).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54397).length < 2 ^ (prefixWord ++ tailWord_54397).sum := by decide
  have hdescent : baseEnd_54397 < baseStart_54397 := by decide
  rcases family_descends (prefixWord ++ tailWord_54397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54431 : List Nat := [1, 1, 2, 6, 2, 2, 1, 4]
def baseStart_54431 : Nat := 118140960795 + 54431 * 2 ^ 59
def prefixEnd_54431 : Nat := 4983230072969 + 3 ^ 40 * 54431 * 2
def baseEnd_54431 : Nat := 16562527706655864984997

theorem tailTrace_54431 : CollatzResearch.WordTrace tailWord_54431 prefixEnd_54431 16562527706655864984997 := by
  unfold tailWord_54431
  simp only [CollatzResearch.WordTrace]
  refine ⟨1985261665813257919811147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1323507777208838613207431 1985261665813257919811147)
  ·
    refine ⟨2977892498719886879716721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1985261665813257919811147 2977892498719886879716721)
    ·
      refine ⟨2233419374039915159787541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2977892498719886879716721 2233419374039915159787541)
      ·
        refine ⟨104691533158121023115041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2233419374039915159787541 104691533158121023115041)
        ·
          refine ⟨78518649868590767336281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104691533158121023115041 78518649868590767336281)
          ·
            refine ⟨58888987401443075502211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78518649868590767336281 58888987401443075502211)
            ·
              refine ⟨88333481102164613253317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58888987401443075502211 88333481102164613253317)
              ·
                refine ⟨16562527706655864984997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88333481102164613253317 16562527706655864984997)
                ·
                  rfl

theorem cell19_54431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 4].length) (baseStart_54431 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_54431 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_54431 prefixEnd_54431 := by exact prefixLift 54431
  have htrace : WordTrace (prefixWord ++ tailWord_54431) baseStart_54431 baseEnd_54431 := by
    simpa [prefixWord, tailWord_54431, baseEnd_54431] using wordTrace_append hprefix tailTrace_54431
  have hstable : (prefixWord ++ tailWord_54431).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54431).length < 2 ^ (prefixWord ++ tailWord_54431).sum := by decide
  have hdescent : baseEnd_54431 < baseStart_54431 := by decide
  rcases family_descends (prefixWord ++ tailWord_54431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54509 : List Nat := [1, 5, 1, 2, 2, 2, 1, 5]
def baseStart_54509 : Nat := 118140960795 + 54509 * 2 ^ 59
def prefixEnd_54509 : Nat := 4983230072969 + 3 ^ 40 * 54509 * 2
def baseEnd_54509 : Nat := 16586261923574795251451

theorem tailTrace_54509 : CollatzResearch.WordTrace tailWord_54509 prefixEnd_54509 16586261923574795251451 := by
  unfold tailWord_54509
  simp only [CollatzResearch.WordTrace]
  refine ⟨1988106559530677241150581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1325404373020451494100387 1988106559530677241150581)
  ·
    refine ⟨186384989956000991357867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1988106559530677241150581 186384989956000991357867)
    ·
      refine ⟨279577484934001487036801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186384989956000991357867 279577484934001487036801)
      ·
        refine ⟨209683113700501115277601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279577484934001487036801 209683113700501115277601)
        ·
          refine ⟨157262335275375836458201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209683113700501115277601 157262335275375836458201)
          ·
            refine ⟨117946751456531877343651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157262335275375836458201 117946751456531877343651)
            ·
              refine ⟨176920127184797816015477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117946751456531877343651 176920127184797816015477)
              ·
                refine ⟨16586261923574795251451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 176920127184797816015477 16586261923574795251451)
                ·
                  rfl

theorem cell19_54509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 5].length) (baseStart_54509 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_54509 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_54509 prefixEnd_54509 := by exact prefixLift 54509
  have htrace : WordTrace (prefixWord ++ tailWord_54509) baseStart_54509 baseEnd_54509 := by
    simpa [prefixWord, tailWord_54509, baseEnd_54509] using wordTrace_append hprefix tailTrace_54509
  have hstable : (prefixWord ++ tailWord_54509).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54509).length < 2 ^ (prefixWord ++ tailWord_54509).sum := by decide
  have hdescent : baseEnd_54509 < baseStart_54509 := by decide
  rcases family_descends (prefixWord ++ tailWord_54509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54585 : List Nat := [1, 2, 1, 6, 3, 6]
def baseStart_54585 : Nat := 118140960795 + 54585 * 2 ^ 59
def prefixEnd_54585 : Nat := 4983230072969 + 3 ^ 40 * 54585 * 2
def baseEnd_54585 : Nat := 1845487507869904173595

theorem tailTrace_54585 : CollatzResearch.WordTrace tailWord_54585 prefixEnd_54585 1845487507869904173595 := by
  unfold tailWord_54585
  simp only [CollatzResearch.WordTrace]
  refine ⟨1990878507255342220917209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1327252338170228147278139 1990878507255342220917209)
  ·
    refine ⟨1493158880441506665687907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1990878507255342220917209 1493158880441506665687907)
    ·
      refine ⟨2239738320662259998531861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1493158880441506665687907 2239738320662259998531861)
      ·
        refine ⟨104987733781043437431181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2239738320662259998531861 104987733781043437431181)
        ·
          refine ⟨39370400167891289036693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104987733781043437431181 39370400167891289036693)
          ·
            refine ⟨1845487507869904173595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 39370400167891289036693 1845487507869904173595)
            ·
              rfl

theorem cell19_54585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 6].length) (baseStart_54585 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_54585 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_54585 prefixEnd_54585 := by exact prefixLift 54585
  have htrace : WordTrace (prefixWord ++ tailWord_54585) baseStart_54585 baseEnd_54585 := by
    simpa [prefixWord, tailWord_54585, baseEnd_54585] using wordTrace_append hprefix tailTrace_54585
  have hstable : (prefixWord ++ tailWord_54585).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54585).length < 2 ^ (prefixWord ++ tailWord_54585).sum := by decide
  have hdescent : baseEnd_54585 < baseStart_54585 := by decide
  rcases family_descends (prefixWord ++ tailWord_54585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54598 : List Nat := [6, 1, 1, 3, 1, 2, 1, 4]
def baseStart_54598 : Nat := 118140960795 + 54598 * 2 ^ 59
def prefixEnd_54598 : Nat := 4983230072969 + 3 ^ 40 * 54598 * 2
def baseEnd_54598 : Nat := 16613343273648959273431

theorem tailTrace_54598 : CollatzResearch.WordTrace tailWord_54598 prefixEnd_54598 16613343273648959273431 := by
  unfold tailWord_54598
  simp only [CollatzResearch.WordTrace]
  refine ⟨62229770506507670035639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1327568437472163627426965 62229770506507670035639)
  ·
    refine ⟨93344655759761505053459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62229770506507670035639 93344655759761505053459)
    ·
      refine ⟨140016983639642257580189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93344655759761505053459 140016983639642257580189)
      ·
        refine ⟨52506368864865846592571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140016983639642257580189 52506368864865846592571)
        ·
          refine ⟨78759553297298769888857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52506368864865846592571 78759553297298769888857)
          ·
            refine ⟨59069664972974077416643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78759553297298769888857 59069664972974077416643)
            ·
              refine ⟨88604497459461116124965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59069664972974077416643 88604497459461116124965)
              ·
                refine ⟨16613343273648959273431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88604497459461116124965 16613343273648959273431)
                ·
                  rfl

theorem cell19_54598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_54598 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_54598 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_54598 prefixEnd_54598 := by exact prefixLift 54598
  have htrace : WordTrace (prefixWord ++ tailWord_54598) baseStart_54598 baseEnd_54598 := by
    simpa [prefixWord, tailWord_54598, baseEnd_54598] using wordTrace_append hprefix tailTrace_54598
  have hstable : (prefixWord ++ tailWord_54598).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54598).length < 2 ^ (prefixWord ++ tailWord_54598).sum := by decide
  have hdescent : baseEnd_54598 < baseStart_54598 := by decide
  rcases family_descends (prefixWord ++ tailWord_54598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54604 : List Nat := [2, 2, 1, 3, 2, 4, 1, 4]
def baseStart_54604 : Nat := 118140960795 + 54604 * 2 ^ 59
def prefixEnd_54604 : Nat := 4983230072969 + 3 ^ 40 * 54604 * 2
def baseEnd_54604 : Nat := 16615168982642723140081

theorem tailTrace_54604 : CollatzResearch.WordTrace tailWord_54604 prefixEnd_54604 16615168982642723140081 := by
  unfold tailWord_54604
  simp only [CollatzResearch.WordTrace]
  refine ⟨995785747093254232929433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1327714329457672310572577 995785747093254232929433)
  ·
    refine ⟨746839310319940674697075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 995785747093254232929433 746839310319940674697075)
    ·
      refine ⟨1120258965479911012045613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 746839310319940674697075 1120258965479911012045613)
      ·
        refine ⟨420097112054966629517105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1120258965479911012045613 420097112054966629517105)
        ·
          refine ⟨315072834041224972137829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 420097112054966629517105 315072834041224972137829)
          ·
            refine ⟨59076156382729682275843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 315072834041224972137829 59076156382729682275843)
            ·
              refine ⟨88614234574094523413765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59076156382729682275843 88614234574094523413765)
              ·
                refine ⟨16615168982642723140081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88614234574094523413765 16615168982642723140081)
                ·
                  rfl

theorem cell19_54604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 4].length) (baseStart_54604 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_54604 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_54604 prefixEnd_54604 := by exact prefixLift 54604
  have htrace : WordTrace (prefixWord ++ tailWord_54604) baseStart_54604 baseEnd_54604 := by
    simpa [prefixWord, tailWord_54604, baseEnd_54604] using wordTrace_append hprefix tailTrace_54604
  have hstable : (prefixWord ++ tailWord_54604).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54604).length < 2 ^ (prefixWord ++ tailWord_54604).sum := by decide
  have hdescent : baseEnd_54604 < baseStart_54604 := by decide
  rcases family_descends (prefixWord ++ tailWord_54604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54674 : List Nat := [3, 2, 3, 3, 2, 1, 2, 3]
def baseStart_54674 : Nat := 118140960795 + 54674 * 2 ^ 59
def prefixEnd_54674 : Nat := 4983230072969 + 3 ^ 40 * 54674 * 2
def baseEnd_54674 : Nat := 16636468920903301584335

theorem tailTrace_54674 : CollatzResearch.WordTrace tailWord_54674 prefixEnd_54674 16636468920903301584335 := by
  unfold tailWord_54674
  simp only [CollatzResearch.WordTrace]
  refine ⟨498531150983227605226769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1329416402621940280604717 498531150983227605226769)
  ·
    refine ⟨373898363237420703920077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 498531150983227605226769 373898363237420703920077)
    ·
      refine ⟨140211886214032763970029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 373898363237420703920077 140211886214032763970029)
      ·
        refine ⟨52579457330262286488761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140211886214032763970029 52579457330262286488761)
        ·
          refine ⟨39434592997696714866571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52579457330262286488761 39434592997696714866571)
          ·
            refine ⟨59151889496545072299857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39434592997696714866571 59151889496545072299857)
            ·
              refine ⟨44363917122408804224893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59151889496545072299857 44363917122408804224893)
              ·
                refine ⟨16636468920903301584335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44363917122408804224893 16636468920903301584335)
                ·
                  rfl

theorem cell19_54674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 3].length) (baseStart_54674 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_54674 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_54674 prefixEnd_54674 := by exact prefixLift 54674
  have htrace : WordTrace (prefixWord ++ tailWord_54674) baseStart_54674 baseEnd_54674 := by
    simpa [prefixWord, tailWord_54674, baseEnd_54674] using wordTrace_append hprefix tailTrace_54674
  have hstable : (prefixWord ++ tailWord_54674).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54674).length < 2 ^ (prefixWord ++ tailWord_54674).sum := by decide
  have hdescent : baseEnd_54674 < baseStart_54674 := by decide
  rcases family_descends (prefixWord ++ tailWord_54674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54680 : List Nat := [2, 1, 2, 5, 2, 1, 1, 5]
def baseStart_54680 : Nat := 118140960795 + 54680 * 2 ^ 59
def prefixEnd_54680 : Nat := 4983230072969 + 3 ^ 40 * 54680 * 2
def baseEnd_54680 : Nat := 16638294629897065450985

theorem tailTrace_54680 : CollatzResearch.WordTrace tailWord_54680 prefixEnd_54680 16638294629897065450985 := by
  unfold tailWord_54680
  simp only [CollatzResearch.WordTrace]
  refine ⟨997171720955586722812747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1329562294607448963750329 997171720955586722812747)
  ·
    refine ⟨1495757581433380084219121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 997171720955586722812747 1495757581433380084219121)
    ·
      refine ⟨1121818186075035063164341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1495757581433380084219121 1121818186075035063164341)
      ·
        refine ⟨105170454944534537171657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1121818186075035063164341 105170454944534537171657)
        ·
          refine ⟨78877841208400902878743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105170454944534537171657 78877841208400902878743)
          ·
            refine ⟨118316761812601354318115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78877841208400902878743 118316761812601354318115)
            ·
              refine ⟨177475142718902031477173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118316761812601354318115 177475142718902031477173)
              ·
                refine ⟨16638294629897065450985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 177475142718902031477173 16638294629897065450985)
                ·
                  rfl

theorem cell19_54680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 5].length) (baseStart_54680 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_54680 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_54680 prefixEnd_54680 := by exact prefixLift 54680
  have htrace : WordTrace (prefixWord ++ tailWord_54680) baseStart_54680 baseEnd_54680 := by
    simpa [prefixWord, tailWord_54680, baseEnd_54680] using wordTrace_append hprefix tailTrace_54680
  have hstable : (prefixWord ++ tailWord_54680).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54680).length < 2 ^ (prefixWord ++ tailWord_54680).sum := by decide
  have hdescent : baseEnd_54680 < baseStart_54680 := by decide
  rcases family_descends (prefixWord ++ tailWord_54680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54682 : List Nat := [3, 1, 1, 4, 1, 1, 3, 5]
def baseStart_54682 : Nat := 118140960795 + 54682 * 2 ^ 59
def prefixEnd_54682 : Nat := 4983230072969 + 3 ^ 40 * 54682 * 2
def baseEnd_54682 : Nat := 16638903199561653406535

theorem tailTrace_54682 : CollatzResearch.WordTrace tailWord_54682 prefixEnd_54682 16638903199561653406535 := by
  unfold tailWord_54682
  simp only [CollatzResearch.WordTrace]
  refine ⟨498604096975981946799575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1329610925269285191465533 498604096975981946799575)
  ·
    refine ⟨747906145463972920199363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 498604096975981946799575 747906145463972920199363)
    ·
      refine ⟨1121859218195959380299045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 747906145463972920199363 1121859218195959380299045)
      ·
        refine ⟨210348603411742383806071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1121859218195959380299045 210348603411742383806071)
        ·
          refine ⟨315522905117613575709107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210348603411742383806071 315522905117613575709107)
          ·
            refine ⟨473284357676420363563661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315522905117613575709107 473284357676420363563661)
            ·
              refine ⟨177481634128657636336373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 473284357676420363563661 177481634128657636336373)
              ·
                refine ⟨16638903199561653406535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 177481634128657636336373 16638903199561653406535)
                ·
                  rfl

theorem cell19_54682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_54682 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_54682 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_54682 prefixEnd_54682 := by exact prefixLift 54682
  have htrace : WordTrace (prefixWord ++ tailWord_54682) baseStart_54682 baseEnd_54682 := by
    simpa [prefixWord, tailWord_54682, baseEnd_54682] using wordTrace_append hprefix tailTrace_54682
  have hstable : (prefixWord ++ tailWord_54682).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54682).length < 2 ^ (prefixWord ++ tailWord_54682).sum := by decide
  have hdescent : baseEnd_54682 < baseStart_54682 := by decide
  rcases family_descends (prefixWord ++ tailWord_54682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54773 : List Nat := [1, 3, 5, 1, 1, 3, 1, 4]
def baseStart_54773 : Nat := 118140960795 + 54773 * 2 ^ 59
def prefixEnd_54773 : Nat := 4983230072969 + 3 ^ 40 * 54773 * 2
def baseEnd_54773 : Nat := 16666593119300405384065

theorem tailTrace_54773 : CollatzResearch.WordTrace tailWord_54773 prefixEnd_54773 16666593119300405384065 := by
  unfold tailWord_54773
  simp only [CollatzResearch.WordTrace]
  refine ⟨1997735430574250328760973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1331823620382833552507315 1997735430574250328760973)
  ·
    refine ⟨749150786465343873285365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1997735430574250328760973 749150786465343873285365)
    ·
      refine ⟨70232886231125988120503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 749150786465343873285365 70232886231125988120503)
      ·
        refine ⟨105349329346688982180755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70232886231125988120503 105349329346688982180755)
        ·
          refine ⟨158023994020033473271133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105349329346688982180755 158023994020033473271133)
          ·
            refine ⟨59258997757512552476675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158023994020033473271133 59258997757512552476675)
            ·
              refine ⟨88888496636268828715013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59258997757512552476675 88888496636268828715013)
              ·
                refine ⟨16666593119300405384065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88888496636268828715013 16666593119300405384065)
                ·
                  rfl

theorem cell19_54773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 4].length) (baseStart_54773 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_54773 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_54773 prefixEnd_54773 := by exact prefixLift 54773
  have htrace : WordTrace (prefixWord ++ tailWord_54773) baseStart_54773 baseEnd_54773 := by
    simpa [prefixWord, tailWord_54773, baseEnd_54773] using wordTrace_append hprefix tailTrace_54773
  have hstable : (prefixWord ++ tailWord_54773).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54773).length < 2 ^ (prefixWord ++ tailWord_54773).sum := by decide
  have hdescent : baseEnd_54773 < baseStart_54773 := by decide
  rcases family_descends (prefixWord ++ tailWord_54773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54794 : List Nat := [3, 1, 2, 2, 2, 3, 3, 3]
def baseStart_54794 : Nat := 118140960795 + 54794 * 2 ^ 59
def prefixEnd_54794 : Nat := 4983230072969 + 3 ^ 40 * 54794 * 2
def baseEnd_54794 : Nat := 16672983100778578917341

theorem tailTrace_54794 : CollatzResearch.WordTrace tailWord_54794 prefixEnd_54794 16672983100778578917341 := by
  unfold tailWord_54794
  simp only [CollatzResearch.WordTrace]
  refine ⟨499625340874542728818859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1332334242332113943516957 499625340874542728818859)
  ·
    refine ⟨749438011311814093228289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 499625340874542728818859 749438011311814093228289)
    ·
      refine ⟨562078508483860569921217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 749438011311814093228289 562078508483860569921217)
      ·
        refine ⟨421558881362895427440913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 562078508483860569921217 421558881362895427440913)
        ·
          refine ⟨316169161022171570580685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 421558881362895427440913 316169161022171570580685)
          ·
            refine ⟨118563435383314338967757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 316169161022171570580685 118563435383314338967757)
            ·
              refine ⟨44461288268742877112909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118563435383314338967757 44461288268742877112909)
              ·
                refine ⟨16672983100778578917341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44461288268742877112909 16672983100778578917341)
                ·
                  rfl

theorem cell19_54794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_54794 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_54794 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_54794 prefixEnd_54794 := by exact prefixLift 54794
  have htrace : WordTrace (prefixWord ++ tailWord_54794) baseStart_54794 baseEnd_54794 := by
    simpa [prefixWord, tailWord_54794, baseEnd_54794] using wordTrace_append hprefix tailTrace_54794
  have hstable : (prefixWord ++ tailWord_54794).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54794).length < 2 ^ (prefixWord ++ tailWord_54794).sum := by decide
  have hdescent : baseEnd_54794 < baseStart_54794 := by decide
  rcases family_descends (prefixWord ++ tailWord_54794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54912 : List Nat := [2, 1, 1, 2, 1, 4, 1, 7]
def baseStart_54912 : Nat := 118140960795 + 54912 * 2 ^ 59
def prefixEnd_54912 : Nat := 4983230072969 + 3 ^ 40 * 54912 * 2
def baseEnd_54912 : Nat := 16708888710989268294797

theorem tailTrace_54912 : CollatzResearch.WordTrace tailWord_54912 prefixEnd_54912 16708888710989268294797 := by
  unfold tailWord_54912
  simp only [CollatzResearch.WordTrace]
  refine ⟨1001402588535338534035495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1335203451380451378713993 1001402588535338534035495)
  ·
    refine ⟨1502103882803007801053243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1001402588535338534035495 1502103882803007801053243)
    ·
      refine ⟨2253155824204511701579865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1502103882803007801053243 2253155824204511701579865)
      ·
        refine ⟨1689866868153383776184899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2253155824204511701579865 1689866868153383776184899)
        ·
          refine ⟨2534800302230075664277349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1689866868153383776184899 2534800302230075664277349)
          ·
            refine ⟨475275056668139187052003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2534800302230075664277349 475275056668139187052003)
            ·
              refine ⟨712912585002208780578005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 475275056668139187052003 712912585002208780578005)
              ·
                refine ⟨16708888710989268294797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 712912585002208780578005 16708888710989268294797)
                ·
                  rfl

theorem cell19_54912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_54912 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_54912 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_54912 prefixEnd_54912 := by exact prefixLift 54912
  have htrace : WordTrace (prefixWord ++ tailWord_54912) baseStart_54912 baseEnd_54912 := by
    simpa [prefixWord, tailWord_54912, baseEnd_54912] using wordTrace_append hprefix tailTrace_54912
  have hstable : (prefixWord ++ tailWord_54912).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54912).length < 2 ^ (prefixWord ++ tailWord_54912).sum := by decide
  have hdescent : baseEnd_54912 < baseStart_54912 := by decide
  rcases family_descends (prefixWord ++ tailWord_54912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54948 : List Nat := [2, 3, 1, 2, 2, 2, 3, 4]
def baseStart_54948 : Nat := 118140960795 + 54948 * 2 ^ 59
def prefixEnd_54948 : Nat := 4983230072969 + 3 ^ 40 * 54948 * 2
def baseEnd_54948 : Nat := 16719842964951851494699

theorem tailTrace_54948 : CollatzResearch.WordTrace tailWord_54948 prefixEnd_54948 16719842964951851494699 := by
  unfold tailWord_54948
  simp only [CollatzResearch.WordTrace]
  refine ⟨1002059102470127608190749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1336078803293503477587665 1002059102470127608190749)
  ·
    refine ⟨375772163426297853071531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1002059102470127608190749 375772163426297853071531)
    ·
      refine ⟨563658245139446779607297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375772163426297853071531 563658245139446779607297)
      ·
        refine ⟨422743683854585084705473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 563658245139446779607297 422743683854585084705473)
        ·
          refine ⟨317057762890938813529105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 422743683854585084705473 317057762890938813529105)
          ·
            refine ⟨237793322168204110146829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 317057762890938813529105 237793322168204110146829)
            ·
              refine ⟨89172495813076541305061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237793322168204110146829 89172495813076541305061)
              ·
                refine ⟨16719842964951851494699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89172495813076541305061 16719842964951851494699)
                ·
                  rfl

theorem cell19_54948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_54948 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_54948 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_54948 prefixEnd_54948 := by exact prefixLift 54948
  have htrace : WordTrace (prefixWord ++ tailWord_54948) baseStart_54948 baseEnd_54948 := by
    simpa [prefixWord, tailWord_54948, baseEnd_54948] using wordTrace_append hprefix tailTrace_54948
  have hstable : (prefixWord ++ tailWord_54948).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54948).length < 2 ^ (prefixWord ++ tailWord_54948).sum := by decide
  have hdescent : baseEnd_54948 < baseStart_54948 := by decide
  rcases family_descends (prefixWord ++ tailWord_54948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54969 : List Nat := [1, 2, 1, 4, 1, 1, 2, 7]
def baseStart_54969 : Nat := 118140960795 + 54969 * 2 ^ 59
def prefixEnd_54969 : Nat := 4983230072969 + 3 ^ 40 * 54969 * 2
def baseEnd_54969 : Nat := 16726232946430025027975

theorem tailTrace_54969 : CollatzResearch.WordTrace tailWord_54969 prefixEnd_54969 16726232946430025027975 := by
  unfold tailWord_54969
  simp only [CollatzResearch.WordTrace]
  refine ⟨2004884137864175802895961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1336589425242783868597307 2004884137864175802895961)
  ·
    refine ⟨1503663103398131852171971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2004884137864175802895961 1503663103398131852171971)
    ·
      refine ⟨2255494655097197778257957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1503663103398131852171971 2255494655097197778257957)
      ·
        refine ⟨422905247830724583423367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2255494655097197778257957 422905247830724583423367)
        ·
          refine ⟨634357871746086875135051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422905247830724583423367 634357871746086875135051)
          ·
            refine ⟨951536807619130312702577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 634357871746086875135051 951536807619130312702577)
            ·
              refine ⟨713652605714347734526933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 951536807619130312702577 713652605714347734526933)
              ·
                refine ⟨16726232946430025027975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 713652605714347734526933 16726232946430025027975)
                ·
                  rfl

theorem cell19_54969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 7].length) (baseStart_54969 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_54969 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_54969 prefixEnd_54969 := by exact prefixLift 54969
  have htrace : WordTrace (prefixWord ++ tailWord_54969) baseStart_54969 baseEnd_54969 := by
    simpa [prefixWord, tailWord_54969, baseEnd_54969] using wordTrace_append hprefix tailTrace_54969
  have hstable : (prefixWord ++ tailWord_54969).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54969).length < 2 ^ (prefixWord ++ tailWord_54969).sum := by decide
  have hdescent : baseEnd_54969 < baseStart_54969 := by decide
  rcases family_descends (prefixWord ++ tailWord_54969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54982 : List Nat := [6, 1, 2, 1, 1, 2, 6]
def baseStart_54982 : Nat := 118140960795 + 54982 * 2 ^ 59
def prefixEnd_54982 : Nat := 4983230072969 + 3 ^ 40 * 54982 * 2
def baseEnd_54982 : Nat := 5576729549749948913017

theorem tailTrace_54982 : CollatzResearch.WordTrace tailWord_54982 prefixEnd_54982 5576729549749948913017 := by
  unfold tailWord_54982
  simp only [CollatzResearch.WordTrace]
  refine ⟨62667446463033719472475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1336905524544719348746133 62667446463033719472475)
  ·
    refine ⟨94001169694550579208713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62667446463033719472475 94001169694550579208713)
    ·
      refine ⟨70500877270912934406535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94001169694550579208713 70500877270912934406535)
      ·
        refine ⟨105751315906369401609803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70500877270912934406535 105751315906369401609803)
        ·
          refine ⟨158626973859554102414705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105751315906369401609803 158626973859554102414705)
          ·
            refine ⟨118970230394665576811029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158626973859554102414705 118970230394665576811029)
            ·
              refine ⟨5576729549749948913017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 118970230394665576811029 5576729549749948913017)
              ·
                rfl

theorem cell19_54982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 6].length) (baseStart_54982 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_54982 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_54982 prefixEnd_54982 := by exact prefixLift 54982
  have htrace : WordTrace (prefixWord ++ tailWord_54982) baseStart_54982 baseEnd_54982 := by
    simpa [prefixWord, tailWord_54982, baseEnd_54982] using wordTrace_append hprefix tailTrace_54982
  have hstable : (prefixWord ++ tailWord_54982).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54982).length < 2 ^ (prefixWord ++ tailWord_54982).sum := by decide
  have hdescent : baseEnd_54982 < baseStart_54982 := by decide
  rcases family_descends (prefixWord ++ tailWord_54982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54986 : List Nat := [3, 1, 2, 1, 5, 1, 6]
def baseStart_54986 : Nat := 118140960795 + 54986 * 2 ^ 59
def prefixEnd_54986 : Nat := 4983230072969 + 3 ^ 40 * 54986 * 2
def baseEnd_54986 : Nat := 5577135262859674216717

theorem tailTrace_54986 : CollatzResearch.WordTrace tailWord_54986 prefixEnd_54986 5577135262859674216717 := by
  unfold tailWord_54986
  simp only [CollatzResearch.WordTrace]
  refine ⟨501376044700646926566203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1337002785868391804176541 501376044700646926566203)
  ·
    refine ⟨752064067050970389849305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 501376044700646926566203 752064067050970389849305)
    ·
      refine ⟨564048050288227792386979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 752064067050970389849305 564048050288227792386979)
      ·
        refine ⟨846072075432341688580469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564048050288227792386979 846072075432341688580469)
        ·
          refine ⟨79319257071782033304419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 846072075432341688580469 79319257071782033304419)
          ·
            refine ⟨118978885607673049956629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79319257071782033304419 118978885607673049956629)
            ·
              refine ⟨5577135262859674216717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 118978885607673049956629 5577135262859674216717)
              ·
                rfl

theorem cell19_54986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 6].length) (baseStart_54986 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_54986 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_54986 prefixEnd_54986 := by exact prefixLift 54986
  have htrace : WordTrace (prefixWord ++ tailWord_54986) baseStart_54986 baseEnd_54986 := by
    simpa [prefixWord, tailWord_54986, baseEnd_54986] using wordTrace_append hprefix tailTrace_54986
  have hstable : (prefixWord ++ tailWord_54986).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54986).length < 2 ^ (prefixWord ++ tailWord_54986).sum := by decide
  have hdescent : baseEnd_54986 < baseStart_54986 := by decide
  rcases family_descends (prefixWord ++ tailWord_54986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55007 : List Nat := [1, 1, 2, 3, 2, 2, 2, 6]
def baseStart_55007 : Nat := 118140960795 + 55007 * 2 ^ 59
def prefixEnd_55007 : Nat := 4983230072969 + 3 ^ 40 * 55007 * 2
def baseEnd_55007 : Nat := 16737795770057196183427

theorem tailTrace_55007 : CollatzResearch.WordTrace tailWord_55007 prefixEnd_55007 16737795770057196183427 := by
  unfold tailWord_55007
  simp only [CollatzResearch.WordTrace]
  refine ⟨2006270111726508292779275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1337513407817672195186183 2006270111726508292779275)
  ·
    refine ⟨3009405167589762439168913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2006270111726508292779275 3009405167589762439168913)
    ·
      refine ⟨2257053875692321829376685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3009405167589762439168913 2257053875692321829376685)
      ·
        refine ⟨846395203384620686016257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2257053875692321829376685 846395203384620686016257)
        ·
          refine ⟨634796402538465514512193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 846395203384620686016257 634796402538465514512193)
          ·
            refine ⟨476097301903849135884145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 634796402538465514512193 476097301903849135884145)
            ·
              refine ⟨357072976427886851913109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 476097301903849135884145 357072976427886851913109)
              ·
                refine ⟨16737795770057196183427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 357072976427886851913109 16737795770057196183427)
                ·
                  rfl

theorem cell19_55007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 6].length) (baseStart_55007 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_55007 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_55007 prefixEnd_55007 := by exact prefixLift 55007
  have htrace : WordTrace (prefixWord ++ tailWord_55007) baseStart_55007 baseEnd_55007 := by
    simpa [prefixWord, tailWord_55007, baseEnd_55007] using wordTrace_append hprefix tailTrace_55007
  have hstable : (prefixWord ++ tailWord_55007).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55007).length < 2 ^ (prefixWord ++ tailWord_55007).sum := by decide
  have hdescent : baseEnd_55007 < baseStart_55007 := by decide
  rcases family_descends (prefixWord ++ tailWord_55007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55064 : List Nat := [2, 1, 2, 3, 1, 1, 3, 6]
def baseStart_55064 : Nat := 118140960795 + 55064 * 2 ^ 59
def prefixEnd_55064 : Nat := 4983230072969 + 3 ^ 40 * 55064 * 2
def baseEnd_55064 : Nat := 16755140005497952916605

theorem tailTrace_55064 : CollatzResearch.WordTrace tailWord_55064 prefixEnd_55064 16755140005497952916605 := by
  unfold tailWord_55064
  simp only [CollatzResearch.WordTrace]
  refine ⟨1004174536260003513802123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1338899381680004685069497 1004174536260003513802123)
  ·
    refine ⟨1506261804390005270703185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1004174536260003513802123 1506261804390005270703185)
    ·
      refine ⟨1129696353292503953027389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1506261804390005270703185 1129696353292503953027389)
      ·
        refine ⟨423636132484688982385271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1129696353292503953027389 423636132484688982385271)
        ·
          refine ⟨635454198727033473577907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423636132484688982385271 635454198727033473577907)
          ·
            refine ⟨953181298090550210366861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635454198727033473577907 953181298090550210366861)
            ·
              refine ⟨357442986783956328887573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 953181298090550210366861 357442986783956328887573)
              ·
                refine ⟨16755140005497952916605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 357442986783956328887573 16755140005497952916605)
                ·
                  rfl

theorem cell19_55064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_55064 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_55064 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_55064 prefixEnd_55064 := by exact prefixLift 55064
  have htrace : WordTrace (prefixWord ++ tailWord_55064) baseStart_55064 baseEnd_55064 := by
    simpa [prefixWord, tailWord_55064, baseEnd_55064] using wordTrace_append hprefix tailTrace_55064
  have hstable : (prefixWord ++ tailWord_55064).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55064).length < 2 ^ (prefixWord ++ tailWord_55064).sum := by decide
  have hdescent : baseEnd_55064 < baseStart_55064 := by decide
  rcases family_descends (prefixWord ++ tailWord_55064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55117 : List Nat := [1, 6, 1, 2, 1, 1, 3, 4]
def baseStart_55117 : Nat := 118140960795 + 55117 * 2 ^ 59
def prefixEnd_55117 : Nat := 4983230072969 + 3 ^ 40 * 55117 * 2
def baseEnd_55117 : Nat := 16771267101609533738683

theorem tailTrace_55117 : CollatzResearch.WordTrace tailWord_55117 prefixEnd_55117 16771267101609533738683 := by
  unfold tailWord_55117
  simp only [CollatzResearch.WordTrace]
  refine ⟨2010282141327997079283605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1340188094218664719522403 2010282141327997079283605)
  ·
    refine ⟨94231975374749863091419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2010282141327997079283605 94231975374749863091419)
    ·
      refine ⟨141347963062124794637129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94231975374749863091419 141347963062124794637129)
      ·
        refine ⟨106010972296593595977847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141347963062124794637129 106010972296593595977847)
        ·
          refine ⟨159016458444890393966771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106010972296593595977847 159016458444890393966771)
          ·
            refine ⟨238524687667335590950157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159016458444890393966771 238524687667335590950157)
            ·
              refine ⟨89446757875250846606309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 238524687667335590950157 89446757875250846606309)
              ·
                refine ⟨16771267101609533738683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89446757875250846606309 16771267101609533738683)
                ·
                  rfl

theorem cell19_55117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 4].length) (baseStart_55117 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_55117 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_55117 prefixEnd_55117 := by exact prefixLift 55117
  have htrace : WordTrace (prefixWord ++ tailWord_55117) baseStart_55117 baseEnd_55117 := by
    simpa [prefixWord, tailWord_55117, baseEnd_55117] using wordTrace_append hprefix tailTrace_55117
  have hstable : (prefixWord ++ tailWord_55117).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55117).length < 2 ^ (prefixWord ++ tailWord_55117).sum := by decide
  have hdescent : baseEnd_55117 < baseStart_55117 := by decide
  rcases family_descends (prefixWord ++ tailWord_55117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55271 : List Nat := [1, 1, 5, 2, 4, 6]
def baseStart_55271 : Nat := 118140960795 + 55271 * 2 ^ 59
def prefixEnd_55271 : Nat := 4983230072969 + 3 ^ 40 * 55271 * 2
def baseEnd_55271 : Nat := 1868680773975867368449

theorem tailTrace_55271 : CollatzResearch.WordTrace tailWord_55271 prefixEnd_55271 1868680773975867368449 := by
  unfold tailWord_55271
  simp only [CollatzResearch.WordTrace]
  refine ⟨2015898982770081380389667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1343932655180054253593111 2015898982770081380389667)
  ·
    refine ⟨3023848474155122070584501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2015898982770081380389667 3023848474155122070584501)
    ·
      refine ⟨283485794452042694117297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3023848474155122070584501 283485794452042694117297)
      ·
        refine ⟨212614345839032020587973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 283485794452042694117297 212614345839032020587973)
        ·
          refine ⟨39865189844818503860245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 212614345839032020587973 39865189844818503860245)
          ·
            refine ⟨1868680773975867368449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 39865189844818503860245 1868680773975867368449)
            ·
              rfl

theorem cell19_55271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 6].length) (baseStart_55271 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_55271 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_55271 prefixEnd_55271 := by exact prefixLift 55271
  have htrace : WordTrace (prefixWord ++ tailWord_55271) baseStart_55271 baseEnd_55271 := by
    simpa [prefixWord, tailWord_55271, baseEnd_55271] using wordTrace_append hprefix tailTrace_55271
  have hstable : (prefixWord ++ tailWord_55271).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55271).length < 2 ^ (prefixWord ++ tailWord_55271).sum := by decide
  have hdescent : baseEnd_55271 < baseStart_55271 := by decide
  rcases family_descends (prefixWord ++ tailWord_55271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55286 : List Nat := [5, 1, 1, 1, 5, 1, 1, 4]
def baseStart_55286 : Nat := 118140960795 + 55286 * 2 ^ 59
def prefixEnd_55286 : Nat := 4983230072969 + 3 ^ 40 * 55286 * 2
def baseEnd_55286 : Nat := 16822691238267215982667

theorem tailTrace_55286 : CollatzResearch.WordTrace tailWord_55286 prefixEnd_55286 16822691238267215982667 := by
  unfold tailWord_55286
  simp only [CollatzResearch.WordTrace]
  refine ⟨126027879857233683886607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1344297385143825961457141 126027879857233683886607)
  ·
    refine ⟨189041819785850525829911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126027879857233683886607 189041819785850525829911)
    ·
      refine ⟨283562729678775788744867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189041819785850525829911 283562729678775788744867)
      ·
        refine ⟨425344094518163683117301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283562729678775788744867 425344094518163683117301)
        ·
          refine ⟨39876008861077845292247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 425344094518163683117301 39876008861077845292247)
          ·
            refine ⟨59814013291616767938371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39876008861077845292247 59814013291616767938371)
            ·
              refine ⟨89721019937425151907557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59814013291616767938371 89721019937425151907557)
              ·
                refine ⟨16822691238267215982667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89721019937425151907557 16822691238267215982667)
                ·
                  rfl

theorem cell19_55286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_55286 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_55286 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_55286 prefixEnd_55286 := by exact prefixLift 55286
  have htrace : WordTrace (prefixWord ++ tailWord_55286) baseStart_55286 baseEnd_55286 := by
    simpa [prefixWord, tailWord_55286, baseEnd_55286] using wordTrace_append hprefix tailTrace_55286
  have hstable : (prefixWord ++ tailWord_55286).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55286).length < 2 ^ (prefixWord ++ tailWord_55286).sum := by decide
  have hdescent : baseEnd_55286 < baseStart_55286 := by decide
  rcases family_descends (prefixWord ++ tailWord_55286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55330 : List Nat := [3, 3, 1, 1, 1, 2, 8]
def baseStart_55330 : Nat := 118140960795 + 55330 * 2 ^ 59
def prefixEnd_55330 : Nat := 4983230072969 + 3 ^ 40 * 55330 * 2
def baseEnd_55330 : Nat := 5612026590296050334923

theorem tailTrace_55330 : CollatzResearch.WordTrace tailWord_55330 prefixEnd_55330 5612026590296050334923 := by
  unfold tailWord_55330
  simp only [CollatzResearch.WordTrace]
  refine ⟨504512722389083614196861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1345367259704222971191629 504512722389083614196861)
  ·
    refine ⟨189192270895906355323823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 504512722389083614196861 189192270895906355323823)
    ·
      refine ⟨283788406343859532985735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189192270895906355323823 283788406343859532985735)
      ·
        refine ⟨425682609515789299478603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283788406343859532985735 425682609515789299478603)
        ·
          refine ⟨638523914273683949217905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425682609515789299478603 638523914273683949217905)
          ·
            refine ⟨478892935705262961913429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 638523914273683949217905 478892935705262961913429)
            ·
              refine ⟨5612026590296050334923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 478892935705262961913429 5612026590296050334923)
              ·
                rfl

theorem cell19_55330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 8].length) (baseStart_55330 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_55330 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_55330 prefixEnd_55330 := by exact prefixLift 55330
  have htrace : WordTrace (prefixWord ++ tailWord_55330) baseStart_55330 baseEnd_55330 := by
    simpa [prefixWord, tailWord_55330, baseEnd_55330] using wordTrace_append hprefix tailTrace_55330
  have hstable : (prefixWord ++ tailWord_55330).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55330).length < 2 ^ (prefixWord ++ tailWord_55330).sum := by decide
  have hdescent : baseEnd_55330 < baseStart_55330 := by decide
  rcases family_descends (prefixWord ++ tailWord_55330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55503 : List Nat := [1, 1, 2, 1, 1, 3, 10]
def baseStart_55503 : Nat := 118140960795 + 55503 * 2 ^ 59
def prefixEnd_55503 : Nat := 4983230072969 + 3 ^ 40 * 55503 * 2
def baseEnd_55503 : Nat := 5629573682291669719951

theorem tailTrace_55503 : CollatzResearch.WordTrace tailWord_55503 prefixEnd_55503 5629573682291669719951 := by
  unfold tailWord_55503
  simp only [CollatzResearch.WordTrace]
  refine ⟨2024360717929585002835163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1349573811953056668556775 2024360717929585002835163)
  ·
    refine ⟨3036541076894377504252745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2024360717929585002835163 3036541076894377504252745)
    ·
      refine ⟨2277405807670783128189559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3036541076894377504252745 2277405807670783128189559)
      ·
        refine ⟨3416108711506174692284339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2277405807670783128189559 3416108711506174692284339)
        ·
          refine ⟨5124163067259262038426509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3416108711506174692284339 5124163067259262038426509)
          ·
            refine ⟨1921561150222223264409941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5124163067259262038426509 1921561150222223264409941)
            ·
              refine ⟨5629573682291669719951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1921561150222223264409941 5629573682291669719951)
              ·
                rfl

theorem cell19_55503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 10].length) (baseStart_55503 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_55503 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_55503 prefixEnd_55503 := by exact prefixLift 55503
  have htrace : WordTrace (prefixWord ++ tailWord_55503) baseStart_55503 baseEnd_55503 := by
    simpa [prefixWord, tailWord_55503, baseEnd_55503] using wordTrace_append hprefix tailTrace_55503
  have hstable : (prefixWord ++ tailWord_55503).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55503).length < 2 ^ (prefixWord ++ tailWord_55503).sum := by decide
  have hdescent : baseEnd_55503 < baseStart_55503 := by decide
  rcases family_descends (prefixWord ++ tailWord_55503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55533 : List Nat := [1, 5, 1, 2, 4, 1, 2, 3]
def baseStart_55533 : Nat := 118140960795 + 55533 * 2 ^ 59
def prefixEnd_55533 : Nat := 4983230072969 + 3 ^ 40 * 55533 * 2
def baseEnd_55533 : Nat := 16897849591843828493105

theorem tailTrace_55533 : CollatzResearch.WordTrace tailWord_55533 prefixEnd_55533 16897849591843828493105 := by
  unfold tailWord_55533
  simp only [CollatzResearch.WordTrace]
  refine ⟨2025454907820900126427253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1350303271880600084284835 2025454907820900126427253)
  ·
    refine ⟨189886397608209386852555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2025454907820900126427253 189886397608209386852555)
    ·
      refine ⟨284829596412314080278833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189886397608209386852555 284829596412314080278833)
      ·
        refine ⟨213622197309235560209125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284829596412314080278833 213622197309235560209125)
        ·
          refine ⟨40054161995481667539211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 213622197309235560209125 40054161995481667539211)
          ·
            refine ⟨60081242993222501308817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40054161995481667539211 60081242993222501308817)
            ·
              refine ⟨45060932244916875981613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60081242993222501308817 45060932244916875981613)
              ·
                refine ⟨16897849591843828493105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45060932244916875981613 16897849591843828493105)
                ·
                  rfl

theorem cell19_55533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 3].length) (baseStart_55533 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_55533 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_55533 prefixEnd_55533 := by exact prefixLift 55533
  have htrace : WordTrace (prefixWord ++ tailWord_55533) baseStart_55533 baseEnd_55533 := by
    simpa [prefixWord, tailWord_55533, baseEnd_55533] using wordTrace_append hprefix tailTrace_55533
  have hstable : (prefixWord ++ tailWord_55533).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55533).length < 2 ^ (prefixWord ++ tailWord_55533).sum := by decide
  have hdescent : baseEnd_55533 < baseStart_55533 := by decide
  rcases family_descends (prefixWord ++ tailWord_55533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55556 : List Nat := [2, 3, 2, 2, 3, 2, 5]
def baseStart_55556 : Nat := 118140960795 + 55556 * 2 ^ 59
def prefixEnd_55556 : Nat := 4983230072969 + 3 ^ 40 * 55556 * 2
def baseEnd_55556 : Nat := 5634949380995529993977

theorem tailTrace_55556 : CollatzResearch.WordTrace tailWord_55556 prefixEnd_55556 5634949380995529993977 := by
  unfold tailWord_55556
  simp only [CollatzResearch.WordTrace]
  refine ⟨1013146893368787527257261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1350862524491716703009681 1013146893368787527257261)
  ·
    refine ⟨379930085013295322721473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1013146893368787527257261 379930085013295322721473)
    ·
      refine ⟨284947563759971492041105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379930085013295322721473 284947563759971492041105)
      ·
        refine ⟨213710672819978619030829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284947563759971492041105 213710672819978619030829)
        ·
          refine ⟨80141502307491982136561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213710672819978619030829 80141502307491982136561)
          ·
            refine ⟨60106126730618986602421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80141502307491982136561 60106126730618986602421)
            ·
              refine ⟨5634949380995529993977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60106126730618986602421 5634949380995529993977)
              ·
                rfl

theorem cell19_55556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 5].length) (baseStart_55556 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_55556 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_55556 prefixEnd_55556 := by exact prefixLift 55556
  have htrace : WordTrace (prefixWord ++ tailWord_55556) baseStart_55556 baseEnd_55556 := by
    simpa [prefixWord, tailWord_55556, baseEnd_55556] using wordTrace_append hprefix tailTrace_55556
  have hstable : (prefixWord ++ tailWord_55556).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55556).length < 2 ^ (prefixWord ++ tailWord_55556).sum := by decide
  have hdescent : baseEnd_55556 < baseStart_55556 := by decide
  rcases family_descends (prefixWord ++ tailWord_55556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55579 : List Nat := [1, 1, 1, 1, 1, 1, 7, 6]
def baseStart_55579 : Nat := 118140960795 + 55579 * 2 ^ 59
def prefixEnd_55579 : Nat := 4983230072969 + 3 ^ 40 * 55579 * 2
def baseEnd_55579 : Nat := 16911846694129351470757

theorem tailTrace_55579 : CollatzResearch.WordTrace tailWord_55579 prefixEnd_55579 16911846694129351470757 := by
  unfold tailWord_55579
  simp only [CollatzResearch.WordTrace]
  refine ⟨2027132665654249982601791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1351421777102833321734527 2027132665654249982601791)
  ·
    refine ⟨3040698998481374973902687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2027132665654249982601791 3040698998481374973902687)
    ·
      refine ⟨4561048497722062460854031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3040698998481374973902687 4561048497722062460854031)
      ·
        refine ⟨6841572746583093691281047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4561048497722062460854031 6841572746583093691281047)
        ·
          refine ⟨10262359119874640536921571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6841572746583093691281047 10262359119874640536921571)
          ·
            refine ⟨15393538679811960805382357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10262359119874640536921571 15393538679811960805382357)
            ·
              refine ⟨360786062808092831376149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 15393538679811960805382357 360786062808092831376149)
              ·
                refine ⟨16911846694129351470757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 360786062808092831376149 16911846694129351470757)
                ·
                  rfl

theorem cell19_55579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 6].length) (baseStart_55579 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_55579 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_55579 prefixEnd_55579 := by exact prefixLift 55579
  have htrace : WordTrace (prefixWord ++ tailWord_55579) baseStart_55579 baseEnd_55579 := by
    simpa [prefixWord, tailWord_55579, baseEnd_55579] using wordTrace_append hprefix tailTrace_55579
  have hstable : (prefixWord ++ tailWord_55579).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55579).length < 2 ^ (prefixWord ++ tailWord_55579).sum := by decide
  have hdescent : baseEnd_55579 < baseStart_55579 := by decide
  rcases family_descends (prefixWord ++ tailWord_55579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55634 : List Nat := [3, 2, 2, 1, 1, 1, 5, 4]
def baseStart_55634 : Nat := 118140960795 + 55634 * 2 ^ 59
def prefixEnd_55634 : Nat := 4983230072969 + 3 ^ 40 * 55634 * 2
def baseEnd_55634 : Nat := 16928582359905520248385

theorem tailTrace_55634 : CollatzResearch.WordTrace tailWord_55634 prefixEnd_55634 16928582359905520248385 := by
  unfold tailWord_55634
  simp only [CollatzResearch.WordTrace]
  refine ⟨507284670113748593963489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1352759120303329583902637 507284670113748593963489)
  ·
    refine ⟨380463502585311445472617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 507284670113748593963489 380463502585311445472617)
    ·
      refine ⟨285347626938983584104463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380463502585311445472617 285347626938983584104463)
      ·
        refine ⟨428021440408475376156695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285347626938983584104463 428021440408475376156695)
        ·
          refine ⟨642032160612713064235043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428021440408475376156695 642032160612713064235043)
          ·
            refine ⟨963048240919069596352565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642032160612713064235043 963048240919069596352565)
            ·
              refine ⟨90285772586162774658053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 963048240919069596352565 90285772586162774658053)
              ·
                refine ⟨16928582359905520248385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90285772586162774658053 16928582359905520248385)
                ·
                  rfl

theorem cell19_55634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_55634 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_55634 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_55634 prefixEnd_55634 := by exact prefixLift 55634
  have htrace : WordTrace (prefixWord ++ tailWord_55634) baseStart_55634 baseEnd_55634 := by
    simpa [prefixWord, tailWord_55634, baseEnd_55634] using wordTrace_append hprefix tailTrace_55634
  have hstable : (prefixWord ++ tailWord_55634).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55634).length < 2 ^ (prefixWord ++ tailWord_55634).sum := by decide
  have hdescent : baseEnd_55634 < baseStart_55634 := by decide
  rcases family_descends (prefixWord ++ tailWord_55634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55725 : List Nat := [1, 5, 2, 2, 3, 1, 5]
def baseStart_55725 : Nat := 118140960795 + 55725 * 2 ^ 59
def prefixEnd_55725 : Nat := 4983230072969 + 3 ^ 40 * 55725 * 2
def baseEnd_55725 : Nat := 5652090759881424075305

theorem tailTrace_55725 : CollatzResearch.WordTrace tailWord_55725 prefixEnd_55725 5652090759881424075305 := by
  unfold tailWord_55725
  simp only [CollatzResearch.WordTrace]
  refine ⟨2032457723125316917416629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1354971815416877944944419 2032457723125316917416629)
  ·
    refine ⟨190542911542998461007809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2032457723125316917416629 190542911542998461007809)
    ·
      refine ⟨142907183657248845755857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190542911542998461007809 142907183657248845755857)
      ·
        refine ⟨107180387742936634316893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142907183657248845755857 107180387742936634316893)
        ·
          refine ⟨40192645403601237868835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107180387742936634316893 40192645403601237868835)
          ·
            refine ⟨60288968105401856803253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40192645403601237868835 60288968105401856803253)
            ·
              refine ⟨5652090759881424075305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60288968105401856803253 5652090759881424075305)
              ·
                rfl

theorem cell19_55725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 5].length) (baseStart_55725 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_55725 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_55725 prefixEnd_55725 := by exact prefixLift 55725
  have htrace : WordTrace (prefixWord ++ tailWord_55725) baseStart_55725 baseEnd_55725 := by
    simpa [prefixWord, tailWord_55725, baseEnd_55725] using wordTrace_append hprefix tailTrace_55725
  have hstable : (prefixWord ++ tailWord_55725).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55725).length < 2 ^ (prefixWord ++ tailWord_55725).sum := by decide
  have hdescent : baseEnd_55725 < baseStart_55725 := by decide
  rcases family_descends (prefixWord ++ tailWord_55725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55729 : List Nat := [1, 2, 2, 4, 1, 4, 5]
def baseStart_55729 : Nat := 118140960795 + 55729 * 2 ^ 59
def prefixEnd_55729 : Nat := 4983230072969 + 3 ^ 40 * 55729 * 2
def baseEnd_55729 : Nat := 5652496472991149379005

theorem tailTrace_55729 : CollatzResearch.WordTrace tailWord_55729 prefixEnd_55729 5652496472991149379005 := by
  unfold tailWord_55729
  simp only [CollatzResearch.WordTrace]
  refine ⟨2032603615110825600562241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1355069076740550400374827 2032603615110825600562241)
  ·
    refine ⟨1524452711333119200421681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2032603615110825600562241 1524452711333119200421681)
    ·
      refine ⟨1143339533499839400316261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1524452711333119200421681 1143339533499839400316261)
      ·
        refine ⟨214376162531219887559299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1143339533499839400316261 214376162531219887559299)
        ·
          refine ⟨321564243796829831338949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214376162531219887559299 321564243796829831338949)
          ·
            refine ⟨60293295711905593376053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 321564243796829831338949 60293295711905593376053)
            ·
              refine ⟨5652496472991149379005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60293295711905593376053 5652496472991149379005)
              ·
                rfl

theorem cell19_55729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 5].length) (baseStart_55729 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_55729 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_55729 prefixEnd_55729 := by exact prefixLift 55729
  have htrace : WordTrace (prefixWord ++ tailWord_55729) baseStart_55729 baseEnd_55729 := by
    simpa [prefixWord, tailWord_55729, baseEnd_55729] using wordTrace_append hprefix tailTrace_55729
  have hstable : (prefixWord ++ tailWord_55729).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55729).length < 2 ^ (prefixWord ++ tailWord_55729).sum := by decide
  have hdescent : baseEnd_55729 < baseStart_55729 := by decide
  rcases family_descends (prefixWord ++ tailWord_55729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55769 : List Nat := [1, 2, 1, 2, 4, 1, 1, 7]
def baseStart_55769 : Nat := 118140960795 + 55769 * 2 ^ 59
def prefixEnd_55769 : Nat := 4983230072969 + 3 ^ 40 * 55769 * 2
def baseEnd_55769 : Nat := 16969660812265207248017

theorem tailTrace_55769 : CollatzResearch.WordTrace tailWord_55769 prefixEnd_55769 16969660812265207248017 := by
  unfold tailWord_55769
  simp only [CollatzResearch.WordTrace]
  refine ⟨2034062534965912432018361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1356041689977274954678907 2034062534965912432018361)
  ·
    refine ⟨1525546901224434324013771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2034062534965912432018361 1525546901224434324013771)
    ·
      refine ⟨2288320351836651486020657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1525546901224434324013771 2288320351836651486020657)
      ·
        refine ⟨1716240263877488614515493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2288320351836651486020657 1716240263877488614515493)
        ·
          refine ⟨321795049477029115221655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1716240263877488614515493 321795049477029115221655)
          ·
            refine ⟨482692574215543672832483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321795049477029115221655 482692574215543672832483)
            ·
              refine ⟨724038861323315509248725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482692574215543672832483 724038861323315509248725)
              ·
                refine ⟨16969660812265207248017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 724038861323315509248725 16969660812265207248017)
                ·
                  rfl

theorem cell19_55769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 7].length) (baseStart_55769 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_55769 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_55769 prefixEnd_55769 := by exact prefixLift 55769
  have htrace : WordTrace (prefixWord ++ tailWord_55769) baseStart_55769 baseEnd_55769 := by
    simpa [prefixWord, tailWord_55769, baseEnd_55769] using wordTrace_append hprefix tailTrace_55769
  have hstable : (prefixWord ++ tailWord_55769).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55769).length < 2 ^ (prefixWord ++ tailWord_55769).sum := by decide
  have hdescent : baseEnd_55769 < baseStart_55769 := by decide
  rcases family_descends (prefixWord ++ tailWord_55769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55822 : List Nat := [4, 1, 1, 2, 3, 2, 3, 3]
def baseStart_55822 : Nat := 118140960795 + 55822 * 2 ^ 59
def prefixEnd_55822 : Nat := 4983230072969 + 3 ^ 40 * 55822 * 2
def baseEnd_55822 : Nat := 16985787908376788070095

theorem tailTrace_55822 : CollatzResearch.WordTrace tailWord_55822 prefixEnd_55822 16985787908376788070095 := by
  unfold tailWord_55822
  simp only [CollatzResearch.WordTrace]
  refine ⟨254499450471737810462215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1357330402515934989131813 254499450471737810462215)
  ·
    refine ⟨381749175707606715693323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254499450471737810462215 381749175707606715693323)
    ·
      refine ⟨572623763561410073539985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381749175707606715693323 572623763561410073539985)
      ·
        refine ⟨429467822671057555154989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 572623763561410073539985 429467822671057555154989)
        ·
          refine ⟨161050433501646583183121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 429467822671057555154989 161050433501646583183121)
          ·
            refine ⟨120787825126234937387341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161050433501646583183121 120787825126234937387341)
            ·
              refine ⟨45295434422338101520253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120787825126234937387341 45295434422338101520253)
              ·
                refine ⟨16985787908376788070095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45295434422338101520253 16985787908376788070095)
                ·
                  rfl

theorem cell19_55822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_55822 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_55822 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_55822 prefixEnd_55822 := by exact prefixLift 55822
  have htrace : WordTrace (prefixWord ++ tailWord_55822) baseStart_55822 baseEnd_55822 := by
    simpa [prefixWord, tailWord_55822, baseEnd_55822] using wordTrace_append hprefix tailTrace_55822
  have hstable : (prefixWord ++ tailWord_55822).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55822).length < 2 ^ (prefixWord ++ tailWord_55822).sum := by decide
  have hdescent : baseEnd_55822 < baseStart_55822 := by decide
  rcases family_descends (prefixWord ++ tailWord_55822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55864 : List Nat := [2, 1, 2, 1, 4, 1, 2, 6]
def baseStart_55864 : Nat := 118140960795 + 55864 * 2 ^ 59
def prefixEnd_55864 : Nat := 4983230072969 + 3 ^ 40 * 55864 * 2
def baseEnd_55864 : Nat := 16998567871333135136647

theorem tailTrace_55864 : CollatzResearch.WordTrace tailWord_55864 prefixEnd_55864 16998567871333135136647 := by
  unfold tailWord_55864
  simp only [CollatzResearch.WordTrace]
  refine ⟨1018763734810871828363323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1358351646414495771151097 1018763734810871828363323)
  ·
    refine ⟨1528145602216307742544985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1018763734810871828363323 1528145602216307742544985)
    ·
      refine ⟨1146109201662230806908739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1528145602216307742544985 1146109201662230806908739)
      ·
        refine ⟨1719163802493346210363109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1146109201662230806908739 1719163802493346210363109)
        ·
          refine ⟨322343212967502414443083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1719163802493346210363109 322343212967502414443083)
          ·
            refine ⟨483514819451253621664625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322343212967502414443083 483514819451253621664625)
            ·
              refine ⟨362636114588440216248469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 483514819451253621664625 362636114588440216248469)
              ·
                refine ⟨16998567871333135136647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 362636114588440216248469 16998567871333135136647)
                ·
                  rfl

theorem cell19_55864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_55864 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_55864 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_55864 prefixEnd_55864 := by exact prefixLift 55864
  have htrace : WordTrace (prefixWord ++ tailWord_55864) baseStart_55864 baseEnd_55864 := by
    simpa [prefixWord, tailWord_55864, baseEnd_55864] using wordTrace_append hprefix tailTrace_55864
  have hstable : (prefixWord ++ tailWord_55864).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55864).length < 2 ^ (prefixWord ++ tailWord_55864).sum := by decide
  have hdescent : baseEnd_55864 < baseStart_55864 := by decide
  rcases family_descends (prefixWord ++ tailWord_55864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55879 : List Nat := [1, 1, 4, 1, 4, 3, 2, 3]
def baseStart_55879 : Nat := 118140960795 + 55879 * 2 ^ 59
def prefixEnd_55879 : Nat := 4983230072969 + 3 ^ 40 * 55879 * 2
def baseEnd_55879 : Nat := 17003132143817544803273

theorem tailTrace_55879 : CollatzResearch.WordTrace tailWord_55879 prefixEnd_55879 17003132143817544803273 := by
  unfold tailWord_55879
  simp only [CollatzResearch.WordTrace]
  refine ⟨2038074564567401218522691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1358716376378267479015127 2038074564567401218522691)
  ·
    refine ⟨3057111846851101827784037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2038074564567401218522691 3057111846851101827784037)
    ·
      refine ⟨573208471284581592709507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3057111846851101827784037 573208471284581592709507)
      ·
        refine ⟨859812706926872389064261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573208471284581592709507 859812706926872389064261)
        ·
          refine ⟨161214882548788572949549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 859812706926872389064261 161214882548788572949549)
          ·
            refine ⟨60455580955795714856081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161214882548788572949549 60455580955795714856081)
            ·
              refine ⟨45341685716846786142061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60455580955795714856081 45341685716846786142061)
              ·
                refine ⟨17003132143817544803273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45341685716846786142061 17003132143817544803273)
                ·
                  rfl

theorem cell19_55879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 3].length) (baseStart_55879 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_55879 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_55879 prefixEnd_55879 := by exact prefixLift 55879
  have htrace : WordTrace (prefixWord ++ tailWord_55879) baseStart_55879 baseEnd_55879 := by
    simpa [prefixWord, tailWord_55879, baseEnd_55879] using wordTrace_append hprefix tailTrace_55879
  have hstable : (prefixWord ++ tailWord_55879).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55879).length < 2 ^ (prefixWord ++ tailWord_55879).sum := by decide
  have hdescent : baseEnd_55879 < baseStart_55879 := by decide
  rcases family_descends (prefixWord ++ tailWord_55879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56050 : List Nat := [3, 2, 1, 3, 1, 4, 2, 3]
def baseStart_56050 : Nat := 118140960795 + 56050 * 2 ^ 59
def prefixEnd_56050 : Nat := 4983230072969 + 3 ^ 40 * 56050 * 2
def baseEnd_56050 : Nat := 17055164850139815002807

theorem tailTrace_56050 : CollatzResearch.WordTrace tailWord_56050 prefixEnd_56050 17055164850139815002807 := by
  unfold tailWord_56050
  simp only [CollatzResearch.WordTrace]
  refine ⟨511077861736974355749401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1362874297965264948665069 511077861736974355749401)
  ·
    refine ⟨383308396302730766812051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 511077861736974355749401 383308396302730766812051)
    ·
      refine ⟨574962594454096150218077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383308396302730766812051 574962594454096150218077)
      ·
        refine ⟨215610972920286056331779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 574962594454096150218077 215610972920286056331779)
        ·
          refine ⟨323416459380429084497669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215610972920286056331779 323416459380429084497669)
          ·
            refine ⟨60640586133830453343313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 323416459380429084497669 60640586133830453343313)
            ·
              refine ⟨45480439600372840007485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60640586133830453343313 45480439600372840007485)
              ·
                refine ⟨17055164850139815002807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45480439600372840007485 17055164850139815002807)
                ·
                  rfl

theorem cell19_56050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_56050 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_56050 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_56050 prefixEnd_56050 := by exact prefixLift 56050
  have htrace : WordTrace (prefixWord ++ tailWord_56050) baseStart_56050 baseEnd_56050 := by
    simpa [prefixWord, tailWord_56050, baseEnd_56050] using wordTrace_append hprefix tailTrace_56050
  have hstable : (prefixWord ++ tailWord_56050).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56050).length < 2 ^ (prefixWord ++ tailWord_56050).sum := by decide
  have hdescent : baseEnd_56050 < baseStart_56050 := by decide
  rcases family_descends (prefixWord ++ tailWord_56050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56071 : List Nat := [1, 1, 4, 4, 1, 3, 5]
def baseStart_56071 : Nat := 118140960795 + 56071 * 2 ^ 59
def prefixEnd_56071 : Nat := 4983230072969 + 3 ^ 40 * 56071 * 2
def baseEnd_56071 : Nat := 5687184943872662845361

theorem tailTrace_56071 : CollatzResearch.WordTrace tailWord_56071 prefixEnd_56071 5687184943872662845361 := by
  unfold tailWord_56071
  simp only [CollatzResearch.WordTrace]
  refine ⟨2045077379871818009512067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1363384919914545339674711 2045077379871818009512067)
  ·
    refine ⟨3067616069807727014268101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2045077379871818009512067 3067616069807727014268101)
    ·
      refine ⟨575178013088948815175269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3067616069807727014268101 575178013088948815175269)
      ·
        refine ⟨107845877454177902845363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 575178013088948815175269 107845877454177902845363)
        ·
          refine ⟨161768816181266854268045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107845877454177902845363 161768816181266854268045)
          ·
            refine ⟨60663306067975070350517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161768816181266854268045 60663306067975070350517)
            ·
              refine ⟨5687184943872662845361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60663306067975070350517 5687184943872662845361)
              ·
                rfl

theorem cell19_56071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 5].length) (baseStart_56071 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_56071 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_56071 prefixEnd_56071 := by exact prefixLift 56071
  have htrace : WordTrace (prefixWord ++ tailWord_56071) baseStart_56071 baseEnd_56071 := by
    simpa [prefixWord, tailWord_56071, baseEnd_56071] using wordTrace_append hprefix tailTrace_56071
  have hstable : (prefixWord ++ tailWord_56071).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56071).length < 2 ^ (prefixWord ++ tailWord_56071).sum := by decide
  have hdescent : baseEnd_56071 < baseStart_56071 := by decide
  rcases family_descends (prefixWord ++ tailWord_56071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56092 : List Nat := [2, 2, 3, 1, 1, 3, 1, 6]
def baseStart_56092 : Nat := 118140960795 + 56092 * 2 ^ 59
def prefixEnd_56092 : Nat := 4983230072969 + 3 ^ 40 * 56092 * 2
def baseEnd_56092 : Nat := 17067944813096162069359

theorem tailTrace_56092 : CollatzResearch.WordTrace tailWord_56092 prefixEnd_56092 17067944813096162069359 := by
  unfold tailWord_56092
  simp only [CollatzResearch.WordTrace]
  refine ⟨1022921656397869298013265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1363895541863825730684353 1022921656397869298013265)
  ·
    refine ⟨767191242298401973509949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1022921656397869298013265 767191242298401973509949)
    ·
      refine ⟨287696715861900740066231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 767191242298401973509949 287696715861900740066231)
      ·
        refine ⟨431545073792851110099347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287696715861900740066231 431545073792851110099347)
        ·
          refine ⟨647317610689276665149021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431545073792851110099347 647317610689276665149021)
          ·
            refine ⟨242744104008478749430883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 647317610689276665149021 242744104008478749430883)
            ·
              refine ⟨364116156012718124146325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242744104008478749430883 364116156012718124146325)
              ·
                refine ⟨17067944813096162069359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 364116156012718124146325 17067944813096162069359)
                ·
                  rfl

theorem cell19_56092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_56092 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_56092 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_56092 prefixEnd_56092 := by exact prefixLift 56092
  have htrace : WordTrace (prefixWord ++ tailWord_56092) baseStart_56092 baseEnd_56092 := by
    simpa [prefixWord, tailWord_56092, baseEnd_56092] using wordTrace_append hprefix tailTrace_56092
  have hstable : (prefixWord ++ tailWord_56092).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56092).length < 2 ^ (prefixWord ++ tailWord_56092).sum := by decide
  have hdescent : baseEnd_56092 < baseStart_56092 := by decide
  rcases family_descends (prefixWord ++ tailWord_56092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56145 : List Nat := [1, 2, 2, 1, 7, 1, 1, 4]
def baseStart_56145 : Nat := 118140960795 + 56145 * 2 ^ 59
def prefixEnd_56145 : Nat := 4983230072969 + 3 ^ 40 * 56145 * 2
def baseEnd_56145 : Nat := 17084071909207742891437

theorem tailTrace_56145 : CollatzResearch.WordTrace tailWord_56145 prefixEnd_56145 17084071909207742891437 := by
  unfold tailWord_56145
  simp only [CollatzResearch.WordTrace]
  refine ⟨2047776381603728647705889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1365184254402485765137259 2047776381603728647705889)
  ·
    refine ⟨1535832286202796485779417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2047776381603728647705889 1535832286202796485779417)
    ·
      refine ⟨1151874214652097364334563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1535832286202796485779417 1151874214652097364334563)
      ·
        refine ⟨1727811321978146046501845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1151874214652097364334563 1727811321978146046501845)
        ·
          refine ⟨40495577858862797964887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 1727811321978146046501845 40495577858862797964887)
          ·
            refine ⟨60743366788294196947331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40495577858862797964887 60743366788294196947331)
            ·
              refine ⟨91115050182441295420997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60743366788294196947331 91115050182441295420997)
              ·
                refine ⟨17084071909207742891437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91115050182441295420997 17084071909207742891437)
                ·
                  rfl

theorem cell19_56145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 4].length) (baseStart_56145 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_56145 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_56145 prefixEnd_56145 := by exact prefixLift 56145
  have htrace : WordTrace (prefixWord ++ tailWord_56145) baseStart_56145 baseEnd_56145 := by
    simpa [prefixWord, tailWord_56145, baseEnd_56145] using wordTrace_append hprefix tailTrace_56145
  have hstable : (prefixWord ++ tailWord_56145).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56145).length < 2 ^ (prefixWord ++ tailWord_56145).sum := by decide
  have hdescent : baseEnd_56145 < baseStart_56145 := by decide
  rcases family_descends (prefixWord ++ tailWord_56145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56223 : List Nat := [1, 1, 2, 5, 2, 1, 4, 3]
def baseStart_56223 : Nat := 118140960795 + 56223 * 2 ^ 59
def prefixEnd_56223 : Nat := 4983230072969 + 3 ^ 40 * 56223 * 2
def baseEnd_56223 : Nat := 17107806126126673157891

theorem tailTrace_56223 : CollatzResearch.WordTrace tailWord_56223 prefixEnd_56223 17107806126126673157891 := by
  unfold tailWord_56223
  simp only [CollatzResearch.WordTrace]
  refine ⟨2050621275321147969045323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1367080850214098646030215 2050621275321147969045323)
  ·
    refine ⟨3075931912981721953567985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2050621275321147969045323 3075931912981721953567985)
    ·
      refine ⟨2306948934736291465175989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3075931912981721953567985 2306948934736291465175989)
      ·
        refine ⟨216276462631527324860249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2306948934736291465175989 216276462631527324860249)
        ·
          refine ⟨162207346973645493645187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216276462631527324860249 162207346973645493645187)
          ·
            refine ⟨243311020460468240467781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162207346973645493645187 243311020460468240467781)
            ·
              refine ⟨45620816336337795087709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 243311020460468240467781 45620816336337795087709)
              ·
                refine ⟨17107806126126673157891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45620816336337795087709 17107806126126673157891)
                ·
                  rfl

theorem cell19_56223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 3].length) (baseStart_56223 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_56223 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_56223 prefixEnd_56223 := by exact prefixLift 56223
  have htrace : WordTrace (prefixWord ++ tailWord_56223) baseStart_56223 baseEnd_56223 := by
    simpa [prefixWord, tailWord_56223, baseEnd_56223] using wordTrace_append hprefix tailTrace_56223
  have hstable : (prefixWord ++ tailWord_56223).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56223).length < 2 ^ (prefixWord ++ tailWord_56223).sum := by decide
  have hdescent : baseEnd_56223 < baseStart_56223 := by decide
  rcases family_descends (prefixWord ++ tailWord_56223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56282 : List Nat := [3, 1, 1, 2, 4, 1, 2, 5]
def baseStart_56282 : Nat := 118140960795 + 56282 * 2 ^ 59
def prefixEnd_56282 : Nat := 4983230072969 + 3 ^ 40 * 56282 * 2
def baseEnd_56282 : Nat := 17125758931232017846619

theorem tailTrace_56282 : CollatzResearch.WordTrace tailWord_56282 prefixEnd_56282 17125758931232017846619 := by
  unfold tailWord_56282
  simp only [CollatzResearch.WordTrace]
  refine ⟨513193295526850261360775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1368515454738267363628733 513193295526850261360775)
  ·
    refine ⟨769789943290275392041163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 513193295526850261360775 769789943290275392041163)
    ·
      refine ⟨1154684914935413088061745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 769789943290275392041163 1154684914935413088061745)
      ·
        refine ⟨866013686201559816046309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1154684914935413088061745 866013686201559816046309)
        ·
          refine ⟨162377566162792465508683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 866013686201559816046309 162377566162792465508683)
          ·
            refine ⟨243566349244188698263025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162377566162792465508683 243566349244188698263025)
            ·
              refine ⟨182674761933141523697269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243566349244188698263025 182674761933141523697269)
              ·
                refine ⟨17125758931232017846619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 182674761933141523697269 17125758931232017846619)
                ·
                  rfl

theorem cell19_56282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_56282 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_56282 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_56282 prefixEnd_56282 := by exact prefixLift 56282
  have htrace : WordTrace (prefixWord ++ tailWord_56282) baseStart_56282 baseEnd_56282 := by
    simpa [prefixWord, tailWord_56282, baseEnd_56282] using wordTrace_append hprefix tailTrace_56282
  have hstable : (prefixWord ++ tailWord_56282).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56282).length < 2 ^ (prefixWord ++ tailWord_56282).sum := by decide
  have hdescent : baseEnd_56282 < baseStart_56282 := by decide
  rcases family_descends (prefixWord ++ tailWord_56282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56303 : List Nat := [1, 1, 2, 1, 4, 10]
def baseStart_56303 : Nat := 118140960795 + 56303 * 2 ^ 59
def prefixEnd_56303 : Nat := 4983230072969 + 3 ^ 40 * 56303 * 2
def baseEnd_56303 : Nat := 1903572101412243486655

theorem tailTrace_56303 : CollatzResearch.WordTrace tailWord_56303 prefixEnd_56303 1903572101412243486655 := by
  unfold tailWord_56303
  simp only [CollatzResearch.WordTrace]
  refine ⟨2053539115031321631957563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1369026076687547754638375 2053539115031321631957563)
  ·
    refine ⟨3080308672546982447936345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2053539115031321631957563 3080308672546982447936345)
    ·
      refine ⟨2310231504410236835952259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3080308672546982447936345 2310231504410236835952259)
      ·
        refine ⟨3465347256615355253928389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2310231504410236835952259 3465347256615355253928389)
        ·
          refine ⟨649752610615379110111573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3465347256615355253928389 649752610615379110111573)
          ·
            refine ⟨1903572101412243486655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 649752610615379110111573 1903572101412243486655)
            ·
              rfl

theorem cell19_56303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 10].length) (baseStart_56303 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_56303 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_56303 prefixEnd_56303 := by exact prefixLift 56303
  have htrace : WordTrace (prefixWord ++ tailWord_56303) baseStart_56303 baseEnd_56303 := by
    simpa [prefixWord, tailWord_56303, baseEnd_56303] using wordTrace_append hprefix tailTrace_56303
  have hstable : (prefixWord ++ tailWord_56303).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56303).length < 2 ^ (prefixWord ++ tailWord_56303).sum := by decide
  have hdescent : baseEnd_56303 < baseStart_56303 := by decide
  rcases family_descends (prefixWord ++ tailWord_56303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56390 : List Nat := [6, 1, 1, 1, 1, 4, 2, 3]
def baseStart_56390 : Nat := 118140960795 + 56390 * 2 ^ 59
def prefixEnd_56390 : Nat := 4983230072969 + 3 ^ 40 * 56390 * 2
def baseEnd_56390 : Nat := 17158621693119767446325

theorem tailTrace_56390 : CollatzResearch.WordTrace tailWord_56390 prefixEnd_56390 17158621693119767446325 := by
  unfold tailWord_56390
  simp only [CollatzResearch.WordTrace]
  refine ⟨64272258303629234074207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1371141510477423660249749 64272258303629234074207)
  ·
    refine ⟨96408387455443851111311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64272258303629234074207 96408387455443851111311)
    ·
      refine ⟨144612581183165776666967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96408387455443851111311 144612581183165776666967)
      ·
        refine ⟨216918871774748665000451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144612581183165776666967 216918871774748665000451)
        ·
          refine ⟨325378307662122997500677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216918871774748665000451 325378307662122997500677)
          ·
            refine ⟨61008432686648062031377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 325378307662122997500677 61008432686648062031377)
            ·
              refine ⟨45756324514986046523533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61008432686648062031377 45756324514986046523533)
              ·
                refine ⟨17158621693119767446325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45756324514986046523533 17158621693119767446325)
                ·
                  rfl

theorem cell19_56390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_56390 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_56390 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_56390 prefixEnd_56390 := by exact prefixLift 56390
  have htrace : WordTrace (prefixWord ++ tailWord_56390) baseStart_56390 baseEnd_56390 := by
    simpa [prefixWord, tailWord_56390, baseEnd_56390] using wordTrace_append hprefix tailTrace_56390
  have hstable : (prefixWord ++ tailWord_56390).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56390).length < 2 ^ (prefixWord ++ tailWord_56390).sum := by decide
  have hdescent : baseEnd_56390 < baseStart_56390 := by decide
  rcases family_descends (prefixWord ++ tailWord_56390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56417 : List Nat := [1, 2, 3, 1, 1, 2, 9]
def baseStart_56417 : Nat := 118140960795 + 56417 * 2 ^ 59
def prefixEnd_56417 : Nat := 4983230072969 + 3 ^ 40 * 56417 * 2
def baseEnd_56417 : Nat := 5722279127863901615417

theorem tailTrace_56417 : CollatzResearch.WordTrace tailWord_56417 prefixEnd_56417 5722279127863901615417 := by
  unfold tailWord_56417
  simp only [CollatzResearch.WordTrace]
  refine ⟨2057697036618319101607505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1371798024412212734405003 2057697036618319101607505)
  ·
    refine ⟨1543272777463739326205629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2057697036618319101607505 1543272777463739326205629)
    ·
      refine ⟨578727291548902247327111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1543272777463739326205629 578727291548902247327111)
      ·
        refine ⟨868090937323353370990667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 578727291548902247327111 868090937323353370990667)
        ·
          refine ⟨1302136405985030056486001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 868090937323353370990667 1302136405985030056486001)
          ·
            refine ⟨976602304488772542364501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1302136405985030056486001 976602304488772542364501)
            ·
              refine ⟨5722279127863901615417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 976602304488772542364501 5722279127863901615417)
              ·
                rfl

theorem cell19_56417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 9].length) (baseStart_56417 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_56417 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_56417 prefixEnd_56417 := by exact prefixLift 56417
  have htrace : WordTrace (prefixWord ++ tailWord_56417) baseStart_56417 baseEnd_56417 := by
    simpa [prefixWord, tailWord_56417, baseEnd_56417] using wordTrace_append hprefix tailTrace_56417
  have hstable : (prefixWord ++ tailWord_56417).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56417).length < 2 ^ (prefixWord ++ tailWord_56417).sum := by decide
  have hdescent : baseEnd_56417 < baseStart_56417 := by decide
  rcases family_descends (prefixWord ++ tailWord_56417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56434 : List Nat := [3, 2, 1, 2, 2, 1, 4, 4]
def baseStart_56434 : Nat := 118140960795 + 56434 * 2 ^ 59
def prefixEnd_56434 : Nat := 4983230072969 + 3 ^ 40 * 56434 * 2
def baseEnd_56434 : Nat := 17172010225740702468427

theorem tailTrace_56434 : CollatzResearch.WordTrace tailWord_56434 prefixEnd_56434 17172010225740702468427 := by
  unfold tailWord_56434
  simp only [CollatzResearch.WordTrace]
  refine ⟨514579269389182751244089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1372211385037820669984237 514579269389182751244089)
  ·
    refine ⟨385934452041887063433067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 514579269389182751244089 385934452041887063433067)
    ·
      refine ⟨578901678062830595149601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385934452041887063433067 578901678062830595149601)
      ·
        refine ⟨434176258547122946362201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 578901678062830595149601 434176258547122946362201)
        ·
          refine ⟨325632193910342209771651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434176258547122946362201 325632193910342209771651)
          ·
            refine ⟨488448290865513314657477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325632193910342209771651 488448290865513314657477)
            ·
              refine ⟨91584054537283746498277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 488448290865513314657477 91584054537283746498277)
              ·
                refine ⟨17172010225740702468427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91584054537283746498277 17172010225740702468427)
                ·
                  rfl

theorem cell19_56434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_56434 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_56434 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_56434 prefixEnd_56434 := by exact prefixLift 56434
  have htrace : WordTrace (prefixWord ++ tailWord_56434) baseStart_56434 baseEnd_56434 := by
    simpa [prefixWord, tailWord_56434, baseEnd_56434] using wordTrace_append hprefix tailTrace_56434
  have hstable : (prefixWord ++ tailWord_56434).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56434).length < 2 ^ (prefixWord ++ tailWord_56434).sum := by decide
  have hdescent : baseEnd_56434 < baseStart_56434 := by decide
  rcases family_descends (prefixWord ++ tailWord_56434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56508 : List Nat := [2, 2, 2, 3, 2, 2, 3, 3]
def baseStart_56508 : Nat := 118140960795 + 56508 * 2 ^ 59
def prefixEnd_56508 : Nat := 4983230072969 + 3 ^ 40 * 56508 * 2
def baseEnd_56508 : Nat := 17194527303330456823781

theorem tailTrace_56508 : CollatzResearch.WordTrace tailWord_56508 prefixEnd_56508 17194527303330456823781 := by
  unfold tailWord_56508
  simp only [CollatzResearch.WordTrace]
  refine ⟨1030508039644320821585089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1374010719525761095446785 1030508039644320821585089)
  ·
    refine ⟨772881029733240616188817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1030508039644320821585089 772881029733240616188817)
    ·
      refine ⟨579660772299930462141613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 772881029733240616188817 579660772299930462141613)
      ·
        refine ⟨217372789612473923303105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 579660772299930462141613 217372789612473923303105)
        ·
          refine ⟨163029592209355442477329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217372789612473923303105 163029592209355442477329)
          ·
            refine ⟨122272194157016581857997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163029592209355442477329 122272194157016581857997)
            ·
              refine ⟨45852072808881218196749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122272194157016581857997 45852072808881218196749)
              ·
                refine ⟨17194527303330456823781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45852072808881218196749 17194527303330456823781)
                ·
                  rfl

theorem cell19_56508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 3].length) (baseStart_56508 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_56508 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_56508 prefixEnd_56508 := by exact prefixLift 56508
  have htrace : WordTrace (prefixWord ++ tailWord_56508) baseStart_56508 baseEnd_56508 := by
    simpa [prefixWord, tailWord_56508, baseEnd_56508] using wordTrace_append hprefix tailTrace_56508
  have hstable : (prefixWord ++ tailWord_56508).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56508).length < 2 ^ (prefixWord ++ tailWord_56508).sum := by decide
  have hdescent : baseEnd_56508 < baseStart_56508 := by decide
  rcases family_descends (prefixWord ++ tailWord_56508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56525 : List Nat := [1, 6, 2, 2, 1, 1, 6]
def baseStart_56525 : Nat := 118140960795 + 56525 * 2 ^ 59
def prefixEnd_56525 : Nat := 4983230072969 + 3 ^ 40 * 56525 * 2
def baseEnd_56525 : Nat := 5733233381826484815319

theorem tailTrace_56525 : CollatzResearch.WordTrace tailWord_56525 prefixEnd_56525 5733233381826484815319 := by
  unfold tailWord_56525
  simp only [CollatzResearch.WordTrace]
  refine ⟨2061636120227053546539029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1374424080151369031026019 2061636120227053546539029)
  ·
    refine ⟨96639193135643134994017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2061636120227053546539029 96639193135643134994017)
    ·
      refine ⟨72479394851732351245513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96639193135643134994017 72479394851732351245513)
      ·
        refine ⟨54359546138799263434135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72479394851732351245513 54359546138799263434135)
        ·
          refine ⟨81539319208198895151203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54359546138799263434135 81539319208198895151203)
          ·
            refine ⟨122308978812298342726805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81539319208198895151203 122308978812298342726805)
            ·
              refine ⟨5733233381826484815319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 122308978812298342726805 5733233381826484815319)
              ·
                rfl

theorem cell19_56525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 6].length) (baseStart_56525 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_56525 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_56525 prefixEnd_56525 := by exact prefixLift 56525
  have htrace : WordTrace (prefixWord ++ tailWord_56525) baseStart_56525 baseEnd_56525 := by
    simpa [prefixWord, tailWord_56525, baseEnd_56525] using wordTrace_append hprefix tailTrace_56525
  have hstable : (prefixWord ++ tailWord_56525).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56525).length < 2 ^ (prefixWord ++ tailWord_56525).sum := by decide
  have hdescent : baseEnd_56525 < baseStart_56525 := by decide
  rcases family_descends (prefixWord ++ tailWord_56525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56569 : List Nat := [1, 2, 1, 3, 1, 1, 5, 5]
def baseStart_56569 : Nat := 118140960795 + 56569 * 2 ^ 59
def prefixEnd_56569 : Nat := 4983230072969 + 3 ^ 40 * 56569 * 2
def baseEnd_56569 : Nat := 17213088678100389468059

theorem tailTrace_56569 : CollatzResearch.WordTrace tailWord_56569 prefixEnd_56569 17213088678100389468059 := by
  unfold tailWord_56569
  simp only [CollatzResearch.WordTrace]
  refine ⟨2063240932067649061140761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1375493954711766040760507 2063240932067649061140761)
  ·
    refine ⟨1547430699050736795855571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2063240932067649061140761 1547430699050736795855571)
    ·
      refine ⟨2321146048576105193783357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1547430699050736795855571 2321146048576105193783357)
      ·
        refine ⟨870429768216039447668759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2321146048576105193783357 870429768216039447668759)
        ·
          refine ⟨1305644652324059171503139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 870429768216039447668759 1305644652324059171503139)
          ·
            refine ⟨1958466978486088757254709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1305644652324059171503139 1958466978486088757254709)
            ·
              refine ⟨183606279233070820992629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1958466978486088757254709 183606279233070820992629)
              ·
                refine ⟨17213088678100389468059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 183606279233070820992629 17213088678100389468059)
                ·
                  rfl

theorem cell19_56569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 5].length) (baseStart_56569 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_56569 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_56569 prefixEnd_56569 := by exact prefixLift 56569
  have htrace : WordTrace (prefixWord ++ tailWord_56569) baseStart_56569 baseEnd_56569 := by
    simpa [prefixWord, tailWord_56569, baseEnd_56569] using wordTrace_append hprefix tailTrace_56569
  have hstable : (prefixWord ++ tailWord_56569).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56569).length < 2 ^ (prefixWord ++ tailWord_56569).sum := by decide
  have hdescent : baseEnd_56569 < baseStart_56569 := by decide
  rcases family_descends (prefixWord ++ tailWord_56569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56584 : List Nat := [2, 1, 3, 2, 5, 1, 5]
def baseStart_56584 : Nat := 118140960795 + 56584 * 2 ^ 59
def prefixEnd_56584 : Nat := 4983230072969 + 3 ^ 40 * 56584 * 2
def baseEnd_56584 : Nat := 5739217650194933044895

theorem tailTrace_56584 : CollatzResearch.WordTrace tailWord_56584 prefixEnd_56584 5739217650194933044895 := by
  unfold tailWord_56584
  simp only [CollatzResearch.WordTrace]
  refine ⟨1031894013506653311468403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1375858684675537748624537 1031894013506653311468403)
  ·
    refine ⟨1547841020259979967202605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1031894013506653311468403 1547841020259979967202605)
    ·
      refine ⟨580440382597492487700977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1547841020259979967202605 580440382597492487700977)
      ·
        refine ⟨435330286948119365775733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 580440382597492487700977 435330286948119365775733)
        ·
          refine ⟨40812214401386190541475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 435330286948119365775733 40812214401386190541475)
          ·
            refine ⟨61218321602079285812213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40812214401386190541475 61218321602079285812213)
            ·
              refine ⟨5739217650194933044895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61218321602079285812213 5739217650194933044895)
              ·
                rfl

theorem cell19_56584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 5].length) (baseStart_56584 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_56584 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_56584 prefixEnd_56584 := by exact prefixLift 56584
  have htrace : WordTrace (prefixWord ++ tailWord_56584) baseStart_56584 baseEnd_56584 := by
    simpa [prefixWord, tailWord_56584, baseEnd_56584] using wordTrace_append hprefix tailTrace_56584
  have hstable : (prefixWord ++ tailWord_56584).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56584).length < 2 ^ (prefixWord ++ tailWord_56584).sum := by decide
  have hdescent : baseEnd_56584 < baseStart_56584 := by decide
  rcases family_descends (prefixWord ++ tailWord_56584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56588 : List Nat := [2, 2, 1, 2, 2, 3, 7]
def baseStart_56588 : Nat := 118140960795 + 56588 * 2 ^ 59
def prefixEnd_56588 : Nat := 4983230072969 + 3 ^ 40 * 56588 * 2
def baseEnd_56588 : Nat := 5739623363304658348595

theorem tailTrace_56588 : CollatzResearch.WordTrace tailWord_56588 prefixEnd_56588 5739623363304658348595 := by
  unfold tailWord_56588
  simp only [CollatzResearch.WordTrace]
  refine ⟨1031966959499407653041209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1375955945999210204054945 1031966959499407653041209)
  ·
    refine ⟨773975219624555739780907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1031966959499407653041209 773975219624555739780907)
    ·
      refine ⟨1160962829436833609671361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 773975219624555739780907 1160962829436833609671361)
      ·
        refine ⟨870722122077625207253521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1160962829436833609671361 870722122077625207253521)
        ·
          refine ⟨653041591558218905440141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 870722122077625207253521 653041591558218905440141)
          ·
            refine ⟨244890596834332089540053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 653041591558218905440141 244890596834332089540053)
            ·
              refine ⟨5739623363304658348595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 244890596834332089540053 5739623363304658348595)
              ·
                rfl

theorem cell19_56588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 7].length) (baseStart_56588 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_56588 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_56588 prefixEnd_56588 := by exact prefixLift 56588
  have htrace : WordTrace (prefixWord ++ tailWord_56588) baseStart_56588 baseEnd_56588 := by
    simpa [prefixWord, tailWord_56588, baseEnd_56588] using wordTrace_append hprefix tailTrace_56588
  have hstable : (prefixWord ++ tailWord_56588).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56588).length < 2 ^ (prefixWord ++ tailWord_56588).sum := by decide
  have hdescent : baseEnd_56588 < baseStart_56588 := by decide
  rcases family_descends (prefixWord ++ tailWord_56588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56605 : List Nat := [1, 4, 2, 3, 1, 1, 1, 6]
def baseStart_56605 : Nat := 118140960795 + 56605 * 2 ^ 59
def prefixEnd_56605 : Nat := 4983230072969 + 3 ^ 40 * 56605 * 2
def baseEnd_56605 : Nat := 17224042932062972667961

theorem tailTrace_56605 : CollatzResearch.WordTrace tailWord_56605 prefixEnd_56605 17224042932062972667961 := by
  unfold tailWord_56605
  simp only [CollatzResearch.WordTrace]
  refine ⟨2064553959937227209451269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1376369306624818139634179 2064553959937227209451269)
  ·
    refine ⟨387103867488230101772113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2064553959937227209451269 387103867488230101772113)
    ·
      refine ⟨290327900616172576329085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387103867488230101772113 290327900616172576329085)
      ·
        refine ⟨108872962731064716123407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290327900616172576329085 108872962731064716123407)
        ·
          refine ⟨163309444096597074185111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108872962731064716123407 163309444096597074185111)
          ·
            refine ⟨244964166144895611277667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163309444096597074185111 244964166144895611277667)
            ·
              refine ⟨367446249217343416916501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244964166144895611277667 367446249217343416916501)
              ·
                refine ⟨17224042932062972667961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 367446249217343416916501 17224042932062972667961)
                ·
                  rfl

theorem cell19_56605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 6].length) (baseStart_56605 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_56605 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_56605 prefixEnd_56605 := by exact prefixLift 56605
  have htrace : WordTrace (prefixWord ++ tailWord_56605) baseStart_56605 baseEnd_56605 := by
    simpa [prefixWord, tailWord_56605, baseEnd_56605] using wordTrace_append hprefix tailTrace_56605
  have hstable : (prefixWord ++ tailWord_56605).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56605).length < 2 ^ (prefixWord ++ tailWord_56605).sum := by decide
  have hdescent : baseEnd_56605 < baseStart_56605 := by decide
  rcases family_descends (prefixWord ++ tailWord_56605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56679 : List Nat := [1, 1, 5, 1, 4, 1, 3, 3]
def baseStart_56679 : Nat := 118140960795 + 56679 * 2 ^ 59
def prefixEnd_56679 : Nat := 4983230072969 + 3 ^ 40 * 56679 * 2
def baseEnd_56679 : Nat := 17246560009652727023315

theorem tailTrace_56679 : CollatzResearch.WordTrace tailWord_56679 prefixEnd_56679 17246560009652727023315 := by
  unfold tailWord_56679
  simp only [CollatzResearch.WordTrace]
  refine ⟨2067252961669137847645091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1378168641112758565096727 2067252961669137847645091)
  ·
    refine ⟨3100879442503706771467637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2067252961669137847645091 3100879442503706771467637)
    ·
      refine ⟨290707447734722509825091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3100879442503706771467637 290707447734722509825091)
      ·
        refine ⟨436061171602083764737637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290707447734722509825091 436061171602083764737637)
        ·
          refine ⟨81761469675390705888307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 436061171602083764737637 81761469675390705888307)
          ·
            refine ⟨122642204513086058832461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81761469675390705888307 122642204513086058832461)
            ·
              refine ⟨45990826692407272062173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122642204513086058832461 45990826692407272062173)
              ·
                refine ⟨17246560009652727023315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45990826692407272062173 17246560009652727023315)
                ·
                  rfl

theorem cell19_56679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 3].length) (baseStart_56679 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_56679 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_56679 prefixEnd_56679 := by exact prefixLift 56679
  have htrace : WordTrace (prefixWord ++ tailWord_56679) baseStart_56679 baseEnd_56679 := by
    simpa [prefixWord, tailWord_56679, baseEnd_56679] using wordTrace_append hprefix tailTrace_56679
  have hstable : (prefixWord ++ tailWord_56679).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56679).length < 2 ^ (prefixWord ++ tailWord_56679).sum := by decide
  have hdescent : baseEnd_56679 < baseStart_56679 := by decide
  rcases family_descends (prefixWord ++ tailWord_56679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56732 : List Nat := [2, 2, 3, 4, 2, 1, 2, 3]
def baseStart_56732 : Nat := 118140960795 + 56732 * 2 ^ 59
def prefixEnd_56732 : Nat := 4983230072969 + 3 ^ 40 * 56732 * 2
def baseEnd_56732 : Nat := 17262687105764307845393

theorem tailTrace_56732 : CollatzResearch.WordTrace tailWord_56732 prefixEnd_56732 17262687105764307845393 := by
  unfold tailWord_56732
  simp only [CollatzResearch.WordTrace]
  refine ⟨1034593015238563949662225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1379457353651418599549633 1034593015238563949662225)
  ·
    refine ⟨775944761428922962246669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1034593015238563949662225 775944761428922962246669)
    ·
      refine ⟨290979285535846110842501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 775944761428922962246669 290979285535846110842501)
      ·
        refine ⟨54558616037971145782969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 290979285535846110842501 54558616037971145782969)
        ·
          refine ⟨40918962028478359337227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54558616037971145782969 40918962028478359337227)
          ·
            refine ⟨61378443042717539005841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40918962028478359337227 61378443042717539005841)
            ·
              refine ⟨46033832282038154254381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61378443042717539005841 46033832282038154254381)
              ·
                refine ⟨17262687105764307845393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46033832282038154254381 17262687105764307845393)
                ·
                  rfl

theorem cell19_56732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 3].length) (baseStart_56732 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_56732 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_56732 prefixEnd_56732 := by exact prefixLift 56732
  have htrace : WordTrace (prefixWord ++ tailWord_56732) baseStart_56732 baseEnd_56732 := by
    simpa [prefixWord, tailWord_56732, baseEnd_56732] using wordTrace_append hprefix tailTrace_56732
  have hstable : (prefixWord ++ tailWord_56732).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56732).length < 2 ^ (prefixWord ++ tailWord_56732).sum := by decide
  have hdescent : baseEnd_56732 < baseStart_56732 := by decide
  rcases family_descends (prefixWord ++ tailWord_56732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56738 : List Nat := [3, 3, 1, 2, 1, 3, 1, 5]
def baseStart_56738 : Nat := 118140960795 + 56738 * 2 ^ 59
def prefixEnd_56738 : Nat := 4983230072969 + 3 ^ 40 * 56738 * 2
def baseEnd_56738 : Nat := 17264512814758071712043

theorem tailTrace_56738 : CollatzResearch.WordTrace tailWord_56738 prefixEnd_56738 17264512814758071712043 := by
  unfold tailWord_56738
  simp only [CollatzResearch.WordTrace]
  refine ⟨517351217113847731010717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1379603245636927282695245 517351217113847731010717)
  ·
    refine ⟨194006706417692899129019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 517351217113847731010717 194006706417692899129019)
    ·
      refine ⟨291010059626539348693529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194006706417692899129019 291010059626539348693529)
      ·
        refine ⟨218257544719904511520147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291010059626539348693529 218257544719904511520147)
        ·
          refine ⟨327386317079856767280221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218257544719904511520147 327386317079856767280221)
          ·
            refine ⟨122769868904946287730083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 327386317079856767280221 122769868904946287730083)
            ·
              refine ⟨184154803357419431595125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122769868904946287730083 184154803357419431595125)
              ·
                refine ⟨17264512814758071712043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 184154803357419431595125 17264512814758071712043)
                ·
                  rfl

theorem cell19_56738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_56738 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_56738 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_56738 prefixEnd_56738 := by exact prefixLift 56738
  have htrace : WordTrace (prefixWord ++ tailWord_56738) baseStart_56738 baseEnd_56738 := by
    simpa [prefixWord, tailWord_56738, baseEnd_56738] using wordTrace_append hprefix tailTrace_56738
  have hstable : (prefixWord ++ tailWord_56738).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56738).length < 2 ^ (prefixWord ++ tailWord_56738).sum := by decide
  have hdescent : baseEnd_56738 < baseStart_56738 := by decide
  rcases family_descends (prefixWord ++ tailWord_56738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56757 : List Nat := [1, 3, 3, 2, 2, 3, 5]
def baseStart_56757 : Nat := 118140960795 + 56757 * 2 ^ 59
def prefixEnd_56757 : Nat := 4983230072969 + 3 ^ 40 * 56757 * 2
def baseEnd_56757 : Nat := 5756764742190552429923

theorem tailTrace_56757 : CollatzResearch.WordTrace tailWord_56757 prefixEnd_56757 5756764742190552429923 := by
  unfold tailWord_56757
  simp only [CollatzResearch.WordTrace]
  refine ⟨2070097855386557168984525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1380065236924371445989683 2070097855386557168984525)
  ·
    refine ⟨776286695769958938369197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2070097855386557168984525 776286695769958938369197)
    ·
      refine ⟨291107510913734601888449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 776286695769958938369197 291107510913734601888449)
      ·
        refine ⟨218330633185300951416337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291107510913734601888449 218330633185300951416337)
        ·
          refine ⟨163747974888975713562253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218330633185300951416337 163747974888975713562253)
          ·
            refine ⟨61405490583365892585845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163747974888975713562253 61405490583365892585845)
            ·
              refine ⟨5756764742190552429923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61405490583365892585845 5756764742190552429923)
              ·
                rfl

theorem cell19_56757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 5].length) (baseStart_56757 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_56757 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_56757 prefixEnd_56757 := by exact prefixLift 56757
  have htrace : WordTrace (prefixWord ++ tailWord_56757) baseStart_56757 baseEnd_56757 := by
    simpa [prefixWord, tailWord_56757, baseEnd_56757] using wordTrace_append hprefix tailTrace_56757
  have hstable : (prefixWord ++ tailWord_56757).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56757).length < 2 ^ (prefixWord ++ tailWord_56757).sum := by decide
  have hdescent : baseEnd_56757 < baseStart_56757 := by decide
  rcases family_descends (prefixWord ++ tailWord_56757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56778 : List Nat := [3, 1, 2, 1, 2, 3, 1, 6]
def baseStart_56778 : Nat := 118140960795 + 56778 * 2 ^ 59
def prefixEnd_56778 : Nat := 4983230072969 + 3 ^ 40 * 56778 * 2
def baseEnd_56778 : Nat := 17276684208049830823045

theorem tailTrace_56778 : CollatzResearch.WordTrace tailWord_56778 prefixEnd_56778 17276684208049830823045 := by
  unfold tailWord_56778
  simp only [CollatzResearch.WordTrace]
  refine ⟨517715947077619438874747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1380575858873651836999325 517715947077619438874747)
  ·
    refine ⟨776573920616429158312121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 517715947077619438874747 776573920616429158312121)
    ·
      refine ⟨582430440462321868734091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 776573920616429158312121 582430440462321868734091)
      ·
        refine ⟨873645660693482803101137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582430440462321868734091 873645660693482803101137)
        ·
          refine ⟨655234245520112102325853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 873645660693482803101137 655234245520112102325853)
          ·
            refine ⟨245712842070042038372195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 655234245520112102325853 245712842070042038372195)
            ·
              refine ⟨368569263105063057558293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245712842070042038372195 368569263105063057558293)
              ·
                refine ⟨17276684208049830823045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 368569263105063057558293 17276684208049830823045)
                ·
                  rfl

theorem cell19_56778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_56778 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_56778 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_56778 prefixEnd_56778 := by exact prefixLift 56778
  have htrace : WordTrace (prefixWord ++ tailWord_56778) baseStart_56778 baseEnd_56778 := by
    simpa [prefixWord, tailWord_56778, baseEnd_56778] using wordTrace_append hprefix tailTrace_56778
  have hstable : (prefixWord ++ tailWord_56778).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56778).length < 2 ^ (prefixWord ++ tailWord_56778).sum := by decide
  have hdescent : baseEnd_56778 < baseStart_56778 := by decide
  rcases family_descends (prefixWord ++ tailWord_56778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57065 : List Nat := [1, 2, 1, 1, 1, 2, 3, 8]
def baseStart_57065 : Nat := 118140960795 + 57065 * 2 ^ 59
def prefixEnd_57065 : Nat := 4983230072969 + 3 ^ 40 * 57065 * 2
def baseEnd_57065 : Nat := 17364013954918202444485

theorem tailTrace_57065 : CollatzResearch.WordTrace tailWord_57065 prefixEnd_57065 17364013954918202444485 := by
  unfold tailWord_57065
  simp only [CollatzResearch.WordTrace]
  refine ⟨2081331538270725771196649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1387554358847150514131099 2081331538270725771196649)
  ·
    refine ⟨1560998653703044328397487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2081331538270725771196649 1560998653703044328397487)
    ·
      refine ⟨2341497980554566492596231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1560998653703044328397487 2341497980554566492596231)
      ·
        refine ⟨3512246970831849738894347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2341497980554566492596231 3512246970831849738894347)
        ·
          refine ⟨5268370456247774608341521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3512246970831849738894347 5268370456247774608341521)
          ·
            refine ⟨3951277842185830956256141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5268370456247774608341521 3951277842185830956256141)
            ·
              refine ⟨1481729190819686608596053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3951277842185830956256141 1481729190819686608596053)
              ·
                refine ⟨17364013954918202444485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1481729190819686608596053 17364013954918202444485)
                ·
                  rfl

theorem cell19_57065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 8].length) (baseStart_57065 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_57065 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_57065 prefixEnd_57065 := by exact prefixLift 57065
  have htrace : WordTrace (prefixWord ++ tailWord_57065) baseStart_57065 baseEnd_57065 := by
    simpa [prefixWord, tailWord_57065, baseEnd_57065] using wordTrace_append hprefix tailTrace_57065
  have hstable : (prefixWord ++ tailWord_57065).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57065).length < 2 ^ (prefixWord ++ tailWord_57065).sum := by decide
  have hdescent : baseEnd_57065 < baseStart_57065 := by decide
  rcases family_descends (prefixWord ++ tailWord_57065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57076 : List Nat := [2, 6, 1, 1, 1, 1, 4, 3]
def baseStart_57076 : Nat := 118140960795 + 57076 * 2 ^ 59
def prefixEnd_57076 : Nat := 4983230072969 + 3 ^ 40 * 57076 * 2
def baseEnd_57076 : Nat := 17367361088073436200011

theorem tailTrace_57076 : CollatzResearch.WordTrace tailWord_57076 prefixEnd_57076 17367361088073436200011 := by
  unfold tailWord_57076
  simp only [CollatzResearch.WordTrace]
  refine ⟨1040866370615437324923541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1387821827487249766564721 1040866370615437324923541)
  ·
    refine ⟨48790611122598624605791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1040866370615437324923541 48790611122598624605791)
    ·
      refine ⟨73185916683897936908687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48790611122598624605791 73185916683897936908687)
      ·
        refine ⟨109778875025846905363031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73185916683897936908687 109778875025846905363031)
        ·
          refine ⟨164668312538770358044547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109778875025846905363031 164668312538770358044547)
          ·
            refine ⟨247002468808155537066821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164668312538770358044547 247002468808155537066821)
            ·
              refine ⟨46312962901529163200029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 247002468808155537066821 46312962901529163200029)
              ·
                refine ⟨17367361088073436200011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46312962901529163200029 17367361088073436200011)
                ·
                  rfl

theorem cell19_57076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 3].length) (baseStart_57076 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_57076 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_57076 prefixEnd_57076 := by exact prefixLift 57076
  have htrace : WordTrace (prefixWord ++ tailWord_57076) baseStart_57076 baseEnd_57076 := by
    simpa [prefixWord, tailWord_57076, baseEnd_57076] using wordTrace_append hprefix tailTrace_57076
  have hstable : (prefixWord ++ tailWord_57076).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57076).length < 2 ^ (prefixWord ++ tailWord_57076).sum := by decide
  have hdescent : baseEnd_57076 < baseStart_57076 := by decide
  rcases family_descends (prefixWord ++ tailWord_57076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57078 : List Nat := [5, 1, 1, 1, 1, 5, 2, 3]
def baseStart_57078 : Nat := 118140960795 + 57078 * 2 ^ 59
def prefixEnd_57078 : Nat := 4983230072969 + 3 ^ 40 * 57078 * 2
def baseEnd_57078 : Nat := 17367969657738024155561

theorem tailTrace_57078 : CollatzResearch.WordTrace tailWord_57078 prefixEnd_57078 17367969657738024155561 := by
  unfold tailWord_57078
  simp only [CollatzResearch.WordTrace]
  refine ⟨130112855451476811963743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1387870458149085994279925 130112855451476811963743)
  ·
    refine ⟨195169283177215217945615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130112855451476811963743 195169283177215217945615)
    ·
      refine ⟨292753924765822826918423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195169283177215217945615 292753924765822826918423)
      ·
        refine ⟨439130887148734240377635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292753924765822826918423 439130887148734240377635)
        ·
          refine ⟨658696330723101360566453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439130887148734240377635 658696330723101360566453)
          ·
            refine ⟨61752781005290752553105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 658696330723101360566453 61752781005290752553105)
            ·
              refine ⟨46314585753968064414829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61752781005290752553105 46314585753968064414829)
              ·
                refine ⟨17367969657738024155561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46314585753968064414829 17367969657738024155561)
                ·
                  rfl

theorem cell19_57078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_57078 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_57078 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_57078 prefixEnd_57078 := by exact prefixLift 57078
  have htrace : WordTrace (prefixWord ++ tailWord_57078) baseStart_57078 baseEnd_57078 := by
    simpa [prefixWord, tailWord_57078, baseEnd_57078] using wordTrace_append hprefix tailTrace_57078
  have hstable : (prefixWord ++ tailWord_57078).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57078).length < 2 ^ (prefixWord ++ tailWord_57078).sum := by decide
  have hdescent : baseEnd_57078 < baseStart_57078 := by decide
  rcases family_descends (prefixWord ++ tailWord_57078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57120 : List Nat := [2, 1, 1, 5, 1, 1, 4, 4]
def baseStart_57120 : Nat := 118140960795 + 57120 * 2 ^ 59
def prefixEnd_57120 : Nat := 4983230072969 + 3 ^ 40 * 57120 * 2
def baseEnd_57120 : Nat := 17380749620694371222113

theorem tailTrace_57120 : CollatzResearch.WordTrace tailWord_57120 prefixEnd_57120 17380749620694371222113 := by
  unfold tailWord_57120
  simp only [CollatzResearch.WordTrace]
  refine ⟨1041668776535735082224407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1388891702047646776299209 1041668776535735082224407)
  ·
    refine ⟨1562503164803602623336611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1041668776535735082224407 1562503164803602623336611)
    ·
      refine ⟨2343754747205403935004917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1562503164803602623336611 2343754747205403935004917)
      ·
        refine ⟨219727007550506618906711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2343754747205403935004917 219727007550506618906711)
        ·
          refine ⟨329590511325759928360067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219727007550506618906711 329590511325759928360067)
          ·
            refine ⟨494385766988639892540101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329590511325759928360067 494385766988639892540101)
            ·
              refine ⟨92697331310369979851269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 494385766988639892540101 92697331310369979851269)
              ·
                refine ⟨17380749620694371222113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92697331310369979851269 17380749620694371222113)
                ·
                  rfl

theorem cell19_57120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_57120 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_57120 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_57120 prefixEnd_57120 := by exact prefixLift 57120
  have htrace : WordTrace (prefixWord ++ tailWord_57120) baseStart_57120 baseEnd_57120 := by
    simpa [prefixWord, tailWord_57120, baseEnd_57120] using wordTrace_append hprefix tailTrace_57120
  have hstable : (prefixWord ++ tailWord_57120).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57120).length < 2 ^ (prefixWord ++ tailWord_57120).sum := by decide
  have hdescent : baseEnd_57120 < baseStart_57120 := by decide
  rcases family_descends (prefixWord ++ tailWord_57120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57160 : List Nat := [2, 1, 3, 1, 1, 11]
def baseStart_57160 : Nat := 118140960795 + 57160 * 2 ^ 59
def prefixEnd_57160 : Nat := 4983230072969 + 3 ^ 40 * 57160 * 2
def baseEnd_57160 : Nat := 1932546779331792259235

theorem tailTrace_57160 : CollatzResearch.WordTrace tailWord_57160 prefixEnd_57160 1932546779331792259235 := by
  unfold tailWord_57160
  simp only [CollatzResearch.WordTrace]
  refine ⟨1042398236463278497952467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1389864315284371330603289 1042398236463278497952467)
  ·
    refine ⟨1563597354694917746928701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1042398236463278497952467 1563597354694917746928701)
    ·
      refine ⟨586349008010594155098263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1563597354694917746928701 586349008010594155098263)
      ·
        refine ⟨879523512015891232647395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586349008010594155098263 879523512015891232647395)
        ·
          refine ⟨1319285268023836848971093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 879523512015891232647395 1319285268023836848971093)
          ·
            refine ⟨1932546779331792259235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1319285268023836848971093 1932546779331792259235)
            ·
              rfl

theorem cell19_57160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 11].length) (baseStart_57160 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_57160 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_57160 prefixEnd_57160 := by exact prefixLift 57160
  have htrace : WordTrace (prefixWord ++ tailWord_57160) baseStart_57160 baseEnd_57160 := by
    simpa [prefixWord, tailWord_57160, baseEnd_57160] using wordTrace_append hprefix tailTrace_57160
  have hstable : (prefixWord ++ tailWord_57160).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57160).length < 2 ^ (prefixWord ++ tailWord_57160).sum := by decide
  have hdescent : baseEnd_57160 < baseStart_57160 := by decide
  rcases family_descends (prefixWord ++ tailWord_57160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57175 : List Nat := [1, 1, 3, 2, 5, 2, 1, 4]
def baseStart_57175 : Nat := 118140960795 + 57175 * 2 ^ 59
def prefixEnd_57175 : Nat := 4983230072969 + 3 ^ 40 * 57175 * 2
def baseEnd_57175 : Nat := 17397485286470539999741

theorem tailTrace_57175 : CollatzResearch.WordTrace tailWord_57175 prefixEnd_57175 17397485286470539999741 := by
  unfold tailWord_57175
  simp only [CollatzResearch.WordTrace]
  refine ⟨2085343567872214557700979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1390229045248143038467319 2085343567872214557700979)
  ·
    refine ⟨3128015351808321836551469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2085343567872214557700979 3128015351808321836551469)
    ·
      refine ⟨1173005756928120688706801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3128015351808321836551469 1173005756928120688706801)
      ·
        refine ⟨879754317696090516530101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1173005756928120688706801 879754317696090516530101)
        ·
          refine ⟨82476967284008485924697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 879754317696090516530101 82476967284008485924697)
          ·
            refine ⟨61857725463006364443523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82476967284008485924697 61857725463006364443523)
            ·
              refine ⟨92786588194509546665285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61857725463006364443523 92786588194509546665285)
              ·
                refine ⟨17397485286470539999741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92786588194509546665285 17397485286470539999741)
                ·
                  rfl

theorem cell19_57175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 4].length) (baseStart_57175 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_57175 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_57175 prefixEnd_57175 := by exact prefixLift 57175
  have htrace : WordTrace (prefixWord ++ tailWord_57175) baseStart_57175 baseEnd_57175 := by
    simpa [prefixWord, tailWord_57175, baseEnd_57175] using wordTrace_append hprefix tailTrace_57175
  have hstable : (prefixWord ++ tailWord_57175).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57175).length < 2 ^ (prefixWord ++ tailWord_57175).sum := by decide
  have hdescent : baseEnd_57175 < baseStart_57175 := by decide
  rcases family_descends (prefixWord ++ tailWord_57175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57249 : List Nat := [1, 2, 3, 4, 2, 2, 2, 3]
def baseStart_57249 : Nat := 118140960795 + 57249 * 2 ^ 59
def prefixEnd_57249 : Nat := 4983230072969 + 3 ^ 40 * 57249 * 2
def baseEnd_57249 : Nat := 17420002364060294355095

theorem tailTrace_57249 : CollatzResearch.WordTrace tailWord_57249 prefixEnd_57249 17420002364060294355095 := by
  unfold tailWord_57249
  simp only [CollatzResearch.WordTrace]
  refine ⟨2088042569604125195894801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1392028379736083463929867 2088042569604125195894801)
  ·
    refine ⟨1566031927203093896921101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2088042569604125195894801 1566031927203093896921101)
    ·
      refine ⟨587261972701160211345413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1566031927203093896921101 587261972701160211345413)
      ·
        refine ⟨110111619881467539627265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 587261972701160211345413 110111619881467539627265)
        ·
          refine ⟨82583714911100654720449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110111619881467539627265 82583714911100654720449)
          ·
            refine ⟨61937786183325491040337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82583714911100654720449 61937786183325491040337)
            ·
              refine ⟨46453339637494118280253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61937786183325491040337 46453339637494118280253)
              ·
                refine ⟨17420002364060294355095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46453339637494118280253 17420002364060294355095)
                ·
                  rfl

theorem cell19_57249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 3].length) (baseStart_57249 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_57249 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_57249 prefixEnd_57249 := by exact prefixLift 57249
  have htrace : WordTrace (prefixWord ++ tailWord_57249) baseStart_57249 baseEnd_57249 := by
    simpa [prefixWord, tailWord_57249, baseEnd_57249] using wordTrace_append hprefix tailTrace_57249
  have hstable : (prefixWord ++ tailWord_57249).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57249).length < 2 ^ (prefixWord ++ tailWord_57249).sum := by decide
  have hdescent : baseEnd_57249 < baseStart_57249 := by decide
  rcases family_descends (prefixWord ++ tailWord_57249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57268 : List Nat := [2, 5, 2, 1, 2, 2, 5]
def baseStart_57268 : Nat := 118140960795 + 57268 * 2 ^ 59
def prefixEnd_57268 : Nat := 4983230072969 + 3 ^ 40 * 57268 * 2
def baseEnd_57268 : Nat := 5808594591957959977607

theorem tailTrace_57268 : CollatzResearch.WordTrace tailWord_57268 prefixEnd_57268 5808594591957959977607 := by
  unfold tailWord_57268
  simp only [CollatzResearch.WordTrace]
  refine ⟨1044367778267645720418229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1392490371023527627224305 1044367778267645720418229)
  ·
    refine ⟨97909479212591786289209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1044367778267645720418229 97909479212591786289209)
    ·
      refine ⟨73432109409443839716907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97909479212591786289209 73432109409443839716907)
      ·
        refine ⟨110148164114165759575361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73432109409443839716907 110148164114165759575361)
        ·
          refine ⟨82611123085624319681521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110148164114165759575361 82611123085624319681521)
          ·
            refine ⟨61958342314218239761141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82611123085624319681521 61958342314218239761141)
            ·
              refine ⟨5808594591957959977607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61958342314218239761141 5808594591957959977607)
              ·
                rfl

theorem cell19_57268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 5].length) (baseStart_57268 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_57268 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_57268 prefixEnd_57268 := by exact prefixLift 57268
  have htrace : WordTrace (prefixWord ++ tailWord_57268) baseStart_57268 baseEnd_57268 := by
    simpa [prefixWord, tailWord_57268, baseEnd_57268] using wordTrace_append hprefix tailTrace_57268
  have hstable : (prefixWord ++ tailWord_57268).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57268).length < 2 ^ (prefixWord ++ tailWord_57268).sum := by decide
  have hdescent : baseEnd_57268 < baseStart_57268 := by decide
  rcases family_descends (prefixWord ++ tailWord_57268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57329 : List Nat := [1, 2, 2, 2, 6, 6]
def baseStart_57329 : Nat := 118140960795 + 57329 * 2 ^ 59
def prefixEnd_57329 : Nat := 4983230072969 + 3 ^ 40 * 57329 * 2
def baseEnd_57329 : Nat := 1938260572293756953011

theorem tailTrace_57329 : CollatzResearch.WordTrace tailWord_57329 prefixEnd_57329 1938260572293756953011 := by
  unfold tailWord_57329
  simp only [CollatzResearch.WordTrace]
  refine ⟨2090960409314298858807041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1393973606209532572538027 2090960409314298858807041)
  ·
    refine ⟨1568220306985724144105281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2090960409314298858807041 1568220306985724144105281)
    ·
      refine ⟨1176165230239293108078961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1568220306985724144105281 1176165230239293108078961)
      ·
        refine ⟨882123922679469831059221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1176165230239293108078961 882123922679469831059221)
        ·
          refine ⟨41349558875600148330901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 882123922679469831059221 41349558875600148330901)
          ·
            refine ⟨1938260572293756953011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41349558875600148330901 1938260572293756953011)
            ·
              rfl

theorem cell19_57329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 6].length) (baseStart_57329 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_57329 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_57329 prefixEnd_57329 := by exact prefixLift 57329
  have htrace : WordTrace (prefixWord ++ tailWord_57329) baseStart_57329 baseEnd_57329 := by
    simpa [prefixWord, tailWord_57329, baseEnd_57329] using wordTrace_append hprefix tailTrace_57329
  have hstable : (prefixWord ++ tailWord_57329).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57329).length < 2 ^ (prefixWord ++ tailWord_57329).sum := by decide
  have hdescent : baseEnd_57329 < baseStart_57329 := by decide
  rcases family_descends (prefixWord ++ tailWord_57329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57365 : List Nat := [1, 3, 2, 1, 5, 1, 3, 3]
def baseStart_57365 : Nat := 118140960795 + 57365 * 2 ^ 59
def prefixEnd_57365 : Nat := 4983230072969 + 3 ^ 40 * 57365 * 2
def baseEnd_57365 : Nat := 17455299404606395777001

theorem tailTrace_57365 : CollatzResearch.WordTrace tailWord_57365 prefixEnd_57365 17455299404606395777001 := by
  unfold tailWord_57365
  simp only [CollatzResearch.WordTrace]
  refine ⟨2092273437183877007117549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1394848958122584671411699 2092273437183877007117549)
  ·
    refine ⟨784602538943953877669081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2092273437183877007117549 784602538943953877669081)
    ·
      refine ⟨588451904207965408251811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 784602538943953877669081 588451904207965408251811)
      ·
        refine ⟨882677856311948112377717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588451904207965408251811 882677856311948112377717)
        ·
          refine ⟨82751049029245135535411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 882677856311948112377717 82751049029245135535411)
          ·
            refine ⟨124126573543867703303117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82751049029245135535411 124126573543867703303117)
            ·
              refine ⟨46547465078950388738669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124126573543867703303117 46547465078950388738669)
              ·
                refine ⟨17455299404606395777001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46547465078950388738669 17455299404606395777001)
                ·
                  rfl

theorem cell19_57365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 3].length) (baseStart_57365 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_57365 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_57365 prefixEnd_57365 := by exact prefixLift 57365
  have htrace : WordTrace (prefixWord ++ tailWord_57365) baseStart_57365 baseEnd_57365 := by
    simpa [prefixWord, tailWord_57365, baseEnd_57365] using wordTrace_append hprefix tailTrace_57365
  have hstable : (prefixWord ++ tailWord_57365).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57365).length < 2 ^ (prefixWord ++ tailWord_57365).sum := by decide
  have hdescent : baseEnd_57365 < baseStart_57365 := by decide
  rcases family_descends (prefixWord ++ tailWord_57365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57384 : List Nat := [2, 1, 5, 3, 1, 1, 6]
def baseStart_57384 : Nat := 118140960795 + 57384 * 2 ^ 59
def prefixEnd_57384 : Nat := 4983230072969 + 3 ^ 40 * 57384 * 2
def baseEnd_57384 : Nat := 5820360272139993784909

theorem tailTrace_57384 : CollatzResearch.WordTrace tailWord_57384 prefixEnd_57384 5820360272139993784909 := by
  unfold tailWord_57384
  simp only [CollatzResearch.WordTrace]
  refine ⟨1046483212057521626029603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1395310949410028834706137 1046483212057521626029603)
  ·
    refine ⟨1569724818086282439044405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1046483212057521626029603 1569724818086282439044405)
    ·
      refine ⟨147161701695588978660413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1569724818086282439044405 147161701695588978660413)
      ·
        refine ⟨55185638135845866997655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147161701695588978660413 55185638135845866997655)
        ·
          refine ⟨82778457203768800496483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55185638135845866997655 82778457203768800496483)
          ·
            refine ⟨124167685805653200744725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82778457203768800496483 124167685805653200744725)
            ·
              refine ⟨5820360272139993784909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 124167685805653200744725 5820360272139993784909)
              ·
                rfl

theorem cell19_57384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 6].length) (baseStart_57384 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_57384 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_57384 prefixEnd_57384 := by exact prefixLift 57384
  have htrace : WordTrace (prefixWord ++ tailWord_57384) baseStart_57384 baseEnd_57384 := by
    simpa [prefixWord, tailWord_57384, baseEnd_57384] using wordTrace_append hprefix tailTrace_57384
  have hstable : (prefixWord ++ tailWord_57384).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57384).length < 2 ^ (prefixWord ++ tailWord_57384).sum := by decide
  have hdescent : baseEnd_57384 < baseStart_57384 := by decide
  rcases family_descends (prefixWord ++ tailWord_57384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57386 : List Nat := [3, 1, 4, 1, 2, 2, 6]
def baseStart_57386 : Nat := 118140960795 + 57386 * 2 ^ 59
def prefixEnd_57386 : Nat := 4983230072969 + 3 ^ 40 * 57386 * 2
def baseEnd_57386 : Nat := 5820563128694856436759

theorem tailTrace_57386 : CollatzResearch.WordTrace tailWord_57386 prefixEnd_57386 5820563128694856436759 := by
  unfold tailWord_57386
  simp only [CollatzResearch.WordTrace]
  refine ⟨523259842526949398408003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1395359580071865062421341 523259842526949398408003)
  ·
    refine ⟨784889763790424097612005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 523259842526949398408003 784889763790424097612005)
    ·
      refine ⟨147166830710704518302251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 784889763790424097612005 147166830710704518302251)
      ·
        refine ⟨220750246066056777453377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147166830710704518302251 220750246066056777453377)
        ·
          refine ⟨165562684549542583090033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220750246066056777453377 165562684549542583090033)
          ·
            refine ⟨124172013412156937317525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165562684549542583090033 124172013412156937317525)
            ·
              refine ⟨5820563128694856436759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 124172013412156937317525 5820563128694856436759)
              ·
                rfl

theorem cell19_57386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 6].length) (baseStart_57386 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_57386 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_57386 prefixEnd_57386 := by exact prefixLift 57386
  have htrace : WordTrace (prefixWord ++ tailWord_57386) baseStart_57386 baseEnd_57386 := by
    simpa [prefixWord, tailWord_57386, baseEnd_57386] using wordTrace_append hprefix tailTrace_57386
  have hstable : (prefixWord ++ tailWord_57386).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57386).length < 2 ^ (prefixWord ++ tailWord_57386).sum := by decide
  have hdescent : baseEnd_57386 < baseStart_57386 := by decide
  rcases family_descends (prefixWord ++ tailWord_57386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57422 : List Nat := [4, 1, 1, 1, 1, 6, 2, 3]
def baseStart_57422 : Nat := 118140960795 + 57422 * 2 ^ 59
def prefixEnd_57422 : Nat := 4983230072969 + 3 ^ 40 * 57422 * 2
def baseEnd_57422 : Nat := 17472643640047152510179

theorem tailTrace_57422 : CollatzResearch.WordTrace tailWord_57422 prefixEnd_57422 17472643640047152510179 := by
  unfold tailWord_57422
  simp only [CollatzResearch.WordTrace]
  refine ⟨261794049747171967742815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1396234931984917161295013 261794049747171967742815)
  ·
    refine ⟨392691074620757951614223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261794049747171967742815 392691074620757951614223)
    ·
      refine ⟨589036611931136927421335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392691074620757951614223 589036611931136927421335)
      ·
        refine ⟨883554917896705391132003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589036611931136927421335 883554917896705391132003)
        ·
          refine ⟨1325332376845058086698005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 883554917896705391132003 1325332376845058086698005)
          ·
            refine ⟨62124955164612097813969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1325332376845058086698005 62124955164612097813969)
            ·
              refine ⟨46593716373459073360477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62124955164612097813969 46593716373459073360477)
              ·
                refine ⟨17472643640047152510179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46593716373459073360477 17472643640047152510179)
                ·
                  rfl

theorem cell19_57422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_57422 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_57422 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_57422 prefixEnd_57422 := by exact prefixLift 57422
  have htrace : WordTrace (prefixWord ++ tailWord_57422) baseStart_57422 baseEnd_57422 := by
    simpa [prefixWord, tailWord_57422, baseEnd_57422] using wordTrace_append hprefix tailTrace_57422
  have hstable : (prefixWord ++ tailWord_57422).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57422).length < 2 ^ (prefixWord ++ tailWord_57422).sum := by decide
  have hdescent : baseEnd_57422 < baseStart_57422 := by decide
  rcases family_descends (prefixWord ++ tailWord_57422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57445 : List Nat := [1, 3, 1, 3, 2, 2, 7]
def baseStart_57445 : Nat := 118140960795 + 57445 * 2 ^ 59
def prefixEnd_57445 : Nat := 4983230072969 + 3 ^ 40 * 57445 * 2
def baseEnd_57445 : Nat := 5826547397063304666335

theorem tailTrace_57445 : CollatzResearch.WordTrace tailWord_57445 prefixEnd_57445 5826547397063304666335 := by
  unfold tailWord_57445
  simp only [CollatzResearch.WordTrace]
  refine ⟨2095191276894050670029789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1396794184596033780019859 2095191276894050670029789)
  ·
    refine ⟨785696728835269001261171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2095191276894050670029789 785696728835269001261171)
    ·
      refine ⟨1178545093252903501891757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 785696728835269001261171 1178545093252903501891757)
      ·
        refine ⟨441954409969838813209409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1178545093252903501891757 441954409969838813209409)
        ·
          refine ⟨331465807477379109907057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 441954409969838813209409 331465807477379109907057)
          ·
            refine ⟨248599355608034332430293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331465807477379109907057 248599355608034332430293)
            ·
              refine ⟨5826547397063304666335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 248599355608034332430293 5826547397063304666335)
              ·
                rfl

theorem cell19_57445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 7].length) (baseStart_57445 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_57445 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_57445 prefixEnd_57445 := by exact prefixLift 57445
  have htrace : WordTrace (prefixWord ++ tailWord_57445) baseStart_57445 baseEnd_57445 := by
    simpa [prefixWord, tailWord_57445, baseEnd_57445] using wordTrace_append hprefix tailTrace_57445
  have hstable : (prefixWord ++ tailWord_57445).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57445).length < 2 ^ (prefixWord ++ tailWord_57445).sum := by decide
  have hdescent : baseEnd_57445 < baseStart_57445 := by decide
  rcases family_descends (prefixWord ++ tailWord_57445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57462 : List Nat := [5, 1, 1, 2, 1, 2, 1, 6]
def baseStart_57462 : Nat := 118140960795 + 57462 * 2 ^ 59
def prefixEnd_57462 : Nat := 4983230072969 + 3 ^ 40 * 57462 * 2
def baseEnd_57462 : Nat := 17484815033338911621181

theorem tailTrace_57462 : CollatzResearch.WordTrace tailWord_57462 prefixEnd_57462 17484815033338911621181 := by
  unfold tailWord_57462
  simp only [CollatzResearch.WordTrace]
  refine ⟨130988207364528910837415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1397207545221641715599093 130988207364528910837415)
  ·
    refine ⟨196482311046793366256123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130988207364528910837415 196482311046793366256123)
    ·
      refine ⟨294723466570190049384185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196482311046793366256123 294723466570190049384185)
      ·
        refine ⟨221042599927642537038139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294723466570190049384185 221042599927642537038139)
        ·
          refine ⟨331563899891463805557209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221042599927642537038139 331563899891463805557209)
          ·
            refine ⟨248672924918597854167907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331563899891463805557209 248672924918597854167907)
            ·
              refine ⟨373009387377896781251861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248672924918597854167907 373009387377896781251861)
              ·
                refine ⟨17484815033338911621181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 373009387377896781251861 17484815033338911621181)
                ·
                  rfl

theorem cell19_57462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_57462 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_57462 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_57462 prefixEnd_57462 := by exact prefixLift 57462
  have htrace : WordTrace (prefixWord ++ tailWord_57462) baseStart_57462 baseEnd_57462 := by
    simpa [prefixWord, tailWord_57462, baseEnd_57462] using wordTrace_append hprefix tailTrace_57462
  have hstable : (prefixWord ++ tailWord_57462).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57462).length < 2 ^ (prefixWord ++ tailWord_57462).sum := by decide
  have hdescent : baseEnd_57462 < baseStart_57462 := by decide
  rcases family_descends (prefixWord ++ tailWord_57462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57494 : List Nat := [5, 3, 2, 1, 1, 7]
def baseStart_57494 : Nat := 118140960795 + 57494 * 2 ^ 59
def prefixEnd_57494 : Nat := 4983230072969 + 3 ^ 40 * 57494 * 2
def baseEnd_57494 : Nat := 1943839127552479878887

theorem tailTrace_57494 : CollatzResearch.WordTrace tailWord_57494 prefixEnd_57494 1943839127552479878887 := by
  unfold tailWord_57494
  simp only [CollatzResearch.WordTrace]
  refine ⟨131061153357283252410221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1397985635811021359042357 131061153357283252410221)
  ·
    refine ⟨49147932508981219653833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131061153357283252410221 49147932508981219653833)
    ·
      refine ⟨36860949381735914740375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49147932508981219653833 36860949381735914740375)
      ·
        refine ⟨55291424072603872110563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36860949381735914740375 55291424072603872110563)
        ·
          refine ⟨82937136108905808165845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55291424072603872110563 82937136108905808165845)
          ·
            refine ⟨1943839127552479878887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 82937136108905808165845 1943839127552479878887)
            ·
              rfl

theorem cell19_57494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 7].length) (baseStart_57494 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_57494 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_57494 prefixEnd_57494 := by exact prefixLift 57494
  have htrace : WordTrace (prefixWord ++ tailWord_57494) baseStart_57494 baseEnd_57494 := by
    simpa [prefixWord, tailWord_57494, baseEnd_57494] using wordTrace_append hprefix tailTrace_57494
  have hstable : (prefixWord ++ tailWord_57494).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57494).length < 2 ^ (prefixWord ++ tailWord_57494).sum := by decide
  have hdescent : baseEnd_57494 < baseStart_57494 := by decide
  rcases family_descends (prefixWord ++ tailWord_57494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57517 : List Nat := [1, 5, 2, 1, 2, 3, 1, 4]
def baseStart_57517 : Nat := 118140960795 + 57517 * 2 ^ 59
def prefixEnd_57517 : Nat := 4983230072969 + 3 ^ 40 * 57517 * 2
def baseEnd_57517 : Nat := 17501550699115080398809

theorem tailTrace_57517 : CollatzResearch.WordTrace tailWord_57517 prefixEnd_57517 17501550699115080398809 := by
  unfold tailWord_57517
  simp only [CollatzResearch.WordTrace]
  refine ⟨2097817332633206966650805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1398544888422137977767203 2097817332633206966650805)
  ·
    refine ⟨196670374934363153123513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2097817332633206966650805 196670374934363153123513)
    ·
      refine ⟨147502781200772364842635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196670374934363153123513 147502781200772364842635)
      ·
        refine ⟨221254171801158547263953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147502781200772364842635 221254171801158547263953)
        ·
          refine ⟨165940628850868910447965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221254171801158547263953 165940628850868910447965)
          ·
            refine ⟨62227735819075841417987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165940628850868910447965 62227735819075841417987)
            ·
              refine ⟨93341603728613762126981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62227735819075841417987 93341603728613762126981)
              ·
                refine ⟨17501550699115080398809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93341603728613762126981 17501550699115080398809)
                ·
                  rfl

theorem cell19_57517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 4].length) (baseStart_57517 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_57517 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_57517 prefixEnd_57517 := by exact prefixLift 57517
  have htrace : WordTrace (prefixWord ++ tailWord_57517) baseStart_57517 baseEnd_57517 := by
    simpa [prefixWord, tailWord_57517, baseEnd_57517] using wordTrace_append hprefix tailTrace_57517
  have hstable : (prefixWord ++ tailWord_57517).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57517).length < 2 ^ (prefixWord ++ tailWord_57517).sum := by decide
  have hdescent : baseEnd_57517 < baseStart_57517 := by decide
  rcases family_descends (prefixWord ++ tailWord_57517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57557 : List Nat := [1, 3, 2, 4, 2, 1, 6]
def baseStart_57557 : Nat := 118140960795 + 57557 * 2 ^ 59
def prefixEnd_57557 : Nat := 4983230072969 + 3 ^ 40 * 57557 * 2
def baseEnd_57557 : Nat := 5837907364135613169937

theorem tailTrace_57557 : CollatzResearch.WordTrace tailWord_57557 prefixEnd_57557 5837907364135613169937 := by
  unfold tailWord_57557
  simp only [CollatzResearch.WordTrace]
  refine ⟨2099276252488293798106925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1399517501658862532071283 2099276252488293798106925)
  ·
    refine ⟨787228594683110174290097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2099276252488293798106925 787228594683110174290097)
    ·
      refine ⟨590421446012332630717573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 787228594683110174290097 590421446012332630717573)
      ·
        refine ⟨110704021127312368259545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 590421446012332630717573 110704021127312368259545)
        ·
          refine ⟨83028015845484276194659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110704021127312368259545 83028015845484276194659)
          ·
            refine ⟨124542023768226414291989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83028015845484276194659 124542023768226414291989)
            ·
              refine ⟨5837907364135613169937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 124542023768226414291989 5837907364135613169937)
              ·
                rfl

theorem cell19_57557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 6].length) (baseStart_57557 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_57557 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_57557 prefixEnd_57557 := by exact prefixLift 57557
  have htrace : WordTrace (prefixWord ++ tailWord_57557) baseStart_57557 baseEnd_57557 := by
    simpa [prefixWord, tailWord_57557, baseEnd_57557] using wordTrace_append hprefix tailTrace_57557
  have hstable : (prefixWord ++ tailWord_57557).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57557).length < 2 ^ (prefixWord ++ tailWord_57557).sum := by decide
  have hdescent : baseEnd_57557 < baseStart_57557 := by decide
  rcases family_descends (prefixWord ++ tailWord_57557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57578 : List Nat := [3, 1, 3, 1, 1, 2, 2, 6]
def baseStart_57578 : Nat := 118140960795 + 57578 * 2 ^ 59
def prefixEnd_57578 : Nat := 4983230072969 + 3 ^ 40 * 57578 * 2
def baseEnd_57578 : Nat := 17520112073885013043087

theorem tailTrace_57578 : CollatzResearch.WordTrace tailWord_57578 prefixEnd_57578 17520112073885013043087 := by
  unfold tailWord_57578
  simp only [CollatzResearch.WordTrace]
  refine ⟨525010546353053596155347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1400028123608142923080925 525010546353053596155347)
  ·
    refine ⟨787515819529580394233021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 525010546353053596155347 787515819529580394233021)
    ·
      refine ⟨295318432323592647837383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 787515819529580394233021 295318432323592647837383)
      ·
        refine ⟨442977648485388971756075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295318432323592647837383 442977648485388971756075)
        ·
          refine ⟨664466472728083457634113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442977648485388971756075 664466472728083457634113)
          ·
            refine ⟨498349854546062593225585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 664466472728083457634113 498349854546062593225585)
            ·
              refine ⟨373762390909546944919189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 498349854546062593225585 373762390909546944919189)
              ·
                refine ⟨17520112073885013043087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 373762390909546944919189 17520112073885013043087)
                ·
                  rfl

theorem cell19_57578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_57578 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_57578 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_57578 prefixEnd_57578 := by exact prefixLift 57578
  have htrace : WordTrace (prefixWord ++ tailWord_57578) baseStart_57578 baseEnd_57578 := by
    simpa [prefixWord, tailWord_57578, baseEnd_57578] using wordTrace_append hprefix tailTrace_57578
  have hstable : (prefixWord ++ tailWord_57578).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57578).length < 2 ^ (prefixWord ++ tailWord_57578).sum := by decide
  have hdescent : baseEnd_57578 < baseStart_57578 := by decide
  rcases family_descends (prefixWord ++ tailWord_57578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57635 : List Nat := [1, 1, 1, 4, 2, 2, 4, 4]
def baseStart_57635 : Nat := 118140960795 + 57635 * 2 ^ 59
def prefixEnd_57635 : Nat := 4983230072969 + 3 ^ 40 * 57635 * 2
def baseEnd_57635 : Nat := 17537456309325769776265

theorem tailTrace_57635 : CollatzResearch.WordTrace tailWord_57635 prefixEnd_57635 17537456309325769776265 := by
  unfold tailWord_57635
  simp only [CollatzResearch.WordTrace]
  refine ⟨2102121146205713119446359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1401414097470475412964239 2102121146205713119446359)
  ·
    refine ⟨3153181719308569679169539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2102121146205713119446359 3153181719308569679169539)
    ·
      refine ⟨4729772578962854518754309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3153181719308569679169539 4729772578962854518754309)
      ·
        refine ⟨886832358555535222266433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4729772578962854518754309 886832358555535222266433)
        ·
          refine ⟨665124268916651416699825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 886832358555535222266433 665124268916651416699825)
          ·
            refine ⟨498843201687488562524869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 665124268916651416699825 498843201687488562524869)
            ·
              refine ⟨93533100316404105473413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 498843201687488562524869 93533100316404105473413)
              ·
                refine ⟨17537456309325769776265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93533100316404105473413 17537456309325769776265)
                ·
                  rfl

theorem cell19_57635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 4].length) (baseStart_57635 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_57635 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_57635 prefixEnd_57635 := by exact prefixLift 57635
  have htrace : WordTrace (prefixWord ++ tailWord_57635) baseStart_57635 baseEnd_57635 := by
    simpa [prefixWord, tailWord_57635, baseEnd_57635] using wordTrace_append hprefix tailTrace_57635
  have hstable : (prefixWord ++ tailWord_57635).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57635).length < 2 ^ (prefixWord ++ tailWord_57635).sum := by decide
  have hdescent : baseEnd_57635 < baseStart_57635 := by decide
  rcases family_descends (prefixWord ++ tailWord_57635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57652 : List Nat := [2, 5, 1, 1, 1, 2, 2, 5]
def baseStart_57652 : Nat := 118140960795 + 57652 * 2 ^ 59
def prefixEnd_57652 : Nat := 4983230072969 + 3 ^ 40 * 57652 * 2
def baseEnd_57652 : Nat := 17542629151474767398441

theorem tailTrace_57652 : CollatzResearch.WordTrace tailWord_57652 prefixEnd_57652 17542629151474767398441 := by
  unfold tailWord_57652
  simp only [CollatzResearch.WordTrace]
  refine ⟨1051370593572062511407605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1401827458096083348543473 1051370593572062511407605)
  ·
    refine ⟨98565993147380860444463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1051370593572062511407605 98565993147380860444463)
    ·
      refine ⟨147848989721071290666695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98565993147380860444463 147848989721071290666695)
      ·
        refine ⟨221773484581606936000043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147848989721071290666695 221773484581606936000043)
        ·
          refine ⟨332660226872410404000065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221773484581606936000043 332660226872410404000065)
          ·
            refine ⟨249495170154307803000049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332660226872410404000065 249495170154307803000049)
            ·
              refine ⟨187121377615730852250037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249495170154307803000049 187121377615730852250037)
              ·
                refine ⟨17542629151474767398441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 187121377615730852250037 17542629151474767398441)
                ·
                  rfl

theorem cell19_57652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_57652 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_57652 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_57652 prefixEnd_57652 := by exact prefixLift 57652
  have htrace : WordTrace (prefixWord ++ tailWord_57652) baseStart_57652 baseEnd_57652 := by
    simpa [prefixWord, tailWord_57652, baseEnd_57652] using wordTrace_append hprefix tailTrace_57652
  have hstable : (prefixWord ++ tailWord_57652).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57652).length < 2 ^ (prefixWord ++ tailWord_57652).sum := by decide
  have hdescent : baseEnd_57652 < baseStart_57652 := by decide
  rcases family_descends (prefixWord ++ tailWord_57652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57709 : List Nat := [1, 5, 1, 1, 1, 2, 5, 3]
def baseStart_57709 : Nat := 118140960795 + 57709 * 2 ^ 59
def prefixEnd_57709 : Nat := 4983230072969 + 3 ^ 40 * 57709 * 2
def baseEnd_57709 : Nat := 17559973386915524131619

theorem tailTrace_57709 : CollatzResearch.WordTrace tailWord_57709 prefixEnd_57709 17559973386915524131619 := by
  unfold tailWord_57709
  simp only [CollatzResearch.WordTrace]
  refine ⟨2104820147937623757640181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1403213431958415838426787 2104820147937623757640181)
  ·
    refine ⟨197326888869152227278767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2104820147937623757640181 197326888869152227278767)
    ·
      refine ⟨295990333303728340918151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197326888869152227278767 295990333303728340918151)
      ·
        refine ⟨443985499955592511377227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295990333303728340918151 443985499955592511377227)
        ·
          refine ⟨665978249933388767065841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443985499955592511377227 665978249933388767065841)
          ·
            refine ⟨499483687450041575299381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 665978249933388767065841 499483687450041575299381)
            ·
              refine ⟨46826595698441397684317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 499483687450041575299381 46826595698441397684317)
              ·
                refine ⟨17559973386915524131619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46826595698441397684317 17559973386915524131619)
                ·
                  rfl

theorem cell19_57709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 3].length) (baseStart_57709 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_57709 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_57709 prefixEnd_57709 := by exact prefixLift 57709
  have htrace : WordTrace (prefixWord ++ tailWord_57709) baseStart_57709 baseEnd_57709 := by
    simpa [prefixWord, tailWord_57709, baseEnd_57709] using wordTrace_append hprefix tailTrace_57709
  have hstable : (prefixWord ++ tailWord_57709).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57709).length < 2 ^ (prefixWord ++ tailWord_57709).sum := by decide
  have hdescent : baseEnd_57709 < baseStart_57709 := by decide
  rcases family_descends (prefixWord ++ tailWord_57709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57804 : List Nat := [2, 2, 1, 4, 3, 1, 2, 4]
def baseStart_57804 : Nat := 118140960795 + 57804 * 2 ^ 59
def prefixEnd_57804 : Nat := 4983230072969 + 3 ^ 40 * 57804 * 2
def baseEnd_57804 : Nat := 17588880445983452020249

theorem tailTrace_57804 : CollatzResearch.WordTrace tailWord_57804 prefixEnd_57804 17588880445983452020249 := by
  unfold tailWord_57804
  simp only [CollatzResearch.WordTrace]
  refine ⟨1054142541296727491174233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1405523388395636654898977 1054142541296727491174233)
  ·
    refine ⟨790606905972545618380675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1054142541296727491174233 790606905972545618380675)
    ·
      refine ⟨1185910358958818427571013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 790606905972545618380675 1185910358958818427571013)
      ·
        refine ⟨222358192304778455169565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1185910358958818427571013 222358192304778455169565)
        ·
          refine ⟨83384322114291920688587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222358192304778455169565 83384322114291920688587)
          ·
            refine ⟨125076483171437881032881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83384322114291920688587 125076483171437881032881)
            ·
              refine ⟨93807362378578410774661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125076483171437881032881 93807362378578410774661)
              ·
                refine ⟨17588880445983452020249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93807362378578410774661 17588880445983452020249)
                ·
                  rfl

theorem cell19_57804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 4].length) (baseStart_57804 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_57804 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_57804 prefixEnd_57804 := by exact prefixLift 57804
  have htrace : WordTrace (prefixWord ++ tailWord_57804) baseStart_57804 baseEnd_57804 := by
    simpa [prefixWord, tailWord_57804, baseEnd_57804] using wordTrace_append hprefix tailTrace_57804
  have hstable : (prefixWord ++ tailWord_57804).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57804).length < 2 ^ (prefixWord ++ tailWord_57804).sum := by decide
  have hdescent : baseEnd_57804 < baseStart_57804 := by decide
  rcases family_descends (prefixWord ++ tailWord_57804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57842 : List Nat := [3, 2, 1, 4, 3, 6]
def baseStart_57842 : Nat := 118140960795 + 57842 * 2 ^ 59
def prefixEnd_57842 : Nat := 4983230072969 + 3 ^ 40 * 57842 * 2
def baseEnd_57842 : Nat := 1955604807734513686189

theorem tailTrace_57842 : CollatzResearch.WordTrace tailWord_57842 prefixEnd_57842 1955604807734513686189 := by
  unfold tailWord_57842
  simp only [CollatzResearch.WordTrace]
  refine ⟨527417764113946868057945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1406447370970524981487853 527417764113946868057945)
  ·
    refine ⟨395563323085460151043459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 527417764113946868057945 395563323085460151043459)
    ·
      refine ⟨593344984628190226565189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395563323085460151043459 593344984628190226565189)
      ·
        refine ⟨111252184617785667480973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 593344984628190226565189 111252184617785667480973)
        ·
          refine ⟨41719569231669625305365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111252184617785667480973 41719569231669625305365)
          ·
            refine ⟨1955604807734513686189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41719569231669625305365 1955604807734513686189)
            ·
              rfl

theorem cell19_57842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 6].length) (baseStart_57842 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_57842 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_57842 prefixEnd_57842 := by exact prefixLift 57842
  have htrace : WordTrace (prefixWord ++ tailWord_57842) baseStart_57842 baseEnd_57842 := by
    simpa [prefixWord, tailWord_57842, baseEnd_57842] using wordTrace_append hprefix tailTrace_57842
  have hstable : (prefixWord ++ tailWord_57842).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57842).length < 2 ^ (prefixWord ++ tailWord_57842).sum := by decide
  have hdescent : baseEnd_57842 < baseStart_57842 := by decide
  rcases family_descends (prefixWord ++ tailWord_57842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57844 : List Nat := [2, 6, 11]
def baseStart_57844 : Nat := 118140960795 + 57844 * 2 ^ 59
def prefixEnd_57844 : Nat := 4983230072969 + 3 ^ 40 * 57844 * 2
def baseEnd_57844 : Nat := 72432312095782761857

theorem tailTrace_57844 : CollatzResearch.WordTrace tailWord_57844 prefixEnd_57844 72432312095782761857 := by
  unfold tailWord_57844
  simp only [CollatzResearch.WordTrace]
  refine ⟨1054872001224270906902293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1406496001632361209203057 1054872001224270906902293)
  ·
    refine ⟨49447125057387698761045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1054872001224270906902293 49447125057387698761045)
    ·
      refine ⟨72432312095782761857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 11 49447125057387698761045 72432312095782761857)
      ·
        rfl

theorem cell19_57844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 11].length) (baseStart_57844 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_57844 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_57844 prefixEnd_57844 := by exact prefixLift 57844
  have htrace : WordTrace (prefixWord ++ tailWord_57844) baseStart_57844 baseEnd_57844 := by
    simpa [prefixWord, tailWord_57844, baseEnd_57844] using wordTrace_append hprefix tailTrace_57844
  have hstable : (prefixWord ++ tailWord_57844).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57844).length < 2 ^ (prefixWord ++ tailWord_57844).sum := by decide
  have hdescent : baseEnd_57844 < baseStart_57844 := by decide
  rcases family_descends (prefixWord ++ tailWord_57844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57865 : List Nat := [1, 2, 1, 1, 3, 1, 2, 8]
def baseStart_57865 : Nat := 118140960795 + 57865 * 2 ^ 59
def prefixEnd_57865 : Nat := 4983230072969 + 3 ^ 40 * 57865 * 2
def baseEnd_57865 : Nat := 17607441820753384664527

theorem tailTrace_57865 : CollatzResearch.WordTrace tailWord_57865 prefixEnd_57865 17607441820753384664527 := by
  unfold tailWord_57865
  simp only [CollatzResearch.WordTrace]
  refine ⟨2110509935372462400319049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1407006623581641600212699 2110509935372462400319049)
  ·
    refine ⟨1582882451529346800239287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2110509935372462400319049 1582882451529346800239287)
    ·
      refine ⟨2374323677294020200358931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1582882451529346800239287 2374323677294020200358931)
      ·
        refine ⟨3561485515941030300538397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2374323677294020200358931 3561485515941030300538397)
        ·
          refine ⟨1335557068477886362701899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3561485515941030300538397 1335557068477886362701899)
          ·
            refine ⟨2003335602716829544052849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1335557068477886362701899 2003335602716829544052849)
            ·
              refine ⟨1502501702037622158039637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2003335602716829544052849 1502501702037622158039637)
              ·
                refine ⟨17607441820753384664527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1502501702037622158039637 17607441820753384664527)
                ·
                  rfl

theorem cell19_57865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 8].length) (baseStart_57865 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_57865 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_57865 prefixEnd_57865 := by exact prefixLift 57865
  have htrace : WordTrace (prefixWord ++ tailWord_57865) baseStart_57865 baseEnd_57865 := by
    simpa [prefixWord, tailWord_57865, baseEnd_57865] using wordTrace_append hprefix tailTrace_57865
  have hstable : (prefixWord ++ tailWord_57865).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57865).length < 2 ^ (prefixWord ++ tailWord_57865).sum := by decide
  have hdescent : baseEnd_57865 < baseStart_57865 := by decide
  rcases family_descends (prefixWord ++ tailWord_57865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57880 : List Nat := [2, 1, 2, 3, 3, 2, 3, 3]
def baseStart_57880 : Nat := 118140960795 + 57880 * 2 ^ 59
def prefixEnd_57880 : Nat := 4983230072969 + 3 ^ 40 * 57880 * 2
def baseEnd_57880 : Nat := 17612006093237794331153

theorem tailTrace_57880 : CollatzResearch.WordTrace tailWord_57880 prefixEnd_57880 17612006093237794331153 := by
  unfold tailWord_57880
  simp only [CollatzResearch.WordTrace]
  refine ⟨1055528515159059981057547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1407371353545413308076729 1055528515159059981057547)
  ·
    refine ⟨1583292772738589971586321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1055528515159059981057547 1583292772738589971586321)
    ·
      refine ⟨1187469579553942478689741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1583292772738589971586321 1187469579553942478689741)
      ·
        refine ⟨445301092332728429508653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1187469579553942478689741 445301092332728429508653)
        ·
          refine ⟨166987909624773161065745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 445301092332728429508653 166987909624773161065745)
          ·
            refine ⟨125240932218579870799309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166987909624773161065745 125240932218579870799309)
            ·
              refine ⟨46965349581967451549741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125240932218579870799309 46965349581967451549741)
              ·
                refine ⟨17612006093237794331153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46965349581967451549741 17612006093237794331153)
                ·
                  rfl

theorem cell19_57880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 3].length) (baseStart_57880 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_57880 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_57880 prefixEnd_57880 := by exact prefixLift 57880
  have htrace : WordTrace (prefixWord ++ tailWord_57880) baseStart_57880 baseEnd_57880 := by
    simpa [prefixWord, tailWord_57880, baseEnd_57880] using wordTrace_append hprefix tailTrace_57880
  have hstable : (prefixWord ++ tailWord_57880).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57880).length < 2 ^ (prefixWord ++ tailWord_57880).sum := by decide
  have hdescent : baseEnd_57880 < baseStart_57880 := by decide
  rcases family_descends (prefixWord ++ tailWord_57880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57937 : List Nat := [1, 2, 2, 1, 3, 5, 2, 3]
def baseStart_57937 : Nat := 118140960795 + 57937 * 2 ^ 59
def prefixEnd_57937 : Nat := 4983230072969 + 3 ^ 40 * 57937 * 2
def baseEnd_57937 : Nat := 17629350328678551064331

theorem tailTrace_57937 : CollatzResearch.WordTrace tailWord_57937 prefixEnd_57937 17629350328678551064331 := by
  unfold tailWord_57937
  simp only [CollatzResearch.WordTrace]
  refine ⟨2113135991111618696940065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1408757327407745797960043 2113135991111618696940065)
  ·
    refine ⟨1584851993333714022705049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2113135991111618696940065 1584851993333714022705049)
    ·
      refine ⟨1188638995000285517028787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1584851993333714022705049 1188638995000285517028787)
      ·
        refine ⟨1782958492500428275543181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1188638995000285517028787 1782958492500428275543181)
        ·
          refine ⟨668609434687660603328693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1782958492500428275543181 668609434687660603328693)
          ·
            refine ⟨62682134501968181562065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 668609434687660603328693 62682134501968181562065)
            ·
              refine ⟨47011600876476136171549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62682134501968181562065 47011600876476136171549)
              ·
                refine ⟨17629350328678551064331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47011600876476136171549 17629350328678551064331)
                ·
                  rfl

theorem cell19_57937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 3].length) (baseStart_57937 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_57937 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_57937 prefixEnd_57937 := by exact prefixLift 57937
  have htrace : WordTrace (prefixWord ++ tailWord_57937) baseStart_57937 baseEnd_57937 := by
    simpa [prefixWord, tailWord_57937, baseEnd_57937] using wordTrace_append hprefix tailTrace_57937
  have hstable : (prefixWord ++ tailWord_57937).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57937).length < 2 ^ (prefixWord ++ tailWord_57937).sum := by decide
  have hdescent : baseEnd_57937 < baseStart_57937 := by decide
  rcases family_descends (prefixWord ++ tailWord_57937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57950 : List Nat := [4, 4, 1, 2, 2, 1, 5]
def baseStart_57950 : Nat := 118140960795 + 57950 * 2 ^ 59
def prefixEnd_57950 : Nat := 4983230072969 + 3 ^ 40 * 57950 * 2
def baseEnd_57950 : Nat := 5877768677166124258469

theorem tailTrace_57950 : CollatzResearch.WordTrace tailWord_57950 prefixEnd_57950 5877768677166124258469 := by
  unfold tailWord_57950
  simp only [CollatzResearch.WordTrace]
  refine ⟨264201267508065239645413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1409073426709681278108869 264201267508065239645413)
  ·
    refine ⟨49537737657762232433515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264201267508065239645413 49537737657762232433515)
    ·
      refine ⟨74306606486643348650273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49537737657762232433515 74306606486643348650273)
      ·
        refine ⟨55729954864982511487705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74306606486643348650273 55729954864982511487705)
        ·
          refine ⟨41797466148736883615779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55729954864982511487705 41797466148736883615779)
          ·
            refine ⟨62696199223105325423669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41797466148736883615779 62696199223105325423669)
            ·
              refine ⟨5877768677166124258469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62696199223105325423669 5877768677166124258469)
              ·
                rfl

theorem cell19_57950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 5].length) (baseStart_57950 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_57950 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_57950 prefixEnd_57950 := by exact prefixLift 57950
  have htrace : WordTrace (prefixWord ++ tailWord_57950) baseStart_57950 baseEnd_57950 := by
    simpa [prefixWord, tailWord_57950, baseEnd_57950] using wordTrace_append hprefix tailTrace_57950
  have hstable : (prefixWord ++ tailWord_57950).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57950).length < 2 ^ (prefixWord ++ tailWord_57950).sum := by decide
  have hdescent : baseEnd_57950 < baseStart_57950 := by decide
  rcases family_descends (prefixWord ++ tailWord_57950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57954 : List Nat := [3, 3, 2, 3, 1, 2, 5]
def baseStart_57954 : Nat := 118140960795 + 57954 * 2 ^ 59
def prefixEnd_57954 : Nat := 4983230072969 + 3 ^ 40 * 57954 * 2
def baseEnd_57954 : Nat := 5878174390275849562169

theorem tailTrace_57954 : CollatzResearch.WordTrace tailWord_57954 prefixEnd_57954 5878174390275849562169 := by
  unfold tailWord_57954
  simp only [CollatzResearch.WordTrace]
  refine ⟨528439008012507650077229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1409170688033353733539277 528439008012507650077229)
  ·
    refine ⟨198164628004690368778961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 528439008012507650077229 198164628004690368778961)
    ·
      refine ⟨148623471003517776584221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198164628004690368778961 148623471003517776584221)
      ·
        refine ⟨55733801626319166219083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148623471003517776584221 55733801626319166219083)
        ·
          refine ⟨83600702439478749328625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55733801626319166219083 83600702439478749328625)
          ·
            refine ⟨62700526829609061996469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83600702439478749328625 62700526829609061996469)
            ·
              refine ⟨5878174390275849562169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62700526829609061996469 5878174390275849562169)
              ·
                rfl

theorem cell19_57954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 5].length) (baseStart_57954 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_57954 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_57954 prefixEnd_57954 := by exact prefixLift 57954
  have htrace : WordTrace (prefixWord ++ tailWord_57954) baseStart_57954 baseEnd_57954 := by
    simpa [prefixWord, tailWord_57954, baseEnd_57954] using wordTrace_append hprefix tailTrace_57954
  have hstable : (prefixWord ++ tailWord_57954).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57954).length < 2 ^ (prefixWord ++ tailWord_57954).sum := by decide
  have hdescent : baseEnd_57954 < baseStart_57954 := by decide
  rcases family_descends (prefixWord ++ tailWord_57954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57977 : List Nat := [1, 2, 1, 3, 3, 3, 2, 4]
def baseStart_57977 : Nat := 118140960795 + 57977 * 2 ^ 59
def prefixEnd_57977 : Nat := 4983230072969 + 3 ^ 40 * 57977 * 2
def baseEnd_57977 : Nat := 17641521721970310175333

theorem tailTrace_57977 : CollatzResearch.WordTrace tailWord_57977 prefixEnd_57977 17641521721970310175333 := by
  unfold tailWord_57977
  simp only [CollatzResearch.WordTrace]
  refine ⟨2114594910966705528396185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1409729940644470352264123 2114594910966705528396185)
  ·
    refine ⟨1585946183225029146297139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2114594910966705528396185 1585946183225029146297139)
    ·
      refine ⟨2378919274837543719445709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1585946183225029146297139 2378919274837543719445709)
      ·
        refine ⟨892094728064078894792141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2378919274837543719445709 892094728064078894792141)
        ·
          refine ⟨334535523024029585547053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 892094728064078894792141 334535523024029585547053)
          ·
            refine ⟨125450821134011094580145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 334535523024029585547053 125450821134011094580145)
            ·
              refine ⟨94088115850508320935109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125450821134011094580145 94088115850508320935109)
              ·
                refine ⟨17641521721970310175333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94088115850508320935109 17641521721970310175333)
                ·
                  rfl

theorem cell19_57977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 4].length) (baseStart_57977 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_57977 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_57977 prefixEnd_57977 := by exact prefixLift 57977
  have htrace : WordTrace (prefixWord ++ tailWord_57977) baseStart_57977 baseEnd_57977 := by
    simpa [prefixWord, tailWord_57977, baseEnd_57977] using wordTrace_append hprefix tailTrace_57977
  have hstable : (prefixWord ++ tailWord_57977).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57977).length < 2 ^ (prefixWord ++ tailWord_57977).sum := by decide
  have hdescent : baseEnd_57977 < baseStart_57977 := by decide
  rcases family_descends (prefixWord ++ tailWord_57977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58017 : List Nat := [1, 2, 3, 3, 10]
def baseStart_58017 : Nat := 118140960795 + 58017 * 2 ^ 59
def prefixEnd_58017 : Nat := 4983230072969 + 3 ^ 40 * 58017 * 2
def baseEnd_58017 : Nat := 653840485750447010605

theorem tailTrace_58017 : CollatzResearch.WordTrace tailWord_58017 prefixEnd_58017 653840485750447010605 := by
  unfold tailWord_58017
  simp only [CollatzResearch.WordTrace]
  refine ⟨2116053830821792359852305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1410702553881194906568203 2116053830821792359852305)
  ·
    refine ⟨1587040373116344269889229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2116053830821792359852305 1587040373116344269889229)
    ·
      refine ⟨595140139918629101208461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1587040373116344269889229 595140139918629101208461)
      ·
        refine ⟨223177552469485912953173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 595140139918629101208461 223177552469485912953173)
        ·
          refine ⟨653840485750447010605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 223177552469485912953173 653840485750447010605)
          ·
            rfl

theorem cell19_58017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 10].length) (baseStart_58017 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_58017 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_58017 prefixEnd_58017 := by exact prefixLift 58017
  have htrace : WordTrace (prefixWord ++ tailWord_58017) baseStart_58017 baseEnd_58017 := by
    simpa [prefixWord, tailWord_58017, baseEnd_58017] using wordTrace_append hprefix tailTrace_58017
  have hstable : (prefixWord ++ tailWord_58017).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58017).length < 2 ^ (prefixWord ++ tailWord_58017).sum := by decide
  have hdescent : baseEnd_58017 < baseStart_58017 := by decide
  rcases family_descends (prefixWord ++ tailWord_58017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58030 : List Nat := [4, 1, 4, 1, 1, 3, 1, 4]
def baseStart_58030 : Nat := 118140960795 + 58030 * 2 ^ 59
def prefixEnd_58030 : Nat := 4983230072969 + 3 ^ 40 * 58030 * 2
def baseEnd_58030 : Nat := 17657648818081890997411

theorem tailTrace_58030 : CollatzResearch.WordTrace tailWord_58030 prefixEnd_58030 17657648818081890997411 := by
  unfold tailWord_58030
  simp only [CollatzResearch.WordTrace]
  refine ⟨264565997471836947509443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1411018653183130386717029 264565997471836947509443)
  ·
    refine ⟨396848996207755421264165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264565997471836947509443 396848996207755421264165)
    ·
      refine ⟨74409186788954141487031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 396848996207755421264165 74409186788954141487031)
      ·
        refine ⟨111613780183431212230547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74409186788954141487031 111613780183431212230547)
        ·
          refine ⟨167420670275146818345821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111613780183431212230547 167420670275146818345821)
          ·
            refine ⟨62782751353180056879683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167420670275146818345821 62782751353180056879683)
            ·
              refine ⟨94174127029770085319525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62782751353180056879683 94174127029770085319525)
              ·
                refine ⟨17657648818081890997411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94174127029770085319525 17657648818081890997411)
                ·
                  rfl

theorem cell19_58030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_58030 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_58030 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_58030 prefixEnd_58030 := by exact prefixLift 58030
  have htrace : WordTrace (prefixWord ++ tailWord_58030) baseStart_58030 baseEnd_58030 := by
    simpa [prefixWord, tailWord_58030, baseEnd_58030] using wordTrace_append hprefix tailTrace_58030
  have hstable : (prefixWord ++ tailWord_58030).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58030).length < 2 ^ (prefixWord ++ tailWord_58030).sum := by decide
  have hdescent : baseEnd_58030 < baseStart_58030 := by decide
  rcases family_descends (prefixWord ++ tailWord_58030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58074 : List Nat := [3, 1, 1, 2, 2, 2, 8]
def baseStart_58074 : Nat := 118140960795 + 58074 * 2 ^ 59
def prefixEnd_58074 : Nat := 4983230072969 + 3 ^ 40 * 58074 * 2
def baseEnd_58074 : Nat := 5890345783567608673171

theorem tailTrace_58074 : CollatzResearch.WordTrace tailWord_58074 prefixEnd_58074 5890345783567608673171 := by
  unfold tailWord_58074
  simp only [CollatzResearch.WordTrace]
  refine ⟨529533197903822773669319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1412088527743527396451517 529533197903822773669319)
  ·
    refine ⟨794299796855734160503979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 529533197903822773669319 794299796855734160503979)
    ·
      refine ⟨1191449695283601240755969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 794299796855734160503979 1191449695283601240755969)
      ·
        refine ⟨893587271462700930566977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1191449695283601240755969 893587271462700930566977)
        ·
          refine ⟨670190453597025697925233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 893587271462700930566977 670190453597025697925233)
          ·
            refine ⟨502642840197769273443925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 670190453597025697925233 502642840197769273443925)
            ·
              refine ⟨5890345783567608673171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 502642840197769273443925 5890345783567608673171)
              ·
                rfl

theorem cell19_58074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 8].length) (baseStart_58074 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_58074 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_58074 prefixEnd_58074 := by exact prefixLift 58074
  have htrace : WordTrace (prefixWord ++ tailWord_58074) baseStart_58074 baseEnd_58074 := by
    simpa [prefixWord, tailWord_58074, baseEnd_58074] using wordTrace_append hprefix tailTrace_58074
  have hstable : (prefixWord ++ tailWord_58074).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58074).length < 2 ^ (prefixWord ++ tailWord_58074).sum := by decide
  have hdescent : baseEnd_58074 < baseStart_58074 := by decide
  rcases family_descends (prefixWord ++ tailWord_58074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58108 : List Nat := [2, 2, 2, 1, 3, 4, 2, 3]
def baseStart_58108 : Nat := 118140960795 + 58108 * 2 ^ 59
def prefixEnd_58108 : Nat := 4983230072969 + 3 ^ 40 * 58108 * 2
def baseEnd_58108 : Nat := 17681383035000821263865

theorem tailTrace_58108 : CollatzResearch.WordTrace tailWord_58108 prefixEnd_58108 17681383035000821263865 := by
  unfold tailWord_58108
  simp only [CollatzResearch.WordTrace]
  refine ⟨1059686436746057450707489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1412915248994743267609985 1059686436746057450707489)
  ·
    refine ⟨794764827559543088030617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1059686436746057450707489 794764827559543088030617)
    ·
      refine ⟨596073620669657316022963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 794764827559543088030617 596073620669657316022963)
      ·
        refine ⟨894110431004485974034445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596073620669657316022963 894110431004485974034445)
        ·
          refine ⟨335291411626682240262917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 894110431004485974034445 335291411626682240262917)
          ·
            refine ⟨62867139680002920049297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 335291411626682240262917 62867139680002920049297)
            ·
              refine ⟨47150354760002190036973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62867139680002920049297 47150354760002190036973)
              ·
                refine ⟨17681383035000821263865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47150354760002190036973 17681383035000821263865)
                ·
                  rfl

theorem cell19_58108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 3].length) (baseStart_58108 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_58108 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_58108 prefixEnd_58108 := by exact prefixLift 58108
  have htrace : WordTrace (prefixWord ++ tailWord_58108) baseStart_58108 baseEnd_58108 := by
    simpa [prefixWord, tailWord_58108, baseEnd_58108] using wordTrace_append hprefix tailTrace_58108
  have hstable : (prefixWord ++ tailWord_58108).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58108).length < 2 ^ (prefixWord ++ tailWord_58108).sum := by decide
  have hdescent : baseEnd_58108 < baseStart_58108 := by decide
  rcases family_descends (prefixWord ++ tailWord_58108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58182 : List Nat := [6, 1, 1, 2, 3, 6]
def baseStart_58182 : Nat := 118140960795 + 58182 * 2 ^ 59
def prefixEnd_58182 : Nat := 4983230072969 + 3 ^ 40 * 58182 * 2
def baseEnd_58182 : Nat := 1967100012510063957691

theorem tailTrace_58182 : CollatzResearch.WordTrace tailWord_58182 prefixEnd_58182 1967100012510063957691 := by
  unfold tailWord_58182
  simp only [CollatzResearch.WordTrace]
  refine ⟨66314746100750798112775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1414714583482683693072533 66314746100750798112775)
  ·
    refine ⟨99472119151126197169163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66314746100750798112775 99472119151126197169163)
    ·
      refine ⟨149208178726689295753745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99472119151126197169163 149208178726689295753745)
      ·
        refine ⟨111906134045016971815309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149208178726689295753745 111906134045016971815309)
        ·
          refine ⟨41964800266881364430741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111906134045016971815309 41964800266881364430741)
          ·
            refine ⟨1967100012510063957691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41964800266881364430741 1967100012510063957691)
            ·
              rfl

theorem cell19_58182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 6].length) (baseStart_58182 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_58182 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_58182 prefixEnd_58182 := by exact prefixLift 58182
  have htrace : WordTrace (prefixWord ++ tailWord_58182) baseStart_58182 baseEnd_58182 := by
    simpa [prefixWord, tailWord_58182, baseEnd_58182] using wordTrace_append hprefix tailTrace_58182
  have hstable : (prefixWord ++ tailWord_58182).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58182).length < 2 ^ (prefixWord ++ tailWord_58182).sum := by decide
  have hdescent : baseEnd_58182 < baseStart_58182 := by decide
  rcases family_descends (prefixWord ++ tailWord_58182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58188 : List Nat := [2, 2, 1, 3, 3, 8]
def baseStart_58188 : Nat := 118140960795 + 58188 * 2 ^ 59
def prefixEnd_58188 : Nat := 4983230072969 + 3 ^ 40 * 58188 * 2
def baseEnd_58188 : Nat := 1967302869064926609541

theorem tailTrace_58188 : CollatzResearch.WordTrace tailWord_58188 prefixEnd_58188 1967302869064926609541 := by
  unfold tailWord_58188
  simp only [CollatzResearch.WordTrace]
  refine ⟨1061145356601144282163609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1414860475468192376218145 1061145356601144282163609)
  ·
    refine ⟨795859017450858211622707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1061145356601144282163609 795859017450858211622707)
    ·
      refine ⟨1193788526176287317434061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 795859017450858211622707 1193788526176287317434061)
      ·
        refine ⟨447670697316107744037773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1193788526176287317434061 447670697316107744037773)
        ·
          refine ⟨167876511493540404014165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 447670697316107744037773 167876511493540404014165)
          ·
            refine ⟨1967302869064926609541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 167876511493540404014165 1967302869064926609541)
            ·
              rfl

theorem cell19_58188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 8].length) (baseStart_58188 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_58188 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_58188 prefixEnd_58188 := by exact prefixLift 58188
  have htrace : WordTrace (prefixWord ++ tailWord_58188) baseStart_58188 baseEnd_58188 := by
    simpa [prefixWord, tailWord_58188, baseEnd_58188] using wordTrace_append hprefix tailTrace_58188
  have hstable : (prefixWord ++ tailWord_58188).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58188).length < 2 ^ (prefixWord ++ tailWord_58188).sum := by decide
  have hdescent : baseEnd_58188 < baseStart_58188 := by decide
  rcases family_descends (prefixWord ++ tailWord_58188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58226 : List Nat := [3, 2, 1, 2, 1, 1, 2, 7]
def baseStart_58226 : Nat := 118140960795 + 58226 * 2 ^ 59
def prefixEnd_58226 : Nat := 4983230072969 + 3 ^ 40 * 58226 * 2
def baseEnd_58226 : Nat := 17717288645211510641321

theorem tailTrace_58226 : CollatzResearch.WordTrace tailWord_58226 prefixEnd_58226 17717288645211510641321 := by
  unfold tailWord_58226
  simp only [CollatzResearch.WordTrace]
  refine ⟨530919171766155263552633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1415784458043080702807021 530919171766155263552633)
  ·
    refine ⟨398189378824616447664475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 530919171766155263552633 398189378824616447664475)
    ·
      refine ⟨597284068236924671496713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398189378824616447664475 597284068236924671496713)
      ·
        refine ⟨447963051177693503622535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 597284068236924671496713 447963051177693503622535)
        ·
          refine ⟨671944576766540255433803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447963051177693503622535 671944576766540255433803)
          ·
            refine ⟨1007916865149810383150705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671944576766540255433803 1007916865149810383150705)
            ·
              refine ⟨755937648862357787363029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1007916865149810383150705 755937648862357787363029)
              ·
                refine ⟨17717288645211510641321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 755937648862357787363029 17717288645211510641321)
                ·
                  rfl

theorem cell19_58226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_58226 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_58226 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_58226 prefixEnd_58226 := by exact prefixLift 58226
  have htrace : WordTrace (prefixWord ++ tailWord_58226) baseStart_58226 baseEnd_58226 := by
    simpa [prefixWord, tailWord_58226, baseEnd_58226] using wordTrace_append hprefix tailTrace_58226
  have hstable : (prefixWord ++ tailWord_58226).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58226).length < 2 ^ (prefixWord ++ tailWord_58226).sum := by decide
  have hdescent : baseEnd_58226 < baseStart_58226 := by decide
  rcases family_descends (prefixWord ++ tailWord_58226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58245 : List Nat := [1, 3, 1, 1, 3, 4, 6]
def baseStart_58245 : Nat := 118140960795 + 58245 * 2 ^ 59
def prefixEnd_58245 : Nat := 4983230072969 + 3 ^ 40 * 58245 * 2
def baseEnd_58245 : Nat := 5907690019008365406349

theorem tailTrace_58245 : CollatzResearch.WordTrace tailWord_58245 prefixEnd_58245 5907690019008365406349 := by
  unfold tailWord_58245
  simp only [CollatzResearch.WordTrace]
  refine ⟨2124369673995787299152189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1416246449330524866101459 2124369673995787299152189)
  ·
    refine ⟨796638627748420237182071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2124369673995787299152189 796638627748420237182071)
    ·
      refine ⟨1194957941622630355773107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 796638627748420237182071 1194957941622630355773107)
      ·
        refine ⟨1792436912433945533659661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1194957941622630355773107 1792436912433945533659661)
        ·
          refine ⟨672163842162729575122373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1792436912433945533659661 672163842162729575122373)
          ·
            refine ⟨126030720405511795335445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 672163842162729575122373 126030720405511795335445)
            ·
              refine ⟨5907690019008365406349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 126030720405511795335445 5907690019008365406349)
              ·
                rfl

theorem cell19_58245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 6].length) (baseStart_58245 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_58245 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_58245 prefixEnd_58245 := by exact prefixLift 58245
  have htrace : WordTrace (prefixWord ++ tailWord_58245) baseStart_58245 baseEnd_58245 := by
    simpa [prefixWord, tailWord_58245, baseEnd_58245] using wordTrace_append hprefix tailTrace_58245
  have hstable : (prefixWord ++ tailWord_58245).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58245).length < 2 ^ (prefixWord ++ tailWord_58245).sum := by decide
  have hdescent : baseEnd_58245 < baseStart_58245 := by decide
  rcases family_descends (prefixWord ++ tailWord_58245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58294 : List Nat := [5, 1, 4, 1, 1, 2, 5]
def baseStart_58294 : Nat := 118140960795 + 58294 * 2 ^ 59
def prefixEnd_58294 : Nat := 4983230072969 + 3 ^ 40 * 58294 * 2
def baseEnd_58294 : Nat := 5912660004602500376675

theorem tailTrace_58294 : CollatzResearch.WordTrace tailWord_58294 prefixEnd_58294 5912660004602500376675 := by
  unfold tailWord_58294
  simp only [CollatzResearch.WordTrace]
  refine ⟨132884803176141791730371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1417437900545512445123957 132884803176141791730371)
  ·
    refine ⟨199327204764212687595557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132884803176141791730371 199327204764212687595557)
    ·
      refine ⟨37373850893289878924167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199327204764212687595557 37373850893289878924167)
      ·
        refine ⟨56060776339934818386251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37373850893289878924167 56060776339934818386251)
        ·
          refine ⟨84091164509902227579377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56060776339934818386251 84091164509902227579377)
          ·
            refine ⟨63068373382426670684533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84091164509902227579377 63068373382426670684533)
            ·
              refine ⟨5912660004602500376675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63068373382426670684533 5912660004602500376675)
              ·
                rfl

theorem cell19_58294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 5].length) (baseStart_58294 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_58294 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_58294 prefixEnd_58294 := by exact prefixLift 58294
  have htrace : WordTrace (prefixWord ++ tailWord_58294) baseStart_58294 baseEnd_58294 := by
    simpa [prefixWord, tailWord_58294, baseEnd_58294] using wordTrace_append hprefix tailTrace_58294
  have hstable : (prefixWord ++ tailWord_58294).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58294).length < 2 ^ (prefixWord ++ tailWord_58294).sum := by decide
  have hdescent : baseEnd_58294 < baseStart_58294 := by decide
  rcases family_descends (prefixWord ++ tailWord_58294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58321 : List Nat := [1, 2, 2, 1, 2, 1, 6, 4]
def baseStart_58321 : Nat := 118140960795 + 58321 * 2 ^ 59
def prefixEnd_58321 : Nat := 4983230072969 + 3 ^ 40 * 58321 * 2
def baseEnd_58321 : Nat := 17746195704279438529951

theorem tailTrace_58321 : CollatzResearch.WordTrace tailWord_58321 prefixEnd_58321 17746195704279438529951 := by
  unfold tailWord_58321
  simp only [CollatzResearch.WordTrace]
  refine ⟨2127141621720452278918817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1418094414480301519279211 2127141621720452278918817)
  ·
    refine ⟨1595356216290339209189113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2127141621720452278918817 1595356216290339209189113)
    ·
      refine ⟨1196517162217754406891835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1595356216290339209189113 1196517162217754406891835)
      ·
        refine ⟨1794775743326631610337753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1196517162217754406891835 1794775743326631610337753)
        ·
          refine ⟨1346081807494973707753315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1794775743326631610337753 1346081807494973707753315)
          ·
            refine ⟨2019122711242460561629973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1346081807494973707753315 2019122711242460561629973)
            ·
              refine ⟨94646377089490338826405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2019122711242460561629973 94646377089490338826405)
              ·
                refine ⟨17746195704279438529951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94646377089490338826405 17746195704279438529951)
                ·
                  rfl

theorem cell19_58321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 4].length) (baseStart_58321 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_58321 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_58321 prefixEnd_58321 := by exact prefixLift 58321
  have htrace : WordTrace (prefixWord ++ tailWord_58321) baseStart_58321 baseEnd_58321 := by
    simpa [prefixWord, tailWord_58321, baseEnd_58321] using wordTrace_append hprefix tailTrace_58321
  have hstable : (prefixWord ++ tailWord_58321).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58321).length < 2 ^ (prefixWord ++ tailWord_58321).sum := by decide
  have hdescent : baseEnd_58321 < baseStart_58321 := by decide
  rcases family_descends (prefixWord ++ tailWord_58321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58357 : List Nat := [1, 3, 5, 2, 8]
def baseStart_58357 : Nat := 118140960795 + 58357 * 2 ^ 59
def prefixEnd_58357 : Nat := 4983230072969 + 3 ^ 40 * 58357 * 2
def baseEnd_58357 : Nat := 657672220675630434439

theorem tailTrace_58357 : CollatzResearch.WordTrace tailWord_58357 prefixEnd_58357 657672220675630434439 := by
  unfold tailWord_58357
  simp only [CollatzResearch.WordTrace]
  refine ⟨2128454649590030427229325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1418969766393353618152883 2128454649590030427229325)
  ·
    refine ⟨798170493596261410210997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2128454649590030427229325 798170493596261410210997)
    ·
      refine ⟨74828483774649507207281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 798170493596261410210997 74828483774649507207281)
      ·
        refine ⟨56121362830987130405461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74828483774649507207281 56121362830987130405461)
        ·
          refine ⟨657672220675630434439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 56121362830987130405461 657672220675630434439)
          ·
            rfl

theorem cell19_58357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 8].length) (baseStart_58357 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_58357 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_58357 prefixEnd_58357 := by exact prefixLift 58357
  have htrace : WordTrace (prefixWord ++ tailWord_58357) baseStart_58357 baseEnd_58357 := by
    simpa [prefixWord, tailWord_58357, baseEnd_58357] using wordTrace_append hprefix tailTrace_58357
  have hstable : (prefixWord ++ tailWord_58357).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58357).length < 2 ^ (prefixWord ++ tailWord_58357).sum := by decide
  have hdescent : baseEnd_58357 < baseStart_58357 := by decide
  rcases family_descends (prefixWord ++ tailWord_58357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58370 : List Nat := [3, 4, 1, 3, 2, 1, 1, 4]
def baseStart_58370 : Nat := 118140960795 + 58370 * 2 ^ 59
def prefixEnd_58370 : Nat := 4983230072969 + 3 ^ 40 * 58370 * 2
def baseEnd_58370 : Nat := 17761105661061843440929

theorem tailTrace_58370 : CollatzResearch.WordTrace tailWord_58370 prefixEnd_58370 17761105661061843440929 := by
  unfold tailWord_58370
  simp only [CollatzResearch.WordTrace]
  refine ⟨532232199635733411863141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1419285865695289098301709 532232199635733411863141)
  ·
    refine ⟨99793537431700014724339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 532232199635733411863141 99793537431700014724339)
    ·
      refine ⟨149690306147550022086509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99793537431700014724339 149690306147550022086509)
      ·
        refine ⟨56133864805331258282441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149690306147550022086509 56133864805331258282441)
        ·
          refine ⟨42100398603998443711831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56133864805331258282441 42100398603998443711831)
          ·
            refine ⟨63150597905997665567747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42100398603998443711831 63150597905997665567747)
            ·
              refine ⟨94725896858996498351621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63150597905997665567747 94725896858996498351621)
              ·
                refine ⟨17761105661061843440929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94725896858996498351621 17761105661061843440929)
                ·
                  rfl

theorem cell19_58370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 4].length) (baseStart_58370 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_58370 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_58370 prefixEnd_58370 := by exact prefixLift 58370
  have htrace : WordTrace (prefixWord ++ tailWord_58370) baseStart_58370 baseEnd_58370 := by
    simpa [prefixWord, tailWord_58370, baseEnd_58370] using wordTrace_append hprefix tailTrace_58370
  have hstable : (prefixWord ++ tailWord_58370).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58370).length < 2 ^ (prefixWord ++ tailWord_58370).sum := by decide
  have hdescent : baseEnd_58370 < baseStart_58370 := by decide
  rcases family_descends (prefixWord ++ tailWord_58370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58376 : List Nat := [2, 1, 3, 2, 1, 5, 1, 4]
def baseStart_58376 : Nat := 118140960795 + 58376 * 2 ^ 59
def prefixEnd_58376 : Nat := 4983230072969 + 3 ^ 40 * 58376 * 2
def baseEnd_58376 : Nat := 17762931370055607307579

theorem tailTrace_58376 : CollatzResearch.WordTrace tailWord_58376 prefixEnd_58376 17762931370055607307579 := by
  unfold tailWord_58376
  simp only [CollatzResearch.WordTrace]
  refine ⟨1064573818260598336085491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1419431757680797781447321 1064573818260598336085491)
  ·
    refine ⟨1596860727390897504128237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1064573818260598336085491 1596860727390897504128237)
    ·
      refine ⟨598822772771586564048089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1596860727390897504128237 598822772771586564048089)
      ·
        refine ⟨449117079578689923036067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 598822772771586564048089 449117079578689923036067)
        ·
          refine ⟨673675619368034884554101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449117079578689923036067 673675619368034884554101)
          ·
            refine ⟨63157089315753270426947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 673675619368034884554101 63157089315753270426947)
            ·
              refine ⟨94735633973629905640421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63157089315753270426947 94735633973629905640421)
              ·
                refine ⟨17762931370055607307579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94735633973629905640421 17762931370055607307579)
                ·
                  rfl

theorem cell19_58376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 4].length) (baseStart_58376 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_58376 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_58376 prefixEnd_58376 := by exact prefixLift 58376
  have htrace : WordTrace (prefixWord ++ tailWord_58376) baseStart_58376 baseEnd_58376 := by
    simpa [prefixWord, tailWord_58376, baseEnd_58376] using wordTrace_append hprefix tailTrace_58376
  have hstable : (prefixWord ++ tailWord_58376).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58376).length < 2 ^ (prefixWord ++ tailWord_58376).sum := by decide
  have hdescent : baseEnd_58376 < baseStart_58376 := by decide
  rcases family_descends (prefixWord ++ tailWord_58376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58450 : List Nat := [3, 2, 2, 1, 3, 3, 2, 3]
def baseStart_58450 : Nat := 118140960795 + 58450 * 2 ^ 59
def prefixEnd_58450 : Nat := 4983230072969 + 3 ^ 40 * 58450 * 2
def baseEnd_58450 : Nat := 17785448447645361662933

theorem tailTrace_58450 : CollatzResearch.WordTrace tailWord_58450 prefixEnd_58450 17785448447645361662933 := by
  unfold tailWord_58450
  simp only [CollatzResearch.WordTrace]
  refine ⟨532961659563276827591201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1421231092168738206909869 532961659563276827591201)
  ·
    refine ⟨399721244672457620693401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 532961659563276827591201 399721244672457620693401)
    ·
      refine ⟨299790933504343215520051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399721244672457620693401 299790933504343215520051)
      ·
        refine ⟨449686400256514823280077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299790933504343215520051 449686400256514823280077)
        ·
          refine ⟨168632400096193058730029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 449686400256514823280077 168632400096193058730029)
          ·
            refine ⟨63237150036072397023761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168632400096193058730029 63237150036072397023761)
            ·
              refine ⟨47427862527054297767821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63237150036072397023761 47427862527054297767821)
              ·
                refine ⟨17785448447645361662933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47427862527054297767821 17785448447645361662933)
                ·
                  rfl

theorem cell19_58450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_58450 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_58450 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_58450 prefixEnd_58450 := by exact prefixLift 58450
  have htrace : WordTrace (prefixWord ++ tailWord_58450) baseStart_58450 baseEnd_58450 := by
    simpa [prefixWord, tailWord_58450, baseEnd_58450] using wordTrace_append hprefix tailTrace_58450
  have hstable : (prefixWord ++ tailWord_58450).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58450).length < 2 ^ (prefixWord ++ tailWord_58450).sum := by decide
  have hdescent : baseEnd_58450 < baseStart_58450 := by decide
  rcases family_descends (prefixWord ++ tailWord_58450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58452 : List Nat := [2, 4, 1, 1, 1, 1, 6, 3]
def baseStart_58452 : Nat := 118140960795 + 58452 * 2 ^ 59
def prefixEnd_58452 : Nat := 4983230072969 + 3 ^ 40 * 58452 * 2
def baseEnd_58452 : Nat := 17786057017309949618483

theorem tailTrace_58452 : CollatzResearch.WordTrace tailWord_58452 prefixEnd_58452 17786057017309949618483 := by
  unfold tailWord_58452
  simp only [CollatzResearch.WordTrace]
  refine ⟨1065959792122930825968805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1421279722830574434625073 1065959792122930825968805)
  ·
    refine ⟨199867461023049529869151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1065959792122930825968805 199867461023049529869151)
    ·
      refine ⟨299801191534574294803727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199867461023049529869151 299801191534574294803727)
      ·
        refine ⟨449701787301861442205591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299801191534574294803727 449701787301861442205591)
        ·
          refine ⟨674552680952792163308387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449701787301861442205591 674552680952792163308387)
          ·
            refine ⟨1011829021429188244962581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674552680952792163308387 1011829021429188244962581)
            ·
              refine ⟨47429485379493198982621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1011829021429188244962581 47429485379493198982621)
              ·
                refine ⟨17786057017309949618483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47429485379493198982621 17786057017309949618483)
                ·
                  rfl

theorem cell19_58452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 3].length) (baseStart_58452 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_58452 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_58452 prefixEnd_58452 := by exact prefixLift 58452
  have htrace : WordTrace (prefixWord ++ tailWord_58452) baseStart_58452 baseEnd_58452 := by
    simpa [prefixWord, tailWord_58452, baseEnd_58452] using wordTrace_append hprefix tailTrace_58452
  have hstable : (prefixWord ++ tailWord_58452).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58452).length < 2 ^ (prefixWord ++ tailWord_58452).sum := by decide
  have hdescent : baseEnd_58452 < baseStart_58452 := by decide
  rcases family_descends (prefixWord ++ tailWord_58452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58473 : List Nat := [1, 2, 1, 1, 1, 8, 5]
def baseStart_58473 : Nat := 118140960795 + 58473 * 2 ^ 59
def prefixEnd_58473 : Nat := 4983230072969 + 3 ^ 40 * 58473 * 2
def baseEnd_58473 : Nat := 5930815666262707717253

theorem tailTrace_58473 : CollatzResearch.WordTrace tailWord_58473 prefixEnd_58473 5930815666262707717253 := by
  unfold tailWord_58473
  simp only [CollatzResearch.WordTrace]
  refine ⟨2132685517169782238452073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1421790344779854825634715 2132685517169782238452073)
  ·
    refine ⟨1599514137877336678839055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2132685517169782238452073 1599514137877336678839055)
    ·
      refine ⟨2399271206816005018258583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1599514137877336678839055 2399271206816005018258583)
      ·
        refine ⟨3598906810224007527387875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2399271206816005018258583 3598906810224007527387875)
        ·
          refine ⟨5398360215336011291081813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3598906810224007527387875 5398360215336011291081813)
          ·
            refine ⟨63262033773468882317365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 5398360215336011291081813 63262033773468882317365)
            ·
              refine ⟨5930815666262707717253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63262033773468882317365 5930815666262707717253)
              ·
                rfl

theorem cell19_58473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 5].length) (baseStart_58473 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_58473 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_58473 prefixEnd_58473 := by exact prefixLift 58473
  have htrace : WordTrace (prefixWord ++ tailWord_58473) baseStart_58473 baseEnd_58473 := by
    simpa [prefixWord, tailWord_58473, baseEnd_58473] using wordTrace_append hprefix tailTrace_58473
  have hstable : (prefixWord ++ tailWord_58473).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58473).length < 2 ^ (prefixWord ++ tailWord_58473).sum := by decide
  have hdescent : baseEnd_58473 < baseStart_58473 := by decide
  rcases family_descends (prefixWord ++ tailWord_58473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58492 : List Nat := [2, 2, 2, 1, 1, 3, 4, 4]
def baseStart_58492 : Nat := 118140960795 + 58492 * 2 ^ 59
def prefixEnd_58492 : Nat := 4983230072969 + 3 ^ 40 * 58492 * 2
def baseEnd_58492 : Nat := 17798228410601708729485

theorem tailTrace_58492 : CollatzResearch.WordTrace tailWord_58492 prefixEnd_58492 17798228410601708729485 := by
  unfold tailWord_58492
  simp only [CollatzResearch.WordTrace]
  refine ⟨1066689252050474241696865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1422252336067298988929153 1066689252050474241696865)
  ·
    refine ⟨800016939037855681272649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1066689252050474241696865 800016939037855681272649)
    ·
      refine ⟨600012704278391760954487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 800016939037855681272649 600012704278391760954487)
      ·
        refine ⟨900019056417587641431731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600012704278391760954487 900019056417587641431731)
        ·
          refine ⟨1350028584626381462147597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 900019056417587641431731 1350028584626381462147597)
          ·
            refine ⟨506260719234893048305349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1350028584626381462147597 506260719234893048305349)
            ·
              refine ⟨94923884856542446557253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 506260719234893048305349 94923884856542446557253)
              ·
                refine ⟨17798228410601708729485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94923884856542446557253 17798228410601708729485)
                ·
                  rfl

theorem cell19_58492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_58492 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_58492 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_58492 prefixEnd_58492 := by exact prefixLift 58492
  have htrace : WordTrace (prefixWord ++ tailWord_58492) baseStart_58492 baseEnd_58492 := by
    simpa [prefixWord, tailWord_58492, baseEnd_58492] using wordTrace_append hprefix tailTrace_58492
  have hstable : (prefixWord ++ tailWord_58492).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58492).length < 2 ^ (prefixWord ++ tailWord_58492).sum := by decide
  have hdescent : baseEnd_58492 < baseStart_58492 := by decide
  rcases family_descends (prefixWord ++ tailWord_58492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58530 : List Nat := [3, 3, 1, 3, 9]
def baseStart_58530 : Nat := 118140960795 + 58530 * 2 ^ 59
def prefixEnd_58530 : Nat := 4983230072969 + 3 ^ 40 * 58530 * 2
def baseEnd_58530 : Nat := 659621897564032588331

theorem tailTrace_58530 : CollatzResearch.WordTrace tailWord_58530 prefixEnd_58530 659621897564032588331 := by
  unfold tailWord_58530
  simp only [CollatzResearch.WordTrace]
  refine ⟨533691119490820243319261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1423176318642187315518029 533691119490820243319261)
  ·
    refine ⟨200134169809057591244723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 533691119490820243319261 200134169809057591244723)
    ·
      refine ⟨300201254713586386867085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200134169809057591244723 300201254713586386867085)
      ·
        refine ⟨112575470517594895075157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300201254713586386867085 112575470517594895075157)
        ·
          refine ⟨659621897564032588331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 112575470517594895075157 659621897564032588331)
          ·
            rfl

theorem cell19_58530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 9].length) (baseStart_58530 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_58530 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_58530 prefixEnd_58530 := by exact prefixLift 58530
  have htrace : WordTrace (prefixWord ++ tailWord_58530) baseStart_58530 baseEnd_58530 := by
    simpa [prefixWord, tailWord_58530, baseEnd_58530] using wordTrace_append hprefix tailTrace_58530
  have hstable : (prefixWord ++ tailWord_58530).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58530).length < 2 ^ (prefixWord ++ tailWord_58530).sum := by decide
  have hdescent : baseEnd_58530 < baseStart_58530 := by decide
  rcases family_descends (prefixWord ++ tailWord_58530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58564 : List Nat := [2, 3, 3, 1, 3, 1, 3, 3]
def baseStart_58564 : Nat := 118140960795 + 58564 * 2 ^ 59
def prefixEnd_58564 : Nat := 4983230072969 + 3 ^ 40 * 58564 * 2
def baseEnd_58564 : Nat := 17820136918526875129289

theorem tailTrace_58564 : CollatzResearch.WordTrace tailWord_58564 prefixEnd_58564 17820136918526875129289 := by
  unfold tailWord_58564
  simp only [CollatzResearch.WordTrace]
  refine ⟨1068002279920052390007373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1424003039893403186676497 1068002279920052390007373)
  ·
    refine ⟨400500854970019646252765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1068002279920052390007373 400500854970019646252765)
    ·
      refine ⟨150187820613757367344787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 400500854970019646252765 150187820613757367344787)
      ·
        refine ⟨225281730920636051017181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150187820613757367344787 225281730920636051017181)
        ·
          refine ⟨84480649095238519131443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225281730920636051017181 84480649095238519131443)
          ·
            refine ⟨126720973642857778697165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84480649095238519131443 126720973642857778697165)
            ·
              refine ⟨47520365116071667011437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126720973642857778697165 47520365116071667011437)
              ·
                refine ⟨17820136918526875129289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47520365116071667011437 17820136918526875129289)
                ·
                  rfl

theorem cell19_58564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 3].length) (baseStart_58564 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_58564 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_58564 prefixEnd_58564 := by exact prefixLift 58564
  have htrace : WordTrace (prefixWord ++ tailWord_58564) baseStart_58564 baseEnd_58564 := by
    simpa [prefixWord, tailWord_58564, baseEnd_58564] using wordTrace_append hprefix tailTrace_58564
  have hstable : (prefixWord ++ tailWord_58564).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58564).length < 2 ^ (prefixWord ++ tailWord_58564).sum := by decide
  have hdescent : baseEnd_58564 < baseStart_58564 := by decide
  rcases family_descends (prefixWord ++ tailWord_58564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58623 : List Nat := [1, 1, 2, 2, 1, 7, 2, 3]
def baseStart_58623 : Nat := 118140960795 + 58623 * 2 ^ 59
def prefixEnd_58623 : Nat := 4983230072969 + 3 ^ 40 * 58623 * 2
def baseEnd_58623 : Nat := 17838089723632219818017

theorem tailTrace_58623 : CollatzResearch.WordTrace tailWord_58623 prefixEnd_58623 17838089723632219818017 := by
  unfold tailWord_58623
  simp only [CollatzResearch.WordTrace]
  refine ⟨2138156466626357856412523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1425437644417571904275015 2138156466626357856412523)
  ·
    refine ⟨3207234699939536784618785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2138156466626357856412523 3207234699939536784618785)
    ·
      refine ⟨2405426024954652588464089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3207234699939536784618785 2405426024954652588464089)
      ·
        refine ⟨1804069518715989441348067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2405426024954652588464089 1804069518715989441348067)
        ·
          refine ⟨2706104278073984162022101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1804069518715989441348067 2706104278073984162022101)
          ·
            refine ⟨63424319017359003797393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 2706104278073984162022101 63424319017359003797393)
            ·
              refine ⟨47568239263019252848045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63424319017359003797393 47568239263019252848045)
              ·
                refine ⟨17838089723632219818017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47568239263019252848045 17838089723632219818017)
                ·
                  rfl

theorem cell19_58623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 3].length) (baseStart_58623 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_58623 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_58623 prefixEnd_58623 := by exact prefixLift 58623
  have htrace : WordTrace (prefixWord ++ tailWord_58623) baseStart_58623 baseEnd_58623 := by
    simpa [prefixWord, tailWord_58623, baseEnd_58623] using wordTrace_append hprefix tailTrace_58623
  have hstable : (prefixWord ++ tailWord_58623).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58623).length < 2 ^ (prefixWord ++ tailWord_58623).sum := by decide
  have hdescent : baseEnd_58623 < baseStart_58623 := by decide
  rcases family_descends (prefixWord ++ tailWord_58623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58625 : List Nat := [1, 2, 4, 1, 1, 4, 1, 5]
def baseStart_58625 : Nat := 118140960795 + 58625 * 2 ^ 59
def prefixEnd_58625 : Nat := 4983230072969 + 3 ^ 40 * 58625 * 2
def baseEnd_58625 : Nat := 17838698293296807773567

theorem tailTrace_58625 : CollatzResearch.WordTrace tailWord_58625 prefixEnd_58625 17838698293296807773567 := by
  unfold tailWord_58625
  simp only [CollatzResearch.WordTrace]
  refine ⟨2138229412619112197985329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1425486275079408131990219 2138229412619112197985329)
  ·
    refine ⟨1603672059464334148488997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2138229412619112197985329 1603672059464334148488997)
    ·
      refine ⟨300688511149562652841687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1603672059464334148488997 300688511149562652841687)
      ·
        refine ⟨451032766724343979262531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300688511149562652841687 451032766724343979262531)
        ·
          refine ⟨676549150086515968893797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451032766724343979262531 676549150086515968893797)
          ·
            refine ⟨126852965641221744167587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 676549150086515968893797 126852965641221744167587)
            ·
              refine ⟨190279448461832616251381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126852965641221744167587 190279448461832616251381)
              ·
                refine ⟨17838698293296807773567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190279448461832616251381 17838698293296807773567)
                ·
                  rfl

theorem cell19_58625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 5].length) (baseStart_58625 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_58625 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_58625 prefixEnd_58625 := by exact prefixLift 58625
  have htrace : WordTrace (prefixWord ++ tailWord_58625) baseStart_58625 baseEnd_58625 := by
    simpa [prefixWord, tailWord_58625, baseEnd_58625] using wordTrace_append hprefix tailTrace_58625
  have hstable : (prefixWord ++ tailWord_58625).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58625).length < 2 ^ (prefixWord ++ tailWord_58625).sum := by decide
  have hdescent : baseEnd_58625 < baseStart_58625 := by decide
  rcases family_descends (prefixWord ++ tailWord_58625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58710 : List Nat := [5, 2, 3, 1, 2, 1, 1, 4]
def baseStart_58710 : Nat := 118140960795 + 58710 * 2 ^ 59
def prefixEnd_58710 : Nat := 4983230072969 + 3 ^ 40 * 58710 * 2
def baseEnd_58710 : Nat := 17864562504041795884447

theorem tailTrace_58710 : CollatzResearch.WordTrace tailWord_58710 prefixEnd_58710 17864562504041795884447 := by
  unfold tailWord_58710
  simp only [CollatzResearch.WordTrace]
  refine ⟨133833101081948232176849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1427553078207447809886389 133833101081948232176849)
  ·
    refine ⟨100374825811461174132637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133833101081948232176849 100374825811461174132637)
    ·
      refine ⟨37640559679297940299739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100374825811461174132637 37640559679297940299739)
      ·
        refine ⟨56460839518946910449609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37640559679297940299739 56460839518946910449609)
        ·
          refine ⟨42345629639210182837207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56460839518946910449609 42345629639210182837207)
          ·
            refine ⟨63518444458815274255811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42345629639210182837207 63518444458815274255811)
            ·
              refine ⟨95277666688222911383717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63518444458815274255811 95277666688222911383717)
              ·
                refine ⟨17864562504041795884447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95277666688222911383717 17864562504041795884447)
                ·
                  rfl

theorem cell19_58710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_58710 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_58710 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_58710 prefixEnd_58710 := by exact prefixLift 58710
  have htrace : WordTrace (prefixWord ++ tailWord_58710) baseStart_58710 baseEnd_58710 := by
    simpa [prefixWord, tailWord_58710, baseEnd_58710] using wordTrace_append hprefix tailTrace_58710
  have hstable : (prefixWord ++ tailWord_58710).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58710).length < 2 ^ (prefixWord ++ tailWord_58710).sum := by decide
  have hdescent : baseEnd_58710 < baseStart_58710 := by decide
  rcases family_descends (prefixWord ++ tailWord_58710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58720 : List Nat := [2, 1, 1, 3, 4, 1, 3, 4]
def baseStart_58720 : Nat := 118140960795 + 58720 * 2 ^ 59
def prefixEnd_58720 : Nat := 4983230072969 + 3 ^ 40 * 58720 * 2
def baseEnd_58720 : Nat := 17867605352364735662197

theorem tailTrace_58720 : CollatzResearch.WordTrace tailWord_58720 prefixEnd_58720 17867605352364735662197 := by
  unfold tailWord_58720
  simp only [CollatzResearch.WordTrace]
  refine ⟨1070847173637471711346807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1427796231516628948462409 1070847173637471711346807)
  ·
    refine ⟨1606270760456207567020211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1070847173637471711346807 1606270760456207567020211)
    ·
      refine ⟨2409406140684311350530317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1606270760456207567020211 2409406140684311350530317)
      ·
        refine ⟨903527302756616756448869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2409406140684311350530317 903527302756616756448869)
        ·
          refine ⟨169411369266865641834163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 903527302756616756448869 169411369266865641834163)
          ·
            refine ⟨254117053900298462751245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169411369266865641834163 254117053900298462751245)
            ·
              refine ⟨95293895212611923531717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254117053900298462751245 95293895212611923531717)
              ·
                refine ⟨17867605352364735662197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95293895212611923531717 17867605352364735662197)
                ·
                  rfl

theorem cell19_58720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_58720 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_58720 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_58720 prefixEnd_58720 := by exact prefixLift 58720
  have htrace : WordTrace (prefixWord ++ tailWord_58720) baseStart_58720 baseEnd_58720 := by
    simpa [prefixWord, tailWord_58720, baseEnd_58720] using wordTrace_append hprefix tailTrace_58720
  have hstable : (prefixWord ++ tailWord_58720).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58720).length < 2 ^ (prefixWord ++ tailWord_58720).sum := by decide
  have hdescent : baseEnd_58720 < baseStart_58720 := by decide
  rcases family_descends (prefixWord ++ tailWord_58720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58796 : List Nat := [2, 2, 1, 1, 1, 1, 8, 3]
def baseStart_58796 : Nat := 118140960795 + 58796 * 2 ^ 59
def prefixEnd_58796 : Nat := 4983230072969 + 3 ^ 40 * 58796 * 2
def baseEnd_58796 : Nat := 17890730999619077973101

theorem tailTrace_58796 : CollatzResearch.WordTrace tailWord_58796 prefixEnd_58796 17890730999619077973101 := by
  unfold tailWord_58796
  simp only [CollatzResearch.WordTrace]
  refine ⟨1072233147499804201230121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1429644196666405601640161 1072233147499804201230121)
  ·
    refine ⟨804174860624853150922591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1072233147499804201230121 804174860624853150922591)
    ·
      refine ⟨1206262290937279726383887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 804174860624853150922591 1206262290937279726383887)
      ·
        refine ⟨1809393436405919589575831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1206262290937279726383887 1809393436405919589575831)
        ·
          refine ⟨2714090154608879384363747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1809393436405919589575831 2714090154608879384363747)
          ·
            refine ⟨4071135231913319076545621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2714090154608879384363747 4071135231913319076545621)
            ·
              refine ⟨47708615998984207928269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4071135231913319076545621 47708615998984207928269)
              ·
                refine ⟨17890730999619077973101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47708615998984207928269 17890730999619077973101)
                ·
                  rfl

theorem cell19_58796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 3].length) (baseStart_58796 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_58796 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_58796 prefixEnd_58796 := by exact prefixLift 58796
  have htrace : WordTrace (prefixWord ++ tailWord_58796) baseStart_58796 baseEnd_58796 := by
    simpa [prefixWord, tailWord_58796, baseEnd_58796] using wordTrace_append hprefix tailTrace_58796
  have hstable : (prefixWord ++ tailWord_58796).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58796).length < 2 ^ (prefixWord ++ tailWord_58796).sum := by decide
  have hdescent : baseEnd_58796 < baseStart_58796 := by decide
  rcases family_descends (prefixWord ++ tailWord_58796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58853 : List Nat := [1, 3, 1, 5, 1, 1, 2, 5]
def baseStart_58853 : Nat := 118140960795 + 58853 * 2 ^ 59
def prefixEnd_58853 : Nat := 4983230072969 + 3 ^ 40 * 58853 * 2
def baseEnd_58853 : Nat := 17908075235059834706279

theorem tailTrace_58853 : CollatzResearch.WordTrace tailWord_58853 prefixEnd_58853 17908075235059834706279 := by
  unfold tailWord_58853
  simp only [CollatzResearch.WordTrace]
  refine ⟨2146545255793107137285213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1431030170528738091523475 2146545255793107137285213)
  ·
    refine ⟨804954470922415176481955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2146545255793107137285213 804954470922415176481955)
    ·
      refine ⟨1207431706383622764722933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 804954470922415176481955 1207431706383622764722933)
      ·
        refine ⟨113196722473464634192775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1207431706383622764722933 113196722473464634192775)
        ·
          refine ⟨169795083710196951289163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113196722473464634192775 169795083710196951289163)
          ·
            refine ⟨254692625565295426933745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169795083710196951289163 254692625565295426933745)
            ·
              refine ⟨191019469173971570200309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254692625565295426933745 191019469173971570200309)
              ·
                refine ⟨17908075235059834706279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 191019469173971570200309 17908075235059834706279)
                ·
                  rfl

theorem cell19_58853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 5].length) (baseStart_58853 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_58853 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_58853 prefixEnd_58853 := by exact prefixLift 58853
  have htrace : WordTrace (prefixWord ++ tailWord_58853) baseStart_58853 baseEnd_58853 := by
    simpa [prefixWord, tailWord_58853, baseEnd_58853] using wordTrace_append hprefix tailTrace_58853
  have hstable : (prefixWord ++ tailWord_58853).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58853).length < 2 ^ (prefixWord ++ tailWord_58853).sum := by decide
  have hdescent : baseEnd_58853 < baseStart_58853 := by decide
  rcases family_descends (prefixWord ++ tailWord_58853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58931 : List Nat := [1, 1, 1, 2, 4, 4, 6]
def baseStart_58931 : Nat := 118140960795 + 58931 * 2 ^ 59
def prefixEnd_58931 : Nat := 4983230072969 + 3 ^ 40 * 58931 * 2
def baseEnd_58931 : Nat := 5977269817326254990911

theorem tailTrace_58931 : CollatzResearch.WordTrace tailWord_58931 prefixEnd_58931 5977269817326254990911 := by
  unfold tailWord_58931
  simp only [CollatzResearch.WordTrace]
  refine ⟨2149390149510526458624647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1432926766340350972416431 2149390149510526458624647)
  ·
    refine ⟨3224085224265789687936971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2149390149510526458624647 3224085224265789687936971)
    ·
      refine ⟨4836127836398684531905457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3224085224265789687936971 4836127836398684531905457)
      ·
        refine ⟨3627095877299013398929093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4836127836398684531905457 3627095877299013398929093)
        ·
          refine ⟨680080476993565012299205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3627095877299013398929093 680080476993565012299205)
          ·
            refine ⟨127515089436293439806101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 680080476993565012299205 127515089436293439806101)
            ·
              refine ⟨5977269817326254990911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 127515089436293439806101 5977269817326254990911)
              ·
                rfl

theorem cell19_58931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 6].length) (baseStart_58931 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_58931 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_58931 prefixEnd_58931 := by exact prefixLift 58931
  have htrace : WordTrace (prefixWord ++ tailWord_58931) baseStart_58931 baseEnd_58931 := by
    simpa [prefixWord, tailWord_58931, baseEnd_58931] using wordTrace_append hprefix tailTrace_58931
  have hstable : (prefixWord ++ tailWord_58931).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58931).length < 2 ^ (prefixWord ++ tailWord_58931).sum := by decide
  have hdescent : baseEnd_58931 < baseStart_58931 := by decide
  rcases family_descends (prefixWord ++ tailWord_58931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58967 : List Nat := [1, 1, 3, 2, 2, 3, 4, 3]
def baseStart_58967 : Nat := 118140960795 + 58967 * 2 ^ 59
def prefixEnd_58967 : Nat := 4983230072969 + 3 ^ 40 * 58967 * 2
def baseEnd_58967 : Nat := 17942763705941348172635

theorem tailTrace_58967 : CollatzResearch.WordTrace tailWord_58967 prefixEnd_58967 17942763705941348172635 := by
  unfold tailWord_58967
  simp only [CollatzResearch.WordTrace]
  refine ⟨2150703177380104606935155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1433802118253403071290103 2150703177380104606935155)
  ·
    refine ⟨3226054766070156910402733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2150703177380104606935155 3226054766070156910402733)
    ·
      refine ⟨1209770537276308841401025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3226054766070156910402733 1209770537276308841401025)
      ·
        refine ⟨907327902957231631050769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1209770537276308841401025 907327902957231631050769)
        ·
          refine ⟨680495927217923723288077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 907327902957231631050769 680495927217923723288077)
          ·
            refine ⟨255185972706721396233029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 680495927217923723288077 255185972706721396233029)
            ·
              refine ⟨47847369882510261793693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 255185972706721396233029 47847369882510261793693)
              ·
                refine ⟨17942763705941348172635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47847369882510261793693 17942763705941348172635)
                ·
                  rfl

theorem cell19_58967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 3].length) (baseStart_58967 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_58967 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_58967 prefixEnd_58967 := by exact prefixLift 58967
  have htrace : WordTrace (prefixWord ++ tailWord_58967) baseStart_58967 baseEnd_58967 := by
    simpa [prefixWord, tailWord_58967, baseEnd_58967] using wordTrace_append hprefix tailTrace_58967
  have hstable : (prefixWord ++ tailWord_58967).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58967).length < 2 ^ (prefixWord ++ tailWord_58967).sum := by decide
  have hdescent : baseEnd_58967 < baseStart_58967 := by decide
  rcases family_descends (prefixWord ++ tailWord_58967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58986 : List Nat := [3, 1, 3, 2, 1, 4, 5]
def baseStart_58986 : Nat := 118140960795 + 58986 * 2 ^ 59
def prefixEnd_58986 : Nat := 4983230072969 + 3 ^ 40 * 58986 * 2
def baseEnd_58986 : Nat := 5982848372584977916787

theorem tailTrace_58986 : CollatzResearch.WordTrace tailWord_58986 prefixEnd_58986 5982848372584977916787 := by
  unfold tailWord_58986
  simp only [CollatzResearch.WordTrace]
  refine ⟨537849041077817712969203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1434264109540847234584541 537849041077817712969203)
  ·
    refine ⟨806773561616726569453805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 537849041077817712969203 806773561616726569453805)
    ·
      refine ⟨302540085606272463545177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 806773561616726569453805 302540085606272463545177)
      ·
        refine ⟨226905064204704347658883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302540085606272463545177 226905064204704347658883)
        ·
          refine ⟨340357596307056521488325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226905064204704347658883 340357596307056521488325)
          ·
            refine ⟨63817049307573097779061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 340357596307056521488325 63817049307573097779061)
            ·
              refine ⟨5982848372584977916787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63817049307573097779061 5982848372584977916787)
              ·
                rfl

theorem cell19_58986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 5].length) (baseStart_58986 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_58986 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_58986 prefixEnd_58986 := by exact prefixLift 58986
  have htrace : WordTrace (prefixWord ++ tailWord_58986) baseStart_58986 baseEnd_58986 := by
    simpa [prefixWord, tailWord_58986, baseEnd_58986] using wordTrace_append hprefix tailTrace_58986
  have hstable : (prefixWord ++ tailWord_58986).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58986).length < 2 ^ (prefixWord ++ tailWord_58986).sum := by decide
  have hdescent : baseEnd_58986 < baseStart_58986 := by decide
  rcases family_descends (prefixWord ++ tailWord_58986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59005 : List Nat := [1, 4, 1, 1, 4, 2, 2, 4]
def baseStart_59005 : Nat := 118140960795 + 59005 * 2 ^ 59
def prefixEnd_59005 : Nat := 4983230072969 + 3 ^ 40 * 59005 * 2
def baseEnd_59005 : Nat := 17954326529568519328087

theorem tailTrace_59005 : CollatzResearch.WordTrace tailWord_59005 prefixEnd_59005 17954326529568519328087 := by
  unfold tailWord_59005
  simp only [CollatzResearch.WordTrace]
  refine ⟨2152089151242437096818469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1434726100828291397878979 2152089151242437096818469)
  ·
    refine ⟨403516715857956955653463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2152089151242437096818469 403516715857956955653463)
    ·
      refine ⟨605275073786935433480195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403516715857956955653463 605275073786935433480195)
      ·
        refine ⟨907912610680403150220293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605275073786935433480195 907912610680403150220293)
        ·
          refine ⟨170233614502575590666305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 907912610680403150220293 170233614502575590666305)
          ·
            refine ⟨127675210876931692999729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170233614502575590666305 127675210876931692999729)
            ·
              refine ⟨95756408157698769749797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127675210876931692999729 95756408157698769749797)
              ·
                refine ⟨17954326529568519328087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95756408157698769749797 17954326529568519328087)
                ·
                  rfl

theorem cell19_59005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 4].length) (baseStart_59005 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_59005 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_59005 prefixEnd_59005 := by exact prefixLift 59005
  have htrace : WordTrace (prefixWord ++ tailWord_59005) baseStart_59005 baseEnd_59005 := by
    simpa [prefixWord, tailWord_59005, baseEnd_59005] using wordTrace_append hprefix tailTrace_59005
  have hstable : (prefixWord ++ tailWord_59005).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59005).length < 2 ^ (prefixWord ++ tailWord_59005).sum := by decide
  have hdescent : baseEnd_59005 < baseStart_59005 := by decide
  rcases family_descends (prefixWord ++ tailWord_59005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59134 : List Nat := [4, 2, 2, 1, 3, 2, 2, 3]
def baseStart_59134 : Nat := 118140960795 + 59134 * 2 ^ 59
def prefixEnd_59134 : Nat := 4983230072969 + 3 ^ 40 * 59134 * 2
def baseEnd_59134 : Nat := 17993579272934442461069

theorem tailTrace_59134 : CollatzResearch.WordTrace tailWord_59134 prefixEnd_59134 17993579272934442461069 := by
  unfold tailWord_59134
  simp only [CollatzResearch.WordTrace]
  refine ⟨269599270971886516033057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1437862778516728085509637 269599270971886516033057)
  ·
    refine ⟨202199453228914887024793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 269599270971886516033057 202199453228914887024793)
    ·
      refine ⟨151649589921686165268595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202199453228914887024793 151649589921686165268595)
      ·
        refine ⟨227474384882529247902893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151649589921686165268595 227474384882529247902893)
        ·
          refine ⟨85302894330948467963585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227474384882529247902893 85302894330948467963585)
          ·
            refine ⟨63977170748211350972689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85302894330948467963585 63977170748211350972689)
            ·
              refine ⟨47982878061158513229517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63977170748211350972689 47982878061158513229517)
              ·
                refine ⟨17993579272934442461069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47982878061158513229517 17993579272934442461069)
                ·
                  rfl

theorem cell19_59134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_59134 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_59134 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_59134 prefixEnd_59134 := by exact prefixLift 59134
  have htrace : WordTrace (prefixWord ++ tailWord_59134) baseStart_59134 baseEnd_59134 := by
    simpa [prefixWord, tailWord_59134, baseEnd_59134] using wordTrace_append hprefix tailTrace_59134
  have hstable : (prefixWord ++ tailWord_59134).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59134).length < 2 ^ (prefixWord ++ tailWord_59134).sum := by decide
  have hdescent : baseEnd_59134 < baseStart_59134 := by decide
  rcases family_descends (prefixWord ++ tailWord_59134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59138 : List Nat := [3, 4, 1, 1, 1, 1, 3, 5]
def baseStart_59138 : Nat := 118140960795 + 59138 * 2 ^ 59
def prefixEnd_59138 : Nat := 4983230072969 + 3 ^ 40 * 59138 * 2
def baseEnd_59138 : Nat := 17994796412263618372169

theorem tailTrace_59138 : CollatzResearch.WordTrace tailWord_59138 prefixEnd_59138 17994796412263618372169 := by
  unfold tailWord_59138
  simp only [CollatzResearch.WordTrace]
  refine ⟨539235014940150202852517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1437960039840400540940045 539235014940150202852517)
  ·
    refine ⟨101106565301278163034847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 539235014940150202852517 101106565301278163034847)
    ·
      refine ⟨151659847951917244552271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101106565301278163034847 151659847951917244552271)
      ·
        refine ⟨227489771927875866828407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151659847951917244552271 227489771927875866828407)
        ·
          refine ⟨341234657891813800242611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227489771927875866828407 341234657891813800242611)
          ·
            refine ⟨511851986837720700363917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341234657891813800242611 511851986837720700363917)
            ·
              refine ⟨191944495064145262636469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 511851986837720700363917 191944495064145262636469)
              ·
                refine ⟨17994796412263618372169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 191944495064145262636469 17994796412263618372169)
                ·
                  rfl

theorem cell19_59138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_59138 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_59138 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_59138 prefixEnd_59138 := by exact prefixLift 59138
  have htrace : WordTrace (prefixWord ++ tailWord_59138) baseStart_59138 baseEnd_59138 := by
    simpa [prefixWord, tailWord_59138, baseEnd_59138] using wordTrace_append hprefix tailTrace_59138
  have hstable : (prefixWord ++ tailWord_59138).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59138).length < 2 ^ (prefixWord ++ tailWord_59138).sum := by decide
  have hdescent : baseEnd_59138 < baseStart_59138 := by decide
  rcases family_descends (prefixWord ++ tailWord_59138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59149 : List Nat := [1, 7, 2, 1, 2, 1, 5]
def baseStart_59149 : Nat := 118140960795 + 59149 * 2 ^ 59
def prefixEnd_59149 : Nat := 4983230072969 + 3 ^ 40 * 59149 * 2
def baseEnd_59149 : Nat := 5999381181806284042565

theorem tailTrace_59149 : CollatzResearch.WordTrace tailWord_59149 prefixEnd_59149 5999381181806284042565 := by
  unfold tailWord_59149
  simp only [CollatzResearch.WordTrace]
  refine ⟨2157341262720749690060501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1438227508480499793373667 2157341262720749690060501)
  ·
    refine ⟨50562685845017570860793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 2157341262720749690060501 50562685845017570860793)
    ·
      refine ⟨37922014383763178145595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50562685845017570860793 37922014383763178145595)
      ·
        refine ⟨56883021575644767218393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37922014383763178145595 56883021575644767218393)
        ·
          refine ⟨42662266181733575413795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56883021575644767218393 42662266181733575413795)
          ·
            refine ⟨63993399272600363120693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42662266181733575413795 63993399272600363120693)
            ·
              refine ⟨5999381181806284042565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63993399272600363120693 5999381181806284042565)
              ·
                rfl

theorem cell19_59149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 5].length) (baseStart_59149 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_59149 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_59149 prefixEnd_59149 := by exact prefixLift 59149
  have htrace : WordTrace (prefixWord ++ tailWord_59149) baseStart_59149 baseEnd_59149 := by
    simpa [prefixWord, tailWord_59149, baseEnd_59149] using wordTrace_append hprefix tailTrace_59149
  have hstable : (prefixWord ++ tailWord_59149).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59149).length < 2 ^ (prefixWord ++ tailWord_59149).sum := by decide
  have hdescent : baseEnd_59149 < baseStart_59149 := by decide
  rcases family_descends (prefixWord ++ tailWord_59149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59159 : List Nat := [1, 1, 3, 4, 2, 1, 7]
def baseStart_59159 : Nat := 118140960795 + 59159 * 2 ^ 59
def prefixEnd_59159 : Nat := 4983230072969 + 3 ^ 40 * 59159 * 2
def baseEnd_59159 : Nat := 6000395464580597301815

theorem tailTrace_59159 : CollatzResearch.WordTrace tailWord_59159 prefixEnd_59159 6000395464580597301815 := by
  unfold tailWord_59159
  simp only [CollatzResearch.WordTrace]
  refine ⟨2157705992684521397924531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1438470661789680931949687 2157705992684521397924531)
  ·
    refine ⟨3236558989026782096886797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2157705992684521397924531 3236558989026782096886797)
    ·
      refine ⟨1213709620885043286332549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3236558989026782096886797 1213709620885043286332549)
      ·
        refine ⟨227570553915945616187353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1213709620885043286332549 227570553915945616187353)
        ·
          refine ⟨170677915436959212140515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227570553915945616187353 170677915436959212140515)
          ·
            refine ⟨256016873155438818210773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170677915436959212140515 256016873155438818210773)
            ·
              refine ⟨6000395464580597301815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 256016873155438818210773 6000395464580597301815)
              ·
                rfl

theorem cell19_59159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 7].length) (baseStart_59159 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_59159 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_59159 prefixEnd_59159 := by exact prefixLift 59159
  have htrace : WordTrace (prefixWord ++ tailWord_59159) baseStart_59159 baseEnd_59159 := by
    simpa [prefixWord, tailWord_59159, baseEnd_59159] using wordTrace_append hprefix tailTrace_59159
  have hstable : (prefixWord ++ tailWord_59159).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59159).length < 2 ^ (prefixWord ++ tailWord_59159).sum := by decide
  have hdescent : baseEnd_59159 < baseStart_59159 := by decide
  rcases family_descends (prefixWord ++ tailWord_59159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59176 : List Nat := [2, 1, 5, 1, 1, 3, 2, 4]
def baseStart_59176 : Nat := 118140960795 + 59176 * 2 ^ 59
def prefixEnd_59176 : Nat := 4983230072969 + 3 ^ 40 * 59176 * 2
def baseEnd_59176 : Nat := 18006359235890789527621

theorem tailTrace_59176 : CollatzResearch.WordTrace tailWord_59176 prefixEnd_59176 18006359235890789527621 := by
  unfold tailWord_59176
  simp only [CollatzResearch.WordTrace]
  refine ⟨1079163016811466650646691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1438884022415288867528921 1079163016811466650646691)
  ·
    refine ⟨1618744525217199975970037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1079163016811466650646691 1618744525217199975970037)
    ·
      refine ⟨151757299239112497747191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1618744525217199975970037 151757299239112497747191)
      ·
        refine ⟨227635948858668746620787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151757299239112497747191 227635948858668746620787)
        ·
          refine ⟨341453923288003119931181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227635948858668746620787 341453923288003119931181)
          ·
            refine ⟨128045221233001169974193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 341453923288003119931181 128045221233001169974193)
            ·
              refine ⟨96033915924750877480645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128045221233001169974193 96033915924750877480645)
              ·
                refine ⟨18006359235890789527621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96033915924750877480645 18006359235890789527621)
                ·
                  rfl

theorem cell19_59176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_59176 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_59176 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_59176 prefixEnd_59176 := by exact prefixLift 59176
  have htrace : WordTrace (prefixWord ++ tailWord_59176) baseStart_59176 baseEnd_59176 := by
    simpa [prefixWord, tailWord_59176, baseEnd_59176] using wordTrace_append hprefix tailTrace_59176
  have hstable : (prefixWord ++ tailWord_59176).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59176).length < 2 ^ (prefixWord ++ tailWord_59176).sum := by decide
  have hdescent : baseEnd_59176 < baseStart_59176 := by decide
  rcases family_descends (prefixWord ++ tailWord_59176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59349 : List Nat := [1, 3, 2, 3, 2, 1, 1, 6]
def baseStart_59349 : Nat := 118140960795 + 59349 * 2 ^ 59
def prefixEnd_59349 : Nat := 4983230072969 + 3 ^ 40 * 59349 * 2
def baseEnd_59349 : Nat := 18059000511877647682705

theorem tailTrace_59349 : CollatzResearch.WordTrace tailWord_59349 prefixEnd_59349 18059000511877647682705 := by
  unfold tailWord_59349
  simp only [CollatzResearch.WordTrace]
  refine ⟨2164635861996183847341101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1443090574664122564894067 2164635861996183847341101)
  ·
    refine ⟨811738448248568942752913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2164635861996183847341101 811738448248568942752913)
    ·
      refine ⟨608803836186426707064685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 811738448248568942752913 608803836186426707064685)
      ·
        refine ⟨228301438569910015149257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 608803836186426707064685 228301438569910015149257)
        ·
          refine ⟨171226078927432511361943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228301438569910015149257 171226078927432511361943)
          ·
            refine ⟨256839118391148767042915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171226078927432511361943 256839118391148767042915)
            ·
              refine ⟨385258677586723150564373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256839118391148767042915 385258677586723150564373)
              ·
                refine ⟨18059000511877647682705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 385258677586723150564373 18059000511877647682705)
                ·
                  rfl

theorem cell19_59349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 6].length) (baseStart_59349 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_59349 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_59349 prefixEnd_59349 := by exact prefixLift 59349
  have htrace : WordTrace (prefixWord ++ tailWord_59349) baseStart_59349 baseEnd_59349 := by
    simpa [prefixWord, tailWord_59349, baseEnd_59349] using wordTrace_append hprefix tailTrace_59349
  have hstable : (prefixWord ++ tailWord_59349).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59349).length < 2 ^ (prefixWord ++ tailWord_59349).sum := by decide
  have hdescent : baseEnd_59349 < baseStart_59349 := by decide
  rcases family_descends (prefixWord ++ tailWord_59349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59402 : List Nat := [3, 1, 2, 2, 5, 1, 1, 4]
def baseStart_59402 : Nat := 118140960795 + 59402 * 2 ^ 59
def prefixEnd_59402 : Nat := 4983230072969 + 3 ^ 40 * 59402 * 2
def baseEnd_59402 : Nat := 18075127607989228504783

theorem tailTrace_59402 : CollatzResearch.WordTrace tailWord_59402 prefixEnd_59402 18075127607989228504783 := by
  unfold tailWord_59402
  simp only [CollatzResearch.WordTrace]
  refine ⟨541642232701043474755115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1444379287202782599346973 541642232701043474755115)
  ·
    refine ⟨812463349051565212132673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 541642232701043474755115 812463349051565212132673)
    ·
      refine ⟨609347511788673909099505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 812463349051565212132673 609347511788673909099505)
      ·
        refine ⟨457010633841505431824629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 609347511788673909099505 457010633841505431824629)
        ·
          refine ⟨42844746922641134233559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 457010633841505431824629 42844746922641134233559)
          ·
            refine ⟨64267120383961701350339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42844746922641134233559 64267120383961701350339)
            ·
              refine ⟨96400680575942552025509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64267120383961701350339 96400680575942552025509)
              ·
                refine ⟨18075127607989228504783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96400680575942552025509 18075127607989228504783)
                ·
                  rfl

theorem cell19_59402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 4].length) (baseStart_59402 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_59402 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_59402 prefixEnd_59402 := by exact prefixLift 59402
  have htrace : WordTrace (prefixWord ++ tailWord_59402) baseStart_59402 baseEnd_59402 := by
    simpa [prefixWord, tailWord_59402, baseEnd_59402] using wordTrace_append hprefix tailTrace_59402
  have hstable : (prefixWord ++ tailWord_59402).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59402).length < 2 ^ (prefixWord ++ tailWord_59402).sum := by decide
  have hdescent : baseEnd_59402 < baseStart_59402 := by decide
  rcases family_descends (prefixWord ++ tailWord_59402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59465 : List Nat := [1, 2, 1, 1, 2, 2, 4, 6]
def baseStart_59465 : Nat := 118140960795 + 59465 * 2 ^ 59
def prefixEnd_59465 : Nat := 4983230072969 + 3 ^ 40 * 59465 * 2
def baseEnd_59465 : Nat := 18094297552423749104611

theorem tailTrace_59465 : CollatzResearch.WordTrace tailWord_59465 prefixEnd_59465 18094297552423749104611 := by
  unfold tailWord_59465
  simp only [CollatzResearch.WordTrace]
  refine ⟨2168866729575935658563849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1445911153050623772375899 2168866729575935658563849)
  ·
    refine ⟨1626650047181951743922887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2168866729575935658563849 1626650047181951743922887)
    ·
      refine ⟨2439975070772927615884331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1626650047181951743922887 2439975070772927615884331)
      ·
        refine ⟨3659962606159391423826497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2439975070772927615884331 3659962606159391423826497)
        ·
          refine ⟨2744971954619543567869873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3659962606159391423826497 2744971954619543567869873)
          ·
            refine ⟨2058728965964657675902405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2744971954619543567869873 2058728965964657675902405)
            ·
              refine ⟨386011681118373314231701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2058728965964657675902405 386011681118373314231701)
              ·
                refine ⟨18094297552423749104611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 386011681118373314231701 18094297552423749104611)
                ·
                  rfl

theorem cell19_59465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 6].length) (baseStart_59465 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_59465 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_59465 prefixEnd_59465 := by exact prefixLift 59465
  have htrace : WordTrace (prefixWord ++ tailWord_59465) baseStart_59465 baseEnd_59465 := by
    simpa [prefixWord, tailWord_59465, baseEnd_59465] using wordTrace_append hprefix tailTrace_59465
  have hstable : (prefixWord ++ tailWord_59465).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59465).length < 2 ^ (prefixWord ++ tailWord_59465).sum := by decide
  have hdescent : baseEnd_59465 < baseStart_59465 := by decide
  rcases family_descends (prefixWord ++ tailWord_59465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59478 : List Nat := [5, 2, 2, 1, 1, 2, 1, 5]
def baseStart_59478 : Nat := 118140960795 + 59478 * 2 ^ 59
def prefixEnd_59478 : Nat := 4983230072969 + 3 ^ 40 * 59478 * 2
def baseEnd_59478 : Nat := 18098253255243570815687

theorem tailTrace_59478 : CollatzResearch.WordTrace tailWord_59478 prefixEnd_59478 18098253255243570815687 := by
  unfold tailWord_59478
  simp only [CollatzResearch.WordTrace]
  refine ⟨135583804908052429924193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1446227252352559252524725 135583804908052429924193)
  ·
    refine ⟨101687853681039322443145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135583804908052429924193 101687853681039322443145)
    ·
      refine ⟨76265890260779491832359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101687853681039322443145 76265890260779491832359)
      ·
        refine ⟨114398835391169237748539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76265890260779491832359 114398835391169237748539)
        ·
          refine ⟨171598253086753856622809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114398835391169237748539 171598253086753856622809)
          ·
            refine ⟨128698689815065392467107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171598253086753856622809 128698689815065392467107)
            ·
              refine ⟨193048034722598088700661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128698689815065392467107 193048034722598088700661)
              ·
                refine ⟨18098253255243570815687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 193048034722598088700661 18098253255243570815687)
                ·
                  rfl

theorem cell19_59478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_59478 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_59478 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_59478 prefixEnd_59478 := by exact prefixLift 59478
  have htrace : WordTrace (prefixWord ++ tailWord_59478) baseStart_59478 baseEnd_59478 := by
    simpa [prefixWord, tailWord_59478, baseEnd_59478] using wordTrace_append hprefix tailTrace_59478
  have hstable : (prefixWord ++ tailWord_59478).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59478).length < 2 ^ (prefixWord ++ tailWord_59478).sum := by decide
  have hdescent : baseEnd_59478 < baseStart_59478 := by decide
  rcases family_descends (prefixWord ++ tailWord_59478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59480 : List Nat := [2, 1, 2, 2, 1, 6, 2, 3]
def baseStart_59480 : Nat := 118140960795 + 59480 * 2 ^ 59
def prefixEnd_59480 : Nat := 4983230072969 + 3 ^ 40 * 59480 * 2
def baseEnd_59480 : Nat := 18098861824908158771237

theorem tailTrace_59480 : CollatzResearch.WordTrace tailWord_59480 prefixEnd_59480 18098861824908158771237 := by
  unfold tailWord_59480
  simp only [CollatzResearch.WordTrace]
  refine ⟨1084706912260796610179947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1446275883014395480239929 1084706912260796610179947)
  ·
    refine ⟨1627060368391194915269921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1084706912260796610179947 1627060368391194915269921)
    ·
      refine ⟨1220295276293396186452441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1627060368391194915269921 1220295276293396186452441)
      ·
        refine ⟨915221457220047139839331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1220295276293396186452441 915221457220047139839331)
        ·
          refine ⟨1372832185830070709758997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 915221457220047139839331 1372832185830070709758997)
          ·
            refine ⟨64351508710784564519953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1372832185830070709758997 64351508710784564519953)
            ·
              refine ⟨48263631533088423389965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64351508710784564519953 48263631533088423389965)
              ·
                refine ⟨18098861824908158771237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48263631533088423389965 18098861824908158771237)
                ·
                  rfl

theorem cell19_59480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 3].length) (baseStart_59480 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_59480 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_59480 prefixEnd_59480 := by exact prefixLift 59480
  have htrace : WordTrace (prefixWord ++ tailWord_59480) baseStart_59480 baseEnd_59480 := by
    simpa [prefixWord, tailWord_59480, baseEnd_59480] using wordTrace_append hprefix tailTrace_59480
  have hstable : (prefixWord ++ tailWord_59480).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59480).length < 2 ^ (prefixWord ++ tailWord_59480).sum := by decide
  have hdescent : baseEnd_59480 < baseStart_59480 := by decide
  rcases family_descends (prefixWord ++ tailWord_59480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59503 : List Nat := [1, 1, 2, 1, 3, 4, 7]
def baseStart_59503 : Nat := 118140960795 + 59503 * 2 ^ 59
def prefixEnd_59503 : Nat := 4983230072969 + 3 ^ 40 * 59503 * 2
def baseEnd_59503 : Nat := 6035286792016973420021

theorem tailTrace_59503 : CollatzResearch.WordTrace tailWord_59503 prefixEnd_59503 6035286792016973420021 := by
  unfold tailWord_59503
  simp only [CollatzResearch.WordTrace]
  refine ⟨2170252703438268148447163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1446835135625512098964775 2170252703438268148447163)
  ·
    refine ⟨3255379055157402222670745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2170252703438268148447163 3255379055157402222670745)
    ·
      refine ⟨2441534291368051667003059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3255379055157402222670745 2441534291368051667003059)
      ·
        refine ⟨3662301437052077500504589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2441534291368051667003059 3662301437052077500504589)
        ·
          refine ⟨1373363038894529062689221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3662301437052077500504589 1373363038894529062689221)
          ·
            refine ⟨257505569792724199254229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1373363038894529062689221 257505569792724199254229)
            ·
              refine ⟨6035286792016973420021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 257505569792724199254229 6035286792016973420021)
              ·
                rfl

theorem cell19_59503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 7].length) (baseStart_59503 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_59503 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_59503 prefixEnd_59503 := by exact prefixLift 59503
  have htrace : WordTrace (prefixWord ++ tailWord_59503) baseStart_59503 baseEnd_59503 := by
    simpa [prefixWord, tailWord_59503, baseEnd_59503] using wordTrace_append hprefix tailTrace_59503
  have hstable : (prefixWord ++ tailWord_59503).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59503).length < 2 ^ (prefixWord ++ tailWord_59503).sum := by decide
  have hdescent : baseEnd_59503 < baseStart_59503 := by decide
  rcases family_descends (prefixWord ++ tailWord_59503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59541 : List Nat := [1, 3, 2, 1, 1, 1, 3, 7]
def baseStart_59541 : Nat := 118140960795 + 59541 * 2 ^ 59
def prefixEnd_59541 : Nat := 4983230072969 + 3 ^ 40 * 59541 * 2
def baseEnd_59541 : Nat := 18117423199678091415515

theorem tailTrace_59541 : CollatzResearch.WordTrace tailWord_59541 prefixEnd_59541 18117423199678091415515 := by
  unfold tailWord_59541
  simp only [CollatzResearch.WordTrace]
  refine ⟨2171638677300600638330477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1447759118200400425553651 2171638677300600638330477)
  ·
    refine ⟨814364503987725239373929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2171638677300600638330477 814364503987725239373929)
    ·
      refine ⟨610773377990793929530447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 814364503987725239373929 610773377990793929530447)
      ·
        refine ⟨916160066986190894295671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610773377990793929530447 916160066986190894295671)
        ·
          refine ⟨1374240100479286341443507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 916160066986190894295671 1374240100479286341443507)
          ·
            refine ⟨2061360150718929512165261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1374240100479286341443507 2061360150718929512165261)
            ·
              refine ⟨773010056519598567061973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2061360150718929512165261 773010056519598567061973)
              ·
                refine ⟨18117423199678091415515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 773010056519598567061973 18117423199678091415515)
                ·
                  rfl

theorem cell19_59541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 7].length) (baseStart_59541 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_59541 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_59541 prefixEnd_59541 := by exact prefixLift 59541
  have htrace : WordTrace (prefixWord ++ tailWord_59541) baseStart_59541 baseEnd_59541 := by
    simpa [prefixWord, tailWord_59541, baseEnd_59541] using wordTrace_append hprefix tailTrace_59541
  have hstable : (prefixWord ++ tailWord_59541).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59541).length < 2 ^ (prefixWord ++ tailWord_59541).sum := by decide
  have hdescent : baseEnd_59541 < baseStart_59541 := by decide
  rcases family_descends (prefixWord ++ tailWord_59541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59573 : List Nat := [1, 3, 3, 4, 1, 2, 1, 4]
def baseStart_59573 : Nat := 118140960795 + 59573 * 2 ^ 59
def prefixEnd_59573 : Nat := 4983230072969 + 3 ^ 40 * 59573 * 2
def baseEnd_59573 : Nat := 18127160314311498704317

theorem tailTrace_59573 : CollatzResearch.WordTrace tailWord_59573 prefixEnd_59573 18127160314311498704317 := by
  unfold tailWord_59573
  simp only [CollatzResearch.WordTrace]
  refine ⟨2172805813184670103495373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1448537208789780068996915 2172805813184670103495373)
  ·
    refine ⟨814802179944251288810765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2172805813184670103495373 814802179944251288810765)
    ·
      refine ⟨305550817479094233304037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 814802179944251288810765 305550817479094233304037)
      ·
        refine ⟨57290778277330168744507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305550817479094233304037 57290778277330168744507)
        ·
          refine ⟨85936167415995253116761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57290778277330168744507 85936167415995253116761)
          ·
            refine ⟨64452125561996439837571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85936167415995253116761 64452125561996439837571)
            ·
              refine ⟨96678188342994659756357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64452125561996439837571 96678188342994659756357)
              ·
                refine ⟨18127160314311498704317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96678188342994659756357 18127160314311498704317)
                ·
                  rfl

theorem cell19_59573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 4].length) (baseStart_59573 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_59573 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_59573 prefixEnd_59573 := by exact prefixLift 59573
  have htrace : WordTrace (prefixWord ++ tailWord_59573) baseStart_59573 baseEnd_59573 := by
    simpa [prefixWord, tailWord_59573, baseEnd_59573] using wordTrace_append hprefix tailTrace_59573
  have hstable : (prefixWord ++ tailWord_59573).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59573).length < 2 ^ (prefixWord ++ tailWord_59573).sum := by decide
  have hdescent : baseEnd_59573 < baseStart_59573 := by decide
  rcases family_descends (prefixWord ++ tailWord_59573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59617 : List Nat := [1, 2, 3, 1, 3, 1, 8]
def baseStart_59617 : Nat := 118140960795 + 59617 * 2 ^ 59
def prefixEnd_59617 : Nat := 4983230072969 + 3 ^ 40 * 59617 * 2
def baseEnd_59617 : Nat := 6046849615644144575473

theorem tailTrace_59617 : CollatzResearch.WordTrace tailWord_59617 prefixEnd_59617 6046849615644144575473 := by
  unfold tailWord_59617
  simp only [CollatzResearch.WordTrace]
  refine ⟨2174410625025265618097105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1449607083350177078731403 2174410625025265618097105)
  ·
    refine ⟨1630807968768949213572829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2174410625025265618097105 1630807968768949213572829)
    ·
      refine ⟨611552988288355955089811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1630807968768949213572829 611552988288355955089811)
      ·
        refine ⟨917329482432533932634717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 611552988288355955089811 917329482432533932634717)
        ·
          refine ⟨343998555912200224738019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 917329482432533932634717 343998555912200224738019)
          ·
            refine ⟨515997833868300337107029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343998555912200224738019 515997833868300337107029)
            ·
              refine ⟨6046849615644144575473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 515997833868300337107029 6046849615644144575473)
              ·
                rfl

theorem cell19_59617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 8].length) (baseStart_59617 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_59617 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_59617 prefixEnd_59617 := by exact prefixLift 59617
  have htrace : WordTrace (prefixWord ++ tailWord_59617) baseStart_59617 baseEnd_59617 := by
    simpa [prefixWord, tailWord_59617, baseEnd_59617] using wordTrace_append hprefix tailTrace_59617
  have hstable : (prefixWord ++ tailWord_59617).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59617).length < 2 ^ (prefixWord ++ tailWord_59617).sum := by decide
  have hdescent : baseEnd_59617 < baseStart_59617 := by decide
  rcases family_descends (prefixWord ++ tailWord_59617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59710 : List Nat := [4, 2, 1, 2, 1, 2, 2, 5]
def baseStart_59710 : Nat := 118140960795 + 59710 * 2 ^ 59
def prefixEnd_59710 : Nat := 4983230072969 + 3 ^ 40 * 59710 * 2
def baseEnd_59710 : Nat := 18168847336335773659499

theorem tailTrace_59710 : CollatzResearch.WordTrace tailWord_59710 prefixEnd_59710 18168847336335773659499 := by
  unfold tailWord_59710
  simp only [CollatzResearch.WordTrace]
  refine ⟨272225326711042812654073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1451868409125561667488389 272225326711042812654073)
  ·
    refine ⟨204168995033282109490555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 272225326711042812654073 204168995033282109490555)
    ·
      refine ⟨306253492549923164235833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204168995033282109490555 306253492549923164235833)
      ·
        refine ⟨229690119412442373176875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306253492549923164235833 229690119412442373176875)
        ·
          refine ⟨344535179118663559765313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229690119412442373176875 344535179118663559765313)
          ·
            refine ⟨258401384338997669823985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344535179118663559765313 258401384338997669823985)
            ·
              refine ⟨193801038254248252367989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258401384338997669823985 193801038254248252367989)
              ·
                refine ⟨18168847336335773659499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 193801038254248252367989 18168847336335773659499)
                ·
                  rfl

theorem cell19_59710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_59710 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_59710 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_59710 prefixEnd_59710 := by exact prefixLift 59710
  have htrace : WordTrace (prefixWord ++ tailWord_59710) baseStart_59710 baseEnd_59710 := by
    simpa [prefixWord, tailWord_59710, baseEnd_59710] using wordTrace_append hprefix tailTrace_59710
  have hstable : (prefixWord ++ tailWord_59710).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59710).length < 2 ^ (prefixWord ++ tailWord_59710).sum := by decide
  have hdescent : baseEnd_59710 < baseStart_59710 := by decide
  rcases family_descends (prefixWord ++ tailWord_59710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59746 : List Nat := [3, 3, 2, 1, 1, 4, 1, 4]
def baseStart_59746 : Nat := 118140960795 + 59746 * 2 ^ 59
def prefixEnd_59746 : Nat := 4983230072969 + 3 ^ 40 * 59746 * 2
def baseEnd_59746 : Nat := 18179801590298356859401

theorem tailTrace_59746 : CollatzResearch.WordTrace tailWord_59746 prefixEnd_59746 18179801590298356859401 := by
  unfold tailWord_59746
  simp only [CollatzResearch.WordTrace]
  refine ⟨544778910389480162385773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1452743761038613766362061 544778910389480162385773)
  ·
    refine ⟨204292091396055060894665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 544778910389480162385773 204292091396055060894665)
    ·
      refine ⟨153219068547041295670999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204292091396055060894665 153219068547041295670999)
      ·
        refine ⟨229828602820561943506499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153219068547041295670999 229828602820561943506499)
        ·
          refine ⟨344742904230842915259749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229828602820561943506499 344742904230842915259749)
          ·
            refine ⟨64639294543283046611203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 344742904230842915259749 64639294543283046611203)
            ·
              refine ⟨96958941814924569916805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64639294543283046611203 96958941814924569916805)
              ·
                refine ⟨18179801590298356859401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96958941814924569916805 18179801590298356859401)
                ·
                  rfl

theorem cell19_59746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_59746 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_59746 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_59746 prefixEnd_59746 := by exact prefixLift 59746
  have htrace : WordTrace (prefixWord ++ tailWord_59746) baseStart_59746 baseEnd_59746 := by
    simpa [prefixWord, tailWord_59746, baseEnd_59746] using wordTrace_append hprefix tailTrace_59746
  have hstable : (prefixWord ++ tailWord_59746).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59746).length < 2 ^ (prefixWord ++ tailWord_59746).sum := by decide
  have hdescent : baseEnd_59746 < baseStart_59746 := by decide
  rcases family_descends (prefixWord ++ tailWord_59746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59765 : List Nat := [1, 3, 4, 1, 2, 2, 3, 3]
def baseStart_59765 : Nat := 118140960795 + 59765 * 2 ^ 59
def prefixEnd_59765 : Nat := 4983230072969 + 3 ^ 40 * 59765 * 2
def baseEnd_59765 : Nat := 18185583002111942437127

theorem tailTrace_59765 : CollatzResearch.WordTrace tailWord_59765 prefixEnd_59765 18185583002111942437127 := by
  unfold tailWord_59765
  simp only [CollatzResearch.WordTrace]
  refine ⟨2179808628489086894484749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1453205752326057929656499 2179808628489086894484749)
  ·
    refine ⟨817428235683407585431781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2179808628489086894484749 817428235683407585431781)
    ·
      refine ⟨153267794190638922268459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 817428235683407585431781 153267794190638922268459)
      ·
        refine ⟨229901691285958383402689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153267794190638922268459 229901691285958383402689)
        ·
          refine ⟨172426268464468787552017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229901691285958383402689 172426268464468787552017)
          ·
            refine ⟨129319701348351590664013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172426268464468787552017 129319701348351590664013)
            ·
              refine ⟨48494888005631846499005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129319701348351590664013 48494888005631846499005)
              ·
                refine ⟨18185583002111942437127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48494888005631846499005 18185583002111942437127)
                ·
                  rfl

theorem cell19_59765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 3].length) (baseStart_59765 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_59765 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_59765 prefixEnd_59765 := by exact prefixLift 59765
  have htrace : WordTrace (prefixWord ++ tailWord_59765) baseStart_59765 baseEnd_59765 := by
    simpa [prefixWord, tailWord_59765, baseEnd_59765] using wordTrace_append hprefix tailTrace_59765
  have hstable : (prefixWord ++ tailWord_59765).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59765).length < 2 ^ (prefixWord ++ tailWord_59765).sum := by decide
  have hdescent : baseEnd_59765 < baseStart_59765 := by decide
  rcases family_descends (prefixWord ++ tailWord_59765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59788 : List Nat := [2, 2, 1, 2, 1, 5, 6]
def baseStart_59788 : Nat := 118140960795 + 59788 * 2 ^ 59
def prefixEnd_59788 : Nat := 4983230072969 + 3 ^ 40 * 59788 * 2
def baseEnd_59788 : Nat := 6064193851084901308651

theorem tailTrace_59788 : CollatzResearch.WordTrace tailWord_59788 prefixEnd_59788 6064193851084901308651 := by
  unfold tailWord_59788
  simp only [CollatzResearch.WordTrace]
  refine ⟨1090323753702880911286009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1453765004937174548381345 1090323753702880911286009)
  ·
    refine ⟨817742815277160683464507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1090323753702880911286009 817742815277160683464507)
    ·
      refine ⟨1226614222915741025196761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 817742815277160683464507 1226614222915741025196761)
      ·
        refine ⟨919960667186805768897571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1226614222915741025196761 919960667186805768897571)
        ·
          refine ⟨1379941000780208653346357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 919960667186805768897571 1379941000780208653346357)
          ·
            refine ⟨129369468823144561251221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1379941000780208653346357 129369468823144561251221)
            ·
              refine ⟨6064193851084901308651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 129369468823144561251221 6064193851084901308651)
              ·
                rfl

theorem cell19_59788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 6].length) (baseStart_59788 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_59788 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_59788 prefixEnd_59788 := by exact prefixLift 59788
  have htrace : WordTrace (prefixWord ++ tailWord_59788) baseStart_59788 baseEnd_59788 := by
    simpa [prefixWord, tailWord_59788, baseEnd_59788] using wordTrace_append hprefix tailTrace_59788
  have hstable : (prefixWord ++ tailWord_59788).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59788).length < 2 ^ (prefixWord ++ tailWord_59788).sum := by decide
  have hdescent : baseEnd_59788 < baseStart_59788 := by decide
  rcases family_descends (prefixWord ++ tailWord_59788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59807 : List Nat := [1, 1, 2, 5, 1, 1, 2, 6]
def baseStart_59807 : Nat := 118140960795 + 59807 * 2 ^ 59
def prefixEnd_59807 : Nat := 4983230072969 + 3 ^ 40 * 59807 * 2
def baseEnd_59807 : Nat := 18198362965068289503679

theorem tailTrace_59807 : CollatzResearch.WordTrace tailWord_59807 prefixEnd_59807 18198362965068289503679 := by
  unfold tailWord_59807
  simp only [CollatzResearch.WordTrace]
  refine ⟨2181340494336928067513675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1454226996224618711675783 2181340494336928067513675)
  ·
    refine ⟨3272010741505392101270513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2181340494336928067513675 3272010741505392101270513)
    ·
      refine ⟨2454008056129044075952885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3272010741505392101270513 2454008056129044075952885)
      ·
        refine ⟨230063255262097882120583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2454008056129044075952885 230063255262097882120583)
        ·
          refine ⟨345094882893146823180875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230063255262097882120583 345094882893146823180875)
          ·
            refine ⟨517642324339720234771313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345094882893146823180875 517642324339720234771313)
            ·
              refine ⟨388231743254790176078485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 517642324339720234771313 388231743254790176078485)
              ·
                refine ⟨18198362965068289503679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 388231743254790176078485 18198362965068289503679)
                ·
                  rfl

theorem cell19_59807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 6].length) (baseStart_59807 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_59807 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_59807 prefixEnd_59807 := by exact prefixLift 59807
  have htrace : WordTrace (prefixWord ++ tailWord_59807) baseStart_59807 baseEnd_59807 := by
    simpa [prefixWord, tailWord_59807, baseEnd_59807] using wordTrace_append hprefix tailTrace_59807
  have hstable : (prefixWord ++ tailWord_59807).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59807).length < 2 ^ (prefixWord ++ tailWord_59807).sum := by decide
  have hdescent : baseEnd_59807 < baseStart_59807 := by decide
  rcases family_descends (prefixWord ++ tailWord_59807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59826 : List Nat := [3, 2, 1, 1, 1, 1, 5, 5]
def baseStart_59826 : Nat := 118140960795 + 59826 * 2 ^ 59
def prefixEnd_59826 : Nat := 4983230072969 + 3 ^ 40 * 59826 * 2
def baseEnd_59826 : Nat := 18204144376881875081405

theorem tailTrace_59826 : CollatzResearch.WordTrace tailWord_59826 prefixEnd_59826 18204144376881875081405 := by
  unfold tailWord_59826
  simp only [CollatzResearch.WordTrace]
  refine ⟨545508370317023578113833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1454688987512062874970221 545508370317023578113833)
  ·
    refine ⟨409131277737767683585375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 545508370317023578113833 409131277737767683585375)
    ·
      refine ⟨613696916606651525378063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409131277737767683585375 613696916606651525378063)
      ·
        refine ⟨920545374909977288067095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613696916606651525378063 920545374909977288067095)
        ·
          refine ⟨1380818062364965932100643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 920545374909977288067095 1380818062364965932100643)
          ·
            refine ⟨2071227093547448898150965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1380818062364965932100643 2071227093547448898150965)
            ·
              refine ⟨194177540020073334201653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2071227093547448898150965 194177540020073334201653)
              ·
                refine ⟨18204144376881875081405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 194177540020073334201653 18204144376881875081405)
                ·
                  rfl

theorem cell19_59826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_59826 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_59826 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_59826 prefixEnd_59826 := by exact prefixLift 59826
  have htrace : WordTrace (prefixWord ++ tailWord_59826) baseStart_59826 baseEnd_59826 := by
    simpa [prefixWord, tailWord_59826, baseEnd_59826] using wordTrace_append hprefix tailTrace_59826
  have hstable : (prefixWord ++ tailWord_59826).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59826).length < 2 ^ (prefixWord ++ tailWord_59826).sum := by decide
  have hdescent : baseEnd_59826 < baseStart_59826 := by decide
  rcases family_descends (prefixWord ++ tailWord_59826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59902 : List Nat := [4, 2, 2, 11]
def baseStart_59902 : Nat := 118140960795 + 59902 * 2 ^ 59
def prefixEnd_59902 : Nat := 4983230072969 + 3 ^ 40 * 59902 * 2
def baseEnd_59902 : Nat := 225028024989336017189

theorem tailTrace_59902 : CollatzResearch.WordTrace tailWord_59902 prefixEnd_59902 225028024989336017189 := by
  unfold tailWord_59902
  simp only [CollatzResearch.WordTrace]
  refine ⟨273100678624094911527745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1456536952661839528147973 273100678624094911527745)
  ·
    refine ⟨204825508968071183645809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273100678624094911527745 204825508968071183645809)
    ·
      refine ⟨153619131726053387734357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204825508968071183645809 153619131726053387734357)
      ·
        refine ⟨225028024989336017189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 153619131726053387734357 225028024989336017189)
        ·
          rfl

theorem cell19_59902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 11].length) (baseStart_59902 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_59902 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_59902 prefixEnd_59902 := by exact prefixLift 59902
  have htrace : WordTrace (prefixWord ++ tailWord_59902) baseStart_59902 baseEnd_59902 := by
    simpa [prefixWord, tailWord_59902, baseEnd_59902] using wordTrace_append hprefix tailTrace_59902
  have hstable : (prefixWord ++ tailWord_59902).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59902).length < 2 ^ (prefixWord ++ tailWord_59902).sum := by decide
  have hdescent : baseEnd_59902 < baseStart_59902 := by decide
  rcases family_descends (prefixWord ++ tailWord_59902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59936 : List Nat := [2, 1, 1, 6, 2, 1, 3, 3]
def baseStart_59936 : Nat := 118140960795 + 59936 * 2 ^ 59
def prefixEnd_59936 : Nat := 4983230072969 + 3 ^ 40 * 59936 * 2
def baseEnd_59936 : Nat := 18237615708434212636661

theorem tailTrace_59936 : CollatzResearch.WordTrace tailWord_59936 prefixEnd_59936 18237615708434212636661 := by
  unfold tailWord_59936
  simp only [CollatzResearch.WordTrace]
  refine ⟨1093022755434791549479831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1457363673913055399306441 1093022755434791549479831)
  ·
    refine ⟨1639534133152187324219747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1093022755434791549479831 1639534133152187324219747)
    ·
      refine ⟨2459301199728280986329621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1639534133152187324219747 2459301199728280986329621)
      ·
        refine ⟨115279743737263171234201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2459301199728280986329621 115279743737263171234201)
        ·
          refine ⟨86459807802947378425651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115279743737263171234201 86459807802947378425651)
          ·
            refine ⟨129689711704421067638477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86459807802947378425651 129689711704421067638477)
            ·
              refine ⟨48633641889157900364429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129689711704421067638477 48633641889157900364429)
              ·
                refine ⟨18237615708434212636661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48633641889157900364429 18237615708434212636661)
                ·
                  rfl

theorem cell19_59936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 3].length) (baseStart_59936 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_59936 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_59936 prefixEnd_59936 := by exact prefixLift 59936
  have htrace : WordTrace (prefixWord ++ tailWord_59936) baseStart_59936 baseEnd_59936 := by
    simpa [prefixWord, tailWord_59936, baseEnd_59936] using wordTrace_append hprefix tailTrace_59936
  have hstable : (prefixWord ++ tailWord_59936).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59936).length < 2 ^ (prefixWord ++ tailWord_59936).sum := by decide
  have hdescent : baseEnd_59936 < baseStart_59936 := by decide
  rcases family_descends (prefixWord ++ tailWord_59936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60014 : List Nat := [4, 1, 2, 2, 2, 3, 5]
def baseStart_60014 : Nat := 118140960795 + 60014 * 2 ^ 59
def prefixEnd_60014 : Nat := 4983230072969 + 3 ^ 40 * 60014 * 2
def baseEnd_60014 : Nat := 6087116641784380967705

theorem tailTrace_60014 : CollatzResearch.WordTrace tailWord_60014 prefixEnd_60014 6087116641784380967705 := by
  unfold tailWord_60014
  simp only [CollatzResearch.WordTrace]
  refine ⟨273611300573375302537387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1459260269724668280199397 273611300573375302537387)
  ·
    refine ⟨410416950860062953806081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273611300573375302537387 410416950860062953806081)
    ·
      refine ⟨307812713145047215354561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 410416950860062953806081 307812713145047215354561)
      ·
        refine ⟨230859534858785411515921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307812713145047215354561 230859534858785411515921)
        ·
          refine ⟨173144651144089058636941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230859534858785411515921 173144651144089058636941)
          ·
            refine ⟨64929244179033396988853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173144651144089058636941 64929244179033396988853)
            ·
              refine ⟨6087116641784380967705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64929244179033396988853 6087116641784380967705)
              ·
                rfl

theorem cell19_60014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 5].length) (baseStart_60014 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_60014 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_60014 prefixEnd_60014 := by exact prefixLift 60014
  have htrace : WordTrace (prefixWord ++ tailWord_60014) baseStart_60014 baseEnd_60014 := by
    simpa [prefixWord, tailWord_60014, baseEnd_60014] using wordTrace_append hprefix tailTrace_60014
  have hstable : (prefixWord ++ tailWord_60014).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60014).length < 2 ^ (prefixWord ++ tailWord_60014).sum := by decide
  have hdescent : baseEnd_60014 < baseStart_60014 := by decide
  rcases family_descends (prefixWord ++ tailWord_60014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60052 : List Nat := [2, 4, 2, 2, 1, 1, 2, 5]
def baseStart_60052 : Nat := 118140960795 + 60052 * 2 ^ 59
def prefixEnd_60052 : Nat := 4983230072969 + 3 ^ 40 * 60052 * 2
def baseEnd_60052 : Nat := 18272912748980314058567

theorem tailTrace_60052 : CollatzResearch.WordTrace tailWord_60052 prefixEnd_60052 18272912748980314058567 := by
  unfold tailWord_60052
  simp only [CollatzResearch.WordTrace]
  refine ⟨1095138189224667455091205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1460184252299556606788273 1095138189224667455091205)
  ·
    refine ⟨205338410479625147829601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1095138189224667455091205 205338410479625147829601)
    ·
      refine ⟨154003807859718860872201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205338410479625147829601 154003807859718860872201)
      ·
        refine ⟨115502855894789145654151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154003807859718860872201 115502855894789145654151)
        ·
          refine ⟨173254283842183718481227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115502855894789145654151 173254283842183718481227)
          ·
            refine ⟨259881425763275577721841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173254283842183718481227 259881425763275577721841)
            ·
              refine ⟨194911069322456683291381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259881425763275577721841 194911069322456683291381)
              ·
                refine ⟨18272912748980314058567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 194911069322456683291381 18272912748980314058567)
                ·
                  rfl

theorem cell19_60052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_60052 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_60052 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_60052 prefixEnd_60052 := by exact prefixLift 60052
  have htrace : WordTrace (prefixWord ++ tailWord_60052) baseStart_60052 baseEnd_60052 := by
    simpa [prefixWord, tailWord_60052, baseEnd_60052] using wordTrace_append hprefix tailTrace_60052
  have hstable : (prefixWord ++ tailWord_60052).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60052).length < 2 ^ (prefixWord ++ tailWord_60052).sum := by decide
  have hdescent : baseEnd_60052 < baseStart_60052 := by decide
  rcases family_descends (prefixWord ++ tailWord_60052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60071 : List Nat := [1, 1, 6, 3, 1, 7]
def baseStart_60071 : Nat := 118140960795 + 60071 * 2 ^ 59
def prefixEnd_60071 : Nat := 4983230072969 + 3 ^ 40 * 60071 * 2
def baseEnd_60071 : Nat := 2030966017865988848477

theorem tailTrace_60071 : CollatzResearch.WordTrace tailWord_60071 prefixEnd_60071 2030966017865988848477 := by
  unfold tailWord_60071
  simp only [CollatzResearch.WordTrace]
  refine ⟨2190969365380501155124067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1460646243587000770082711 2190969365380501155124067)
  ·
    refine ⟨3286454048070751732686101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2190969365380501155124067 3286454048070751732686101)
    ·
      refine ⟨154052533503316487469661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3286454048070751732686101 154052533503316487469661)
      ·
        refine ⟨57769700063743682801123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154052533503316487469661 57769700063743682801123)
        ·
          refine ⟨86654550095615524201685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57769700063743682801123 86654550095615524201685)
          ·
            refine ⟨2030966017865988848477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 86654550095615524201685 2030966017865988848477)
            ·
              rfl

theorem cell19_60071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 7].length) (baseStart_60071 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_60071 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_60071 prefixEnd_60071 := by exact prefixLift 60071
  have htrace : WordTrace (prefixWord ++ tailWord_60071) baseStart_60071 baseEnd_60071 := by
    simpa [prefixWord, tailWord_60071, baseEnd_60071] using wordTrace_append hprefix tailTrace_60071
  have hstable : (prefixWord ++ tailWord_60071).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60071).length < 2 ^ (prefixWord ++ tailWord_60071).sum := by decide
  have hdescent : baseEnd_60071 < baseStart_60071 := by decide
  rcases family_descends (prefixWord ++ tailWord_60071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60086 : List Nat := [5, 1, 3, 1, 2, 2, 1, 4]
def baseStart_60086 : Nat := 118140960795 + 60086 * 2 ^ 59
def prefixEnd_60086 : Nat := 4983230072969 + 3 ^ 40 * 60086 * 2
def baseEnd_60086 : Nat := 18283258433278309302919

theorem tailTrace_60086 : CollatzResearch.WordTrace tailWord_60086 prefixEnd_60086 18283258433278309302919 := by
  unfold tailWord_60086
  simp only [CollatzResearch.WordTrace]
  refine ⟨136969778770384919807507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1461010973550772477946741 136969778770384919807507)
  ·
    refine ⟨205454668155577379711261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136969778770384919807507 205454668155577379711261)
    ·
      refine ⟨77045500558341517391723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205454668155577379711261 77045500558341517391723)
      ·
        refine ⟨115568250837512276087585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77045500558341517391723 115568250837512276087585)
        ·
          refine ⟨86676188128134207065689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115568250837512276087585 86676188128134207065689)
          ·
            refine ⟨65007141096100655299267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86676188128134207065689 65007141096100655299267)
            ·
              refine ⟨97510711644150982948901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65007141096100655299267 97510711644150982948901)
              ·
                refine ⟨18283258433278309302919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97510711644150982948901 18283258433278309302919)
                ·
                  rfl

theorem cell19_60086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_60086 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_60086 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_60086 prefixEnd_60086 := by exact prefixLift 60086
  have htrace : WordTrace (prefixWord ++ tailWord_60086) baseStart_60086 baseEnd_60086 := by
    simpa [prefixWord, tailWord_60086, baseEnd_60086] using wordTrace_append hprefix tailTrace_60086
  have hstable : (prefixWord ++ tailWord_60086).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60086).length < 2 ^ (prefixWord ++ tailWord_60086).sum := by decide
  have hdescent : baseEnd_60086 < baseStart_60086 := by decide
  rcases family_descends (prefixWord ++ tailWord_60086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60151 : List Nat := [1, 1, 3, 1, 1, 1, 3, 8]
def baseStart_60151 : Nat := 118140960795 + 60151 * 2 ^ 59
def prefixEnd_60151 : Nat := 4983230072969 + 3 ^ 40 * 60151 * 2
def baseEnd_60151 : Nat := 18303036947377417858297

theorem tailTrace_60151 : CollatzResearch.WordTrace tailWord_60151 prefixEnd_60151 18303036947377417858297 := by
  unfold tailWord_60151
  simp only [CollatzResearch.WordTrace]
  refine ⟨2193887205090674818036307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1462591470060449878690871 2193887205090674818036307)
  ·
    refine ⟨3290830807636012227054461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2193887205090674818036307 3290830807636012227054461)
    ·
      refine ⟨1234061552863504585145423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3290830807636012227054461 1234061552863504585145423)
      ·
        refine ⟨1851092329295256877718135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1234061552863504585145423 1851092329295256877718135)
        ·
          refine ⟨2776638493942885316577203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1851092329295256877718135 2776638493942885316577203)
          ·
            refine ⟨4164957740914327974865805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2776638493942885316577203 4164957740914327974865805)
            ·
              refine ⟨1561859152842872990574677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4164957740914327974865805 1561859152842872990574677)
              ·
                refine ⟨18303036947377417858297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1561859152842872990574677 18303036947377417858297)
                ·
                  rfl

theorem cell19_60151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 8].length) (baseStart_60151 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_60151 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_60151 prefixEnd_60151 := by exact prefixLift 60151
  have htrace : WordTrace (prefixWord ++ tailWord_60151) baseStart_60151 baseEnd_60151 := by
    simpa [prefixWord, tailWord_60151, baseEnd_60151] using wordTrace_append hprefix tailTrace_60151
  have hstable : (prefixWord ++ tailWord_60151).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60151).length < 2 ^ (prefixWord ++ tailWord_60151).sum := by decide
  have hdescent : baseEnd_60151 < baseStart_60151 := by decide
  rcases family_descends (prefixWord ++ tailWord_60151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60168 : List Nat := [2, 1, 3, 2, 2, 3, 1, 5]
def baseStart_60168 : Nat := 118140960795 + 60168 * 2 ^ 59
def prefixEnd_60168 : Nat := 4983230072969 + 3 ^ 40 * 60168 * 2
def baseEnd_60168 : Nat := 18308209789526415480473

theorem tailTrace_60168 : CollatzResearch.WordTrace tailWord_60168 prefixEnd_60168 18308209789526415480473 := by
  unfold tailWord_60168
  simp only [CollatzResearch.WordTrace]
  refine ⟨1097253623014543360702579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1463004830686057814270105 1097253623014543360702579)
  ·
    refine ⟨1645880434521815041053869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1097253623014543360702579 1645880434521815041053869)
    ·
      refine ⟨617205162945680640395201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1645880434521815041053869 617205162945680640395201)
      ·
        refine ⟨462903872209260480296401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 617205162945680640395201 462903872209260480296401)
        ·
          refine ⟨347177904156945360222301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 462903872209260480296401 347177904156945360222301)
          ·
            refine ⟨130191714058854510083363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 347177904156945360222301 130191714058854510083363)
            ·
              refine ⟨195287571088281765125045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130191714058854510083363 195287571088281765125045)
              ·
                refine ⟨18308209789526415480473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 195287571088281765125045 18308209789526415480473)
                ·
                  rfl

theorem cell19_60168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_60168 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_60168 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_60168 prefixEnd_60168 := by exact prefixLift 60168
  have htrace : WordTrace (prefixWord ++ tailWord_60168) baseStart_60168 baseEnd_60168 := by
    simpa [prefixWord, tailWord_60168, baseEnd_60168] using wordTrace_append hprefix tailTrace_60168
  have hstable : (prefixWord ++ tailWord_60168).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60168).length < 2 ^ (prefixWord ++ tailWord_60168).sum := by decide
  have hdescent : baseEnd_60168 < baseStart_60168 := by decide
  rcases family_descends (prefixWord ++ tailWord_60168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60202 : List Nat := [3, 1, 4, 3, 1, 1, 2, 4]
def baseStart_60202 : Nat := 118140960795 + 60202 * 2 ^ 59
def prefixEnd_60202 : Nat := 4983230072969 + 3 ^ 40 * 60202 * 2
def baseEnd_60202 : Nat := 18318555473824410724825

theorem tailTrace_60202 : CollatzResearch.WordTrace tailWord_60202 prefixEnd_60202 18318555473824410724825 := by
  unfold tailWord_60202
  simp only [CollatzResearch.WordTrace]
  refine ⟨548936831976477632035715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1463831551937273685428573 548936831976477632035715)
  ·
    refine ⟨823405247964716448053573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 548936831976477632035715 823405247964716448053573)
    ·
      refine ⟨154388483993384334010045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 823405247964716448053573 154388483993384334010045)
      ·
        refine ⟨57895681497519125253767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154388483993384334010045 57895681497519125253767)
        ·
          refine ⟨86843522246278687880651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57895681497519125253767 86843522246278687880651)
          ·
            refine ⟨130265283369418031820977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86843522246278687880651 130265283369418031820977)
            ·
              refine ⟨97698962527063523865733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130265283369418031820977 97698962527063523865733)
              ·
                refine ⟨18318555473824410724825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97698962527063523865733 18318555473824410724825)
                ·
                  rfl

theorem cell19_60202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_60202 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_60202 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_60202 prefixEnd_60202 := by exact prefixLift 60202
  have htrace : WordTrace (prefixWord ++ tailWord_60202) baseStart_60202 baseEnd_60202 := by
    simpa [prefixWord, tailWord_60202, baseEnd_60202] using wordTrace_append hprefix tailTrace_60202
  have hstable : (prefixWord ++ tailWord_60202).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60202).length < 2 ^ (prefixWord ++ tailWord_60202).sum := by decide
  have hdescent : baseEnd_60202 < baseStart_60202 := by decide
  rcases family_descends (prefixWord ++ tailWord_60202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60227 : List Nat := [1, 1, 1, 3, 1, 4, 1, 7]
def baseStart_60227 : Nat := 118140960795 + 60227 * 2 ^ 59
def prefixEnd_60227 : Nat := 4983230072969 + 3 ^ 40 * 60227 * 2
def baseEnd_60227 : Nat := 18326162594631760169201

theorem tailTrace_60227 : CollatzResearch.WordTrace tailWord_60227 prefixEnd_60227 18326162594631760169201 := by
  unfold tailWord_60227
  simp only [CollatzResearch.WordTrace]
  refine ⟨2196659152815339797802935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1464439435210226531868623 2196659152815339797802935)
  ·
    refine ⟨3294988729223009696704403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2196659152815339797802935 3294988729223009696704403)
    ·
      refine ⟨4942483093834514545056605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3294988729223009696704403 4942483093834514545056605)
      ·
        refine ⟨1853431160187942954396227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4942483093834514545056605 1853431160187942954396227)
        ·
          refine ⟨2780146740281914431594341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1853431160187942954396227 2780146740281914431594341)
          ·
            refine ⟨521277513802858955923939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2780146740281914431594341 521277513802858955923939)
            ·
              refine ⟨781916270704288433885909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521277513802858955923939 781916270704288433885909)
              ·
                refine ⟨18326162594631760169201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 781916270704288433885909 18326162594631760169201)
                ·
                  rfl

theorem cell19_60227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 7].length) (baseStart_60227 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_60227 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_60227 prefixEnd_60227 := by exact prefixLift 60227
  have htrace : WordTrace (prefixWord ++ tailWord_60227) baseStart_60227 baseEnd_60227 := by
    simpa [prefixWord, tailWord_60227, baseEnd_60227] using wordTrace_append hprefix tailTrace_60227
  have hstable : (prefixWord ++ tailWord_60227).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60227).length < 2 ^ (prefixWord ++ tailWord_60227).sum := by decide
  have hdescent : baseEnd_60227 < baseStart_60227 := by decide
  rcases family_descends (prefixWord ++ tailWord_60227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60244 : List Nat := [2, 4, 1, 1, 4, 7]
def baseStart_60244 : Nat := 118140960795 + 60244 * 2 ^ 59
def prefixEnd_60244 : Nat := 4983230072969 + 3 ^ 40 * 60244 * 2
def baseEnd_60244 : Nat := 2036815048531195310153

theorem tailTrace_60244 : CollatzResearch.WordTrace tailWord_60244 prefixEnd_60244 2036815048531195310153 := by
  unfold tailWord_60244
  simp only [CollatzResearch.WordTrace]
  refine ⟨1098639596876875850585893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1464852795835834467447857 1098639596876875850585893)
  ·
    refine ⟨205994924414414221984855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1098639596876875850585893 205994924414414221984855)
    ·
      refine ⟨308992386621621332977283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205994924414414221984855 308992386621621332977283)
      ·
        refine ⟨463488579932431999465925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308992386621621332977283 463488579932431999465925)
        ·
          refine ⟨86904108737330999899861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 463488579932431999465925 86904108737330999899861)
          ·
            refine ⟨2036815048531195310153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 86904108737330999899861 2036815048531195310153)
            ·
              rfl

theorem cell19_60244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 7].length) (baseStart_60244 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_60244 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_60244 prefixEnd_60244 := by exact prefixLift 60244
  have htrace : WordTrace (prefixWord ++ tailWord_60244) baseStart_60244 baseEnd_60244 := by
    simpa [prefixWord, tailWord_60244, baseEnd_60244] using wordTrace_append hprefix tailTrace_60244
  have hstable : (prefixWord ++ tailWord_60244).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60244).length < 2 ^ (prefixWord ++ tailWord_60244).sum := by decide
  have hdescent : baseEnd_60244 < baseStart_60244 := by decide
  rcases family_descends (prefixWord ++ tailWord_60244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60263 : List Nat := [1, 1, 5, 1, 2, 2, 3, 4]
def baseStart_60263 : Nat := 118140960795 + 60263 * 2 ^ 59
def prefixEnd_60263 : Nat := 4983230072969 + 3 ^ 40 * 60263 * 2
def baseEnd_60263 : Nat := 18337116848594343369103

theorem tailTrace_60263 : CollatzResearch.WordTrace tailWord_60263 prefixEnd_60263 18337116848594343369103 := by
  unfold tailWord_60263
  simp only [CollatzResearch.WordTrace]
  refine ⟨2197972180684917946113443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1465314787123278630742295 2197972180684917946113443)
  ·
    refine ⟨3296958271027376919170165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2197972180684917946113443 3296958271027376919170165)
    ·
      refine ⟨309089837908816586172203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3296958271027376919170165 309089837908816586172203)
      ·
        refine ⟨463634756863224879258305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309089837908816586172203 463634756863224879258305)
        ·
          refine ⟨347726067647418659443729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 463634756863224879258305 347726067647418659443729)
          ·
            refine ⟨260794550735563994582797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347726067647418659443729 260794550735563994582797)
            ·
              refine ⟨97797956525836497968549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260794550735563994582797 97797956525836497968549)
              ·
                refine ⟨18337116848594343369103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97797956525836497968549 18337116848594343369103)
                ·
                  rfl

theorem cell19_60263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 4].length) (baseStart_60263 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_60263 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_60263 prefixEnd_60263 := by exact prefixLift 60263
  have htrace : WordTrace (prefixWord ++ tailWord_60263) baseStart_60263 baseEnd_60263 := by
    simpa [prefixWord, tailWord_60263, baseEnd_60263] using wordTrace_append hprefix tailTrace_60263
  have hstable : (prefixWord ++ tailWord_60263).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60263).length < 2 ^ (prefixWord ++ tailWord_60263).sum := by decide
  have hdescent : baseEnd_60263 < baseStart_60263 := by decide
  rcases family_descends (prefixWord ++ tailWord_60263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60278 : List Nat := [5, 1, 1, 3, 1, 2, 3, 3]
def baseStart_60278 : Nat := 118140960795 + 60278 * 2 ^ 59
def prefixEnd_60278 : Nat := 4983230072969 + 3 ^ 40 * 60278 * 2
def baseEnd_60278 : Nat := 18341681121078753035729

theorem tailTrace_60278 : CollatzResearch.WordTrace tailWord_60278 prefixEnd_60278 18341681121078753035729 := by
  unfold tailWord_60278
  simp only [CollatzResearch.WordTrace]
  refine ⟨137407454726910969244343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1465679517087050338606325 137407454726910969244343)
  ·
    refine ⟨206111182090366453866515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137407454726910969244343 206111182090366453866515)
    ·
      refine ⟨309166773135549680799773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206111182090366453866515 309166773135549680799773)
      ·
        refine ⟨115937539925831130299915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309166773135549680799773 115937539925831130299915)
        ·
          refine ⟨173906309888746695449873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115937539925831130299915 173906309888746695449873)
          ·
            refine ⟨130429732416560021587405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173906309888746695449873 130429732416560021587405)
            ·
              refine ⟨48911149656210008095277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130429732416560021587405 48911149656210008095277)
              ·
                refine ⟨18341681121078753035729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48911149656210008095277 18341681121078753035729)
                ·
                  rfl

theorem cell19_60278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_60278 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_60278 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_60278 prefixEnd_60278 := by exact prefixLift 60278
  have htrace : WordTrace (prefixWord ++ tailWord_60278) baseStart_60278 baseEnd_60278 := by
    simpa [prefixWord, tailWord_60278, baseEnd_60278] using wordTrace_append hprefix tailTrace_60278
  have hstable : (prefixWord ++ tailWord_60278).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60278).length < 2 ^ (prefixWord ++ tailWord_60278).sum := by decide
  have hdescent : baseEnd_60278 < baseStart_60278 := by decide
  rcases family_descends (prefixWord ++ tailWord_60278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60284 : List Nat := [2, 2, 2, 1, 1, 1, 1, 9]
def baseStart_60284 : Nat := 118140960795 + 60284 * 2 ^ 59
def prefixEnd_60284 : Nat := 4983230072969 + 3 ^ 40 * 60284 * 2
def baseEnd_60284 : Nat := 18343506830072516902379

theorem tailTrace_60284 : CollatzResearch.WordTrace tailWord_60284 prefixEnd_60284 18343506830072516902379 := by
  unfold tailWord_60284
  simp only [CollatzResearch.WordTrace]
  refine ⟨1099369056804419266313953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1465825409072559021751937 1099369056804419266313953)
  ·
    refine ⟨824526792603314449735465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1099369056804419266313953 824526792603314449735465)
    ·
      refine ⟨618395094452485837301599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 824526792603314449735465 618395094452485837301599)
      ·
        refine ⟨927592641678728755952399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618395094452485837301599 927592641678728755952399)
        ·
          refine ⟨1391388962518093133928599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 927592641678728755952399 1391388962518093133928599)
          ·
            refine ⟨2087083443777139700892899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1391388962518093133928599 2087083443777139700892899)
            ·
              refine ⟨3130625165665709551339349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2087083443777139700892899 3130625165665709551339349)
              ·
                refine ⟨18343506830072516902379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3130625165665709551339349 18343506830072516902379)
                ·
                  rfl

theorem cell19_60284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_60284 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_60284 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_60284 prefixEnd_60284 := by exact prefixLift 60284
  have htrace : WordTrace (prefixWord ++ tailWord_60284) baseStart_60284 baseEnd_60284 := by
    simpa [prefixWord, tailWord_60284, baseEnd_60284] using wordTrace_append hprefix tailTrace_60284
  have hstable : (prefixWord ++ tailWord_60284).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60284).length < 2 ^ (prefixWord ++ tailWord_60284).sum := by decide
  have hdescent : baseEnd_60284 < baseStart_60284 := by decide
  rcases family_descends (prefixWord ++ tailWord_60284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60333 : List Nat := [1, 5, 2, 3, 1, 2, 2, 3]
def baseStart_60333 : Nat := 118140960795 + 60333 * 2 ^ 59
def prefixEnd_60333 : Nat := 4983230072969 + 3 ^ 40 * 60333 * 2
def baseEnd_60333 : Nat := 18358416786854921813357

theorem tailTrace_60333 : CollatzResearch.WordTrace tailWord_60333 prefixEnd_60333 18358416786854921813357 := by
  unfold tailWord_60333
  simp only [CollatzResearch.WordTrace]
  refine ⟨2200525290431319901161653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1467016860287546600774435 2200525290431319901161653)
  ·
    refine ⟨206299245977936240733905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2200525290431319901161653 206299245977936240733905)
    ·
      refine ⟨154724434483452180550429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206299245977936240733905 154724434483452180550429)
      ·
        refine ⟨58021662931294567706411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154724434483452180550429 58021662931294567706411)
        ·
          refine ⟨87032494396941851559617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58021662931294567706411 87032494396941851559617)
          ·
            refine ⟨65274370797706388669713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87032494396941851559617 65274370797706388669713)
            ·
              refine ⟨48955778098279791502285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65274370797706388669713 48955778098279791502285)
              ·
                refine ⟨18358416786854921813357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48955778098279791502285 18358416786854921813357)
                ·
                  rfl

theorem cell19_60333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 3].length) (baseStart_60333 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_60333 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_60333 prefixEnd_60333 := by exact prefixLift 60333
  have htrace : WordTrace (prefixWord ++ tailWord_60333) baseStart_60333 baseEnd_60333 := by
    simpa [prefixWord, tailWord_60333, baseEnd_60333] using wordTrace_append hprefix tailTrace_60333
  have hstable : (prefixWord ++ tailWord_60333).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60333).length < 2 ^ (prefixWord ++ tailWord_60333).sum := by decide
  have hdescent : baseEnd_60333 < baseStart_60333 := by decide
  rcases family_descends (prefixWord ++ tailWord_60333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60377 : List Nat := [1, 2, 1, 2, 5, 2, 2, 4]
def baseStart_60377 : Nat := 118140960795 + 60377 * 2 ^ 59
def prefixEnd_60377 : Nat := 4983230072969 + 3 ^ 40 * 60377 * 2
def baseEnd_60377 : Nat := 18371805319475856835459

theorem tailTrace_60377 : CollatzResearch.WordTrace tailWord_60377 prefixEnd_60377 18371805319475856835459 := by
  unfold tailWord_60377
  simp only [CollatzResearch.WordTrace]
  refine ⟨2202130102271915415763385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1468086734847943610508923 2202130102271915415763385)
  ·
    refine ⟨1651597576703936561822539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2202130102271915415763385 1651597576703936561822539)
    ·
      refine ⟨2477396365055904842733809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1651597576703936561822539 2477396365055904842733809)
      ·
        refine ⟨1858047273791928632050357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2477396365055904842733809 1858047273791928632050357)
        ·
          refine ⟨174191931917993309254721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1858047273791928632050357 174191931917993309254721)
          ·
            refine ⟨130643948938494981941041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174191931917993309254721 130643948938494981941041)
            ·
              refine ⟨97982961703871236455781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130643948938494981941041 97982961703871236455781)
              ·
                refine ⟨18371805319475856835459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97982961703871236455781 18371805319475856835459)
                ·
                  rfl

theorem cell19_60377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 4].length) (baseStart_60377 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_60377 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_60377 prefixEnd_60377 := by exact prefixLift 60377
  have htrace : WordTrace (prefixWord ++ tailWord_60377) baseStart_60377 baseEnd_60377 := by
    simpa [prefixWord, tailWord_60377, baseEnd_60377] using wordTrace_append hprefix tailTrace_60377
  have hstable : (prefixWord ++ tailWord_60377).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60377).length < 2 ^ (prefixWord ++ tailWord_60377).sum := by decide
  have hdescent : baseEnd_60377 < baseStart_60377 := by decide
  rcases family_descends (prefixWord ++ tailWord_60377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60417 : List Nat := [1, 2, 4, 1, 2, 9]
def baseStart_60417 : Nat := 118140960795 + 60417 * 2 ^ 59
def prefixEnd_60417 : Nat := 4983230072969 + 3 ^ 40 * 60417 * 2
def baseEnd_60417 : Nat := 2042664079196401771829

theorem tailTrace_60417 : CollatzResearch.WordTrace tailWord_60417 prefixEnd_60417 2042664079196401771829 := by
  unfold tailWord_60417
  simp only [CollatzResearch.WordTrace]
  refine ⟨2203589022127002247219505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1469059348084668164813003 2203589022127002247219505)
  ·
    refine ⟨1652691766595251685414629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2203589022127002247219505 1652691766595251685414629)
    ·
      refine ⟨309879706236609691015243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1652691766595251685414629 309879706236609691015243)
      ·
        refine ⟨464819559354914536522865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309879706236609691015243 464819559354914536522865)
        ·
          refine ⟨348614669516185902392149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464819559354914536522865 348614669516185902392149)
          ·
            refine ⟨2042664079196401771829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 348614669516185902392149 2042664079196401771829)
            ·
              rfl

theorem cell19_60417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 9].length) (baseStart_60417 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_60417 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_60417 prefixEnd_60417 := by exact prefixLift 60417
  have htrace : WordTrace (prefixWord ++ tailWord_60417) baseStart_60417 baseEnd_60417 := by
    simpa [prefixWord, tailWord_60417, baseEnd_60417] using wordTrace_append hprefix tailTrace_60417
  have hstable : (prefixWord ++ tailWord_60417).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60417).length < 2 ^ (prefixWord ++ tailWord_60417).sum := by decide
  have hdescent : baseEnd_60417 < baseStart_60417 := by decide
  rcases family_descends (prefixWord ++ tailWord_60417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60453 : List Nat := [1, 3, 1, 2, 2, 2, 5, 3]
def baseStart_60453 : Nat := 118140960795 + 60453 * 2 ^ 59
def prefixEnd_60453 : Nat := 4983230072969 + 3 ^ 40 * 60453 * 2
def baseEnd_60453 : Nat := 18394930966730199146363

theorem tailTrace_60453 : CollatzResearch.WordTrace tailWord_60453 prefixEnd_60453 18394930966730199146363 := by
  unfold tailWord_60453
  simp only [CollatzResearch.WordTrace]
  refine ⟨2204902049996580395530013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1469934699997720263686675 2204902049996580395530013)
  ·
    refine ⟨826838268748717648323755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2204902049996580395530013 826838268748717648323755)
    ·
      refine ⟨1240257403123076472485633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 826838268748717648323755 1240257403123076472485633)
      ·
        refine ⟨930193052342307354364225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1240257403123076472485633 930193052342307354364225)
        ·
          refine ⟨697644789256730515773169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 930193052342307354364225 697644789256730515773169)
          ·
            refine ⟨523233591942547886829877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 697644789256730515773169 523233591942547886829877)
            ·
              refine ⟨49053149244613864390301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 523233591942547886829877 49053149244613864390301)
              ·
                refine ⟨18394930966730199146363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49053149244613864390301 18394930966730199146363)
                ·
                  rfl

theorem cell19_60453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 3].length) (baseStart_60453 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_60453 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_60453 prefixEnd_60453 := by exact prefixLift 60453
  have htrace : WordTrace (prefixWord ++ tailWord_60453) baseStart_60453 baseEnd_60453 := by
    simpa [prefixWord, tailWord_60453, baseEnd_60453] using wordTrace_append hprefix tailTrace_60453
  have hstable : (prefixWord ++ tailWord_60453).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60453).length < 2 ^ (prefixWord ++ tailWord_60453).sum := by decide
  have hdescent : baseEnd_60453 < baseStart_60453 := by decide
  rcases family_descends (prefixWord ++ tailWord_60453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60502 : List Nat := [5, 2, 2, 1, 3, 1, 2, 3]
def baseStart_60502 : Nat := 118140960795 + 60502 * 2 ^ 59
def prefixEnd_60502 : Nat := 4983230072969 + 3 ^ 40 * 60502 * 2
def baseEnd_60502 : Nat := 18409840923512604057341

theorem tailTrace_60502 : CollatzResearch.WordTrace tailWord_60502 prefixEnd_60502 18409840923512604057341 := by
  unfold tailWord_60502
  simp only [CollatzResearch.WordTrace]
  refine ⟨137918076676191360253985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1471126151212707842709173 137918076676191360253985)
  ·
    refine ⟨103438557507143520190489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137918076676191360253985 103438557507143520190489)
    ·
      refine ⟨77578918130357640142867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103438557507143520190489 77578918130357640142867)
      ·
        refine ⟨116368377195536460214301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77578918130357640142867 116368377195536460214301)
        ·
          refine ⟨43638141448326172580363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116368377195536460214301 43638141448326172580363)
          ·
            refine ⟨65457212172489258870545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43638141448326172580363 65457212172489258870545)
            ·
              refine ⟨49092909129366944152909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65457212172489258870545 49092909129366944152909)
              ·
                refine ⟨18409840923512604057341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49092909129366944152909 18409840923512604057341)
                ·
                  rfl

theorem cell19_60502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_60502 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_60502 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_60502 prefixEnd_60502 := by exact prefixLift 60502
  have htrace : WordTrace (prefixWord ++ tailWord_60502) baseStart_60502 baseEnd_60502 := by
    simpa [prefixWord, tailWord_60502, baseEnd_60502] using wordTrace_append hprefix tailTrace_60502
  have hstable : (prefixWord ++ tailWord_60502).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60502).length < 2 ^ (prefixWord ++ tailWord_60502).sum := by decide
  have hdescent : baseEnd_60502 < baseStart_60502 := by decide
  rcases family_descends (prefixWord ++ tailWord_60502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60512 : List Nat := [2, 1, 1, 3, 2, 2, 3, 5]
def baseStart_60512 : Nat := 118140960795 + 60512 * 2 ^ 59
def prefixEnd_60512 : Nat := 4983230072969 + 3 ^ 40 * 60512 * 2
def baseEnd_60512 : Nat := 18412883771835543835091

theorem tailTrace_60512 : CollatzResearch.WordTrace tailWord_60512 prefixEnd_60512 18412883771835543835091 := by
  unfold tailWord_60512
  simp only [CollatzResearch.WordTrace]
  refine ⟨1103526978391416735963895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1471369304521888981285193 1103526978391416735963895)
  ·
    refine ⟨1655290467587125103945843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1103526978391416735963895 1655290467587125103945843)
    ·
      refine ⟨2482935701380687655918765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1655290467587125103945843 2482935701380687655918765)
      ·
        refine ⟨931100888017757870969537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2482935701380687655918765 931100888017757870969537)
        ·
          refine ⟨698325666013318403227153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 931100888017757870969537 698325666013318403227153)
          ·
            refine ⟨523744249509988802420365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 698325666013318403227153 523744249509988802420365)
            ·
              refine ⟨196404093566245800907637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 523744249509988802420365 196404093566245800907637)
              ·
                refine ⟨18412883771835543835091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 196404093566245800907637 18412883771835543835091)
                ·
                  rfl

theorem cell19_60512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_60512 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_60512 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_60512 prefixEnd_60512 := by exact prefixLift 60512
  have htrace : WordTrace (prefixWord ++ tailWord_60512) baseStart_60512 baseEnd_60512 := by
    simpa [prefixWord, tailWord_60512, baseEnd_60512] using wordTrace_append hprefix tailTrace_60512
  have hstable : (prefixWord ++ tailWord_60512).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60512).length < 2 ^ (prefixWord ++ tailWord_60512).sum := by decide
  have hdescent : baseEnd_60512 < baseStart_60512 := by decide
  rcases family_descends (prefixWord ++ tailWord_60512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60542 : List Nat := [4, 2, 4, 1, 1, 1, 2, 4]
def baseStart_60542 : Nat := 118140960795 + 60542 * 2 ^ 59
def prefixEnd_60542 : Nat := 4983230072969 + 3 ^ 40 * 60542 * 2
def baseEnd_60542 : Nat := 18422012316804363168343

theorem tailTrace_60542 : CollatzResearch.WordTrace tailWord_60542 prefixEnd_60542 18422012316804363168343 := by
  unfold tailWord_60542
  simp only [CollatzResearch.WordTrace]
  refine ⟨276018518334268574439985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1472098764449432397013253 276018518334268574439985)
  ·
    refine ⟨207013888750701430829989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276018518334268574439985 207013888750701430829989)
    ·
      refine ⟨38815104140756518280623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207013888750701430829989 38815104140756518280623)
      ·
        refine ⟨58222656211134777420935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38815104140756518280623 58222656211134777420935)
        ·
          refine ⟨87333984316702166131403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58222656211134777420935 87333984316702166131403)
          ·
            refine ⟨131000976475053249197105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87333984316702166131403 131000976475053249197105)
            ·
              refine ⟨98250732356289936897829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131000976475053249197105 98250732356289936897829)
              ·
                refine ⟨18422012316804363168343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98250732356289936897829 18422012316804363168343)
                ·
                  rfl

theorem cell19_60542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_60542 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_60542 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_60542 prefixEnd_60542 := by exact prefixLift 60542
  have htrace : WordTrace (prefixWord ++ tailWord_60542) baseStart_60542 baseEnd_60542 := by
    simpa [prefixWord, tailWord_60542, baseEnd_60542] using wordTrace_append hprefix tailTrace_60542
  have hstable : (prefixWord ++ tailWord_60542).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60542).length < 2 ^ (prefixWord ++ tailWord_60542).sum := by decide
  have hdescent : baseEnd_60542 < baseStart_60542 := by decide
  rcases family_descends (prefixWord ++ tailWord_60542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60548 : List Nat := [2, 3, 2, 1, 2, 3, 2, 4]
def baseStart_60548 : Nat := 118140960795 + 60548 * 2 ^ 59
def prefixEnd_60548 : Nat := 4983230072969 + 3 ^ 40 * 60548 * 2
def baseEnd_60548 : Nat := 18423838025798127034993

theorem tailTrace_60548 : CollatzResearch.WordTrace tailWord_60548 prefixEnd_60548 18423838025798127034993 := by
  unfold tailWord_60548
  simp only [CollatzResearch.WordTrace]
  refine ⟨1104183492326205810119149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1472244656434941080158865 1104183492326205810119149)
  ·
    refine ⟨414068809622327178794681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1104183492326205810119149 414068809622327178794681)
    ·
      refine ⟨310551607216745384096011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414068809622327178794681 310551607216745384096011)
      ·
        refine ⟨465827410825118076144017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310551607216745384096011 465827410825118076144017)
        ·
          refine ⟨349370558118838557108013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 465827410825118076144017 349370558118838557108013)
          ·
            refine ⟨131013959294564458915505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 349370558118838557108013 131013959294564458915505)
            ·
              refine ⟨98260469470923344186629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131013959294564458915505 98260469470923344186629)
              ·
                refine ⟨18423838025798127034993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98260469470923344186629 18423838025798127034993)
                ·
                  rfl

theorem cell19_60548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_60548 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_60548 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_60548 prefixEnd_60548 := by exact prefixLift 60548
  have htrace : WordTrace (prefixWord ++ tailWord_60548) baseStart_60548 baseEnd_60548 := by
    simpa [prefixWord, tailWord_60548, baseEnd_60548] using wordTrace_append hprefix tailTrace_60548
  have hstable : (prefixWord ++ tailWord_60548).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60548).length < 2 ^ (prefixWord ++ tailWord_60548).sum := by decide
  have hdescent : baseEnd_60548 < baseStart_60548 := by decide
  rcases family_descends (prefixWord ++ tailWord_60548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
